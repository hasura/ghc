{-# LANGUAGE CPP #-}
#if MIN_TOOL_VERSION_ghc(9,5,0)
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GHCForeignImportPrim #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UnliftedFFITypes #-}

-- TODO: Find better place than top level. Re-export from top-level?
module GHC.Exts.DecodeStack
  ( decodeStack,
    unpackStackFrameIter
  )
where

import Data.Bits
import Data.Maybe
-- TODO: Remove before releasing
import Debug.Trace
import Foreign
import GHC.Exts
import GHC.Exts.Heap.ClosureTypes
import GHC.Exts.Heap.Closures
import GHC.Exts.Heap.Constants (wORD_SIZE_IN_BITS)
import GHC.Exts.Heap.InfoTable
import GHC.Exts.StackConstants
import GHC.Stack.CloneStack
import Prelude

{- Note [Decoding the stack]
   ~~~~~~~~~~~~~~~~~~~~~~~~~

The stack is represented by a chain of StgStack closures. Each of these closures
is subject to garbage collection. I.e. they can be moved in memory (in a
simplified perspective) at any time.

The array of closures inside an StgStack (that makeup the execution stack; the
stack frames) is moved as bare memory by the garbage collector. References
(pointers) to stack frames are not updated.

As the StgStack closure is moved as whole, the relative offsets inside it stay
the same. (Though, the absolute addresses change!)

Stack frame iterator
====================

A StackFrameIter consists of a StackSnapshot# and a relative offset into the the
array of stack frames (StgStack->stack). The StackSnapshot# represents a
StgStack closure. It is updated by the garbage collector when the stack closure
is moved.

The relative offset describes the location of a stack frame. As stack frames
come in various sizes, one cannot simply step over the stack array with a
constant offset.

The head of the stack frame array has offset 0. To traverse the stack frames the
latest stacke frame's offset is incremented by the closure size. The unit of the
offset is machine words (32bit or 64bit).

Boxes
=====

As references into thestack frame array aren't updated by the garbage collector,
creating a Box with a pointer (address) to a stack frame would break as soon as
the StgStack closure is moved.

To deal with this another kind of Box is introduced: A DecodedBox contains a
thunk for a decoded stack frame or the closure for the decoded stack frame
itself. I.e. we're not boxing the closure, but the ghc-heap representation of
it.

Heap-represented closures referenced by stack frames are boxed the usual way,
with a Box that contains a pointer to the closure.

Technical details
=================

- All access to StgStack/StackSnapshot# closures is made through Cmm code. This
  keeps the closure from being moved by the garbage collector during the
  operation.

- As StgStacks are mainly used in Cmm and C code, much of the decoding logic is
  implemented in Cmm and C. It's just easier to reuse existing helper macros and
  functions, than reinventing them in Haskell.

- Offsets and sizes of closures are imported from DerivedConstants.h via HSC.
  This keeps the code very portable.
-}

foreign import prim "derefStackWordzh" derefStackWord# :: StackSnapshot# -> Word# -> Word#

derefStackWord :: StackFrameIter -> Word
derefStackWord (StackFrameIter {..}) = W# (derefStackWord# stackSnapshot# (wordOffsetToWord# index))

foreign import prim "getUpdateFrameTypezh" getUpdateFrameType# :: StackSnapshot# -> Word# -> Word#

getUpdateFrameType :: StackFrameIter -> UpdateFrameType
getUpdateFrameType (StackFrameIter {..}) = (toEnum . fromInteger . toInteger) (W# (getUpdateFrameType# stackSnapshot# (wordOffsetToWord# index)))

foreign import prim "getUnderflowFrameNextChunkzh" getUnderflowFrameNextChunk# :: StackSnapshot# -> Word# -> StackSnapshot#

getUnderflowFrameNextChunk :: StackFrameIter -> StackSnapshot
getUnderflowFrameNextChunk (StackFrameIter {..}) = StackSnapshot s#
  where
    s# = getUnderflowFrameNextChunk# stackSnapshot# (wordOffsetToWord# index)

foreign import prim "getWordzh" getWord# :: StackSnapshot# -> Word# -> Word# -> Word#

foreign import prim "getAddrzh" getAddr# :: StackSnapshot# -> Word# -> Addr#

getWord :: StackFrameIter -> WordOffset -> Word
getWord (StackFrameIter {..}) relativeOffset = W# (getWord# stackSnapshot# (wordOffsetToWord# index) (wordOffsetToWord# relativeOffset))

foreign import prim "getRetFunTypezh" getRetFunType# :: StackSnapshot# -> Word# -> Word#

getRetFunType :: StackFrameIter -> RetFunType
getRetFunType (StackFrameIter {..}) = (toEnum . fromInteger . toInteger) (W# (getRetFunType# stackSnapshot# (wordOffsetToWord# index)))

foreign import prim "getLargeBitmapzh" getLargeBitmap# :: StackSnapshot# -> Word# -> (# ByteArray#, Word# #)

foreign import prim "getBCOLargeBitmapzh" getBCOLargeBitmap# :: StackSnapshot# -> Word# -> (# ByteArray#, Word# #)

foreign import prim "getRetFunLargeBitmapzh" getRetFunLargeBitmap# :: StackSnapshot# -> Word# -> (# ByteArray#, Word# #)

foreign import prim "getSmallBitmapzh" getSmallBitmap# :: StackSnapshot# -> Word# -> (# Word#, Word# #)

foreign import prim "getRetSmallSpecialTypezh" getRetSmallSpecialType# :: StackSnapshot# -> Word# -> Word#

getRetSmallSpecialType :: StackFrameIter -> SpecialRetSmall
getRetSmallSpecialType (StackFrameIter {..}) =
  let special# = getRetSmallSpecialType# stackSnapshot# (wordOffsetToWord# index)
   in (toEnum . fromInteger . toInteger) (W# special#)

foreign import prim "getRetFunSmallBitmapzh" getRetFunSmallBitmap# :: StackSnapshot# -> Word# -> (# Word#, Word# #)

foreign import prim "advanceStackFrameIterzh" advanceStackFrameIter# :: StackSnapshot# -> Word# -> (# StackSnapshot#, Word#, Int# #)

foreign import prim "getInfoTableAddrzh" getInfoTableAddr# :: StackSnapshot# -> Word# -> Addr#

getInfoTable :: StackFrameIter -> IO StgInfoTable
getInfoTable StackFrameIter {..} =
  let infoTablePtr = Ptr (getInfoTableAddr# stackSnapshot# (wordOffsetToWord# index))
   in peekItbl infoTablePtr

foreign import prim "getBoxedClosurezh" getBoxedClosure# :: StackSnapshot# -> Word# -> Any

-- -- TODO: Remove this instance (debug only)
-- instance Show StackFrameIter where
--   show (StackFrameIter {..}) = "StackFrameIter " ++ "(StackSnapshot _" ++ " " ++ show index

-- | Get an interator starting with the top-most stack frame
stackHead :: StackSnapshot -> StackFrameIter
stackHead (StackSnapshot s) = StackFrameIter s 0 False -- GHC stacks are never empty

-- | Advance iterator to the next stack frame (if any)
advanceStackFrameIter :: StackFrameIter -> Maybe StackFrameIter
advanceStackFrameIter (StackFrameIter {..}) =
  let !(# s', i', hasNext #) = advanceStackFrameIter# stackSnapshot# (wordOffsetToWord# index)
   in if (I# hasNext) > 0
        then Just $ StackFrameIter s' (primWordToWordOffset i') False
        else Nothing

primWordToWordOffset :: Word# -> WordOffset
primWordToWordOffset w# = fromIntegral (W# w#)

-- TODO: can be just StackFrameIter
data BitmapEntry = BitmapEntry
  { closureFrame :: StackFrameIter }

wordsToBitmapEntries :: StackFrameIter -> [Word] -> Word -> [BitmapEntry]
wordsToBitmapEntries _ [] 0 = []
wordsToBitmapEntries _ [] i = error $ "Invalid state: Empty list, size " ++ show i
wordsToBitmapEntries _ l 0 = error $ "Invalid state: Size 0, list " ++ show l
wordsToBitmapEntries sfi (b : bs) bitmapSize =
  let entries = toBitmapEntries sfi b (min bitmapSize (fromIntegral wORD_SIZE_IN_BITS))
      mbLastEntry = (listToMaybe . reverse) entries
      mbLastFrame = fmap closureFrame mbLastEntry
   in case mbLastFrame of
        Just (StackFrameIter {..}) ->
          entries ++ wordsToBitmapEntries (StackFrameIter stackSnapshot# (index + 1) False) bs (subtractDecodedBitmapWord bitmapSize)
        Nothing -> error "This should never happen! Recursion ended not in base case."
  where
    subtractDecodedBitmapWord :: Word -> Word
    subtractDecodedBitmapWord bSize = fromIntegral $ max 0 ((fromIntegral bSize) - wORD_SIZE_IN_BITS)

toBitmapEntries :: StackFrameIter -> Word -> Word -> [BitmapEntry]
toBitmapEntries _ _ 0 = []
toBitmapEntries sfi@(StackFrameIter {..}) bitmapWord bSize =
  -- TODO: overriding isPrimitive field is a bit weird. Could be calculated before
  BitmapEntry
    { closureFrame = sfi {
        isPrimitive = (bitmapWord .&. 1) /= 0
        }
    }
    : toBitmapEntries (StackFrameIter stackSnapshot# (index + 1) False) (bitmapWord `shiftR` 1) (bSize - 1)

toBitmapPayload :: BitmapEntry -> Box
toBitmapPayload e
  | (isPrimitive . closureFrame) e = trace "PRIM" $ StackFrameBox $ (closureFrame e) {
                                      isPrimitive = True
                                     }
toBitmapPayload e = getClosure (closureFrame e) 0

getClosure :: StackFrameIter -> WordOffset -> Box
getClosure StackFrameIter {..} relativeOffset =
  let !c = (getBoxedClosure# stackSnapshot# (wordOffsetToWord# (index + relativeOffset)))
  in
      Box c

decodeLargeBitmap :: (StackSnapshot# -> Word# -> (# ByteArray#, Word# #)) -> StackFrameIter -> WordOffset -> [Box]
decodeLargeBitmap getterFun# sfi@(StackFrameIter {..}) relativePayloadOffset =
  let !(# bitmapArray#, size# #) = getterFun# stackSnapshot# (wordOffsetToWord# index)
      bitmapWords :: [Word] = byteArrayToList bitmapArray#
   in decodeBitmaps sfi relativePayloadOffset bitmapWords (W# size#)

decodeBitmaps :: StackFrameIter -> WordOffset -> [Word] -> Word -> [Box]
decodeBitmaps (StackFrameIter {..}) relativePayloadOffset bitmapWords size =
  let bes = wordsToBitmapEntries (StackFrameIter stackSnapshot# (index + relativePayloadOffset) False) bitmapWords size
   in map toBitmapPayload bes

decodeSmallBitmap :: (StackSnapshot# -> Word# -> (# Word#, Word# #)) -> StackFrameIter -> WordOffset -> [Box]
decodeSmallBitmap getterFun# sfi@(StackFrameIter {..}) relativePayloadOffset =
  let !(# bitmap#, size# #) = getterFun# stackSnapshot# (wordOffsetToWord# index)
      size = W# size#
      bitmapWords = if size > 0 then [(W# bitmap#)] else []
   in decodeBitmaps sfi relativePayloadOffset bitmapWords size

byteArrayToList :: ByteArray# -> [Word]
byteArrayToList bArray = go 0
  where
    go i
      | i < maxIndex = (W# (indexWordArray# bArray (toInt# i))) : (go (i + 1))
      | otherwise = []
    maxIndex = sizeofByteArray bArray `quot` sizeOf (undefined :: Word)

wordOffsetToWord# :: WordOffset -> Word#
wordOffsetToWord# wo = intToWord# (fromIntegral wo)

unpackStackFrameIter :: StackFrameIter -> IO Closure
unpackStackFrameIter sfi | isPrimitive sfi = pure $ UnknownTypeWordSizedPrimitive (getWord sfi 0)
unpackStackFrameIter sfi = do
  info <- getInfoTable sfi
  traceM $ "unpackStackFrameIter - sfi " ++ show sfi
  traceM $ "unpackStackFrameIter - unpacked " ++ show (unpackStackFrameIter' info)
  pure $ unpackStackFrameIter' info
  where
    unpackStackFrameIter' :: StgInfoTable -> Closure
    unpackStackFrameIter' info =
      case tipe info of
        RET_BCO ->
          RetBCO
            { info = info,
              bco = getClosure sfi offsetStgClosurePayload,
              -- The arguments begin directly after the payload's one element
              bcoArgs = decodeLargeBitmap getBCOLargeBitmap# sfi (offsetStgClosurePayload + 1)
            }
        RET_SMALL ->
          trace "RET_SMALL" $
          RetSmall
            { info = info,
              knownRetSmallType = getRetSmallSpecialType sfi,
              payload = decodeSmallBitmap getSmallBitmap# sfi offsetStgClosurePayload
            }
        RET_BIG ->
          RetBig
            { info = info,
              payload = decodeLargeBitmap getLargeBitmap# sfi offsetStgClosurePayload
            }
        RET_FUN ->
          RetFun
            { info = info,
              retFunType = getRetFunType sfi,
              retFunSize = getWord sfi offsetStgRetFunFrameSize,
              retFunFun = getClosure sfi offsetStgRetFunFrameFun,
              retFunPayload =
                if getRetFunType sfi == ARG_GEN_BIG
                  then decodeLargeBitmap getRetFunLargeBitmap# sfi offsetStgRetFunFramePayload
                  else decodeSmallBitmap getRetFunSmallBitmap# sfi offsetStgRetFunFramePayload
            }
        UPDATE_FRAME ->
          UpdateFrame
            { info = info,
              knownUpdateFrameType = getUpdateFrameType sfi,
              updatee = getClosure sfi offsetStgUpdateFrameUpdatee
            }
        CATCH_FRAME ->
          CatchFrame
            { info = info,
              exceptions_blocked = getWord sfi offsetStgCatchFrameExceptionsBlocked,
              handler = getClosure sfi offsetStgCatchFrameHandler
            }
        UNDERFLOW_FRAME ->
          UnderflowFrame
            { info = info,
              nextChunk = getUnderflowFrameNextChunk sfi
            }
        STOP_FRAME -> StopFrame {info = info}
        ATOMICALLY_FRAME ->
          AtomicallyFrame
            { info = info,
              atomicallyFrameCode = getClosure sfi offsetStgAtomicallyFrameCode,
              result = getClosure sfi offsetStgAtomicallyFrameResult
            }
        CATCH_RETRY_FRAME ->
          CatchRetryFrame
            { info = info,
              running_alt_code = getWord sfi offsetStgCatchRetryFrameRunningAltCode,
              first_code = getClosure sfi offsetStgCatchRetryFrameRunningFirstCode,
              alt_code = getClosure sfi offsetStgCatchRetryFrameAltCode
            }
        CATCH_STM_FRAME ->
          CatchStmFrame
            { info = info,
              catchFrameCode = getClosure sfi offsetStgCatchSTMFrameCode,
              handler = getClosure sfi offsetStgCatchSTMFrameHandler
            }
        x -> error $ "Unexpected closure type on stack: " ++ show x

-- | Size of the byte array in bytes.
-- Copied from `primitive`
sizeofByteArray :: ByteArray# -> Int
{-# INLINE sizeofByteArray #-}
sizeofByteArray arr# = I# (sizeofByteArray# arr#)

-- | Unbox 'Int#' from 'Int'
toInt# :: Int -> Int#
toInt# (I# i) = i

intToWord# :: Int -> Word#
intToWord# i = int2Word# (toInt# i)

decodeStack :: StackSnapshot -> Closure
decodeStack = SimpleStack . decodeStack'

decodeStack' :: StackSnapshot -> [Box]
decodeStack' s = StackFrameBox (stackHead s) : go (advanceStackFrameIter (stackHead s))
  where
    go :: Maybe StackFrameIter -> [Box]
    go Nothing = []
    go (Just sfi) = (StackFrameBox sfi) : go (advanceStackFrameIter sfi)
#else
module GHC.Exts.DecodeStack where
#endif
