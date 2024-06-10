{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
module Language.Haskell.Syntax.Basic where

import Prelude
import Data.Data

import GHC.Data.FastString (FastString)
import Control.DeepSeq

{-
************************************************************************
*                                                                      *
Boxity
*                                                                      *
************************************************************************
-}

data Boxity
  = Boxed
  | Unboxed
  deriving( Eq, Data )

isBoxed :: Boxity -> Bool
isBoxed Boxed   = True
isBoxed Unboxed = False

{-
************************************************************************
*                                                                      *
Counts and indices
*                                                                      *
************************************************************************
-}

-- | The width of an unboxed sum
type SumWidth = Int

-- | A *one-index* constructor tag
--
-- Type of the tags associated with each constructor possibility or superclass
-- selector
type ConTag = Int

{-
************************************************************************
*                                                                      *
Field Labels
*                                                                      *
************************************************************************
-}

-- | Field labels are just represented as strings;
-- they are not necessarily unique (even within a module)
newtype FieldLabelString = FieldLabelString { field_label:: FastString }
  deriving (Data, Eq, NFData)

{-
************************************************************************
*                                                                      *
Field Labels
*                                                                      *
************************************************************************
-}

-- | See Note [Roles] in GHC.Core.Coercion
--
-- Order of constructors matters: the Ord instance coincides with the *super*typing
-- relation on roles.
data Role = Nominal | Representational | Phantom
  deriving (Eq, Ord, Data)

{-
************************************************************************
*                                                                      *
Source Strictness and Unpackedness
*                                                                      *
************************************************************************
-}

-- | Source Strictness
--
-- What strictness annotation the user wrote
data SrcStrictness = SrcLazy -- ^ Lazy, ie '~'
                   | SrcStrict -- ^ Strict, ie '!'
                   | NoSrcStrict -- ^ no strictness annotation
     deriving (Eq, Data)

-- | Source Unpackedness
--
-- What unpackedness the user requested
data SrcUnpackedness = SrcUnpack -- ^ {-# UNPACK #-} specified
                     | SrcNoUnpack -- ^ {-# NOUNPACK #-} specified
                     | NoSrcUnpack -- ^ no unpack pragma
     deriving (Eq, Data)


{-
************************************************************************
*                                                                      *
Top-level/not-top level flag
*                                                                      *
************************************************************************
-}

data TopLevelFlag
  = TopLevel
  | NotTopLevel
  deriving Data

isTopLevel, isNotTopLevel :: TopLevelFlag -> Bool

isNotTopLevel NotTopLevel = True
isNotTopLevel TopLevel    = False

isTopLevel TopLevel     = True
isTopLevel NotTopLevel  = False

-- | Whether something is a type or a data declaration,
-- e.g. a type family or a data family.
data TypeOrData
  = IAmData
  | IAmType
  deriving (Eq, Data)

-- | Paints a picture of what a 'TyCon' represents, in broad strokes.
-- This is used towards more informative error messages.
data TyConFlavour tc
  = ClassFlavour
  | TupleFlavour Boxity
  | SumFlavour
  | DataTypeFlavour
  | NewtypeFlavour
  | AbstractTypeFlavour
  | OpenFamilyFlavour TypeOrData (Maybe tc) -- Just tc <=> (tc == associated class)
  | ClosedTypeFamilyFlavour
  | TypeSynonymFlavour
  | BuiltInTypeFlavour -- ^ e.g., the @(->)@ 'TyCon'.
  | PromotedDataConFlavour
  deriving (Eq, Data, Functor)
