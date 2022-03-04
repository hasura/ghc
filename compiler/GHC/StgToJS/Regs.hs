{-# LANGUAGE OverloadedStrings #-}

module GHC.StgToJS.Regs
  ( StgReg (..)
  , Special(..)
  , sp
  , stack
  , r1, r2, r3, r4
  , StgRet (..)
  , jsRegToInt
  , intToJSReg
  , maxReg
  , minReg
  )
where

import GHC.Prelude

import GHC.JS.Syntax
import GHC.JS.Make

import qualified GHC.Data.ShortText as ST

import Data.Array
import Data.Char

-- FIXME: Perf: Jeff (2022,03): as far as I can tell, we never pattern match on
-- these registers and make heavy use of the Enum, Bounded, and Ix, instances.
-- This heavily implies to me that we should be using something like: StgReg =
-- StgReg { unStgReg :: Int8# } and then store two nibbles in a single byte. Not
-- only would this be more memory efficient, but it would also allow for
-- optimizations such as pointer tagging and avoiding chasing the info table,
-- although I'm not sure if this would really benefit the backend as currently
-- written. Other than that a newtype wrapper with a custom bounded instance
-- (hand written or deriving via) would be better. In almost all functions that
-- take an StgReg we use either the Bounded or the Enum methods, thus we likely
-- don't gain anything from having these registers explicitly represented in
-- data constructors.
-- | General purpose "registers"
--
-- The JS backend arbitrarily supports 128 registers
data StgReg
  = R1  | R2  | R3  | R4  | R5  | R6  | R7  | R8
  | R9  | R10 | R11 | R12 | R13 | R14 | R15 | R16
  | R17 | R18 | R19 | R20 | R21 | R22 | R23 | R24
  | R25 | R26 | R27 | R28 | R29 | R30 | R31 | R32
  | R33 | R34 | R35 | R36 | R37 | R38 | R39 | R40
  | R41 | R42 | R43 | R44 | R45 | R46 | R47 | R48
  | R49 | R50 | R51 | R52 | R53 | R54 | R55 | R56
  | R57 | R58 | R59 | R60 | R61 | R62 | R63 | R64
  | R65 | R66 | R67 | R68 | R69 | R70 | R71 | R72
  | R73 | R74 | R75 | R76 | R77 | R78 | R79 | R80
  | R81 | R82 | R83 | R84 | R85 | R86 | R87 | R88
  | R89 | R90 | R91 | R92 | R93 | R94 | R95 | R96
  | R97  | R98  | R99  | R100 | R101 | R102 | R103 | R104
  | R105 | R106 | R107 | R108 | R109 | R110 | R111 | R112
  | R113 | R114 | R115 | R116 | R117 | R118 | R119 | R120
  | R121 | R122 | R123 | R124 | R125 | R126 | R127 | R128
  deriving (Eq, Ord, Show, Enum, Bounded, Ix)

-- | Stack registers
data Special
  = Stack
  | Sp
  deriving (Show, Eq)

-- | Return registers
--
-- Extra results from foreign calls can be stored here (while first result is
-- directly returned)
data StgRet = Ret1 | Ret2 | Ret3 | Ret4 | Ret5 | Ret6 | Ret7 | Ret8 | Ret9 | Ret10
  deriving (Eq, Ord, Show, Enum, Bounded, Ix)

instance ToJExpr Special where
  toJExpr Stack  = var "h$stack"
  toJExpr Sp     = var "h$sp"

instance ToJExpr StgReg where
  toJExpr r = registers ! r

instance ToJExpr StgRet where
  toJExpr r = rets ! r

---------------------------------------------------
-- helpers
---------------------------------------------------

sp :: JExpr
sp = toJExpr Sp

stack :: JExpr
stack = toJExpr Stack

r1, r2, r3, r4 :: JExpr
r1 = toJExpr R1
r2 = toJExpr R2
r3 = toJExpr R3
r4 = toJExpr R4


-- FIXME: Jeff (2022,03): remove these serialization functions after adding a
-- StgReg type with a proper bounded and enum instance
jsRegToInt :: StgReg -> Int
jsRegToInt = (+1) . fromEnum

intToJSReg :: Int -> StgReg
intToJSReg r = toEnum (r - 1)

maxReg :: Int
maxReg = jsRegToInt maxBound

minReg :: Int
minReg = jsRegToInt minBound
---------------------------------------------------
-- caches
---------------------------------------------------

-- cache JExpr representing StgReg
registers :: Array StgReg JExpr
registers = listArray (minBound, maxBound) (map regN (enumFrom R1))
  where
    regN r
      | fromEnum r < 32 = var . ST.pack . ("h$"++) . map toLower . show $ r
      | otherwise       = IdxExpr (var "h$regs")
                            (toJExpr ((fromEnum r) - 32))

-- cache JExpr representing StgRet
rets :: Array StgRet JExpr
rets = listArray (minBound, maxBound) (map retN (enumFrom Ret1))
  where
    retN = var . ST.pack . ("h$"++) . map toLower . show
