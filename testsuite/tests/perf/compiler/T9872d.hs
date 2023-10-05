{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -freduction-depth=0 #-}   -- this should terminate!

module T9872d where
-- Code from Jan Stolarek, labelled "exp-tyfams.hs" on #9872,
-- generated by a Template Haskell program


-- This file demonstrates exponential compile times with type
-- families. Code in this file was extracted from encoding generated
-- automatically with Template Haskell by singletons library.

import Data.Kind
import GHC.TypeLits

-- encoding of type-level partially applied functions
data TyFun :: Type -> Type -> Type
type family Apply (f :: TyFun k1 k2 -> Type) (x :: k1) :: k2
type a @@ b = Apply a b

-- some boilerplate
type family Error (a :: k) :: k1
type ErrorSym1 a = Error a
data ErrorSym0 :: TyFun a b -> Type
type instance Apply ErrorSym0 e = Error e
data Proxy a = Proxy
data KProxy (a :: Type) = KProxy
type KindOf (a :: k) = ('KProxy :: KProxy k)

-- type-level addition
type (:+$$$) (t1 :: Nat) (t2 :: Nat) = t1 + t2

data (:+$$) (l :: Nat) (tf :: TyFun Nat Nat)
  = forall a. (KindOf (Apply ((:+$$) l) a)) ~ (KindOf ((:+$$$) l a)) =>
    (:+$$###)
type instance Apply ((:+$$) l1) l2 = (:+$$$) l1 l2

data (:+$) (l :: TyFun Nat (TyFun Nat Nat -> Type))
  = forall a. (KindOf (Apply (:+$) a)) ~ (KindOf ((:+$$) a)) => (:+$###)
type instance Apply (:+$) l = (:+$$) l

-- type-level lists
type NilSym0 = '[]

type ConsSym2 (x :: a) (xs :: [a]) = x ': xs

data ConsSym1 (x :: a) (l_a3t6 :: TyFun [a] [a])
  = forall b. (KindOf (Apply (ConsSym1 x) b)) ~ (KindOf (ConsSym2 x b)) =>
    (:$$###)
type instance Apply (ConsSym1 x) xs = ConsSym2 x xs

data ConsSym0 (l :: TyFun a (TyFun [a] [a] -> Type))
  = forall a. (KindOf (Apply ConsSym0 a)) ~ (KindOf (ConsSym1 a)) => (:$###)
type instance Apply ConsSym0 l = ConsSym1 l

type Let_1627403919Scrutinee_1627403894Sym4 t1 t2 t3 t4 =
    Let_1627403919Scrutinee_1627403894 t1 t2 t3 t4

data Let_1627403919Scrutinee_1627403894Sym3 l_a3Dx
                                            l_a3Dy
                                            l_a3Dz
                                            l_a3Dw
  = forall arg_a3DA. (KindOf (Apply (Let_1627403919Scrutinee_1627403894Sym3
                                     l_a3Dx l_a3Dy l_a3Dz) arg_a3DA)) ~
                     (KindOf (Let_1627403919Scrutinee_1627403894Sym4
                              l_a3Dx l_a3Dy l_a3Dz arg_a3DA)) =>
    Let_1627403919Scrutinee_1627403894Sym3KindInference
type instance Apply (Let_1627403919Scrutinee_1627403894Sym3
                     l_a3Dx l_a3Dy l_a3Dz) l_a3Dw =
  Let_1627403919Scrutinee_1627403894Sym4 l_a3Dx l_a3Dy l_a3Dz l_a3Dw

data Let_1627403919Scrutinee_1627403894Sym2 l_a3Dt l_a3Du l_a3Ds
  = forall arg_a3Dv. (KindOf (Apply (Let_1627403919Scrutinee_1627403894Sym2
                                     l_a3Dt l_a3Du) arg_a3Dv)) ~
                     (KindOf (Let_1627403919Scrutinee_1627403894Sym3
                              l_a3Dt l_a3Du arg_a3Dv)) =>
    Let_1627403919Scrutinee_1627403894Sym2KindInference
type instance Apply
    (Let_1627403919Scrutinee_1627403894Sym2 l_a3Dt l_a3Du) l_a3Ds =
  Let_1627403919Scrutinee_1627403894Sym3 l_a3Dt l_a3Du l_a3Ds
data Let_1627403919Scrutinee_1627403894Sym1 l_a3Dq l_a3Dp
  = forall arg_a3Dr. (KindOf (Apply (Let_1627403919Scrutinee_1627403894Sym1
                                     l_a3Dq) arg_a3Dr)) ~
                     (KindOf (Let_1627403919Scrutinee_1627403894Sym2
                              l_a3Dq arg_a3Dr)) =>
    Let_1627403919Scrutinee_1627403894Sym1KindInference
type instance Apply (Let_1627403919Scrutinee_1627403894Sym1 l_a3Dq)
                    l_a3Dp
  = Let_1627403919Scrutinee_1627403894Sym2 l_a3Dq l_a3Dp
data Let_1627403919Scrutinee_1627403894Sym0 l_a3Dn
  = forall arg_a3Do. (KindOf (Apply Let_1627403919Scrutinee_1627403894Sym0
                              arg_a3Do)) ~
                     (KindOf (Let_1627403919Scrutinee_1627403894Sym1
                              arg_a3Do)) =>
    Let_1627403919Scrutinee_1627403894Sym0KindInference
type instance Apply Let_1627403919Scrutinee_1627403894Sym0 l_a3Dn
  = Let_1627403919Scrutinee_1627403894Sym1 l_a3Dn
type Let_1627403919Scrutinee_1627403894 f_a3Dd
                                        q0_a3De
                                        x_a3Df
                                        xs_a3Dg =
    Apply (Apply (Apply ScanrSym0 f_a3Dd) q0_a3De) xs_a3Dg

type family Case f q0 x xs t :: [k] where
  Case f q0 x xs '[]       = ErrorSym0 @@ "empty list"
  Case f q0 x xs (q ': qs) = ConsSym0 @@ (f @@ x @@ q) @@ (ConsSym0 @@ q @@ qs)

-- type-level scanr
type ScanrSym3 (t1 :: TyFun a (TyFun b b -> Type) -> Type)
               (t2 :: b)
               (t3 :: [a]) =
    Scanr t1 t2 t3

data ScanrSym2 (l1 :: TyFun a (TyFun b b -> Type) -> Type)
               (l2 :: b)
               (l3 :: TyFun [a] [b])
  = forall a. (KindOf (Apply (ScanrSym2 l1 l2) a)) ~
              (KindOf (ScanrSym3 l1 l2 a)) =>
    ScanrSym2KindInference
type instance Apply (ScanrSym2 l1 l2) l3 = ScanrSym3 l1 l2 l3

data ScanrSym1 (l_a3D0 :: TyFun a_a3CJ (TyFun b_a3CK b_a3CK -> Type) -> Type)
               (l_a3CZ :: TyFun b_a3CK (TyFun ([a_a3CJ]) ([b_a3CK])
                                        -> Type))
  = forall arg_a3D1. (KindOf (Apply (ScanrSym1 l_a3D0) arg_a3D1)) ~
                     (KindOf (ScanrSym2 l_a3D0 arg_a3D1)) =>
    ScanrSym1KindInference
type instance Apply (ScanrSym1 l_a3D0) l_a3CZ = ScanrSym2 l_a3D0 l_a3CZ

data ScanrSym0 (l :: TyFun (TyFun a (TyFun  b   b  -> Type) -> Type)
                           (TyFun b (TyFun [a] [b] -> Type) -> Type))
  = forall a. (KindOf (Apply ScanrSym0 a)) ~ (KindOf (ScanrSym1 a)) =>
    ScanrSym0KindInference
type instance Apply ScanrSym0 l1 = ScanrSym1 l1

type family Scanr (a_a3D6 :: TyFun a_a3CJ (TyFun b_a3CK b_a3CK -> Type) -> Type)
                  (a_a3D7 :: b_a3CK)
                  (a_a3D8 :: [a_a3CJ]) :: [b_a3CK] where
  Scanr _z_1627403911_a3Db q0_a3Dc '[] = Apply (Apply ConsSym0 q0_a3Dc) NilSym0
  Scanr f_a3Dd q0_a3De (x_a3Df ': xs_a3Dg) =
    Case f_a3Dd q0_a3De x_a3Df xs_a3Dg (Let_1627403919Scrutinee_1627403894Sym4
                                        f_a3Dd q0_a3De x_a3Df xs_a3Dg)


{-
foo32 :: Proxy ('[528,527,525,522,518,513,507,500,492,483,473,462,450,437,423,
                  408,392,375,357,338,318,297,275,252,228,203,177,150,122,93,
                  63,32,0])
foo32 = Proxy

bar32 :: Proxy (ScanrSym0 @@ (:+$) @@ 0 @@ '[1,2,3,4,5,6,7,8,9,10,11,12,13,14,
                                             15,16,17,18,19,20,21,22,23,24,25,
                                             26,27,28,29,30,31,32])
bar32 = foo32

-}
{-
foo64 :: Proxy ('[2080,2079,2077,2074,2070,2065,2059,2052,2044,2035,2025,2014,
                  2002,1989,1975,1960,1944,1927,1909,1890,1870,1849,1827,1804,
                  1780,1755,1729,1702,1674,1645,1615,1584,1552,1519,1485,1450,
                  1414,1377,1339,1300,1260,1219,1177,1134,1090,1045,999,952,904,
                  855,805,754,702,649,595,540,484,427,369,310,250,189,127,64,0])
foo64 = Proxy

bar64 :: Proxy (ScanrSym0 @@ (:+$) @@ 0 @@ '[1,2,3,4,5,6,7,8,9,10,11,12,13,14,
                                             15,16,17,18,19,20,21,22,23,24,25,
                                             26,27,28,29,30,31,32,33,34,35,36,
                                             37,38,39,40,41,42,43,44,45,46,47,
                                             48,49,50,51,52,53,54,55,56,57,58,
                                             59,60,61,62,63,64])
bar64 = foo64


foo128 :: Proxy ('[8256,8255,8253,8250,8246,8241,8235,8228,8220,8211,8201,8190,
                   8178,8165,8151,8136,8120,8103,8085,8066,8046,8025,8003,7980,
                   7956,7931,7905,7878,7850,7821,7791,7760,7728,7695,7661,7626,
                   7590,7553,7515,7476,7436,7395,7353,7310,7266,7221,7175,7128,
                   7080,7031,6981,6930,6878,6825,6771,6716,6660,6603,6545,6486,
                   6426,6365,6303,6240,6176,6111,6045,5978,5910,5841,5771,5700,
                   5628,5555,5481,5406,5330,5253,5175,5096,5016,4935,4853,4770,
                   4686,4601,4515,4428,4340,4251,4161,4070,3978,3885,3791,3696,
                   3600,3503,3405,3306,3206,3105,3003,2900,2796,2691,2585,2478,
                   2370,2261,2151,2040,1928,1815,1701,1586,1470,1353,1235,1116,
                   996,875,753,630,506,381,255,128,0])
foo128 = Proxy

bar128 :: Proxy (ScanrSym0 @@ (:+$) @@ 0 @@ '[1,2,3,4,5,6,7,8,9,10,11,12,13,14,
                                              15,16,17,18,19,20,21,22,23,24,25,
                                              26,27,28,29,30,31,32,33,34,35,36,
                                              37,38,39,40,41,42,43,44,45,46,47,
                                              48,49,50,51,52,53,54,55,56,57,58,
                                              59,60,61,62,63,64,65,66,67,68,69,
                                              70,71,72,73,74,75,76,77,78,79,80,
                                              81,82,83,84,85,86,87,88,89,90,91,
                                              92,93,94,95,96,97,98,99,100,101,
                                              102,103,104,105,106,107,108,109,
                                              110,111,112,113,114,115,116,117,
                                              118,119,120,121,122,123,124,125,
                                              126,127,128])
bar128 = foo128
-}

foo256 :: Proxy ('[32896,32895,32893,32890,32886,32881,32875,32868,32860,32851,
                   32841,32830,32818,32805,32791,32776,32760,32743,32725,32706,
                   32686,32665,32643,32620,32596,32571,32545,32518,32490,32461,
                   32431,32400,32368,32335,32301,32266,32230,32193,32155,32116,
                   32076,32035,31993,31950,31906,31861,31815,31768,31720,31671,
                   31621,31570,31518,31465,31411,31356,31300,31243,31185,31126,
                   31066,31005,30943,30880,30816,30751,30685,30618,30550,30481,
                   30411,30340,30268,30195,30121,30046,29970,29893,29815,29736,
                   29656,29575,29493,29410,29326,29241,29155,29068,28980,28891,
                   28801,28710,28618,28525,28431,28336,28240,28143,28045,27946,
                   27846,27745,27643,27540,27436,27331,27225,27118,27010,26901,
                   26791,26680,26568,26455,26341,26226,26110,25993,25875,25756,
                   25636,25515,25393,25270,25146,25021,24895,24768,24640,24511,
                   24381,24250,24118,23985,23851,23716,23580,23443,23305,23166,
                   23026,22885,22743,22600,22456,22311,22165,22018,21870,21721,
                   21571,21420,21268,21115,20961,20806,20650,20493,20335,20176,
                   20016,19855,19693,19530,19366,19201,19035,18868,18700,18531,
                   18361,18190,18018,17845,17671,17496,17320,17143,16965,16786,
                   16606,16425,16243,16060,15876,15691,15505,15318,15130,14941,
                   14751,14560,14368,14175,13981,13786,13590,13393,13195,12996,
                   12796,12595,12393,12190,11986,11781,11575,11368,11160,10951,
                   10741,10530,10318,10105,9891,9676,9460,9243,9025,8806,
                   8586,8365,8143,7920,7696,7471,7245,7018,6790,6561,6331,6100,
                   5868,5635,5401,5166,4930,4693,4455,4216,3976,3735,3493,3250,
                   3006,2761,2515,2268,2020,1771,1521,1270,1018,765,511,256,0])
foo256 = Proxy

bar256 :: Proxy (ScanrSym0 @@ (:+$) @@ 0 @@ '[1,2,3,4,5,6,7,8,9,10,11,12,13,14,
                                              15,16,17,18,19,20,21,22,23,24,25,
                                              26,27,28,29,30,31,32,33,34,35,36,
                                              37,38,39,40,41,42,43,44,45,46,47,
                                              48,49,50,51,52,53,54,55,56,57,58,
                                              59,60,61,62,63,64,65,66,67,68,69,
                                              70,71,72,73,74,75,76,77,78,79,80,
                                              81,82,83,84,85,86,87,88,89,90,91,
                                              92,93,94,95,96,97,98,99,100,101,
                                              102,103,104,105,106,107,108,109,
                                              110,111,112,113,114,115,116,117,
                                              118,119,120,121,122,123,124,125,
                                              126,127,128,129,130,131,132,133,
                                              134,135,136,137,138,139,140,141,
                                              142,143,144,145,146,147,148,149,
                                              150,151,152,153,154,155,156,157,
                                              158,159,160,161,162,163,164,165,
                                              166,167,168,169,170,171,172,173,
                                              174,175,176,177,178,179,180,181,
                                              182,183,184,185,186,187,188,189,
                                              190,191,192,193,194,195,196,197,
                                              198,199,200,201,202,203,204,205,
                                              206,207,208,209,210,211,212,213,
                                              214,215,216,217,218,219,220,221,
                                              222,223,224,225,226,227,228,229,
                                              230,231,232,233,234,235,236,237,
                                              238,239,240,241,242,243,244,245,
                                              246,247,248,249,250,251,252,253,
                                              254,255,256])
bar256 = foo256
