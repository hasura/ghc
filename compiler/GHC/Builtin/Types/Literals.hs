{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}   -- See calls to mkTemplateTyVars

module GHC.Builtin.Types.Literals
  ( tryInteractInertFam, tryInteractTopFam, tryMatchFam

  , typeNatTyCons
  , typeNatCoAxiomRules
  , BuiltInSynFamily(..)

    -- If you define a new built-in type family, make sure to export its TyCon
    -- from here as well.
    -- See Note [Adding built-in type families]
  , typeNatAddTyCon
  , typeNatMulTyCon
  , typeNatExpTyCon
  , typeNatSubTyCon
  , typeNatDivTyCon
  , typeNatModTyCon
  , typeNatLogTyCon
  , typeNatCmpTyCon
  , typeSymbolCmpTyCon
  , typeSymbolAppendTyCon
  , typeCharCmpTyCon
  , typeConsSymbolTyCon
  , typeUnconsSymbolTyCon
  , typeCharToNatTyCon
  , typeNatToCharTyCon
  ) where

import GHC.Prelude

import GHC.Core.Type
import GHC.Core.Unify      ( tcMatchTys )
import GHC.Data.Pair
import GHC.Core.TyCon    ( TyCon, FamTyConFlav(..), mkFamilyTyCon
                         , Injectivity(..), isBuiltInSynFamTyCon_maybe )
import GHC.Core.Coercion.Axiom
import GHC.Core.TyCo.Compare   ( tcEqType )
import GHC.Types.Name          ( Name, BuiltInSyntax(..) )
import GHC.Types.Unique.FM
import GHC.Builtin.Types
import GHC.Builtin.Types.Prim  ( mkTemplateAnonTyConBinders, mkTemplateTyVars )
import GHC.Builtin.Names
                  ( gHC_INTERNAL_TYPELITS
                  , gHC_INTERNAL_TYPELITS_INTERNAL
                  , gHC_INTERNAL_TYPENATS
                  , gHC_INTERNAL_TYPENATS_INTERNAL
                  , typeNatAddTyFamNameKey
                  , typeNatMulTyFamNameKey
                  , typeNatExpTyFamNameKey
                  , typeNatSubTyFamNameKey
                  , typeNatDivTyFamNameKey
                  , typeNatModTyFamNameKey
                  , typeNatLogTyFamNameKey
                  , typeNatCmpTyFamNameKey
                  , typeSymbolCmpTyFamNameKey
                  , typeSymbolAppendFamNameKey
                  , typeCharCmpTyFamNameKey
                  , typeConsSymbolTyFamNameKey
                  , typeUnconsSymbolTyFamNameKey
                  , typeCharToNatTyFamNameKey
                  , typeNatToCharTyFamNameKey
                  )
import GHC.Data.FastString
import GHC.Utils.Panic
import GHC.Utils.Misc
import GHC.Utils.Outputable

import Control.Monad ( guard )
import Data.List  ( isPrefixOf, isSuffixOf )
import Data.Maybe ( listToMaybe )
import qualified Data.Char as Char

{-
Note [Type-level literals]
~~~~~~~~~~~~~~~~~~~~~~~~~~
There are currently three forms of type-level literals: natural numbers, symbols, and
characters.

Type-level literals are supported by CoAxiomRules (conditional axioms), which
power the built-in type families (see Note [Adding built-in type families]).
Currently, all built-in type families are for the express purpose of supporting
type-level literals.

See also the Wiki page:

    https://gitlab.haskell.org/ghc/ghc/wikis/type-nats

Note [Adding built-in type families]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
There are a few steps to adding a built-in type family:

* Adding a unique for the type family TyCon

  These go in GHC.Builtin.Names. It will likely be of the form
  @myTyFamNameKey = mkPreludeTyConUnique xyz@, where @xyz@ is a number that
  has not been chosen before in GHC.Builtin.Names. There are several examples already
  in GHC.Builtin.Names—see, for instance, typeNatAddTyFamNameKey.

* Adding the type family TyCon itself

  This goes in GHC.Builtin.Types.Literals. There are plenty of examples of how to define
  these -- see, for instance, typeNatAddTyCon.

  Once your TyCon has been defined, be sure to:

  - Export it from GHC.Builtin.Types.Literals. (Not doing so caused #14632.)
  - Include it in the typeNatTyCons list, defined in GHC.Builtin.Types.Literals.

* Define the type family somewhere

  Finally, you will need to define the type family somewhere, likely in @base@.
  Currently, all of the built-in type families are defined in GHC.TypeLits or
  GHC.TypeNats, so those are likely candidates.

  Since the behavior of your built-in type family is specified in GHC.Builtin.Types.Literals,
  you should give an open type family definition with no instances, like so:

    type family MyTypeFam (m :: Nat) (n :: Nat) :: Nat

  Changing the argument and result kinds as appropriate.

* Update the relevant test cases

  The GHC test suite will likely need to be updated after you add your built-in
  type family. For instance:

  - The T9181 test prints the :browse contents of GHC.TypeLits, so if you added
    a test there, the expected output of T9181 will need to change.
  - The TcTypeNatSimple and TcTypeSymbolSimple tests have compile-time unit
    tests, as well as TcTypeNatSimpleRun and TcTypeSymbolSimpleRun, which have
    runtime unit tests. Consider adding further unit tests to those if your
    built-in type family deals with Nats or Symbols, respectively.
-}

-------------------------------------------------------------------------------
--     Key utility functions
-------------------------------------------------------------------------------

tryInteractTopFam :: BuiltInSynFamily -> TyCon -> [Type] -> Type
                  -> [(CoAxiomRule, TypeEqn)]
tryInteractTopFam fam fam_tc tys r
  = [(BuiltInFamInteract ax_rule, eqn)
    | ax_rule  <- sfInteractTop fam
    , Just eqn <- [bifint_proves ax_rule [eqn]] ]
  where
    eqn :: TypeEqn
    eqn = Pair (mkTyConApp fam_tc tys) r

tryInteractInertFam :: BuiltInSynFamily -> TyCon
                    -> [Type] -> Type  -- F tys1 ~ ty1
                    -> [Type] -> Type  -- F tys2 ~ ty2
                    -> [(CoAxiomRule, TypeEqn)]
tryInteractInertFam builtin_fam fam_tc tys1 ty1 tys2 ty2
  = [(BuiltInFamInteract ax_rule, eqn)
    | ax_rule  <- sfInteractInert builtin_fam
    , Just eqn <- [bifint_proves ax_rule [eqn1,eqn2]] ]
  where
    eqn1 = Pair (mkTyConApp fam_tc tys1) ty1
    eqn2 = Pair (mkTyConApp fam_tc tys2) ty2

tryMatchFam :: BuiltInSynFamily -> [Type]
            -> Maybe (CoAxiomRule, [Type], Type)
-- Does this reduce on the given arguments?
-- If it does, returns (CoAxiomRule, types to instantiate the rule at, rhs type)
-- That is: mkAxiomRuleCo coax (zipWith mkReflCo (coaxrAsmpRoles coax) ts)
--              :: F tys ~r rhs,
tryMatchFam builtin_fam arg_tys
  = listToMaybe $   -- Pick first rule to match
    [ (BuiltInFamRewrite rw_ax, inst_tys, res_ty)
    | rw_ax <- sfMatchFam builtin_fam
    , Just (inst_tys,res_ty) <- [bifrw_match rw_ax arg_tys] ]

-------------------------------------------------------------------------------
--          Constructing BuiltInFamInteract, BuiltInFamRewrite
-------------------------------------------------------------------------------

mkUnaryConstFoldAxiom :: TyCon -> String
                      -> (Type -> Maybe a)
                      -> (a -> Maybe Type)
                      -> BuiltInFamRewrite
-- For the definitional axioms, like  (3+4 --> 7)
mkUnaryConstFoldAxiom tc str isReqTy f
  = BIF_Rewrite
      { bifrw_name      = fsLit str
      , bifrw_arg_roles = [Nominal]
      , bifrw_res_role  = Nominal
      , bifrw_match     = \ts -> do { [t1] <- return ts
                                    ; t1' <- isReqTy t1
                                    ; res <- f t1'
                                    ; return ([t1], res) }
      , bifrw_proves    = \cs -> do { [Pair s1 s2] <- return cs
                                    ; s2' <- isReqTy s2
                                    ; z   <- f s2'
                                    ; return (mkTyConApp tc [s1] === z) }
      }

mkBinConstFoldAxiom :: TyCon -> String
                    -> (Type -> Maybe a)
                    -> (Type -> Maybe b)
                    -> (a -> b -> Maybe Type)
                    -> BuiltInFamRewrite
-- For the definitional axioms, like  (3+4 --> 7)
mkBinConstFoldAxiom tc str isReqTy1 isReqTy2 f
  = BIF_Rewrite
      { bifrw_name      = fsLit str
      , bifrw_arg_roles = [Nominal, Nominal]
      , bifrw_res_role  = Nominal
      , bifrw_match     = \ts -> do { [t1,t2] <- return ts
                                    ; t1' <- isReqTy1 t1
                                    ; t2' <- isReqTy2 t2
                                    ; res <- f t1' t2'
                                    ; return ([t1,t2], res) }
      , bifrw_proves    = \cs -> do { [Pair s1 s2, Pair t1 t2] <- return cs
                                    ; s2' <- isReqTy1 s2
                                    ; t2' <- isReqTy2 t2
                                    ; z   <- f s2' t2'
                                    ; return (mkTyConApp tc [s1,t1] === z) }
      }

mkRewriteAxiom :: TyCon -> String
               -> [TyVar] -> [Type]  -- LHS
               -> Type               -- RHS
               -> BuiltInFamRewrite
mkRewriteAxiom tc str tpl_tvs lhs_tys rhs_ty
  = BIF_Rewrite
      { bifrw_name      = fsLit str
      , bifrw_arg_roles = [Nominal | _ <- tpl_tvs]
      , bifrw_res_role  = Nominal
      , bifrw_match     = match_fn
      , bifrw_proves    = inst_fn }
  where
    match_fn :: [Type] -> Maybe ([Type],Type)
    match_fn arg_tys
      = case tcMatchTys lhs_tys arg_tys of
          Nothing    -> Nothing
          Just subst -> Just (substTyVars subst tpl_tvs, substTy subst rhs_ty)

    inst_fn :: [TypeEqn] -> Maybe TypeEqn
    inst_fn inst_eqns
      = assertPpr (inst_eqns `equalLength` tpl_tvs) (text str $$ ppr inst_eqns) $
        Just (mkTyConApp tc (substTys (zipTCvSubst tpl_tvs tys1) lhs_tys)
              ===
              substTy (zipTCvSubst tpl_tvs tys2) rhs_ty)
      where
        (tys1, tys2) = unzipPairs inst_eqns

mkTopUnaryFamDeduction :: String -> TyCon
                     -> (Type -> Type -> Maybe TypeEqn)
                     -> BuiltInFamInteract
-- Deduction from (F s ~ r) where `F` is a unary type function
mkTopUnaryFamDeduction str fam_tc f
  = BIF_Interact
    { bifint_name      = fsLit str
    , bifint_arg_roles = [Nominal]
    , bifint_res_role  = Nominal
    , bifint_proves    = \cs -> do { [Pair lhs rhs] <- return cs
                                   ; (tc, [a]) <- splitTyConApp_maybe lhs
                                   ; massertPpr (tc == fam_tc) (ppr tc $$ ppr fam_tc)
                                   ; f a rhs } }

mkTopBinFamDeduction :: String -> TyCon
                     -> (Type -> Type -> Type -> Maybe TypeEqn)
                     -> BuiltInFamInteract
-- Deduction from (F s t  ~ r) where `F` is a binary type function
mkTopBinFamDeduction str fam_tc f
  = BIF_Interact
    { bifint_name      = fsLit str
    , bifint_arg_roles = [Nominal]
    , bifint_res_role  = Nominal
    , bifint_proves    = \cs -> do { [Pair lhs rhs] <- return cs
                                   ; (tc, [a,b]) <- splitTyConApp_maybe lhs
                                   ; massertPpr (tc == fam_tc) (ppr tc $$ ppr fam_tc)
                                   ; f a b rhs } }

mkInteractUnaryFamDeduction :: String -> TyCon
                     -> (Type -> Type ->   -- F x1 ~ r1
                         Type -> Type ->   -- F x2 ~ r2
                         Maybe TypeEqn)
                     -> BuiltInFamInteract
mkInteractUnaryFamDeduction str fam_tc f
  = BIF_Interact
    { bifint_name      = fsLit str
    , bifint_arg_roles = [Nominal, Nominal]
    , bifint_res_role  = Nominal
    , bifint_proves    = \cs -> do { [Pair lhs1 rhs1, Pair lhs2 rhs2] <- return cs
                                 ; (tc1, [x1]) <- splitTyConApp_maybe lhs1
                                 ; (tc2, [x2]) <- splitTyConApp_maybe lhs2
                                 ; massertPpr (tc1 == fam_tc) (ppr tc1 $$ ppr fam_tc)
                                 ; massertPpr (tc2 == fam_tc) (ppr tc2 $$ ppr fam_tc)
                                 ; f x1 rhs1 x2 rhs2 } }

mkInteractBinFamDeduction :: String -> TyCon
                     -> (Type -> Type -> Type ->   -- F x1 y1 ~ r1
                         Type -> Type -> Type ->   -- F x2 y2 ~ r2
                         Maybe TypeEqn)
                     -> BuiltInFamInteract
mkInteractBinFamDeduction str fam_tc f
  = BIF_Interact
    { bifint_name      = fsLit str
    , bifint_arg_roles = [Nominal, Nominal]
    , bifint_res_role  = Nominal
    , bifint_proves    = \cs -> do { [Pair lhs1 rhs1, Pair lhs2 rhs2] <- return cs
                                 ; (tc1, [x1,y1]) <- splitTyConApp_maybe lhs1
                                 ; (tc2, [x2,y2]) <- splitTyConApp_maybe lhs2
                                 ; massertPpr (tc1 == fam_tc) (ppr tc1 $$ ppr fam_tc)
                                 ; massertPpr (tc2 == fam_tc) (ppr tc2 $$ ppr fam_tc)
                                 ; f x1 y1 rhs1 x2 y2 rhs2 } }


-------------------------------------------------------------------------------
--     Built-in type constructors for functions on type-level nats
-------------------------------------------------------------------------------

-- The list of built-in type family TyCons that GHC uses.
-- If you define a built-in type family, make sure to add it to this list.
-- See Note [Adding built-in type families]
typeNatTyCons :: [TyCon]
typeNatTyCons =
  [ typeNatAddTyCon
  , typeNatMulTyCon
  , typeNatExpTyCon
  , typeNatSubTyCon
  , typeNatDivTyCon
  , typeNatModTyCon
  , typeNatLogTyCon
  , typeNatCmpTyCon
  , typeSymbolCmpTyCon
  , typeSymbolAppendTyCon
  , typeCharCmpTyCon
  , typeConsSymbolTyCon
  , typeUnconsSymbolTyCon
  , typeCharToNatTyCon
  , typeNatToCharTyCon
  ]


tyConAxiomRules :: TyCon -> [CoAxiomRule]
tyConAxiomRules tc
  | Just ops <- isBuiltInSynFamTyCon_maybe tc
  =    map BuiltInFamInteract (sfInteractTop ops)
    ++ map BuiltInFamInteract (sfInteractInert ops)
    ++ map BuiltInFamRewrite  (sfMatchFam ops)
  | otherwise
  = []

-- The list of built-in type family axioms that GHC uses.
-- If you define new axioms, make sure to include them in this list.
-- See Note [Adding built-in type families]
typeNatCoAxiomRules :: UniqFM FastString CoAxiomRule
typeNatCoAxiomRules = listToUFM $ map (\x -> (coaxrName x, x)) $
                      concatMap tyConAxiomRules typeNatTyCons

-------------------------------------------------------------------------------
--                   Addition (+)
-------------------------------------------------------------------------------

typeNatAddTyCon :: TyCon
typeNatAddTyCon = mkTypeNatFunTyCon2 name
  BuiltInSynFamily
    { sfMatchFam      = axAddMatches
    , sfInteractTop   = axAddTops
    , sfInteractInert = axAddInteracts
    }
  where
    name = mkWiredInTyConName UserSyntax gHC_INTERNAL_TYPENATS (fsLit "+")
              typeNatAddTyFamNameKey typeNatAddTyCon


sn,tn :: TyVar  -- Of kind Natural
(sn: tn: _) = mkTemplateTyVars (repeat typeSymbolKind)

axAddMatches :: [BuiltInFamRewrite]
axAddMatches
  = [ mkRewriteAxiom   tc "Add0L" [tn] [num 0, var tn] (var tn)   -- 0 + t --> t
    , mkRewriteAxiom   tc "Add0R" [sn] [var sn, num 0] (var sn)   -- s + 0 --> s
    , mkBinConstFoldAxiom tc "AddDef" isNumLitTy isNumLitTy $     -- 3 + 4 --> 7
      \x y -> Just $ num (x + y) ]
  where
    tc = typeNatAddTyCon

axAddTops :: [BuiltInFamInteract]
axAddTops
  = [ -- (s + t ~ 0) => (s ~ 0)
      mkTopBinFamDeduction "AddT-0L" typeNatAddTyCon $ \ a _b r ->
      do { _ <- known r (== 0); return (Pair a (num 0)) }

    , -- (s + t ~ 0) => (t ~ 0)
      mkTopBinFamDeduction "AddT-0R" typeNatAddTyCon $ \ _a b r ->
      do { _ <- known r (== 0); return (Pair b (num 0)) }

    , -- (5 + t ~ 8) => (t ~ 3)
      mkTopBinFamDeduction "AddT-KKL" typeNatAddTyCon $ \ a b r ->
      do { na <- isNumLitTy a; nr <- known r (>= na); return (Pair b (num (nr-na))) }

    , -- (s + 5 ~ 8) => (s ~ 3)
      mkTopBinFamDeduction "AddT-KKR" typeNatAddTyCon $ \ a b r ->
      do { nb <- isNumLitTy b; nr <- known r (>= nb); return (Pair a (num (nr-nb))) } ]

axAddInteracts :: [BuiltInFamInteract]
axAddInteracts
  = map mk_ax $
    [ ("AddI-xr", \ x1 y1 z1 x2 y2 z2 -> injCheck x1 x2 z1 z2 y1 y2)
                  -- (x1+y1~z, x2+y2~z) {x1=x2}=> (y1 ~ y2)
    , ("AddI-xr2", \ x1 y1 z1 x2 y2 z2 -> injCheck x2 y1 z1 z2 x1 y2)
                  -- (x1+y1~z, x2+y2~z) {x2=y1}=> (x1 ~ y2)
    , ("AddI-yr", \ x1 y1 z1 x2 y2 z2 -> injCheck y1 y2 z1 z2 x1 x2)
                  -- (x1+y1~z, x2+y2~z) {y1=y2}=> (x1 ~ x2)
    , ("AddI-yr2", \ x1 y1 z1 x2 y2 z2 -> injCheck x1 y2 z1 z2 y1 x2)
                  -- (x1+y1~z, x2+y2~z) {x1=y2}=> (y1 ~ x2)
    ]
  where
    mk_ax (str, fun) = mkInteractBinFamDeduction str typeNatAddTyCon fun


-------------------------------------------------------------------------------
--                   Subtraction (-)
-------------------------------------------------------------------------------

typeNatSubTyCon :: TyCon
typeNatSubTyCon = mkTypeNatFunTyCon2 name
  BuiltInSynFamily
    { sfMatchFam      = axSubMatches
    , sfInteractTop   = axSubTops
    , sfInteractInert = axSubInteracts
    }
  where
  name = mkWiredInTyConName UserSyntax gHC_INTERNAL_TYPENATS (fsLit "-")
            typeNatSubTyFamNameKey typeNatSubTyCon

axSubMatches :: [BuiltInFamRewrite]
axSubMatches
  = [ mkRewriteAxiom   tc "Sub0R" [sn] [var sn, num 0] (var sn)   -- s - 0 --> s
    , mkBinConstFoldAxiom tc "SubDef" isNumLitTy isNumLitTy $     -- 4 - 3 --> 1  if x>=y
      \x y -> fmap num (minus x y) ]
  where
    tc = typeNatSubTyCon

axSubTops :: [BuiltInFamInteract]
axSubTops   -- (a - b ~ 5) => (5 + b ~ a)
  = [ mkTopBinFamDeduction "SubT" typeNatSubTyCon $ \ a b r ->
      do { _ <- isNumLitTy r; return (Pair (r .+. b) a) } ]


axSubInteracts :: [BuiltInFamInteract]
axSubInteracts
  = [ -- (x-y1 ~ z, x-y2 ~ z) => (y1 ~ y2)
      mkInteractBinFamDeduction "SubI-2" typeNatSubTyCon $ \ x1 y1 z1 x2 y2 z2 ->
      injCheck x1 x2 z1 z2 y1 y2
    , -- (x1-y ~ z, x2-y ~ z) => (x1 ~ x2)
      mkInteractBinFamDeduction "SubI-2" typeNatSubTyCon $ \ x1 y1 z1 x2 y2 z2 ->
      injCheck y1 y2 z1 z2 x1 x2 ]

{-
Note [Weakened interaction rule for subtraction]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
A simpler interaction here might be:

  `s - t ~ r` --> `t + r ~ s`

This would enable us to reuse all the code for addition.
Unfortunately, this works a little too well at the moment.
Consider the following example:

    0 - 5 ~ r --> 5 + r ~ 0 --> (5 = 0, r = 0)

This (correctly) spots that the constraint cannot be solved.

However, this may be a problem if the constraint did not
need to be solved in the first place!  Consider the following example:

f :: Proxy (If (5 <=? 0) (0 - 5) (5 - 0)) -> Proxy 5
f = id

Currently, GHC is strict while evaluating functions, so this does not
work, because even though the `If` should evaluate to `5 - 0`, we
also evaluate the "then" branch which generates the constraint `0 - 5 ~ r`,
which fails.

So, for the time being, we only add an improvement when the RHS is a constant,
which happens to work OK for the moment, although clearly we need to do
something more general.
-}


-------------------------------------------------------------------------------
--                   Multiplication (*)
-------------------------------------------------------------------------------

typeNatMulTyCon :: TyCon
typeNatMulTyCon = mkTypeNatFunTyCon2 name
  BuiltInSynFamily
    { sfMatchFam      = axMulMatches
    , sfInteractTop   = axMulTops
    , sfInteractInert = axMulInteracts
    }
  where
  name = mkWiredInTyConName UserSyntax gHC_INTERNAL_TYPENATS (fsLit "*")
            typeNatMulTyFamNameKey typeNatMulTyCon

axMulMatches :: [BuiltInFamRewrite]
axMulMatches
  = [ mkRewriteAxiom   tc "Mul0L" [tn] [num 0, var tn] (num 0)   -- 0 * t --> 0
    , mkRewriteAxiom   tc "Mul0R" [sn] [var sn, num 0] (num 0)   -- s * 0 --> 0
    , mkRewriteAxiom   tc "Mul1L" [tn] [num 1, var tn] (var tn)  -- 1 * t --> t
    , mkRewriteAxiom   tc "Mul1R" [sn] [var sn, num 1] (var sn)  -- s * 1 --> s
    , mkBinConstFoldAxiom tc "MulDef" isNumLitTy isNumLitTy $    -- 3 + 4 --> 12
      \x y -> Just $ num (x * y) ]
  where
    tc = typeNatMulTyCon

axMulTops :: [BuiltInFamInteract]
axMulTops
  = [ -- (s * t ~ 1)  => (s ~ 1)
      mkTopBinFamDeduction "MulT1" typeNatMulTyCon $ \ s _t r ->
      do { _ <- known r (== 1); return (Pair s r) }

    , -- (s * t ~ 1)  => (t ~ 1)
      mkTopBinFamDeduction "MulT2" typeNatMulTyCon $ \ _s t r ->
      do { _ <- known r (== 1); return (Pair t r) }

    , -- (3 * t ~ 15) => (t ~ 5)
      mkTopBinFamDeduction "MulT3" typeNatMulTyCon $ \ s t r ->
      do { ns <- isNumLitTy s; nr <- isNumLitTy r; y <- divide nr ns; return (Pair t (num y)) }

    , -- (s * 3 ~ 15) => (s ~ 5)
      mkTopBinFamDeduction "MulT4" typeNatMulTyCon $ \ s t r ->
      do { nt <- isNumLitTy t; nr <- isNumLitTy r; y <- divide nr nt; return (Pair s (num y)) } ]

axMulInteracts :: [BuiltInFamInteract]
axMulInteracts
  = [ -- (x*y1 ~ z, x*y2 ~ z) => (y1~y2)   if x/=0
      mkInteractBinFamDeduction "MulI1" typeNatMulTyCon $ \ x1 y1 z1 x2 y2 z2 ->
      do { nx1 <- known x1 (/= 0); _ <- known x2 (== nx1); same z1 z2; return (Pair y1 y2) }

    , -- (x1*y ~ z, x2*y ~ z) => (x1~x2)   if  y/0
      mkInteractBinFamDeduction "MulI2" typeNatMulTyCon $ \ x1 y1 z1 x2 y2 z2 ->
      do { ny1 <- known y1 (/= 0); _ <- known y2 (== ny1); same z1 z2; return (Pair x1 x2) } ]


-------------------------------------------------------------------------------
--                   Division: Div and Mod
-------------------------------------------------------------------------------

typeNatDivTyCon :: TyCon
typeNatDivTyCon = mkTypeNatFunTyCon2 name
  BuiltInSynFamily
    { sfMatchFam      = axDivMatches
    , sfInteractTop   = []
    , sfInteractInert = []
    }
  where
  name = mkWiredInTyConName UserSyntax gHC_INTERNAL_TYPENATS (fsLit "Div")
            typeNatDivTyFamNameKey typeNatDivTyCon

typeNatModTyCon :: TyCon
typeNatModTyCon = mkTypeNatFunTyCon2 name
  BuiltInSynFamily
    { sfMatchFam      = axModMatches
    , sfInteractTop   = []
    , sfInteractInert = []
    }
  where
  name = mkWiredInTyConName UserSyntax gHC_INTERNAL_TYPENATS (fsLit "Mod")
            typeNatModTyFamNameKey typeNatModTyCon

axDivMatches :: [BuiltInFamRewrite]
axDivMatches
  = [ mkRewriteAxiom   tc "Div1" [sn] [var sn, num 1] (var sn)   -- s `div` 1 --> s
    , mkBinConstFoldAxiom tc "DivDef" isNumLitTy isNumLitTy $    -- 8 `div` 4 --> 2
      \x y -> do { guard (y /= 0); return (num (div x y)) } ]
  where
    tc = typeNatModTyCon

axModMatches :: [BuiltInFamRewrite]
axModMatches
  = [ mkRewriteAxiom   tc "Mod1" [sn] [var sn, num 1] (num 0)   -- s `mod` 1 --> 0
    , mkBinConstFoldAxiom tc "ModDef" isNumLitTy isNumLitTy $   -- 8 `mod` 3 --> 2
      \x y -> do { guard (y /= 0); return (num (mod x y)) } ]
  where
    tc = typeNatModTyCon

-------------------------------------------------------------------------------
--                   Exponentiation: Exp
-------------------------------------------------------------------------------

typeNatExpTyCon :: TyCon  -- Exponentiation
typeNatExpTyCon = mkTypeNatFunTyCon2 name
  BuiltInSynFamily
    { sfMatchFam      = axExpMatches
    , sfInteractTop   = axExpTops
    , sfInteractInert = axExpInteracts
    }
  where
  name = mkWiredInTyConName UserSyntax gHC_INTERNAL_TYPENATS (fsLit "^")
                typeNatExpTyFamNameKey typeNatExpTyCon

axExpMatches :: [BuiltInFamRewrite]
axExpMatches
  = [ mkRewriteAxiom   tc "Exp0R" [sn] [var sn, num 0] (num 1)   -- s ^ 0 --> 1
    , mkRewriteAxiom   tc "Exp1L" [tn] [num 1, var tn] (num 1)   -- 1 ^ t --> 1
    , mkRewriteAxiom   tc "Exp1R" [sn] [var sn, num 1] (var sn)  -- s ^ 1 --> s
    , mkBinConstFoldAxiom tc "ExpDef" isNumLitTy isNumLitTy $    -- 2 ^ 3 --> 8
      \x y -> Just (num (x ^ y)) ]
  where
    tc = typeNatExpTyCon

axExpTops :: [BuiltInFamInteract]
axExpTops
  = [ -- (s ^ t ~ 0) => (s ~ 0)
      mkTopBinFamDeduction "ExpT1" typeNatExpTyCon $ \ s _t r ->
      do { 0 <- isNumLitTy r; return (Pair s r) }

    , -- (2 ^ t ~ 8) => (t ~ 3)
      mkTopBinFamDeduction "ExpT2" typeNatExpTyCon $ \ s t r ->
      do { ns <- isNumLitTy s; nr <- isNumLitTy r; y <- logExact nr ns; return (Pair t (num y)) }

    , -- (s ^ 2 ~ 9) => (s ~ 3)
      mkTopBinFamDeduction "ExpT3" typeNatExpTyCon $ \ s t r ->
      do { nt <- isNumLitTy t; nr <- isNumLitTy r; y <- rootExact nr nt; return (Pair s (num y)) } ]

axExpInteracts :: [BuiltInFamInteract]
axExpInteracts
  = [ -- (x1^y1 ~ z, x2^y2 ~ z) {x1=x2, x1>1}=> (y1~y2)
      mkInteractBinFamDeduction "ExpI1" typeNatExpTyCon $ \ x1 y1 z1 x2 y2 z2 ->
      do { nx1 <- known x1 (> 1); _ <- known x2 (== nx1); same z1 z2; return (Pair y1 y2) }

    , -- (x1^y1 ~ z, x2^y2 ~ z) {y1=y2, y1>0}=> (x1~x2)
      mkInteractBinFamDeduction "ExpI2" typeNatExpTyCon $ \ x1 y1 z1 x2 y2 z2 ->
      do { ny1 <- known y1 (> 0); _ <- known y2 (== ny1); same z1 z2; return (Pair x1 x2) } ]
-------------------------------------------------------------------------------
--                   Logarithm: Log2
-------------------------------------------------------------------------------

typeNatLogTyCon :: TyCon
typeNatLogTyCon = mkTypeNatFunTyCon1 name
  BuiltInSynFamily
    { sfMatchFam      = axLogMatches
    , sfInteractTop   = []
    , sfInteractInert = []
    }
  where
  name = mkWiredInTyConName UserSyntax gHC_INTERNAL_TYPENATS (fsLit "Log2")
            typeNatLogTyFamNameKey typeNatLogTyCon

axLogMatches :: [BuiltInFamRewrite]
axLogMatches
  = [ mkUnaryConstFoldAxiom tc "LogDef" isNumLitTy $       -- log 8 --> 3
      \x -> do { (a,_) <- genLog x 2; return (num a) } ]
  where
    tc = typeNatLogTyCon

-------------------------------------------------------------------------------
--               Comparision of Nats: CmpNat
-------------------------------------------------------------------------------

typeNatCmpTyCon :: TyCon
typeNatCmpTyCon
  = mkFamilyTyCon name
      (mkTemplateAnonTyConBinders [ naturalTy, naturalTy ])
      orderingKind
      Nothing
      (BuiltInSynFamTyCon ops)
      Nothing
      NotInjective

  where
    name = mkWiredInTyConName UserSyntax gHC_INTERNAL_TYPENATS_INTERNAL (fsLit "CmpNat")
                  typeNatCmpTyFamNameKey typeNatCmpTyCon
    ops = BuiltInSynFamily
      { sfMatchFam      = axCmpNatMatches
      , sfInteractTop   = axCmpNatTops
      , sfInteractInert = [] }

axCmpNatMatches :: [BuiltInFamRewrite]
axCmpNatMatches
  = [ mkRewriteAxiom   tc "CmpNatRefl" [sn] [var sn, var sn] (ordering EQ)    -- s `cmp` s --> EQ
    , mkBinConstFoldAxiom tc "CmpNatDef" isNumLitTy isNumLitTy $              -- 2 `cmp` 3 --> LT
      \x y -> Just (ordering (compare x y)) ]
  where
    tc = typeNatCmpTyCon

axCmpNatTops :: [BuiltInFamInteract]
axCmpNatTops
  = [ mkTopBinFamDeduction "CmpNatT3" typeNatCmpTyCon $ \ s t r ->
      do { EQ <- isOrderingLitTy r; return (Pair s t) } ]

-------------------------------------------------------------------------------
--              Comparsion of Symbols: CmpSymbol
-------------------------------------------------------------------------------

typeSymbolCmpTyCon :: TyCon
typeSymbolCmpTyCon =
  mkFamilyTyCon name
    (mkTemplateAnonTyConBinders [typeSymbolKind, typeSymbolKind])
    orderingKind
    Nothing
    (BuiltInSynFamTyCon ops)
    Nothing
    NotInjective

  where
  name = mkWiredInTyConName UserSyntax gHC_INTERNAL_TYPELITS_INTERNAL (fsLit "CmpSymbol")
                typeSymbolCmpTyFamNameKey typeSymbolCmpTyCon
  ops = BuiltInSynFamily
    { sfMatchFam      = axSymbolCmpMatches
    , sfInteractTop   = axSymbolCmpTops
    , sfInteractInert = [] }

ss,ts :: TyVar  -- Of kind Symbol
(ss: ts: _) = mkTemplateTyVars (repeat typeSymbolKind)

axSymbolCmpMatches :: [BuiltInFamRewrite]
axSymbolCmpMatches
  = [ mkRewriteAxiom   tc "CmpSymbolRefl" [ss] [var ss, var ss] (ordering EQ) -- s `cmp` s --> EQ
    , mkBinConstFoldAxiom tc "CmpSymbolDef" isStrLitTy isStrLitTy $           -- "a" `cmp` "b" --> LT
      \x y -> Just (ordering (lexicalCompareFS x y)) ]
  where
    tc = typeSymbolCmpTyCon

axSymbolCmpTops :: [BuiltInFamInteract]
axSymbolCmpTops
  = [ mkTopBinFamDeduction "CmpSymbolT" typeSymbolCmpTyCon $ \ s t r ->
      do { EQ <- isOrderingLitTy r; return (Pair s t) } ]


-------------------------------------------------------------------------------
--            AppendSymbol
-------------------------------------------------------------------------------

typeSymbolAppendTyCon :: TyCon
typeSymbolAppendTyCon = mkTypeSymbolFunTyCon2 name
  BuiltInSynFamily
    { sfMatchFam      = axAppendMatches
    , sfInteractTop   = axAppendTops
    , sfInteractInert = axAppendInteracts }
  where
  name = mkWiredInTyConName UserSyntax gHC_INTERNAL_TYPELITS (fsLit "AppendSymbol")
                typeSymbolAppendFamNameKey typeSymbolAppendTyCon

axAppendMatches :: [BuiltInFamRewrite]
axAppendMatches
  = [ mkRewriteAxiom   tc "Concat0R" [ts] [nullStrLitTy, var ts] (var ts) -- "" ++ t --> t
    , mkRewriteAxiom   tc "Concat0L" [ss] [var ss, nullStrLitTy] (var ss) -- s ++ "" --> s
    , mkBinConstFoldAxiom tc "AppendSymbolDef" isStrLitTy isStrLitTy $    -- "a" ++ "b" --> "ab"
      \x y -> Just (mkStrLitTy (appendFS x y)) ]
  where
    tc = typeSymbolAppendTyCon

axAppendTops :: [BuiltInFamInteract]
axAppendTops
 = [ -- (AppendSymbol a b ~ "") => (a ~ "")
     mkTopBinFamDeduction "AppendSymbolT1" typeSymbolAppendTyCon $ \ a _b r ->
     do { rs <- isStrLitTy r; guard (nullFS rs); return (Pair a nullStrLitTy) }

   , -- (AppendSymbol a b ~ "") => (b ~ "")
     mkTopBinFamDeduction "AppendSymbolT2" typeSymbolAppendTyCon $ \ _a b r ->
     do { rs <- isStrLitTy r; guard (nullFS rs); return (Pair b nullStrLitTy) }

   , -- (AppendSymbol "foo" b ~ "foobar") => (b ~ "bar")
     mkTopBinFamDeduction "AppendSymbolT3" typeSymbolAppendTyCon $ \ a b r ->
     do { as <- isStrLitTyS a; rs <- isStrLitTyS r; guard (as `isPrefixOf` rs)
        ; return (Pair b (mkStrLitTyS (drop (length as) rs))) }

   , -- (AppendSymbol f "bar" ~ "foobar") => (f ~ "foo")
     mkTopBinFamDeduction "AppendSymbolT3" typeSymbolAppendTyCon $ \ a b r ->
     do { bs <- isStrLitTyS b; rs <- isStrLitTyS r; guard (bs `isSuffixOf` rs)
        ; return (Pair a (mkStrLitTyS (take (length rs - length bs) rs))) } ]

axAppendInteracts :: [BuiltInFamInteract]
axAppendInteracts
  = [ -- (AppendSymbol x1 y1 ~ z, AppendSymbol x2 y2 ~ z) {x1=x2}=> (y1 ~ y2)
      mkInteractBinFamDeduction "AppI1" typeSymbolAppendTyCon $ \ x1 y1 z1 x2 y2 z2 ->
      injCheck x1 x2 z1 z2 y1 y2
    , -- (AppendSymbol x1 y1 ~ z, AppendSymbol x2 y2 ~ z) {y1=y2}=> (x1 ~ x2)
      mkInteractBinFamDeduction "AppI2" typeSymbolAppendTyCon $ \ x1 y1 z1 x2 y2 z2 ->
      injCheck y1 y2 z1 z2 x1 x2 ]

-------------------------------------------------------------------------------
--            ConsSymbol
-------------------------------------------------------------------------------

typeConsSymbolTyCon :: TyCon
typeConsSymbolTyCon =
  mkFamilyTyCon name
    (mkTemplateAnonTyConBinders [ charTy, typeSymbolKind ])
    typeSymbolKind
    Nothing
    (BuiltInSynFamTyCon ops)
    Nothing
    (Injective [True, True])
  where
  name = mkWiredInTyConName UserSyntax gHC_INTERNAL_TYPELITS (fsLit "ConsSymbol")
                  typeConsSymbolTyFamNameKey typeConsSymbolTyCon
  ops = BuiltInSynFamily
      { sfMatchFam      = axConsMatches
      , sfInteractTop   = axConsTops
      , sfInteractInert = axConsInteracts }

axConsMatches :: [BuiltInFamRewrite]
axConsMatches
  = [ mkBinConstFoldAxiom tc "ConsSymbolDef" isCharLitTy isStrLitTy $    -- 'a' : "bc" --> "abc"
      \x y -> Just $ mkStrLitTy (consFS x y) ]
  where
    tc = typeConsSymbolTyCon

axConsTops :: [BuiltInFamInteract]
axConsTops
  = [ -- ConsSymbol a b ~ "blah" => (a ~ 'b')
      mkTopBinFamDeduction "ConsSymbolT1" typeConsSymbolTyCon $ \ a _b r ->
      do { rs <- isStrLitTy r; (x,_) <- unconsFS rs; return (Pair a (mkCharLitTy x)) }

    , -- ConsSymbol a b ~ "blah" => (b ~ "lah")
      mkTopBinFamDeduction "ConsSymbolT2" typeConsSymbolTyCon $ \ _a b r ->
      do { rs <- isStrLitTy r; (_,xs) <- unconsFS rs; return (Pair b (mkStrLitTy xs)) } ]

axConsInteracts :: [BuiltInFamInteract]
axConsInteracts
  = [ -- (ConsSymbol x1 y1 ~ z, ConsSymbol x2 y2 ~ z) {x1=x2}=> (y1 ~ y2)
      mkInteractBinFamDeduction "AppI1" typeConsSymbolTyCon $ \ x1 y1 z1 x2 y2 z2 ->
      injCheck x1 x2 z1 z2 y1 y2
    , -- (ConsSymbol x1 y1 ~ z, AppendSymbol x2 y2 ~ z) {y1=y2}=> (x1 ~ x2)
      mkInteractBinFamDeduction "AppI1" typeConsSymbolTyCon $ \ x1 y1 z1 x2 y2 z2 ->
      injCheck y1 y2 z1 z2 x1 x2 ]

-------------------------------------------------------------------------------
--            UnconsSymbol
-------------------------------------------------------------------------------

typeUnconsSymbolTyCon :: TyCon
typeUnconsSymbolTyCon =
  mkFamilyTyCon name
    (mkTemplateAnonTyConBinders [ typeSymbolKind ])
    (mkMaybeTy charSymbolPairKind)
    Nothing
    (BuiltInSynFamTyCon ops)
    Nothing
    (Injective [True])
  where
  name = mkWiredInTyConName UserSyntax gHC_INTERNAL_TYPELITS (fsLit "UnconsSymbol")
                  typeUnconsSymbolTyFamNameKey typeUnconsSymbolTyCon
  ops = BuiltInSynFamily
      { sfMatchFam      = axUnconsMatches
      , sfInteractTop   = axUnconsTops
      , sfInteractInert = axUnconsInteracts }

computeUncons :: FastString -> Type
computeUncons str
  = mkPromotedMaybeTy charSymbolPairKind (fmap reify (unconsFS str))
  where
    reify :: (Char, FastString) -> Type
    reify (c, s) = charSymbolPair (mkCharLitTy c) (mkStrLitTy s)

axUnconsMatches :: [BuiltInFamRewrite]
axUnconsMatches
  = [ mkUnaryConstFoldAxiom tc "ConsSymbolDef" isStrLitTy $    -- 'a' : "bc" --> "abc"
      \x -> Just $ computeUncons x ]
  where
    tc = typeUnconsSymbolTyCon

axUnconsTops :: [BuiltInFamInteract]
axUnconsTops
  = [ -- (UnconsSymbol b ~ Nothing) => (b ~ "")
      mkTopUnaryFamDeduction "UnconsSymbolT1" typeUnconsSymbolTyCon $ \b r ->
      do { Nothing  <- isPromotedMaybeTy r; return (Pair b nullStrLitTy) }

    , -- (UnconsSymbol b ~ Just ('f',"oobar")) => (b ~ "foobar")
      mkTopUnaryFamDeduction "UnconsSymbolT2" typeUnconsSymbolTyCon $ \b r ->
      do { Just pr <- isPromotedMaybeTy r
         ; (c,s) <- isPromotedPairType pr
         ; chr <- isCharLitTy c
         ; str <- isStrLitTy s
         ; return (Pair b (mkStrLitTy (consFS chr str))) } ]

axUnconsInteracts :: [BuiltInFamInteract]
axUnconsInteracts
  = [ -- (UnconsSymbol x1 ~ z, UnconsSymbol x2 ~ z) => (x1 ~ x2)
      mkInteractUnaryFamDeduction "UnconsI1" typeUnconsSymbolTyCon $ \ x1 z1 x2 z2 ->
      do { same z1 z2; return (Pair x1 x2) } ]

-------------------------------------------------------------------------------
--            CharToNat
-------------------------------------------------------------------------------

typeCharToNatTyCon :: TyCon
typeCharToNatTyCon =
  mkFamilyTyCon name
    (mkTemplateAnonTyConBinders [ charTy ])
    naturalTy
    Nothing
    (BuiltInSynFamTyCon ops)
    Nothing
    (Injective [True])
  where
  name = mkWiredInTyConName UserSyntax gHC_INTERNAL_TYPELITS (fsLit "CharToNat")
                  typeCharToNatTyFamNameKey typeCharToNatTyCon
  ops = BuiltInSynFamily
      { sfMatchFam      = axCharToNatMatches
      , sfInteractTop   = axCharToNatTops
      , sfInteractInert = []
      }

axCharToNatMatches :: [BuiltInFamRewrite]
axCharToNatMatches
  = [ mkUnaryConstFoldAxiom tc "CharToNatDef" isCharLitTy $    -- CharToNat 'a' --> 97
      \x -> Just $ num (charToInteger x) ]
  where
    tc = typeCharToNatTyCon

axCharToNatTops :: [BuiltInFamInteract]
axCharToNatTops
  = [ -- (CharToNat c ~ 122) => (c ~ 'z')
      mkTopUnaryFamDeduction "CharToNatT1" typeCharToNatTyCon $ \c r ->
      do { nr <- isNumLitTy r; chr <- integerToChar nr; return (Pair c (mkCharLitTy chr)) } ]

-------------------------------------------------------------------------------
--            NatToChar
-------------------------------------------------------------------------------

typeNatToCharTyCon :: TyCon
typeNatToCharTyCon =
  mkFamilyTyCon name
    (mkTemplateAnonTyConBinders [ naturalTy ])
    charTy
    Nothing
    (BuiltInSynFamTyCon ops)
    Nothing
    (Injective [True])
  where
  name = mkWiredInTyConName UserSyntax gHC_INTERNAL_TYPELITS (fsLit "NatToChar")
                  typeNatToCharTyFamNameKey typeNatToCharTyCon
  ops = BuiltInSynFamily
      { sfMatchFam      = axNatToCharMatches
      , sfInteractTop   = axNatToCharTops
      , sfInteractInert = [] }

axNatToCharMatches :: [BuiltInFamRewrite]
axNatToCharMatches
  = [ mkUnaryConstFoldAxiom tc "NatToCharDef" isNumLitTy $    -- NatToChar 97 --> 'a'
      \n -> fmap mkCharLitTy (integerToChar n) ]
  where
    tc = typeNatToCharTyCon

axNatToCharTops :: [BuiltInFamInteract]
axNatToCharTops
  = [ -- (NatToChar n ~ 'z') => (n ~ 122)
      mkTopUnaryFamDeduction "CharToNatT1" typeNatToCharTyCon $ \n r ->
      do { c <- isCharLitTy r; return (Pair n (mkNumLitTy (charToInteger c))) } ]


-----------------------------------------------------------------------------
--                       CmpChar
-----------------------------------------------------------------------------

typeCharCmpTyCon :: TyCon
typeCharCmpTyCon =
  mkFamilyTyCon name
    (mkTemplateAnonTyConBinders [ charTy, charTy ])
    orderingKind
    Nothing
    (BuiltInSynFamTyCon ops)
    Nothing
    NotInjective
  where
  name = mkWiredInTyConName UserSyntax gHC_INTERNAL_TYPELITS_INTERNAL (fsLit "CmpChar")
                  typeCharCmpTyFamNameKey typeCharCmpTyCon
  ops = BuiltInSynFamily
      { sfMatchFam      = axCharCmpMatches
      , sfInteractTop   = axCharCmpTops
      , sfInteractInert = []
      }

sc :: TyVar  -- Of kind Char
(sc: _) = mkTemplateTyVars (repeat charTy)

axCharCmpMatches :: [BuiltInFamRewrite]
axCharCmpMatches
  = [ mkRewriteAxiom   tc "CmpCharRefl" [sc] [var sc, var sc] (ordering EQ) -- s `cmp` s --> EQ
    , mkBinConstFoldAxiom tc "CmpCharDef" isCharLitTy isCharLitTy $         -- 'a' `cmp` 'b' --> LT
      \chr1 chr2 -> Just $ ordering $ compare chr1 chr2 ]
  where
    tc = typeCharCmpTyCon

axCharCmpTops :: [BuiltInFamInteract]
axCharCmpTops
  = [  -- (CmpChar s t ~ EQ) => s ~ t
      mkTopBinFamDeduction "CmpCharT" typeCharCmpTyCon $ \ s t r ->
      do { EQ <- isOrderingLitTy r; return (Pair s t) } ]


{-------------------------------------------------------------------------------
Various utilities for making axioms and types
-------------------------------------------------------------------------------}

(===) :: Type -> Type -> Pair Type
x === y = Pair x y

num :: Integer -> Type
num = mkNumLitTy

var :: TyVar -> Type
var = mkTyVarTy

(.+.) :: Type -> Type -> Type
s .+. t = mkTyConApp typeNatAddTyCon [s,t]

{-
(.-.) :: Type -> Type -> Type
s .-. t = mkTyConApp typeNatSubTyCon [s,t]

(.*.) :: Type -> Type -> Type
s .*. t = mkTyConApp typeNatMulTyCon [s,t]

tDiv :: Type -> Type -> Type
tDiv s t = mkTyConApp typeNatDivTyCon [s,t]

tMod :: Type -> Type -> Type
tMod s t = mkTyConApp typeNatModTyCon [s,t]

(.^.) :: Type -> Type -> Type
s .^. t = mkTyConApp typeNatExpTyCon [s,t]

cmpNat :: Type -> Type -> Type
cmpNat s t = mkTyConApp typeNatCmpTyCon [s,t]

cmpSymbol :: Type -> Type -> Type
cmpSymbol s t = mkTyConApp typeSymbolCmpTyCon [s,t]

appendSymbol :: Type -> Type -> Type
appendSymbol s t = mkTyConApp typeSymbolAppendTyCon [s, t]
-}


nullStrLitTy :: Type  -- The type ""
nullStrLitTy = mkStrLitTy nilFS

isStrLitTyS :: Type -> Maybe String
isStrLitTyS ty = do { fs <- isStrLitTy ty; return (unpackFS fs) }

mkStrLitTyS :: String -> Type
mkStrLitTyS s = mkStrLitTy (mkFastString s)

charSymbolPair :: Type -> Type -> Type
charSymbolPair = mkPromotedPairTy charTy typeSymbolKind

charSymbolPairKind :: Kind
charSymbolPairKind = mkTyConApp pairTyCon [charTy, typeSymbolKind]

orderingKind :: Kind
orderingKind = mkTyConApp orderingTyCon []

ordering :: Ordering -> Type
ordering o =
  case o of
    LT -> mkTyConApp promotedLTDataCon []
    EQ -> mkTyConApp promotedEQDataCon []
    GT -> mkTyConApp promotedGTDataCon []

isOrderingLitTy :: Type -> Maybe Ordering
isOrderingLitTy tc =
  do (tc1,[]) <- splitTyConApp_maybe tc
     case () of
       _ | tc1 == promotedLTDataCon -> return LT
         | tc1 == promotedEQDataCon -> return EQ
         | tc1 == promotedGTDataCon -> return GT
         | otherwise                -> Nothing

-- Make a unary built-in constructor of kind: Nat -> Nat
mkTypeNatFunTyCon1 :: Name -> BuiltInSynFamily -> TyCon
mkTypeNatFunTyCon1 op tcb =
  mkFamilyTyCon op
    (mkTemplateAnonTyConBinders [ naturalTy ])
    naturalTy
    Nothing
    (BuiltInSynFamTyCon tcb)
    Nothing
    NotInjective

-- Make a binary built-in constructor of kind: Nat -> Nat -> Nat
mkTypeNatFunTyCon2 :: Name -> BuiltInSynFamily -> TyCon
mkTypeNatFunTyCon2 op tcb =
  mkFamilyTyCon op
    (mkTemplateAnonTyConBinders [ naturalTy, naturalTy ])
    naturalTy
    Nothing
    (BuiltInSynFamTyCon tcb)
    Nothing
    NotInjective

-- Make a binary built-in constructor of kind: Symbol -> Symbol -> Symbol
mkTypeSymbolFunTyCon2 :: Name -> BuiltInSynFamily -> TyCon
mkTypeSymbolFunTyCon2 op tcb =
  mkFamilyTyCon op
    (mkTemplateAnonTyConBinders [ typeSymbolKind, typeSymbolKind ])
    typeSymbolKind
    Nothing
    (BuiltInSynFamTyCon tcb)
    Nothing
    NotInjective

injCheck :: Type -> Type -> Type -> Type -> Type -> Type -> Maybe TypeEqn
-- If x1=x2 and y1=y2, emit z1=z2
injCheck x1 x2 y1 y2 z1 z2
  = do { guard (x1 `tcEqType` x2); guard (y1 `tcEqType` y2); return (Pair z1 z2) }

same :: Type -> Type -> Maybe ()
same ty1 ty2 = guard (ty1 `tcEqType` ty2)

known :: Type -> (Integer -> Bool) -> Maybe Integer
known x p = do { nx <- isNumLitTy x; guard (p nx); return nx }

charToInteger :: Char -> Integer
charToInteger c = fromIntegral (Char.ord c)

integerToChar :: Integer -> Maybe Char
integerToChar n | inBounds = Just (Char.chr (fromInteger n))
  where inBounds = n >= charToInteger minBound &&
                   n <= charToInteger maxBound
integerToChar _ = Nothing


{- -----------------------------------------------------------------------------
These inverse functions are used for simplifying propositions using
concrete natural numbers.
----------------------------------------------------------------------------- -}

-- | Subtract two natural numbers.
minus :: Integer -> Integer -> Maybe Integer
minus x y = if x >= y then Just (x - y) else Nothing

-- | Compute the exact logarithm of a natural number.
-- The logarithm base is the second argument.
logExact :: Integer -> Integer -> Maybe Integer
logExact x y = do (z,True) <- genLog x y
                  return z


-- | Divide two natural numbers.
divide :: Integer -> Integer -> Maybe Integer
divide _ 0  = Nothing
divide x y  = case divMod x y of
                (a,0) -> Just a
                _     -> Nothing

-- | Compute the exact root of a natural number.
-- The second argument specifies which root we are computing.
rootExact :: Integer -> Integer -> Maybe Integer
rootExact x y = do (z,True) <- genRoot x y
                   return z



{- | Compute the n-th root of a natural number, rounded down to
the closest natural number.  The boolean indicates if the result
is exact (i.e., True means no rounding was done, False means rounded down).
The second argument specifies which root we are computing. -}
genRoot :: Integer -> Integer -> Maybe (Integer, Bool)
genRoot _  0    = Nothing
genRoot x0 1    = Just (x0, True)
genRoot x0 root = Just (search 0 (x0+1))
  where
  search from to = let x = from + div (to - from) 2
                       a = x ^ root
                   in case compare a x0 of
                        EQ              -> (x, True)
                        LT | x /= from  -> search x to
                           | otherwise  -> (from, False)
                        GT | x /= to    -> search from x
                           | otherwise  -> (from, False)

{- | Compute the logarithm of a number in the given base, rounded down to the
closest integer.  The boolean indicates if we the result is exact
(i.e., True means no rounding happened, False means we rounded down).
The logarithm base is the second argument. -}
genLog :: Integer -> Integer -> Maybe (Integer, Bool)
genLog x 0    = if x == 1 then Just (0, True) else Nothing
genLog _ 1    = Nothing
genLog 0 _    = Nothing
genLog x base = Just (exactLoop 0 x)
  where
  exactLoop s i
    | i == 1     = (s,True)
    | i < base   = (s,False)
    | otherwise  =
        let s1 = s + 1
        in s1 `seq` case divMod i base of
                      (j,r)
                        | r == 0    -> exactLoop s1 j
                        | otherwise -> (underLoop s1 j, False)

  underLoop s i
    | i < base  = s
    | otherwise = let s1 = s + 1 in s1 `seq` underLoop s1 (div i base)

