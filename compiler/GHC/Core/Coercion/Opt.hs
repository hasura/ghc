-- (c) The University of Glasgow 2006

{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module GHC.Core.Coercion.Opt
   ( optCoercion
   , OptCoercionOpts (..)
   , OptDCoMethod (..)
   )
where

import GHC.Prelude

import GHC.Tc.Utils.TcType   ( exactTyCoVarsOfType )

import GHC.Core.TyCo.Rep
import GHC.Core.TyCo.Subst
import GHC.Core.TyCo.Compare( eqType )
import GHC.Core.Coercion
import GHC.Core.Type as Type hiding( substTyVarBndr, substTy )
import GHC.Core.TyCon
import GHC.Core.Coercion.Axiom
import GHC.Core.Unify

import GHC.Types.Var
import GHC.Types.Var.Set
import GHC.Types.Var.Env
import GHC.Types.Unique.Set

import GHC.Data.Pair
import GHC.Data.List.SetOps ( getNth )

import GHC.Utils.Outputable
import GHC.Utils.Constants (debugIsOn)
import GHC.Utils.Misc
import GHC.Utils.Panic
import GHC.Utils.Panic.Plain

import Control.Monad   ( zipWithM )
import qualified Data.Kind ( Type )

{-
%************************************************************************
%*                                                                      *
                 Optimising coercions
%*                                                                      *
%************************************************************************

This module does coercion optimisation.  See the paper

   Evidence normalization in Systtem FV (RTA'13)
   https://simon.peytonjones.org/evidence-normalization/

The paper is also in the GHC repo, in docs/opt-coercion.

Note [Optimising coercion optimisation]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Looking up a coercion's role or kind is linear in the size of the
coercion. Thus, doing this repeatedly during the recursive descent
of coercion optimisation is disastrous. We must be careful to avoid
doing this if at all possible.

Because it is generally easy to know a coercion's components' roles
from the role of the outer coercion, we pass down the known role of
the input in the algorithm below. We also keep functions opt_co2
and opt_co3 separate from opt_co4, so that the former two do Phantom
checks that opt_co4 can avoid. This is a big win because Phantom coercions
rarely appear within non-phantom coercions -- only in some TyConAppCos
and some AxiomInstCos. We handle these cases specially by calling
opt_co2.

Note [Optimising InstCo]
~~~~~~~~~~~~~~~~~~~~~~~~
(1) tv is a type variable
When we have (InstCo (ForAllCo tv h g) g2), we want to optimise.

Let's look at the typing rules.

h : k1 ~ k2
tv:k1 |- g : t1 ~ t2
-----------------------------
ForAllCo tv h g : (all tv:k1.t1) ~ (all tv:k2.t2[tv |-> tv |> sym h])

g1 : (all tv:k1.t1') ~ (all tv:k2.t2')
g2 : s1 ~ s2
--------------------
InstCo g1 g2 : t1'[tv |-> s1] ~ t2'[tv |-> s2]

We thus want some coercion proving this:

  (t1[tv |-> s1]) ~ (t2[tv |-> s2 |> sym h])

If we substitute the *type* tv for the *coercion*
(g2 ; t2 ~ t2 |> sym h) in g, we'll get this result exactly.
This is bizarre,
though, because we're substituting a type variable with a coercion. However,
this operation already exists: it's called *lifting*, and defined in GHC.Core.Coercion.
We just need to enhance the lifting operation to be able to deal with
an ambient substitution, which is why a LiftingContext stores a TCvSubst.

(2) cv is a coercion variable
Now consider we have (InstCo (ForAllCo cv h g) g2), we want to optimise.

h : (t1 ~r t2) ~N (t3 ~r t4)
cv : t1 ~r t2 |- g : t1' ~r2 t2'
n1 = nth r 2 (downgradeRole r N h) :: t1 ~r t3
n2 = nth r 3 (downgradeRole r N h) :: t2 ~r t4
------------------------------------------------
ForAllCo cv h g : (all cv:t1 ~r t2. t1') ~r2
                  (all cv:t3 ~r t4. t2'[cv |-> n1 ; cv ; sym n2])

g1 : (all cv:t1 ~r t2. t1') ~ (all cv: t3 ~r t4. t2')
g2 : h1 ~N h2
h1 : t1 ~r t2
h2 : t3 ~r t4
------------------------------------------------
InstCo g1 g2 : t1'[cv |-> h1] ~ t2'[cv |-> h2]

We thus want some coercion proving this:

  t1'[cv |-> h1] ~ t2'[cv |-> n1 ; h2; sym n2]

So we substitute the coercion variable c for the coercion
(h1 ~N (n1; h2; sym n2)) in g.
-}

-- | Coercion optimisation options
newtype OptCoercionOpts = OptCoercionOpts
   { optCoercionOpts :: Maybe OptDCoMethod
       -- ^ @Nothing@: no coercion optimisation.
       -- ^ @Just opt@: do full coercion optimisation, with @opt@ specifying
       --   how to deal with directed coercions.
   }

data OptDCoMethod
  = HydrateDCos
      -- ^ Turn directed coercions back into fully-fledged coercions in the
      -- coercion optimiser, so that they can be fully optimised.
  | OptDCos
      -- ^ Optimise directed coercions with the (currently limited)
      -- forms of optimisation avaiable for directed coercions.
      { skipDCoOpt :: !Bool
        -- ^ Whether to skip optimisation of directed coercions entirely
        -- when possible.
        }

data OptCoParams =
  OptCoParams { optDCoMethod :: !OptDCoMethod }

optCoercion :: OptCoercionOpts -> Subst -> Coercion -> NormalCo
-- ^ optCoercion applies a substitution to a coercion,
--   *and* optimises it to reduce its size
optCoercion (OptCoercionOpts opts) env co
  | Just dco_method <- opts = optCoercion'
                                (OptCoParams { optDCoMethod = dco_method }) env
                            $ co
  | otherwise               = substCo env $ co

optCoercion' :: OptCoParams -> Subst -> Coercion -> NormalCo
optCoercion' opts env co
  | debugIsOn
  = let out_co = opt_co1 opts lc False co
        (Pair in_ty1  in_ty2,  in_role)  = coercionKindRole co
        (Pair out_ty1 out_ty2, out_role) = coercionKindRole out_co
    in
    assertPpr (substTyUnchecked env in_ty1 `eqType` out_ty1 &&
               substTyUnchecked env in_ty2 `eqType` out_ty2 &&
               in_role == out_role)
              (hang (text "optCoercion changed types!")
                  2 (vcat [ text "in_co:" <+> ppr co
                          , text "in_ty1:" <+> ppr in_ty1
                          , text "in_ty2:" <+> ppr in_ty2
                          , text "out_co:" <+> ppr out_co
                          , text "out_ty1:" <+> ppr out_ty1
                          , text "out_ty2:" <+> ppr out_ty2
                          , text "in_role:" <+> ppr in_role
                          , text "out_role:" <+> ppr out_role
                          , vcat $ map ppr_one $ nonDetEltsUniqSet $ coVarsOfCo co
                          , text "subst:" <+> ppr env ]))
               out_co

  | otherwise         = opt_co1 opts lc False co
  where
    lc = mkSubstLiftingContext env
    ppr_one cv = ppr cv <+> dcolon <+> ppr (coVarKind cv)


type NormalCo    = Coercion
  -- Invariants:
  --  * The substitution has been fully applied
  --  * For trans coercions (co1 `trans` co2)
  --       co1 is not a trans, and neither co1 nor co2 is identity

type NormalDCo = DCoercion

type NormalNonIdCo = NormalCo  -- Extra invariant: not the identity
type NormalNonIdDCo = NormalDCo  -- Extra invariant: not the identity

-- | Do we apply a @sym@ to the result?
type SymFlag = Bool

-- | Do we force the result to be representational?
type ReprFlag = Bool

-- | Optimize a coercion, making no assumptions. All coercions in
-- the lifting context are already optimized (and sym'd if nec'y)
opt_co1 :: OptCoParams
        -> LiftingContext
        -> SymFlag
        -> Coercion -> NormalCo
opt_co1 opts env sym co = opt_co2 opts env sym (coercionRole co) co

-- See Note [Optimising coercion optimisation]
-- | Optimize a coercion, knowing the coercion's role. No other assumptions.
opt_co2 :: OptCoParams
        -> LiftingContext
        -> SymFlag
        -> Role   -- ^ The role of the input coercion
        -> Coercion -> NormalCo
opt_co2 opts env sym Phantom co = opt_phantom opts env sym co
opt_co2 opts env sym r       co = opt_co3 opts env sym Nothing r co

-- See Note [Optimising coercion optimisation]
-- | Optimize a coercion, knowing the coercion's non-Phantom role.
opt_co3 :: OptCoParams -> LiftingContext -> SymFlag -> Maybe Role -> Role -> Coercion -> NormalCo
opt_co3 opts env sym (Just Phantom)          _ co = opt_phantom opts env sym co
opt_co3 opts env sym (Just Representational) r co = opt_co4 opts env sym True  r co
  -- if mrole is Just Nominal, that can't be a downgrade, so we can ignore
opt_co3 opts env sym _                       r co = opt_co4 opts env sym False r co

-- | Utility function for debugging coercion optimisation: uncomment
-- the logging functions in the body of this function, and the coercion
-- optimiser will produce a log of what it is doing.
wrap :: (Outputable in_co, Outputable out_co) => String -> Optimiser in_co out_co -> Optimiser in_co out_co
wrap _str opt_thing opts env sym rep r co
  = {- pprTrace (_str ++ " wrap {")
    ( vcat [ text "Sym:" <+> ppr sym
           , text "Rep:" <+> ppr rep
           , text "Role:" <+> ppr r
           , text "Co:" <+> ppr co
           , text "LC:" <+> ppr env
           , text "Subst:" <+> ppr (lcTCvSubst env)]) $
    --assert (r == coercionRole co)
    pprTrace (_str ++ " wrap }") (ppr co $$ text "---" $$ ppr result) $ -}
    result
  where result = opt_thing opts env sym rep r co

-- See Note [Optimising coercion optimisation]
-- | Optimize a non-phantom coercion.
opt_co4_wrap :: String -> OptCoParams -> LiftingContext -> SymFlag -> ReprFlag -> Role -> Coercion -> NormalCo
-- Precondition: In every call (opt_co4 lc sym rep role co)
--               we should have role = coercionRole co

opt_co4_wrap str opts env sym rep r co = wrap ("opt_co4 " ++ str) opt_co4 opts env sym rep r co

opt_co4 :: OptCoParams -> LiftingContext -> SymFlag -> ReprFlag -> Role -> Coercion -> NormalCo
opt_co4 _ env _   rep r (Refl ty)
  = assertPpr (r == Nominal)
              (text "Expected role:" <+> ppr r    $$
               text "Found role:" <+> ppr Nominal $$
               text "Type:" <+> ppr ty) $
    liftCoSubst (chooseRole rep r) env ty

opt_co4 _ env _   rep r (GRefl _r ty MRefl)
  = assertPpr (r == _r)
              (text "Expected role:" <+> ppr r $$
               text "Found role:" <+> ppr _r   $$
               text "Type:" <+> ppr ty) $
    liftCoSubst (chooseRole rep r) env ty

opt_co4 opts env sym  rep r (GRefl _r ty (MCo co))
  = assertPpr (r == _r)
              (text "Expected role:" <+> ppr r $$
               text "Found role:" <+> ppr _r   $$
               text "Type:" <+> ppr ty) $
    if isGReflCo co || isGReflCo co'
    then liftCoSubst r' env ty
    else wrapSym sym $ mkCoherenceRightCo r' ty' co' (liftCoSubst r' env ty)
  where
    r'  = chooseRole rep r
    ty' = substTy (lcSubstLeft env) ty
    co' = opt_co4 opts env False False Nominal co

opt_co4 opts env sym rep r (SymCo co)  = opt_co4_wrap "SymCo" opts env (not sym) rep r co
  -- surprisingly, we don't have to do anything to the env here. This is
  -- because any "lifting" substitutions in the env are tied to ForAllCos,
  -- which treat their left and right sides differently. We don't want to
  -- exchange them.

opt_co4 opts env sym rep r g@(TyConAppCo _r tc cos)
  = assert (r == _r) $
    case (rep, r) of
      (True, Nominal) ->
        mkTyConAppCo Representational tc
                     (zipWith3 (opt_co3 opts env sym)
                               (map Just (tyConRoleListRepresentational tc))
                               (repeat Nominal)
                               cos)
      (False, Nominal) ->
        mkTyConAppCo Nominal tc (map (opt_co4_wrap "TyConAppCo (False, Nominal)" opts env sym False Nominal) cos)
      (_, Representational) ->
                      -- must use opt_co2 here, because some roles may be P
                      -- See Note [Optimising coercion optimisation]
        mkTyConAppCo r tc (zipWith (opt_co2 opts env sym)
                                   (tyConRoleListRepresentational tc)  -- the current roles
                                   cos)
      (_, Phantom) -> pprPanic "opt_co4 sees a phantom!" (ppr g)

opt_co4 opts env sym rep r (AppCo co1 co2)
  = mkAppCo (opt_co4_wrap "AppCo co1" opts env sym rep r co1)
            (opt_co4_wrap "AppCo co2" opts env sym False Nominal co2)

opt_co4 opts env sym rep r (ForAllCo tv k_co co)
  = case optForAllCoBndr opts env sym tv k_co of
      (env', tv', k_co') -> mkForAllCo tv' k_co' $
                            opt_co4_wrap "ForAllCo" opts env' sym rep r co
     -- Use the "mk" functions to check for nested Refls

opt_co4 opts env sym rep r (FunCo _r afl afr cow co1 co2)
  = assert (r == _r) $
    mkFunCo2 r' afl' afr' cow' co1' co2'
  where
    co1' = opt_co4_wrap "FunCo co1" opts env sym rep r co1
    co2' = opt_co4_wrap "FunCo co2" opts env sym rep r co2
    cow' = opt_co1 opts env sym cow
    !r' | rep       = Representational
        | otherwise = r
    !(afl', afr') | sym       = (afr,afl)
                  | otherwise = (afl,afr)

opt_co4 opts env sym rep r (CoVarCo cv)
  | Just co <- lookupCoVar (lcSubst env) cv
  = opt_co4_wrap "CoVarCo" opts (zapLiftingContext env) sym rep r co

  | ty1 `eqType` ty2   -- See Note [Optimise CoVarCo to Refl]
  = mkReflCo (chooseRole rep r) ty1

  | otherwise
  = assert (isCoVar cv1 )
    wrapRole rep r $ wrapSym sym $
    CoVarCo cv1

  where
    Pair ty1 ty2 = coVarTypes cv1

    cv1 = case lookupInScope (lcInScopeSet env) cv of
             Just cv1 -> cv1
             Nothing  -> warnPprTrace True
                          "opt_co: not in scope"
                          (ppr cv $$ ppr env)
                          cv
          -- cv1 might have a substituted kind!

opt_co4 _ _ _ _ _ (HoleCo h)
  = pprPanic "opt_univ fell into a hole" (ppr h)

opt_co4 opts env sym rep r (AxiomInstCo con ind cos)
    -- Do *not* push sym inside top-level axioms
    -- e.g. if g is a top-level axiom
    --   g a : f a ~ a
    -- then (sym (g ty)) /= g (sym ty) !!
  = assert (r == coAxiomRole con )
    wrapRole rep (coAxiomRole con) $
    wrapSym sym $
                       -- some sub-cos might be P: use opt_co2
                       -- See Note [Optimising coercion optimisation]
    AxiomInstCo con ind (zipWith (opt_co2 opts env False)
                                 (coAxBranchRoles (coAxiomNthBranch con ind))
                                 cos)
      -- Note that the_co does *not* have sym pushed into it

opt_co4 opts env@(LC _ _lift_co_env) sym rep r (HydrateDCo _r lhs_ty dco rhs_ty)
  = case optDCoMethod opts of
      HydrateDCos ->
        opt_co4 opts env sym rep r (hydrateOneLayerDCo r lhs_ty dco)
      OptDCos { skipDCoOpt = do_skip }
        | do_skip && isEmptyVarEnv _lift_co_env
        -> let res = substCo (lcSubst env) (HydrateDCo r lhs_ty dco rhs_ty)
        in assert (r == _r) $
           wrapSym sym $
           wrapRole rep r $
           res
        | otherwise
        -> assert (r == _r) $
             wrapSym sym $
             (\ (lhs', dco') -> mkHydrateDCo r' lhs' dco' rhs') $
             opt_dco4_wrap "HydrateDCo" opts env rep r lhs_ty dco
  where
    rhs' = substTyUnchecked (lcSubstRight env) rhs_ty
    r'   = chooseRole rep r

opt_co4 opts env sym rep r (UnivCo prov _r t1 t2)
  = assert (r == _r) $
    opt_univ Co opts env sym prov (chooseRole rep r) t1 t2

opt_co4 opts env sym rep r (TransCo co1 co2)
                      -- sym (g `o` h) = sym h `o` sym g
  | sym       = opt_trans opts in_scope co2' co1'
  | otherwise = opt_trans opts in_scope co1' co2'

  where
    co1' = opt_co4_wrap "TransCo co1" opts env sym rep r co1
    co2' = opt_co4_wrap "TransCo co2" opts env sym rep r co2
    in_scope = lcInScopeSet env

opt_co4 _ env _sym rep r (SelCo n co)
  | Just (ty, _co_role) <- isReflCo_maybe co
  = liftCoSubst (chooseRole rep r) env (getNthFromType n ty)
    -- NB: it is /not/ true that r = _co_role
    --     Rather, r = coercionRole (SelCo n co)

opt_co4 opts env sym rep r (SelCo (SelTyCon n r1) (TyConAppCo _ _ cos))
  = assert (r == r1 )
    opt_co4_wrap "SelTyCon" opts env sym rep r (cos `getNth` n)

-- see the definition of GHC.Builtin.Types.Prim.funTyCon
opt_co4 opts env sym rep r (SelCo (SelFun fs) (FunCo _r2 _afl _afr w co1 co2))
  = opt_co4_wrap "SelFun" opts env sym rep r (getNthFun fs w co1 co2)

opt_co4 opts env sym rep _ (SelCo SelForAll (ForAllCo _ eta _))
      -- works for both tyvar and covar
  = opt_co4_wrap "SelForAll" opts env sym rep Nominal eta

opt_co4 opts env sym rep r (SelCo n co)
  | Just nth_co <- case (co', n) of
      (TyConAppCo _ _ cos, SelTyCon n _) -> Just (cos `getNth` n)
      (FunCo _ _ _ w co1 co2, SelFun fs) -> Just (getNthFun fs w co1 co2)
      (ForAllCo _ eta _, SelForAll)      -> Just eta
      _                  -> Nothing
  = if rep && (r == Nominal)
      -- keep propagating the SubCo
    then opt_co4_wrap "NthCo" opts (zapLiftingContext env) False True Nominal nth_co
    else nth_co

  | otherwise
  = wrapRole rep r $ SelCo n co'
  where
    co' = opt_co1 opts env sym co

opt_co4 opts env sym rep r (LRCo lr co)
  | Just pr_co <- splitAppCo_maybe co
  = assert (r == Nominal )
    opt_co4_wrap "LrCO AppCo" opts env sym rep Nominal (pick_lr lr pr_co)
  | Just pr_co <- splitAppCo_maybe co'
  = assert (r == Nominal) $
    if rep
    then opt_co4_wrap "LrCo AppCo'" opts (zapLiftingContext env) False True Nominal (pick_lr lr pr_co)
    else pick_lr lr pr_co
  | otherwise
  = wrapRole rep Nominal $ LRCo lr co'
  where
    co' = opt_co4_wrap "LrCo co'" opts env sym False Nominal co

    pick_lr CLeft  (l, _) = l
    pick_lr CRight (_, r) = r

-- See Note [Optimising InstCo]
opt_co4 opts env sym rep r (InstCo co1 arg)
    -- forall over type...
  | Just (tv, kind_co, co_body) <- splitForAllCo_ty_maybe co1
  = opt_co4_wrap "InstCo ForAllTy" opts
        (extendLiftingContext env tv
          (mkCoherenceRightCo Nominal t2 (mkSymCo kind_co) sym_arg))
            -- mkSymCo kind_co :: k1 ~ k2
            -- sym_arg :: (t1 :: k1) ~ (t2 :: k2)
            -- tv |-> (t1 :: k1) ~ (((t2 :: k2) |> (sym kind_co)) :: k1)
        sym rep r co_body

    -- forall over coercion...
  | Just (cv, kind_co, co_body) <- splitForAllCo_co_maybe co1
  , CoercionTy h1 <- t1
  , CoercionTy h2 <- t2
  = let new_co = mk_new_co cv (opt_co4_wrap "InstCo kind_co" opts env sym False Nominal kind_co) h1 h2
    in opt_co4_wrap "InstCo ForAllCo" opts (extendLiftingContext env cv new_co) sym rep r co_body

    -- See if it is a forall after optimization
    -- If so, do an inefficient one-variable substitution, then re-optimize

    -- forall over type...
  | Just (tv', kind_co', co_body') <- splitForAllCo_ty_maybe co1'
  = opt_co4_wrap "InstCo ForAllTy 2" opts
      (extendLiftingContext (zapLiftingContext env) tv'
        (mkCoherenceRightCo Nominal t2' (mkSymCo kind_co') arg'))
      False False r' co_body'

    -- forall over coercion...
  | Just (cv', kind_co', co_body') <- splitForAllCo_co_maybe co1'
  , CoercionTy h1' <- t1'
  , CoercionTy h2' <- t2'
  = let new_co = mk_new_co cv' kind_co' h1' h2'
    in opt_co4_wrap "InstCo ForAllCo 2" opts (extendLiftingContext (zapLiftingContext env) cv' new_co)
                    False False r' co_body'

  | otherwise = InstCo co1' arg'
  where
    co1'    = opt_co4_wrap "InstCo recur co1" opts env sym rep r co1
    r'      = chooseRole rep r
    arg'    = opt_co4_wrap "InstCo recur arg" opts env sym False Nominal arg
    sym_arg = wrapSym sym arg'

    -- Performance note: don't be alarmed by the two calls to coercionKind
    -- here, as only one call to coercionKind is actually demanded per guard.
    -- t1/t2 are used when checking if co1 is a forall, and t1'/t2' are used
    -- when checking if co1' (i.e., co1 post-optimization) is a forall.
    --
    -- t1/t2 must come from sym_arg, not arg', since it's possible that arg'
    -- might have an extra Sym at the front (after being optimized) that co1
    -- lacks, so we need to use sym_arg to balance the number of Syms. (#15725)
    Pair t1  t2  = coercionKind sym_arg
    Pair t1' t2' = coercionKind arg'

    mk_new_co cv kind_co h1 h2
      = let -- h1 :: (t1 ~ t2)
            -- h2 :: (t3 ~ t4)
            -- kind_co :: (t1 ~ t2) ~ (t3 ~ t4)
            -- n1 :: t1 ~ t3
            -- n2 :: t2 ~ t4
            -- new_co = (h1 :: t1 ~ t2) ~ ((n1;h2;sym n2) :: t1 ~ t2)
            r2  = coVarRole cv
            kind_co' = downgradeRole r2 Nominal kind_co
            n1 = mkSelCo (SelTyCon 2 r2) kind_co'
            n2 = mkSelCo (SelTyCon 3 r2) kind_co'
         in mkProofIrrelCo Nominal (Refl (coercionType h1)) h1
                           (n1 `mkTransCo` h2 `mkTransCo` (mkSymCo n2))

opt_co4 opts env sym _rep r (KindCo co)
  = assert (r == Nominal) $
    let kco' = promoteCoercion co in
    case kco' of
      KindCo co' -> promoteCoercion (opt_co1 opts env sym co')
      _          -> opt_co4_wrap "KindCo" opts env sym False Nominal kco'
  -- This might be able to be optimized more to do the promotion
  -- and substitution/optimization at the same time

opt_co4 opts env sym _ _r (SubCo co)
  = assert (_r == Representational) $
    let res = opt_co4_wrap "SubCo" opts env sym True Nominal co
    in case coercionRole res of
         Nominal -> SubCo res
         _       -> res

-- This could perhaps be optimized more.
opt_co4 opts env sym rep r (AxiomRuleCo co cs)
  = assert (r == coaxrRole co) $
    wrapRole rep r $
    wrapSym sym $
    AxiomRuleCo co (zipWith (opt_co2 opts env False) (coaxrAsmpRoles co) cs)

{- Note [Optimise CoVarCo to Refl]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
If we have (c :: t~t) we can optimise it to Refl. That increases the
chances of floating the Refl upwards; e.g. Maybe c --> Refl (Maybe t)

We do so here in optCoercion, not in mkCoVarCo; see Note [mkCoVarCo]
in GHC.Core.Coercion.
-}

-------------
-- | Optimize a phantom coercion. The input coercion may not necessarily
-- be a phantom, but the output sure will be.
opt_phantom :: OptCoParams -> LiftingContext -> SymFlag -> Coercion -> NormalCo
opt_phantom opts env sym co
  = opt_univ Co opts env sym (PhantomProv (mkKindCo co)) Phantom ty1 ty2
  where
    Pair ty1 ty2 = coercionKind co

{- Note [Differing kinds]
   ~~~~~~~~~~~~~~~~~~~~~~
The two types may not have the same kind (although that would be very unusual).
But even if they have the same kind, and the same type constructor, the number
of arguments in a `CoTyConApp` can differ. Consider

  Any :: forall k. k

  Any * Int                      :: *
  Any (*->*) Maybe Int  :: *

Hence the need to compare argument lengths; see #13658

Note [opt_univ needs injectivity]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
If opt_univ sees a coercion between `T a1 a2` and `T b1 b2` it will optimize it
by producing a TyConAppCo for T, and pushing the UnivCo into the arguments.  But
this works only if T is injective. Otherwise we can have something like

  type family F x where
    F Int  = Int
    F Bool = Int

where `UnivCo :: F Int ~ F Bool` is reasonable (it is effectively just an
alternative representation for a couple of uses of AxiomInstCos) but we do not
want to produce `F (UnivCo :: Int ~ Bool)` where the inner coercion is clearly
inconsistent.  Hence the opt_univ case for TyConApps checks isInjectiveTyCon.
See #19509.

 -}

type OptRes :: Data.Kind.Type -> Data.Kind.Type
type family OptRes co_or_dco where
  OptRes Coercion  = Coercion
  OptRes DCoercion = ( Type, DCoercion )

type Optimiser in_co out_co =
      OptCoParams -> LiftingContext -> SymFlag -> ReprFlag -> Role -> in_co -> out_co

opt_co_or_dco :: CoOrDCo co_or_dco -> Type -> Optimiser co_or_dco co_or_dco
opt_co_or_dco Co  _    = opt_co4
opt_co_or_dco DCo l_ty = \ opts lc sym repr r dco ->
  assert (sym == False) $
  snd $
  opt_dco4 opts lc repr r l_ty dco

opt_univ :: forall co_or_dco
         .  Outputable co_or_dco
         => CoOrDCo co_or_dco
         -> OptCoParams
         -> LiftingContext -> SymFlag -> UnivCoProvenance co_or_dco -> Role
         -> Type -> Type -> OptRes co_or_dco
opt_univ co_or_dco opts env sym (PhantomProv h) _r ty1 ty2
  | sym       = mk_phantom h' ty2' ty1'
  | otherwise = mk_phantom h' ty1' ty2'
  where
    h' = wrap "opt_univ PhantomProv" (opt_co_or_dco co_or_dco ty1) opts env sym False Nominal h
    ty1' = substTy (lcSubstLeft  env) ty1
    ty2' = substTy (lcSubstRight env) ty2

    mk_phantom :: co_or_dco -> Type -> Type -> OptRes co_or_dco
    mk_phantom = case co_or_dco of
      Co  -> mkPhantomCo
      DCo -> \ h t1 t2 -> (t1, mkUnivDCo (PhantomProv h) t2)

opt_univ co_or_dco opts env sym prov role oty1 oty2
  | Just (tc1, tys1) <- splitTyConApp_maybe oty1
  , Just (tc2, tys2) <- splitTyConApp_maybe oty2
  , tc1 == tc2
  , isInjectiveTyCon tc1 role  -- see Note [opt_univ needs injectivity]
  , equalLength tys1 tys2 -- see Note [Differing kinds]
      -- NB: prov must not be the two interesting ones (ProofIrrel & Phantom);
      -- Phantom is already taken care of, and ProofIrrel doesn't relate tyconapps
  = let roles    = tyConRoleListX role tc1
    in case co_or_dco of
          Co ->
            let
              arg_cos  = zipWith3 mk_univ roles tys1 tys2
              arg_cos' = zipWith (opt_co4 opts env sym False) roles arg_cos
            in
              mkTyConAppCo role tc1 arg_cos'
          DCo ->
            let
              arg_cos  = zipWith3 (\ r x y -> snd $ mk_univ r x y) roles tys1 tys2
              (arg_lhs', arg_dcos') = unzip $ zipWith3 (opt_dco4 opts env False) roles tys1 arg_cos
            in
              (mkTyConApp tc1 arg_lhs', mkTyConAppDCo arg_dcos')

  -- can't optimize the AppTy case because we can't build the kind coercions.

  | Just (tv1, ty1) <- splitForAllTyVar_maybe oty1
  , Just (tv2, ty2) <- splitForAllTyVar_maybe oty2
      -- NB: prov isn't interesting here either
  = let k1   = tyVarKind tv1
        k2   = tyVarKind tv2
        eta  = case co_or_dco of
                 Co  -> mk_univ Nominal k1 k2
                 DCo -> snd $ mk_univ Nominal k1 k2
        tv1' = mk_castTy (TyVarTy tv1) k1 eta k2
          -- eta gets opt'ed soon, but not yet.
        ty2' = substTyWith [tv2] [tv1'] ty2

        (env', tv1'', eta') = opt_forall tv1 eta
    in
    mk_forall tv1'' eta' (opt_univ co_or_dco opts env' sym prov' role ty1 ty2')

  | Just (cv1, ty1) <- splitForAllCoVar_maybe oty1
  , Just (cv2, ty2) <- splitForAllCoVar_maybe oty2
      -- NB: prov isn't interesting here either
  = let k1    = varType cv1
        k2    = varType cv2
        r'    = coVarRole cv1
        eta   = case co_or_dco of
                  Co  -> mk_univ Nominal k1 k2
                  DCo -> snd $ mk_univ Nominal k1 k2
        eta_d = downgradeRole r' Nominal $
                case co_or_dco of
                  Co  -> eta
                  DCo -> mkHydrateDCo Nominal k1 eta k2
          -- eta gets opt'ed soon, but not yet.
        n_co  = (mkSymCo $ mkSelCo (SelTyCon 2 r') eta_d) `mkTransCo`
                (mkCoVarCo cv1) `mkTransCo`
                (mkSelCo (SelTyCon 3 r') eta_d)
        ty2'  = substTyWithCoVars [cv2] [n_co] ty2

        (env', cv1', eta') = opt_forall cv1 eta
    in
    mk_forall cv1' eta' (opt_univ co_or_dco opts env' sym prov' role ty1 ty2')

  | otherwise
  = let ty1 = substTyUnchecked (lcSubstLeft  env) oty1
        ty2 = substTyUnchecked (lcSubstRight env) oty2
        (a, b) | sym       = (ty2, ty1)
               | otherwise = (ty1, ty2)
    in
    mk_univ role a b

  where
    mk_castTy :: Type -> Type -> co_or_dco -> Type -> Type
    mk_castTy = case co_or_dco of
      Co  -> \ ty _ co  _ -> CastTy ty co
      DCo -> \ ty l dco r -> CastTy ty (mkHydrateDCo Nominal l dco r)
    mk_univ :: Role -> Type -> Type -> OptRes co_or_dco
    mk_univ = case co_or_dco of
      Co  -> mkUnivCo  prov'
      DCo -> \ _ l_ty r_ty -> (l_ty, mkUnivDCo prov' r_ty)
    mk_forall :: TyCoVar -> co_or_dco -> OptRes co_or_dco -> OptRes co_or_dco
    mk_forall cv eta = case co_or_dco of
      Co  -> mkForAllCo cv eta
      DCo -> \ (_,body) -> (mkTyVarTy cv, mkForAllDCo cv eta body)
    opt_forall :: TyCoVar -> co_or_dco -> (LiftingContext,TyCoVar,co_or_dco)
    opt_forall tv co = case co_or_dco of
      Co  -> optForAllCoBndr  opts env sym tv co
      DCo -> optForAllDCoBndr opts env sym tv co
    prov' :: UnivCoProvenance co_or_dco
    prov' = case prov of
#if __GLASGOW_HASKELL__ < 901
-- This alt is redundant with the first match of the FunDef
      PhantomProv kco    -> PhantomProv
                          $ wrap "univ_co phantom" (opt_co_or_dco co_or_dco oty1)
                              opts env sym False Nominal kco
#endif
      ProofIrrelProv kco -> ProofIrrelProv
                          $ wrap "univ_co proof_irrel" (opt_co_or_dco co_or_dco oty1)
                              opts env sym False Nominal kco
      PluginProv str     -> PluginProv str
      CorePrepProv homo  -> CorePrepProv homo

-------------
opt_transList :: HasDebugCallStack => OptCoParams -> InScopeSet -> [NormalCo] -> [NormalCo] -> [NormalCo]
opt_transList opts is = zipWithEqual "opt_transList" (opt_trans opts is)
  -- The input lists must have identical length.

opt_trans :: OptCoParams -> InScopeSet -> NormalCo -> NormalCo -> NormalCo
opt_trans opts is co1 co2
  | isReflCo co1 = co2
    -- optimize when co1 is a Refl Co
  | otherwise    = opt_trans1 opts is co1 co2

opt_trans1 :: OptCoParams -> InScopeSet -> NormalNonIdCo -> NormalCo -> NormalCo
-- First arg is not the identity
opt_trans1 opts is co1 co2
  | isReflCo co2 = co1
    -- optimize when co2 is a Refl Co
  | otherwise    = opt_trans2 opts is co1 co2

opt_trans2 :: OptCoParams -> InScopeSet -> NormalNonIdCo -> NormalNonIdCo -> NormalCo
-- Neither arg is the identity
opt_trans2 opts is (TransCo co1a co1b) co2
    -- Don't know whether the sub-coercions are the identity
  = opt_trans opts is co1a (opt_trans opts is co1b co2)

opt_trans2 opts is co1 co2
  | Just co <- opt_trans_rule opts is co1 co2
  = co

opt_trans2 opts is co1 (TransCo co2a co2b)
  | Just co1_2a <- opt_trans_rule opts is co1 co2a
  = if isReflCo co1_2a
    then co2b
    else opt_trans1 opts is co1_2a co2b

opt_trans2 _ _ co1 co2
  = mkTransCo co1 co2

------

-- Optimize coercions with a top-level use of transitivity.
opt_trans_rule :: OptCoParams -> InScopeSet -> NormalNonIdCo -> NormalNonIdCo -> Maybe NormalCo

-- Handle a composition of two directed coercions.
opt_trans_rule opts is (HydrateDCo r lty1 dco1 _) (HydrateDCo _ lty2 dco2 rhs2)
  = ( \ dco -> mkHydrateDCo r lty1 dco rhs2 )
  <$> opt_trans_rule_dco opts is r lty1 dco1 lty2 dco2

opt_trans_rule opts is (SymCo (HydrateDCo r lty1 dco1 rhs1)) (SymCo (HydrateDCo _ lty2 dco2 _))
  = ( \ dco -> mkSymCo $ mkHydrateDCo r lty2 dco rhs1 )
  <$> opt_trans_rule_dco opts is r lty2 dco2 lty1 dco1

-- When composing a Coercion with a DCoercion, we could imagine hydrating the DCoercion
-- a single step (e.g. using 'hydrateOneLayerDCo') to expose cancellation opportunities.
-- We don't do that for now.

opt_trans_rule opts is in_co1@(GRefl r1 t1 (MCo co1)) in_co2@(GRefl r2 _ (MCo co2))
  = assert (r1 == r2) $
    fireTransRule "GRefl" in_co1 in_co2 $
    mkGReflRightCo r1 t1 (opt_trans opts is co1 co2)

-- Push transitivity through matching destructors
opt_trans_rule opts is in_co1@(SelCo d1 co1) in_co2@(SelCo d2 co2)
  | d1 == d2
  , coercionRole co1 == coercionRole co2
  , co1 `compatible_co` co2
  = fireTransRule "PushNth" in_co1 in_co2 $
    mkSelCo d1 (opt_trans opts is co1 co2)

opt_trans_rule opts is in_co1@(LRCo d1 co1) in_co2@(LRCo d2 co2)
  | d1 == d2
  , co1 `compatible_co` co2
  = fireTransRule "PushLR" in_co1 in_co2 $
    mkLRCo d1 (opt_trans opts is co1 co2)

-- Push transitivity inside instantiation
opt_trans_rule opts is in_co1@(InstCo co1 ty1) in_co2@(InstCo co2 ty2)
  | ty1 `eqCoercion` ty2
  , co1 `compatible_co` co2
  = fireTransRule "TrPushInst" in_co1 in_co2 $
    mkInstCo (opt_trans opts is co1 co2) ty1

opt_trans_rule opts is in_co1@(UnivCo p1 r1 tyl1 _tyr1)
                       in_co2@(UnivCo p2 r2 _tyl2 tyr2)
  | Just prov' <- opt_trans_prov p1 p2
  = assert (r1 == r2) $
    fireTransRule "UnivCo" in_co1 in_co2 $
    mkUnivCo prov' r1 tyl1 tyr2
  where
    -- if the provenances are different, opt'ing will be very confusing
    opt_trans_prov (PhantomProv kco1)    (PhantomProv kco2)
      = Just $ PhantomProv $ opt_trans opts is kco1 kco2
    opt_trans_prov (ProofIrrelProv kco1) (ProofIrrelProv kco2)
      = Just $ ProofIrrelProv $ opt_trans opts is kco1 kco2
    opt_trans_prov (PluginProv str1)     (PluginProv str2)
      | str1 == str2
      = Just p1
    opt_trans_prov _ _ = Nothing

-- Push transitivity down through matching top-level constructors.
opt_trans_rule opts is in_co1@(TyConAppCo r1 tc1 cos1) in_co2@(TyConAppCo r2 tc2 cos2)
  | tc1 == tc2
  = assert (r1 == r2) $
    fireTransRule "PushTyConApp" in_co1 in_co2 $
    mkTyConAppCo r1 tc1 (opt_transList opts is cos1 cos2)

opt_trans_rule opts is in_co1@(FunCo r1 afl1 afr1 w1 co1a co1b)
                       in_co2@(FunCo r2 afl2 afr2 w2 co2a co2b)
  = assert (r1 == r2)     $     -- Just like the TyConAppCo/TyConAppCo case
    assert (afr1 == afl2) $
    fireTransRule "PushFun" in_co1 in_co2 $
    mkFunCo2 r1 afl1 afr2 (opt_trans opts is w1 w2)
                          (opt_trans opts is co1a co2a)
                          (opt_trans opts is co1b co2b)

opt_trans_rule opts is in_co1@(AppCo co1a co1b) in_co2@(AppCo co2a co2b)
  -- Must call opt_trans_rule_app; see Note [EtaAppCo]
  = opt_trans_rule_app opts is in_co1 in_co2 co1a [co1b] co2a [co2b]

-- Eta rules
opt_trans_rule opts is co1@(TyConAppCo r tc cos1) co2
  | Just cos2 <- etaTyConAppCo_maybe tc co2
  = fireTransRule "EtaCompL" co1 co2 $
    mkTyConAppCo r tc (opt_transList opts is cos1 cos2)

opt_trans_rule opts is co1 co2@(TyConAppCo r tc cos2)
  | Just cos1 <- etaTyConAppCo_maybe tc co1
  = fireTransRule "EtaCompR" co1 co2 $
    mkTyConAppCo r tc (opt_transList opts is cos1 cos2)

opt_trans_rule opts is co1@(AppCo co1a co1b) co2
  | Just (co2a,co2b) <- etaAppCo_maybe co2
  = opt_trans_rule_app opts is co1 co2 co1a [co1b] co2a [co2b]

opt_trans_rule opts is co1 co2@(AppCo co2a co2b)
  | Just (co1a,co1b) <- etaAppCo_maybe co1
  = opt_trans_rule_app opts is co1 co2 co1a [co1b] co2a [co2b]

-- Push transitivity inside forall
-- forall over types.
opt_trans_rule opts is co1 co2
  | Just (tv1, eta1, r1) <- splitForAllCo_ty_maybe co1
  , Just (tv2, eta2, r2) <- etaForAllCo_ty_maybe co2
  = push_trans tv1 eta1 r1 tv2 eta2 r2

  | Just (tv2, eta2, r2) <- splitForAllCo_ty_maybe co2
  , Just (tv1, eta1, r1) <- etaForAllCo_ty_maybe co1
  = push_trans tv1 eta1 r1 tv2 eta2 r2

  where
  push_trans tv1 eta1 r1 tv2 eta2 r2
    -- Given:
    --   co1 = /\ tv1 : eta1. r1
    --   co2 = /\ tv2 : eta2. r2
    -- Wanted:
    --   /\tv1 : (eta1;eta2).  (r1; r2[tv2 |-> tv1 |> eta1])
    = fireTransRule "EtaAllTy_ty" co1 co2 $
      mkForAllCo tv1 (opt_trans opts is eta1 eta2) (opt_trans opts is' r1 r2')
    where
      is' = is `extendInScopeSet` tv1
      r2' = substCoWithUnchecked [tv2] [mkCastTy (TyVarTy tv1) eta1] r2

-- Push transitivity inside forall
-- forall over coercions.
opt_trans_rule opts is co1 co2
  | Just (cv1, eta1, r1) <- splitForAllCo_co_maybe co1
  , Just (cv2, eta2, r2) <- etaForAllCo_co_maybe co2
  = push_trans cv1 eta1 r1 cv2 eta2 r2

  | Just (cv2, eta2, r2) <- splitForAllCo_co_maybe co2
  , Just (cv1, eta1, r1) <- etaForAllCo_co_maybe co1
  = push_trans cv1 eta1 r1 cv2 eta2 r2

  where
  push_trans cv1 eta1 r1 cv2 eta2 r2
    -- Given:
    --   co1 = /\ cv1 : eta1. r1
    --   co2 = /\ cv2 : eta2. r2
    -- Wanted:
    --   n1 = nth 2 eta1
    --   n2 = nth 3 eta1
    --   nco = /\ cv1 : (eta1;eta2). (r1; r2[cv2 |-> (sym n1);cv1;n2])
    = fireTransRule "EtaAllTy_co" co1 co2 $
      mkForAllCo cv1 (opt_trans opts is eta1 eta2) (opt_trans opts is' r1 r2')
    where
      is'  = is `extendInScopeSet` cv1
      role = coVarRole cv1
      eta1' = downgradeRole role Nominal eta1
      n1   = mkSelCo (SelTyCon 2 role) eta1'
      n2   = mkSelCo (SelTyCon 3 role) eta1'
      r2'  = substCo (zipCvSubst [cv2] [(mkSymCo n1) `mkTransCo`
                                        (mkCoVarCo cv1) `mkTransCo` n2])
                    r2

-- Push transitivity inside axioms
opt_trans_rule opts is co1 co2

  -- See Note [Push transitivity inside axioms] and
  -- Note [Push transitivity inside newtype axioms only]
  -- TrPushSymAxR
  | Just (sym, con, ind, cos1) <- co1_is_axiom_maybe
  , isNewTyCon (coAxiomTyCon con)
  , True <- sym
  , Just cos2 <- matchAxiom sym con ind co2
  , let newAxInst = AxiomInstCo con ind (opt_transList opts is (map mkSymCo cos2) cos1)
  = fireTransRule "TrPushSymAxR" co1 co2 $ SymCo newAxInst

  -- TrPushAxR (AxSuckR)
  | Just (sym, con, ind, cos1) <- co1_is_axiom_maybe
  , isNewTyCon (coAxiomTyCon con)
  , False <- sym
  , Just cos2 <- matchAxiom sym con ind co2
  , let newAxInst = AxiomInstCo con ind (opt_transList opts is cos1 cos2)
  = fireTransRule "TrPushAxR" co1 co2 newAxInst

  -- TrPushSymAxL (SymAxSuckL)
  | Just (sym, con, ind, cos2) <- co2_is_axiom_maybe
  , isNewTyCon (coAxiomTyCon con)
  , True <- sym
  , Just cos1 <- matchAxiom (not sym) con ind co1
  , let newAxInst = AxiomInstCo con ind (opt_transList opts is cos2 (map mkSymCo cos1))
  = fireTransRule "TrPushSymAxL" co1 co2 $ SymCo newAxInst

  -- TrPushAxL (AxSuckL)
  | Just (sym, con, ind, cos2) <- co2_is_axiom_maybe
  , isNewTyCon (coAxiomTyCon con)
  , False <- sym
  , Just cos1 <- matchAxiom (not sym) con ind co1
  , let newAxInst = AxiomInstCo con ind (opt_transList opts is cos1 cos2)
  = fireTransRule "TrPushAxL" co1 co2 newAxInst

  -- TrPushAxSym/TrPushSymAx (AxSym/SymAx)
  | Just (sym1, con1, ind1, cos1) <- co1_is_axiom_maybe
  , Just (sym2, con2, ind2, cos2) <- co2_is_axiom_maybe
  , con1 == con2
  , ind1 == ind2
  , sym1 == not sym2
  , let branch = coAxiomNthBranch con1 ind1
        qtvs = coAxBranchTyVars branch ++ coAxBranchCoVars branch
        lhs  = coAxNthLHS con1 ind1
        rhs  = coAxBranchRHS branch
        pivot_tvs = exactTyCoVarsOfType (if sym2 then rhs else lhs)
  , all (`elemVarSet` pivot_tvs) qtvs
  = fireTransRule "TrPushAxSym" co1 co2 $
    if sym2
       -- TrPushAxSym (AxSym)
    then liftCoSubstWith role qtvs (opt_transList opts is cos1 (map mkSymCo cos2)) lhs
       -- TrPushSymAx (SymAx)
    else liftCoSubstWith role qtvs (opt_transList opts is (map mkSymCo cos1) cos2) rhs
  where
    co1_is_axiom_maybe = isAxiom_maybe co1
    co2_is_axiom_maybe = isAxiom_maybe co2
    role = coercionRole co1 -- should be the same as coercionRole co2!

opt_trans_rule _ _ co1 co2        -- Identity rule
  | let ty1 = coercionLKind co1
        r   = coercionRole co1
        ty2 = coercionRKind co2
  , ty1 `eqType` ty2
  = fireTransRule "RedTypeDirRefl" co1 co2 $
    mkReflCo r ty2

opt_trans_rule _ _ _ _ = Nothing

-- See Note [EtaAppCo]
opt_trans_rule_app :: OptCoParams
                   -> InScopeSet
                   -> Coercion   -- original left-hand coercion (printing only)
                   -> Coercion   -- original right-hand coercion (printing only)
                   -> Coercion   -- left-hand coercion "function"
                   -> [Coercion] -- left-hand coercion "args"
                   -> Coercion   -- right-hand coercion "function"
                   -> [Coercion] -- right-hand coercion "args"
                   -> Maybe Coercion
opt_trans_rule_app opts is orig_co1 orig_co2 co1a co1bs co2a co2bs
  | AppCo co1aa co1ab <- co1a
  , Just (co2aa, co2ab) <- etaAppCo_maybe co2a
  = opt_trans_rule_app opts is orig_co1 orig_co2 co1aa (co1ab:co1bs) co2aa (co2ab:co2bs)

  | AppCo co2aa co2ab <- co2a
  , Just (co1aa, co1ab) <- etaAppCo_maybe co1a
  = opt_trans_rule_app opts is orig_co1 orig_co2 co1aa (co1ab:co1bs) co2aa (co2ab:co2bs)

  | otherwise
  = assert (co1bs `equalLength` co2bs) $
    fireTransRule ("EtaApps:" ++ show (length co1bs)) orig_co1 orig_co2 $
    let rt1a = coercionRKind co1a

        lt2a = coercionLKind co2a
        rt2a = coercionRole  co2a

        rt1bs = map coercionRKind co1bs
        lt2bs = map coercionLKind co2bs
        rt2bs = map coercionRole co2bs

        kcoa = mkKindCo $ buildCoercion lt2a rt1a
        kcobs = map mkKindCo $ zipWith buildCoercion lt2bs rt1bs

        co2a'   = mkCoherenceLeftCo rt2a lt2a kcoa co2a
        co2bs'  = zipWith3 mkGReflLeftCo rt2bs lt2bs kcobs
        co2bs'' = zipWith mkTransCo co2bs' co2bs
    in
    mkAppCos (opt_trans opts is co1a co2a')
             (zipWith (opt_trans opts is) co1bs co2bs'')

fireTransRule :: String -> Coercion -> Coercion -> Coercion -> Maybe Coercion
fireTransRule _rule _co1 _co2 res
  = -- pprTrace _rule
    --  (vcat [ text "co1:" <+> ppr _co1
    --        , text "co2:" <+> ppr _co2
    --        , text "res:" <+> ppr res ]) $
    Just res

------
-- Optimize directed coercions

-- N.B.: The reason we return (Type, DCoercion) and not just DCoercion is that we
-- sometimes need the substituted LHS type (see opt_trans_dco).

opt_phantom_dco :: OptCoParams -> LiftingContext -> Role -> Type -> DCoercion -> (Type, NormalDCo)
opt_phantom_dco opts env r l_ty dco = opt_univ DCo opts env False (PhantomProv kco) Phantom l_ty r_ty
  where
    kco = DehydrateCo (mkKindCo $ mkHydrateDCo r l_ty dco r_ty)
    r_ty = followDCo r l_ty dco
    -- A naive attempt at removing this entirely causes issues in test "type_in_type_hole_fits".

opt_dco4_wrap :: String -> OptCoParams -> LiftingContext -> ReprFlag -> Role -> Type -> DCoercion -> (Type, NormalDCo)
opt_dco4_wrap str opts lc rep r l_ty dco = wrap ("opt_dco4 " ++ str) go opts lc False rep r dco
  where
    go opts lc _sym repr r dco = opt_dco4 opts lc repr r l_ty dco

opt_dco2 :: OptCoParams
         -> LiftingContext
         -> Role   -- ^ The role of the input coercion
         -> Type
         -> DCoercion -> (Type, NormalDCo)
opt_dco2 opts env Phantom ty dco = opt_phantom_dco opts env Phantom ty dco
opt_dco2 opts env r       ty dco = opt_dco3 opts env Nothing r ty dco

opt_dco3 :: OptCoParams -> LiftingContext -> Maybe Role -> Role -> Type -> DCoercion -> (Type, NormalDCo)
opt_dco3 opts env (Just Phantom)          r ty dco = opt_phantom_dco opts env r ty dco
opt_dco3 opts env (Just Representational) r ty dco = opt_dco4_wrap "opt_dco3 R" opts env True  r ty dco
opt_dco3 opts env _                       r ty dco = opt_dco4_wrap "opt_dco3 _" opts env False r ty dco

opt_dco4 :: OptCoParams -> LiftingContext -> ReprFlag -> Role -> Type -> DCoercion -> (Type, NormalDCo)
opt_dco4 opts env rep r l_ty dco = case dco of

    ReflDCo
      -> lifted_dco
    GReflRightDCo kco
      | isGReflCo kco || isGReflCo kco'
      -> lifted_dco
      | otherwise
      -> (l_ty', mkGReflRightDCo kco')
      where
        kco' = opt_co4 opts env False False Nominal kco
    GReflLeftDCo kco
      | isGReflCo kco || isGReflCo kco'
      -> lifted_dco
      | otherwise
      -> (l_ty', mkGReflLeftDCo kco')
      where
        kco' = opt_co4 opts env False False Nominal kco

    TyConAppDCo dcos
      | Just (tc, l_tys) <- splitTyConApp_maybe l_ty
      -> let
            (arg_ltys, arg_dcos) =
              case (rep, r) of
                (True, Nominal) ->
                  unzip $
                  zipWith3
                    (\ mb_r' -> opt_dco3 opts env mb_r' Nominal)
                    (map Just (tyConRoleListRepresentational tc))
                    l_tys
                    dcos
                (False, Nominal) ->
                  unzip $
                  zipWith (opt_dco4 opts env False Nominal) l_tys dcos
                (_, Representational) ->
                  unzip $
                  zipWith3
                    (opt_dco2 opts env)
                    (tyConRoleListRepresentational tc)
                    l_tys
                    dcos
                (_, Phantom) -> pprPanic "opt_dco4 sees a phantom!" (ppr dco)
         in (mkTyConApp tc arg_ltys, mkTyConAppDCo arg_dcos)

      | otherwise
      -> pprPanic "opt_dco4: TyConAppDCo where ty is not a TyConApp" $
          vcat [ text "dco =" <+> ppr dco
               , text "l_ty =" <+> ppr l_ty ]

    AppDCo dco1 dco2
      | Just (l_ty1, l_ty2) <- splitAppTy_maybe l_ty
      , let
          (l_ty1', l_dco1) = opt_dco4 opts env rep   r       l_ty1 dco1
          (l_ty2', l_dco2) = opt_dco4 opts env False Nominal l_ty2 dco2
      -> (mkAppTy l_ty1' l_ty2', mkAppDCo l_dco1 l_dco2)
      | otherwise
      -> pprPanic "opt_dco4: AppDCo where ty is not an AppTy" $
           vcat [ text "dco =" <+> ppr dco
                , text "l_ty =" <+> ppr l_ty ]

    ForAllDCo dco_tcv k_dco body_dco
      | ForAllTy (Bndr ty_tv af) body_ty <- coreFullView l_ty
      ->  case optForAllDCoBndr opts env False dco_tcv k_dco of
            (env', dco_tcv', k_dco') ->
              -- SLD TODO: can this be simplified? I made too many mistakes writing this...
              let body_ty' = substTyWithInScope (lcInScopeSet env') [ty_tv] [mkTyVarTy dco_tcv'] body_ty
                  (body_ty'', body_dco') = opt_dco4_wrap "ForAllDCo" opts env' rep r body_ty' body_dco
                  forall_ty = mkForAllTy (Bndr dco_tcv' af) body_ty''
                  forall_dco = mkForAllDCo dco_tcv' k_dco' body_dco'
                  forall_ty' = followDCo r forall_ty forall_dco
              in (forall_ty, wrapRole_dco rep r forall_ty forall_dco forall_ty')
      | otherwise
      -> pprPanic "opt_dco4: ForAllDCo where ty is not a ForAllTy" $
           vcat [ text "dco =" <+> ppr dco
                , text "l_ty =" <+> ppr l_ty ]

    CoVarDCo cv
      -> let co' = opt_co4 opts env False rep r (CoVarCo cv)
         in (coercionLKind co', mkDehydrateCo co')

    AxiomInstDCo {}
      -> (l_ty', rep_dco)
    StepsDCo {}
      -> (l_ty', rep_dco)

    UnivDCo prov rhs_ty
      -> opt_univ DCo opts env False prov r' l_ty rhs_ty

    TransDCo dco1 dco2 ->
      let
        (l_ty', dco1') = opt_dco4 opts env rep r l_ty dco1

        -- Follow the original directed coercion,
        -- to avoid applying the substitution twice.
        mid_ty = followDCo r l_ty dco1
        (mid_ty', dco2') = opt_dco4 opts env rep r mid_ty dco2
      in
        (l_ty', opt_trans_dco opts (lcInScopeSet env) r' l_ty' dco1' mid_ty' dco2')

    SubDCo dco ->
      assert (r == Representational) $
        opt_dco4_wrap "SubDCo" opts env True Nominal l_ty dco

    DehydrateCo co ->
      let co' = opt_co4_wrap "DehydrateCo" opts env False rep r co
      in (coercionLKind co', mkDehydrateCo co')

  where
    lifted_dco = let lifted_co = liftCoSubst r' env l_ty
                 in ( coercionLKind lifted_co, mkDehydrateCo lifted_co )
    l_ty'      = substTyUnchecked (lcSubstLeft env) l_ty
    r'         = chooseRole rep r
    rep_dco    = wrapRole_dco rep r l_ty' dco (followDCo r l_ty' dco)

---------------------------------------------------------
-- Transitivity for directed coercions.

opt_trans_dco :: OptCoParams -> InScopeSet -> Role -> Type -> NormalDCo -> Type -> NormalDCo -> NormalDCo
opt_trans_dco opts is r l_ty dco1 mid_ty dco2
  | isReflDCo dco1 = dco2
    -- optimize when dco1 is a Refl DCo
  | otherwise    = opt_trans1_dco opts is r l_ty dco1 mid_ty dco2

opt_trans1_dco :: OptCoParams -> InScopeSet -> Role -> Type -> NormalNonIdDCo -> Type -> NormalDCo -> NormalDCo
-- First arg is not the identity
opt_trans1_dco opts is r l_ty dco1 mid_ty dco2
  | isReflDCo dco2 = dco1
    -- optimize when co2 is a Refl Co
  | otherwise      = opt_trans2_dco opts is r l_ty dco1 mid_ty dco2

opt_trans2_dco :: OptCoParams -> InScopeSet -> Role -> Type -> NormalNonIdDCo -> Type -> NormalNonIdDCo -> NormalDCo
-- Neither arg is the identity
opt_trans2_dco opts  is r l_ty (TransDCo dco1a dco1b) mid_ty dco2
    -- Don't know whether the sub-coercions are the identity
  = let inner_ty = followDCo r l_ty dco1a
    in opt_trans_dco opts is r l_ty dco1a inner_ty
         (opt_trans_dco opts is r inner_ty dco1b mid_ty dco2)


opt_trans2_dco opts is r l_ty dco1 mid_ty dco2
  | Just co <- opt_trans_rule_dco opts is r l_ty dco1 mid_ty dco2
  = co

opt_trans2_dco opts is r l_ty dco1 mid_ty (TransDCo dco2a dco2b)
  | Just dco1_2a <- opt_trans_rule_dco opts is r l_ty dco1 mid_ty dco2a
  = if isReflDCo dco1_2a
    then dco2b
    else
      let inner_ty = followDCo r mid_ty dco1_2a
      in opt_trans1_dco opts is r mid_ty dco1_2a inner_ty dco2b

opt_trans2_dco _ _ _ _ dco1 _ dco2
  = mkTransDCo dco1 dco2

opt_trans_rule_dco :: OptCoParams -> InScopeSet -> Role -> Type -> NormalNonIdDCo -> Type -> NormalNonIdDCo -> Maybe NormalDCo

-- Handle undirected coercions.
opt_trans_rule_dco opts is _ _ (DehydrateCo co1) _ (DehydrateCo co2)
  = DehydrateCo <$> opt_trans_rule opts is co1 co2

opt_trans_rule_dco _ _ r l_ty dco1 mid_ty dco2
  | let r_ty = followDCo r mid_ty dco2
  , l_ty `eqType` r_ty
  = fireTransRule_dco "RedTypeDirRefl" dco1 dco2 $
    mkReflDCo

opt_trans_rule_dco _ _ _ _ _ _ _ = Nothing

fireTransRule_dco :: String -> DCoercion -> DCoercion -> DCoercion -> Maybe DCoercion
fireTransRule_dco _rule _dco1 _dco2 res
  = --pprTrace _rule
    -- (vcat [ text "dco1:" <+> ppr _dco1
    --       , text "dco2:" <+> ppr _dco2
    --       , text "res:" <+> ppr res ]) $
    Just res

{-
Note [Push transitivity inside axioms]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
opt_trans_rule tries to push transitivity inside axioms to deal with cases like
the following:

    newtype N a = MkN a

    axN :: N a ~R# a

    covar :: a ~R# b
    co1 = axN <a> :: N a ~R# a
    co2 = axN <b> :: N b ~R# b

    co :: a ~R# b
    co = sym co1 ; N covar ; co2

When we are optimising co, we want to notice that the two axiom instantiations
cancel out. This is implemented by rules such as TrPushSymAxR, which transforms
    sym (axN <a>) ; N covar
into
    sym (axN covar)
so that TrPushSymAx can subsequently transform
    sym (axN covar) ; axN <b>
into
    covar
which is much more compact. In some perf test cases this kind of pattern can be
generated repeatedly during simplification, so it is very important we squash it
to stop coercions growing exponentially.  For more details see the paper:

    Evidence normalisation in System FC
    Dimitrios Vytiniotis and Simon Peyton Jones
    RTA'13, 2013
    https://www.microsoft.com/en-us/research/publication/evidence-normalization-system-fc-2/


Note [Push transitivity inside newtype axioms only]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The optimization described in Note [Push transitivity inside axioms] is possible
for both newtype and type family axioms.  However, for type family axioms it is
relatively common to have transitive sequences of axioms instantiations, for
example:

    data Nat = Zero | Suc Nat

    type family Index (n :: Nat) (xs :: [Type]) :: Type where
      Index Zero    (x : xs) = x
      Index (Suc n) (x : xs) = Index n xs

    axIndex :: { forall x::Type. forall xs::[Type]. Index Zero (x : xs) ~ x
               ; forall n::Nat. forall x::Type. forall xs::[Type]. Index (Suc n) (x : xs) ~ Index n xs }

    co :: Index (Suc (Suc Zero)) [a, b, c] ~ c
    co = axIndex[1] <Suc Zero> <a> <[b, c]>
       ; axIndex[1] <Zero> <b> <[c]>
       ; axIndex[0] <c> <[]>

Not only are there no cancellation opportunities here, but calling matchAxiom
repeatedly down the transitive chain is very expensive.  Hence we do not attempt
to push transitivity inside type family axioms.  See #8095, !9210 and related tickets.

This is implemented by opt_trans_rule checking that the axiom is for a newtype
constructor (i.e. not a type family).  Adding these guards substantially
improved performance (reduced bytes allocated by more than 10%) for the tests
CoOpt_Singletons, LargeRecord, T12227, T12545, T13386, T15703, T5030, T8095.

A side benefit is that we do not risk accidentally creating an ill-typed
coercion; see Note [Why call checkAxInstCo during optimisation].

There may exist programs that previously relied on pushing transitivity inside
type family axioms to avoid creating huge coercions, which will regress in
compile time performance as a result of this change.  We do not currently know
of any examples, but if any come to light we may need to reconsider this
behaviour.


Note [Why call checkAxInstCo during optimisation]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
NB: The following is no longer relevant, because we no longer push transitivity
into type family axioms (Note [Push transitivity inside newtype axioms only]).
It is retained for reference in case we change this behaviour in the future.

It is possible that otherwise-good-looking optimisations meet with disaster
in the presence of axioms with multiple equations. Consider

type family Equal (a :: *) (b :: *) :: Bool where
  Equal a a = True
  Equal a b = False
type family Id (a :: *) :: * where
  Id a = a

axEq :: { [a::*].       Equal a a ~ True
        ; [a::*, b::*]. Equal a b ~ False }
axId :: [a::*]. Id a ~ a

co1 = Equal (axId[0] Int) (axId[0] Bool)
  :: Equal (Id Int) (Id Bool) ~  Equal Int Bool
co2 = axEq[1] <Int> <Bool>
  :: Equal Int Bool ~ False

We wish to optimise (co1 ; co2). We end up in rule TrPushAxL, noting that
co2 is an axiom and that matchAxiom succeeds when looking at co1. But, what
happens when we push the coercions inside? We get

co3 = axEq[1] (axId[0] Int) (axId[0] Bool)
  :: Equal (Id Int) (Id Bool) ~ False

which is bogus! This is because the type system isn't smart enough to know
that (Id Int) and (Id Bool) are Surely Apart, as they're headed by type
families. At the time of writing, I (Richard Eisenberg) couldn't think of
a way of detecting this any more efficient than just building the optimised
coercion and checking.

Note [EtaAppCo]
~~~~~~~~~~~~~~~
Suppose we're trying to optimize (co1a co1b ; co2a co2b). Ideally, we'd
like to rewrite this to (co1a ; co2a) (co1b ; co2b). The problem is that
the resultant coercions might not be well kinded. Here is an example (things
labeled with x don't matter in this example):

  k1 :: Type
  k2 :: Type

  a :: k1 -> Type
  b :: k1

  h :: k1 ~ k2

  co1a :: x1 ~ (a |> (h -> <Type>)
  co1b :: x2 ~ (b |> h)

  co2a :: a ~ x3
  co2b :: b ~ x4

First, convince yourself of the following:

  co1a co1b :: x1 x2 ~ (a |> (h -> <Type>)) (b |> h)
  co2a co2b :: a b   ~ x3 x4

  (a |> (h -> <Type>)) (b |> h) `eqType` a b

That last fact is due to Note [Non-trivial definitional equality] in GHC.Core.TyCo.Rep,
where we ignore coercions in types as long as two types' kinds are the same.
In our case, we meet this last condition, because

  (a |> (h -> <Type>)) (b |> h) :: Type
    and
  a b :: Type

So the input coercion (co1a co1b ; co2a co2b) is well-formed. But the
suggested output coercions (co1a ; co2a) and (co1b ; co2b) are not -- the
kinds don't match up.

The solution here is to twiddle the kinds in the output coercions. First, we
need to find coercions

  ak :: kind(a |> (h -> <Type>)) ~ kind(a)
  bk :: kind(b |> h)             ~ kind(b)

This can be done with mkKindCo and buildCoercion. The latter assumes two
types are identical modulo casts and builds a coercion between them.

Then, we build (co1a ; co2a |> sym ak) and (co1b ; co2b |> sym bk) as the
output coercions. These are well-kinded.

Also, note that all of this is done after accumulated any nested AppCo
parameters. This step is to avoid quadratic behavior in calling coercionKind.

The problem described here was first found in dependent/should_compile/dynamic-paper.

-}

-----------
wrapSym :: SymFlag -> Coercion -> Coercion
wrapSym sym co | sym       = mkSymCo co
               | otherwise = co

-- | Conditionally set a role to be representational
wrapRole :: HasDebugCallStack
         => ReprFlag
         -> Role         -- ^ current role
         -> Coercion -> Coercion
wrapRole False _       = id
wrapRole True  current = downgradeRole Representational current

wrapRole_dco :: HasDebugCallStack
             => ReprFlag
             -> Role         -- ^ current role
             -> Type -> DCoercion -> Type
             -> DCoercion
wrapRole_dco False _       _    dco _    = dco
wrapRole_dco True  current l_ty dco r_ty = downgradeDCoToRepresentational current l_ty dco r_ty

-- | If we require a representational role, return that. Otherwise,
-- return the "default" role provided.
chooseRole :: ReprFlag
           -> Role    -- ^ "default" role
           -> Role
chooseRole True _ = Representational
chooseRole _    r = r

-----------
isAxiom_maybe :: Coercion -> Maybe (Bool, CoAxiom Branched, Int, [Coercion])
isAxiom_maybe (SymCo co)
  | Just (sym, con, ind, cos) <- isAxiom_maybe co
  = Just (not sym, con, ind, cos)
isAxiom_maybe (AxiomInstCo con ind cos)
  | isNewTyCon (coAxiomTyCon con) -- Adam Gundry's special sauce
  = Just (False, con, ind, cos)
isAxiom_maybe _ = Nothing

matchAxiom :: Bool -- True = match LHS, False = match RHS
           -> CoAxiom br -> Int -> Coercion -> Maybe [Coercion]
matchAxiom sym ax@(CoAxiom { co_ax_tc = tc }) ind co
  | CoAxBranch { cab_tvs = qtvs
               , cab_cvs = []   -- can't infer these, so fail if there are any
               , cab_roles = roles
               , cab_lhs = lhs
               , cab_rhs = rhs } <- coAxiomNthBranch ax ind
  , Just subst <- liftCoMatch (mkVarSet qtvs)
                              (if sym then (mkTyConApp tc lhs) else rhs)
                              co
  , all (`isMappedByLC` subst) qtvs
  = zipWithM (liftCoSubstTyVar subst) roles qtvs

  | otherwise
  = Nothing

-------------
compatible_co :: Coercion -> Coercion -> Bool
-- Check whether (co1 . co2) will be well-kinded
compatible_co co1 co2
  = x1 `eqType` x2
  where
    x1 = coercionRKind co1
    x2 = coercionLKind co2

-------------
{-
etaForAllCo
~~~~~~~~~~~~~~~~~
(1) etaForAllCo_ty_maybe
Suppose we have

  g : all a1:k1.t1  ~  all a2:k2.t2

but g is *not* a ForAllCo. We want to eta-expand it. So, we do this:

  g' = all a1:(ForAllKindCo g).(InstCo g (a1 ~ a1 |> ForAllKindCo g))

Call the kind coercion h1 and the body coercion h2. We can see that

  h2 : t1 ~ t2[a2 |-> (a1 |> h1)]

According to the typing rule for ForAllCo, we get that

  g' : all a1:k1.t1  ~  all a1:k2.(t2[a2 |-> (a1 |> h1)][a1 |-> a1 |> sym h1])

or

  g' : all a1:k1.t1  ~  all a1:k2.(t2[a2 |-> a1])

as desired.

(2) etaForAllCo_co_maybe
Suppose we have

  g : all c1:(s1~s2). t1 ~ all c2:(s3~s4). t2

Similarly, we do this

  g' = all c1:h1. h2
     : all c1:(s1~s2). t1 ~ all c1:(s3~s4). t2[c2 |-> (sym eta1;c1;eta2)]
                                              [c1 |-> eta1;c1;sym eta2]

Here,

  h1   = mkSelCo Nominal 0 g       :: (s1~s2)~(s3~s4)
  eta1 = mkSelCo (SelTyCon 2 r) h1 :: (s1 ~ s3)
  eta2 = mkSelCo (SelTyCon 3 r) h1 :: (s2 ~ s4)
  h2   = mkInstCo g (cv1 ~ (sym eta1;c1;eta2))
-}
etaForAllCo_ty_maybe :: Coercion -> Maybe (TyVar, Coercion, Coercion)
-- Try to make the coercion be of form (forall tv:kind_co. co)
etaForAllCo_ty_maybe co
  | Just (tv, kind_co, r) <- splitForAllCo_ty_maybe co
  = Just (tv, kind_co, r)

  | Pair ty1 ty2  <- coercionKind co
  , Just (tv1, _) <- splitForAllTyVar_maybe ty1
  , isForAllTy_ty ty2
  , let kind_co = mkSelCo SelForAll co
  = Just ( tv1, kind_co
         , mkInstCo co (mkGReflRightCo Nominal (TyVarTy tv1) kind_co))

  | otherwise
  = Nothing

etaForAllCo_co_maybe :: Coercion -> Maybe (CoVar, Coercion, Coercion)
-- Try to make the coercion be of form (forall cv:kind_co. co)
etaForAllCo_co_maybe co
  | Just (cv, kind_co, r) <- splitForAllCo_co_maybe co
  = Just (cv, kind_co, r)

  | Pair ty1 ty2  <- coercionKind co
  , Just (cv1, _) <- splitForAllCoVar_maybe ty1
  , isForAllTy_co ty2
  = let kind_co  = mkSelCo SelForAll co
        r        = coVarRole cv1
        l_co     = mkCoVarCo cv1
        kind_co' = downgradeRole r Nominal kind_co
        r_co     = mkSymCo (mkSelCo (SelTyCon 2 r) kind_co')
                   `mkTransCo` l_co
                   `mkTransCo` mkSelCo (SelTyCon 3 r) kind_co'
    in Just ( cv1, kind_co
            , mkInstCo co (mkProofIrrelCo Nominal kind_co l_co r_co))

  | otherwise
  = Nothing

etaAppCo_maybe :: Coercion -> Maybe (Coercion,Coercion)
-- If possible, split a coercion
--   g :: t1a t1b ~ t2a t2b
-- into a pair of coercions (left g, right g)
etaAppCo_maybe co
  | Just (co1,co2) <- splitAppCo_maybe co
  = Just (co1,co2)
  | (Pair ty1 ty2, Nominal) <- coercionKindRole co
  , Just (_,t1) <- splitAppTy_maybe ty1
  , Just (_,t2) <- splitAppTy_maybe ty2
  , let isco1 = isCoercionTy t1
  , let isco2 = isCoercionTy t2
  , isco1 == isco2
  = Just (LRCo CLeft co, LRCo CRight co)
  | otherwise
  = Nothing

etaTyConAppCo_maybe :: TyCon -> Coercion -> Maybe [Coercion]
-- If possible, split a coercion
--       g :: T s1 .. sn ~ T t1 .. tn
-- into [ SelCo (SelTyCon 0)     g :: s1~t1
--      , ...
--      , SelCo (SelTyCon (n-1)) g :: sn~tn ]
etaTyConAppCo_maybe tc (TyConAppCo _ tc2 cos2)
  = assert (tc == tc2) $ Just cos2

etaTyConAppCo_maybe tc co
  | not (tyConMustBeSaturated tc)
  , (Pair ty1 ty2, r) <- coercionKindRole co
  , Just (tc1, tys1)  <- splitTyConApp_maybe ty1
  , Just (tc2, tys2)  <- splitTyConApp_maybe ty2
  , tc1 == tc2
  , isInjectiveTyCon tc r  -- See Note [SelCo and newtypes] in GHC.Core.TyCo.Rep
  , let n = length tys1
  , tys2 `lengthIs` n      -- This can fail in an erroneous program
                           -- E.g. T a ~# T a b
                           -- #14607
  = assert (tc == tc1) $
    Just (decomposeCo n co (tyConRolesX r tc1))
    -- NB: n might be <> tyConArity tc
    -- e.g.   data family T a :: * -> *
    --        g :: T a b ~ T c d

  | otherwise
  = Nothing

{-
Note [Eta for AppCo]
~~~~~~~~~~~~~~~~~~~~
Suppose we have
   g :: s1 t1 ~ s2 t2

Then we can't necessarily make
   left  g :: s1 ~ s2
   right g :: t1 ~ t2
because it's possible that
   s1 :: * -> *         t1 :: *
   s2 :: (*->*) -> *    t2 :: * -> *
and in that case (left g) does not have the same
kind on either side.

It's enough to check that
  kind t1 = kind t2
because if g is well-kinded then
  kind (s1 t2) = kind (s2 t2)
and these two imply
  kind s1 = kind s2

-}

optForAllCoBndr :: OptCoParams
                -> LiftingContext -> Bool
                -> TyCoVar -> Coercion -> (LiftingContext, TyCoVar, Coercion)
optForAllCoBndr opts env sym
  = substForAllCoBndrUsingLC sym
      (substTyUnchecked (lcSubstLeft env))
      (opt_co4_wrap "optForAllCoBndr" opts env sym False Nominal) env

optForAllDCoBndr :: OptCoParams
                 -> LiftingContext -> Bool
                 -> TyCoVar -> DCoercion -> (LiftingContext, TyCoVar, DCoercion)
optForAllDCoBndr opts env sym tv
  = substForAllDCoBndrUsingLC sym
      (substTyUnchecked (lcSubstLeft env))
      (snd . opt_dco4_wrap "optForAllDCoBndr" opts env False Nominal (tyVarKind tv)) env
      tv
