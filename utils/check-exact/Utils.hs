{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Utils
  -- (
  --  -- * Manipulating Positons
  --   ss2pos
  -- , ss2posEnd
  -- , undelta
  -- , isPointSrcSpan
  -- , pos2delta
  -- , ss2delta
  -- , addDP
  -- , spanLength
  -- , isGoodDelta
  -- ) where
  where

import Control.Monad (when)
import Data.Function
import Data.Maybe (isJust)
import Data.Ord (comparing)

import GHC.Hs.Dump
import Lookup
import Orphans (Default())
import qualified Orphans as Orphans

import GHC hiding (EpaComment)
import qualified GHC
import GHC.Data.Bag
import GHC.Types.Name
import GHC.Types.Name.Reader
import GHC.Types.SrcLoc
import GHC.Driver.Ppr
import GHC.Data.FastString
import qualified GHC.Data.Strict as Strict

import Data.Data hiding ( Fixity )
import Data.List (sortBy, elemIndex)
import qualified Data.Map.Strict as Map

import Debug.Trace
import Types

-- ---------------------------------------------------------------------

-- |Global switch to enable debug tracing in ghc-exactprint Delta / Print
debugEnabledFlag :: Bool
-- debugEnabledFlag = True
debugEnabledFlag = False

-- |Provide a version of trace that comes at the end of the line, so it can
-- easily be commented out when debugging different things.
debug :: c -> String -> c
debug c s = if debugEnabledFlag
              then trace s c
              else c
debugM :: Monad m => String -> m ()
debugM s = when debugEnabledFlag $ traceM s

-- ---------------------------------------------------------------------

warn :: c -> String -> c
-- warn = flip trace
warn c _ = c

-- | A good delta has no negative values.
isGoodDelta :: DeltaPos -> Bool
isGoodDelta (SameLine co) = co >= 0
isGoodDelta (DifferentLine ro _co) = ro > 0
  -- Note: DifferentLine invariant is ro is nonzero and positive


-- | Create a delta from the current position to the start of the given
-- @RealSrcSpan@.
ss2delta :: Pos -> RealSrcSpan -> DeltaPos
ss2delta ref ss = pos2delta ref (ss2pos ss)

-- | create a delta from the end of a current span.  The +1 is because
-- the stored position ends up one past the span, this is prior to
-- that adjustment
ss2deltaEnd :: RealSrcSpan -> RealSrcSpan -> DeltaPos
ss2deltaEnd rrs ss = ss2delta ref ss
  where
    (r,c) = ss2posEnd rrs
    ref = if r == 0
             then (r,c+1)
             else (r,c)

-- | create a delta from the start of a current span.  The +1 is
-- because the stored position ends up one past the span, this is
-- prior to that adjustment
ss2deltaStart :: RealSrcSpan -> RealSrcSpan -> DeltaPos
ss2deltaStart rrs ss = ss2delta ref ss
  where
    (r,c) = ss2pos rrs
    ref = if r == 0
             then (r,c)
             else (r,c)

-- | Convert the start of the second @Pos@ to be an offset from the
-- first. The assumption is the reference starts before the second @Pos@
pos2delta :: Pos -> Pos -> DeltaPos
pos2delta (refl,refc) (l,c) = deltaPos lo co
  where
    lo = l - refl
    co = if lo == 0 then c - refc
                    else c

-- | Apply the delta to the current position, taking into account the
-- current column offset if advancing to a new line
undelta :: Pos -> DeltaPos -> LayoutStartCol -> Pos
undelta (l,c) (SameLine dc)         (LayoutStartCol _co) = (l, c + dc)
undelta (l,_) (DifferentLine dl dc) (LayoutStartCol co) = (fl,fc)
  where
    -- Note: invariant: dl > 0
    fl = l + dl
    fc = co + dc

undeltaSpan :: RealSrcSpan -> AnnKeywordId -> DeltaPos -> AddEpAnn
undeltaSpan anchor kw dp = AddEpAnn kw (EpaSpan sp Strict.Nothing)
  where
    (l,c) = undelta (ss2pos anchor) dp (LayoutStartCol 0)
    len = length (keywordToString kw)
    sp = range2rs ((l,c),(l,c+len))

-- ---------------------------------------------------------------------

adjustDeltaForOffset :: LayoutStartCol -> DeltaPos -> DeltaPos
adjustDeltaForOffset _colOffset                      dp@(SameLine _) = dp
adjustDeltaForOffset (LayoutStartCol colOffset) (DifferentLine l c)
  = DifferentLine l (c - colOffset)

-- ---------------------------------------------------------------------

ss2pos :: RealSrcSpan -> Pos
ss2pos ss = (srcSpanStartLine ss,srcSpanStartCol ss)

ss2posEnd :: RealSrcSpan -> Pos
ss2posEnd ss = (srcSpanEndLine ss,srcSpanEndCol ss)

ss2range :: SrcSpan -> (Pos,Pos)
ss2range ss = (ss2pos $ rs ss, ss2posEnd $ rs ss)

rs2range :: RealSrcSpan -> (Pos,Pos)
rs2range ss = (ss2pos ss, ss2posEnd ss)

rs :: SrcSpan -> RealSrcSpan
rs (RealSrcSpan s _) = s
rs _ = badRealSrcSpan

range2rs :: (Pos,Pos) -> RealSrcSpan
range2rs (s,e) = mkRealSrcSpan (mkLoc s) (mkLoc e)
  where
    mkLoc (l,c) = mkRealSrcLoc (fsLit "ghc-exactprint") l c

badRealSrcSpan :: RealSrcSpan
badRealSrcSpan = mkRealSrcSpan bad bad
  where
    bad = mkRealSrcLoc (fsLit "ghc-exactprint-nospan") 0 0

spanLength :: RealSrcSpan -> Int
spanLength = (-) <$> srcSpanEndCol <*> srcSpanStartCol

-- ---------------------------------------------------------------------
-- | Checks whether a SrcSpan has zero length.
isPointSrcSpan :: RealSrcSpan -> Bool
isPointSrcSpan ss = spanLength ss == 0
                  && srcSpanStartLine ss == srcSpanEndLine ss

-- ---------------------------------------------------------------------

origDelta :: RealSrcSpan -> RealSrcSpan -> DeltaPos
origDelta pos pp = op
  where
    (r,c) = ss2posEnd pp

    op = if r == 0
           then (             ss2delta (r,c+1) pos)
           else (tweakDelta $ ss2delta (r,c  ) pos)

-- ---------------------------------------------------------------------

-- | For comment-related deltas starting on a new line we have an
-- off-by-one problem. Adjust
tweakDelta :: DeltaPos  -> DeltaPos
tweakDelta (SameLine d) = SameLine d
tweakDelta (DifferentLine l d) = DifferentLine l (d-1)

-- ---------------------------------------------------------------------

-- |Given a list of items and a list of keys, returns a list of items
-- ordered by their position in the list of keys.
orderByKey :: [(DeclTag,a)] -> [DeclTag] -> [(DeclTag,a)]
orderByKey keys order
    -- AZ:TODO: if performance becomes a problem, consider a Map of the order
    -- SrcSpan to an index, and do a lookup instead of elemIndex.

    -- Items not in the ordering are placed to the start
 = sortBy (comparing (flip elemIndex order . fst)) keys

-- ---------------------------------------------------------------------

isListComp :: HsDoFlavour -> Bool
isListComp = isDoComprehensionContext

-- ---------------------------------------------------------------------

needsWhere :: DataDefnCons (LConDecl (GhcPass p)) -> Bool
needsWhere (NewTypeCon _) = True
needsWhere (DataTypeCons _ []) = True
needsWhere (DataTypeCons _ ((L _ (ConDeclGADT{})):_)) = True
needsWhere _ = False

-- ---------------------------------------------------------------------

insertCppComments ::  ParsedSource -> [LEpaComment] -> ParsedSource
insertCppComments (L l p) cs = L l p'
  where
    an' = case GHC.hsmodAnn $ GHC.hsmodExt p of
      (EpAnn a an ocs) -> EpAnn a an (EpaComments cs')
        where
          cs' = sortEpaComments $ priorComments ocs ++ getFollowingComments ocs ++ cs
      unused -> unused
    p' = p { GHC.hsmodExt = (GHC.hsmodExt p) { GHC.hsmodAnn = an' } }

-- ---------------------------------------------------------------------

ghcCommentText :: LEpaComment -> String
ghcCommentText (L _ (GHC.EpaComment (EpaDocComment s) _))      = exactPrintHsDocString s
ghcCommentText (L _ (GHC.EpaComment (EpaDocOptions s) _))      = s
ghcCommentText (L _ (GHC.EpaComment (EpaLineComment s) _))     = s
ghcCommentText (L _ (GHC.EpaComment (EpaBlockComment s) _))    = s
ghcCommentText (L _ (GHC.EpaComment (EpaEofComment) _))        = ""

tokComment :: LEpaComment -> Comment
tokComment t@(L lt c) = mkComment (normaliseCommentText $ ghcCommentText t) lt (ac_prior_tok c)

mkEpaComments :: [Comment] -> [Comment] -> EpAnnComments
mkEpaComments priorCs []
  = EpaComments (map comment2LEpaComment priorCs)
mkEpaComments priorCs postCs
  = EpaCommentsBalanced (map comment2LEpaComment priorCs) (map comment2LEpaComment postCs)

comment2LEpaComment :: Comment -> LEpaComment
comment2LEpaComment (Comment s anc r _mk) = mkLEpaComment s anc r

mkLEpaComment :: String -> Anchor -> RealSrcSpan -> LEpaComment
mkLEpaComment "" anc r = (L anc (GHC.EpaComment (EpaEofComment) r))
mkLEpaComment s anc r = (L anc (GHC.EpaComment (EpaLineComment s) r))

mkComment :: String -> Anchor -> RealSrcSpan -> Comment
mkComment c anc r = Comment c anc r Nothing

-- Windows comments include \r in them from the lexer.
normaliseCommentText :: String -> String
normaliseCommentText [] = []
normaliseCommentText ('\r':xs) = normaliseCommentText xs
normaliseCommentText (x:xs) = x:normaliseCommentText xs

-- |Must compare without span filenames, for CPP injected comments with fake filename
cmpComments :: Comment -> Comment -> Ordering
cmpComments (Comment _ l1 _ _) (Comment _ l2 _ _) = compare (ss2pos $ anchor l1) (ss2pos $ anchor l2)

-- |Sort, comparing without span filenames, for CPP injected comments with fake filename
sortComments :: [Comment] -> [Comment]
sortComments cs = sortBy cmpComments cs

-- |Sort, comparing without span filenames, for CPP injected comments with fake filename
sortEpaComments :: [LEpaComment] -> [LEpaComment]
sortEpaComments cs = sortBy cmp cs
  where
    cmp (L l1 _) (L l2 _) = compare (ss2pos $ anchor l1) (ss2pos $ anchor l2)

-- | Makes a comment which originates from a specific keyword.
mkKWComment :: AnnKeywordId -> EpaLocation -> Comment
mkKWComment kw (EpaSpan ss _)
  = Comment (keywordToString kw) (Anchor ss UnchangedAnchor) ss (Just kw)
mkKWComment kw (EpaDelta dp _)
  = Comment (keywordToString kw) (Anchor placeholderRealSpan (MovedAnchor dp)) placeholderRealSpan (Just kw)

-- | Detects a comment which originates from a specific keyword.
isKWComment :: Comment -> Bool
isKWComment c = isJust (commentOrigin c)

noKWComments :: [Comment] -> [Comment]
noKWComments = filter (\c -> not (isKWComment c))

sortAnchorLocated :: [GenLocated Anchor a] -> [GenLocated Anchor a]
sortAnchorLocated = sortBy (compare `on` (anchor . getLoc))

-- | Calculates the distance from the start of a string to the end of
-- a string.
dpFromString ::  String -> DeltaPos
dpFromString xs = dpFromString' xs 0 0
  where
    dpFromString' "" line col =
      if line == 0
        then SameLine col
        else DifferentLine line col
    dpFromString' ('\n': cs) line _   = dpFromString' cs (line + 1) 0
    dpFromString' (_:cs)     line col = dpFromString' cs line       (col + 1)

-- ---------------------------------------------------------------------

isSymbolRdrName :: RdrName -> Bool
isSymbolRdrName n = isSymOcc $ rdrNameOcc n

rdrName2String :: RdrName -> String
rdrName2String r =
  case isExact_maybe r of
    Just n  -> name2String n
    Nothing ->
      case r of
        Unqual occ       -> occNameString occ
        Qual modname occ -> moduleNameString modname ++ "."
                                ++ occNameString occ
        Orig _ occ       -> occNameString occ
        Exact n          -> getOccString n

name2String :: Name -> String
name2String = showPprUnsafe

-- ---------------------------------------------------------------------

-- occAttributes :: OccName.OccName -> String
-- occAttributes o = "(" ++ ns ++ vo ++ tv ++ tc ++ d ++ ds ++ s ++ v ++ ")"
--   where
--     -- ns = (showSDocUnsafe $ OccName.pprNameSpaceBrief $ occNameSpace o) ++ ", "
--     ns = (showSDocUnsafe $ OccName.pprNameSpaceBrief $ occNameSpace o) ++ ", "
--     vo = if isVarOcc     o then "Var "     else ""
--     tv = if isTvOcc      o then "Tv "      else ""
--     tc = if isTcOcc      o then "Tc "      else ""
--     d  = if isDataOcc    o then "Data "    else ""
--     ds = if isDataSymOcc o then "DataSym " else ""
--     s  = if isSymOcc     o then "Sym "     else ""
--     v  = if isValOcc     o then "Val "     else ""

 -- ---------------------------------------------------------------------

locatedAnAnchor :: LocatedAn a t -> RealSrcSpan
locatedAnAnchor (L (SrcSpanAnn EpAnnNotUsed l) _) = realSrcSpan l
locatedAnAnchor (L (SrcSpanAnn (EpAnn a _ _) _) _) = anchor a

-- ---------------------------------------------------------------------

setAnchorAn :: (Default an) => LocatedAn an a -> Anchor -> EpAnnComments -> LocatedAn an a
setAnchorAn (L (SrcSpanAnn EpAnnNotUsed l)    a) anc cs
  = (L (SrcSpanAnn (EpAnn anc Orphans.def cs) l) a)
     -- `debug` ("setAnchorAn: anc=" ++ showAst anc)
setAnchorAn (L (SrcSpanAnn (EpAnn _ an _) l) a) anc cs
  = (L (SrcSpanAnn (EpAnn anc an cs) l) a)
     -- `debug` ("setAnchorAn: anc=" ++ showAst anc)

setAnchorEpa :: (Default an) => EpAnn an -> Anchor -> EpAnnComments -> EpAnn an
setAnchorEpa EpAnnNotUsed   anc cs = EpAnn anc Orphans.def cs
setAnchorEpa (EpAnn _ an _) anc cs = EpAnn anc an          cs

setAnchorEpaL :: EpAnn AnnList -> Anchor -> EpAnnComments -> EpAnn AnnList
setAnchorEpaL EpAnnNotUsed   anc cs = EpAnn anc mempty cs
setAnchorEpaL (EpAnn _ an _) anc cs = EpAnn anc (an {al_anchor = Nothing}) cs

setAnchorHsModule :: HsModule GhcPs -> Anchor -> EpAnnComments -> HsModule GhcPs
setAnchorHsModule hsmod anc cs = hsmod { hsmodExt = (hsmodExt hsmod) {hsmodAnn = an'} }
  where
    anc' = anc { anchor_op = UnchangedAnchor }
    an' = setAnchorEpa (hsmodAnn $ hsmodExt hsmod) anc' cs

-- |Version of l2l that preserves the anchor, immportant if it has an
-- updated AnchorOperation
moveAnchor :: Monoid b => SrcAnn a -> SrcAnn b
moveAnchor (SrcSpanAnn EpAnnNotUsed l) = noAnnSrcSpan l
moveAnchor (SrcSpanAnn (EpAnn anc _ cs) l) = SrcSpanAnn (EpAnn anc mempty cs) l

-- ---------------------------------------------------------------------

trailingAnnLoc :: TrailingAnn -> EpaLocation
trailingAnnLoc (AddSemiAnn ss)    = ss
trailingAnnLoc (AddCommaAnn ss)   = ss
trailingAnnLoc (AddVbarAnn ss)    = ss

setTrailingAnnLoc :: TrailingAnn -> EpaLocation -> TrailingAnn
setTrailingAnnLoc (AddSemiAnn _)    ss = (AddSemiAnn ss)
setTrailingAnnLoc (AddCommaAnn _)   ss = (AddCommaAnn ss)
setTrailingAnnLoc (AddVbarAnn _)    ss = (AddVbarAnn ss)

addEpAnnLoc :: AddEpAnn -> EpaLocation
addEpAnnLoc (AddEpAnn _ l) = l

-- ---------------------------------------------------------------------

-- TODO: move this to GHC
anchorToEpaLocation :: Anchor -> EpaLocation
anchorToEpaLocation (Anchor r UnchangedAnchor) = EpaSpan r Strict.Nothing
anchorToEpaLocation (Anchor _ (MovedAnchor dp)) = EpaDelta dp []

-- ---------------------------------------------------------------------
-- Horrible hack for dealing with some things still having a SrcSpan,
-- not an Anchor.

{-
A SrcSpan is defined as

data SrcSpan =
    RealSrcSpan !RealSrcSpan !(Maybe BufSpan)  -- See Note [Why Maybe BufPos]
  | UnhelpfulSpan !UnhelpfulSpanReason

data BufSpan =
  BufSpan { bufSpanStart, bufSpanEnd :: {-# UNPACK #-} !BufPos }
  deriving (Eq, Ord, Show)

newtype BufPos = BufPos { bufPos :: Int }


We use the BufPos to encode a delta, using bufSpanStart for the line,
and bufSpanEnd for the col.

To be absolutely sure, we make the delta versions use -ve values.

-}

hackSrcSpanToAnchor :: SrcSpan -> Anchor
hackSrcSpanToAnchor (UnhelpfulSpan s) = error $ "hackSrcSpanToAnchor : UnhelpfulSpan:" ++ show s
hackSrcSpanToAnchor (RealSrcSpan r Strict.Nothing) = Anchor r UnchangedAnchor
hackSrcSpanToAnchor (RealSrcSpan r (Strict.Just (BufSpan (BufPos s) (BufPos e))))
  = if s <= 0 && e <= 0
    then Anchor r (MovedAnchor (deltaPos (-s) (-e)))
      `debug` ("hackSrcSpanToAnchor: (r,s,e)=" ++ showAst (r,s,e) )
    else Anchor r UnchangedAnchor

hackAnchorToSrcSpan :: Anchor -> SrcSpan
hackAnchorToSrcSpan (Anchor r UnchangedAnchor) = RealSrcSpan r Strict.Nothing
hackAnchorToSrcSpan (Anchor r (MovedAnchor dp))
  = RealSrcSpan r (Strict.Just (BufSpan (BufPos s) (BufPos e)))
      `debug` ("hackAnchorToSrcSpan: (r,dp,s,e)=" ++ showAst (r,dp,s,e) )
  where
    s = - (getDeltaLine dp)
    e = - (deltaColumn dp)

-- ---------------------------------------------------------------------

type DeclsByTag a = Map.Map DeclTag [(RealSrcSpan, a)]

orderedDecls
  :: AnnSortKey DeclTag
  -> DeclsByTag a
  -> [(RealSrcSpan, a)]
orderedDecls sortKey declGroup  =
  case sortKey of
    NoAnnSortKey ->
      sortBy (\a b -> compare (fst a) (fst b)) (concat $ Map.elems declGroup)
    AnnSortKey keys ->
      let
        go :: [DeclTag] -> DeclsByTag a -> [(RealSrcSpan, a)]
        go [] _                      = []
        go (tag:ks) dbt = d : go ks dbt'
          where
            dbt' = Map.adjust (\ds -> drop 1 ds) tag dbt
            d = case Map.lookup tag dbt of
              Just (d':_) -> d'
              _           -> error $ "orderedDecls: could not look up "
                                       ++ show tag ++ " in " ++ show (Map.keys dbt)
      in
        go keys declGroup

hsDeclsClassDecl :: TyClDecl GhcPs -> [LHsDecl GhcPs]
hsDeclsClassDecl dec = case dec of
  ClassDecl { tcdCExt = (_an2, sortKey),
              tcdSigs = sigs,tcdMeths = methods,
              tcdATs = ats, tcdATDefs = at_defs
            } -> map snd decls
    where
      srs :: SrcAnn a -> RealSrcSpan
      srs a = realSrcSpan $ locA a
      decls
          = orderedDecls sortKey $ Map.fromList
              [(ClsSigTag,    map (\(L l s) -> (srs l, L l (SigD noExtField s))) sigs),
               (ClsMethodTag, map (\(L l s) -> (srs l, L l (ValD noExtField s))) (bagToList methods)),
               (ClsAtTag,     map (\(L l s) -> (srs l, L l (TyClD noExtField $ FamDecl noExtField s))) ats),
               (ClsAtdTag,    map (\(L l s) -> (srs l, L l (InstD noExtField $ TyFamInstD noExtField s))) at_defs)
              ]
  _ -> error $ "hsDeclsClassDecl:dec=" ++ showAst dec

replaceDeclsClassDecl :: TyClDecl GhcPs -> [LHsDecl GhcPs] -> TyClDecl GhcPs
replaceDeclsClassDecl decl decls = case decl of
  ClassDecl { tcdCExt = (an2, _) } -> decl'
    where
      (tags, methods', sigs', ats', at_defs', _, _docs) = partitionWithSortKey decls
      decl' = decl { tcdCExt = (an2, AnnSortKey tags),
                     tcdSigs = sigs',tcdMeths = methods',
                     tcdATs = ats', tcdATDefs = at_defs'
                   }

  _ -> error $ "replaceDeclsClassDecl:decl=" ++ showAst decl

partitionWithSortKey
  :: [LHsDecl GhcPs]
  -> ([DeclTag], LHsBinds GhcPs, [LSig GhcPs], [LFamilyDecl GhcPs],
      [LTyFamInstDecl GhcPs], [LDataFamInstDecl GhcPs], [LDocDecl GhcPs])
partitionWithSortKey = go
  where
    go [] = ([], emptyBag, [], [], [], [], [])
    go ((L l decl) : ds) =
      let (tags, bs, ss, ts, tfis, dfis, docs) = go ds in
      case decl of
        ValD _ b
          -> (ClsMethodTag:tags, L l b `consBag` bs, ss, ts, tfis, dfis, docs)
        SigD _ s
          -> (ClsSigTag:tags, bs, L l s : ss, ts, tfis, dfis, docs)
        TyClD _ (FamDecl _ t)
          -> (ClsAtTag:tags, bs, ss, L l t : ts, tfis, dfis, docs)
        InstD _ (TyFamInstD { tfid_inst = tfi })
          -> (ClsAtdTag:tags, bs, ss, ts, L l tfi : tfis, dfis, docs)
        InstD _ (DataFamInstD { dfid_inst = dfi })
          -> (tags, bs, ss, ts, tfis, L l dfi : dfis, docs)
        DocD _ d
          -> (tags, bs, ss, ts, tfis, dfis, L l d : docs)
        _ -> error $ "partitionBindsAndSigs" ++ (showAst decl)


-- ---------------------------------------------------------------------

orderedDeclsBinds
  :: AnnSortKey BindTag
  -> [LHsDecl GhcPs] -> [LHsDecl GhcPs]
  -> [LHsDecl GhcPs]
orderedDeclsBinds sortKey binds sigs =
  case sortKey of
    NoAnnSortKey ->
      sortBy (\a b -> compare (realSrcSpan $ getLocA a)
                              (realSrcSpan $ getLocA b)) (binds ++ sigs)
    AnnSortKey keys ->
      let
        go [] _ _                      = []
        go (BindTag:ks) (b:bs) ss = b : go ks bs ss
        go (SigDTag:ks) bs (s:ss) = s : go ks bs ss
        go (_:ks) bs ss           =     go ks bs ss
      in
        go keys binds sigs

hsDeclsLocalBinds :: HsLocalBinds GhcPs -> [LHsDecl GhcPs]
hsDeclsLocalBinds lb = case lb of
    HsValBinds _ (ValBinds sortKey bs sigs) ->
      let
        bds = map wrapDecl (bagToList bs)
        sds = map wrapSig sigs
      in
        orderedDeclsBinds sortKey bds sds
    HsValBinds _ (XValBindsLR _) -> error $ "hsDecls.XValBindsLR not valid"
    HsIPBinds {}       -> []
    EmptyLocalBinds {} -> []

hsDeclsValBinds :: (HsValBindsLR GhcPs GhcPs) -> [LHsDecl GhcPs]
hsDeclsValBinds (ValBinds sortKey bs sigs) =
      let
        bds = map wrapDecl (bagToList bs)
        sds = map wrapSig sigs
      in
        orderedDeclsBinds sortKey bds sds
hsDeclsValBinds XValBindsLR{} = error "hsDeclsValBinds"

-- ---------------------------------------------------------------------

-- |Pure function to convert a 'LHsDecl' to a 'LHsBind'. This does
-- nothing to any annotations that may be attached to either of the elements.
-- It is used as a utility function in 'replaceDecls'
decl2Bind :: LHsDecl GhcPs -> [LHsBind GhcPs]
decl2Bind (L l (ValD _ s)) = [L l s]
decl2Bind _                      = []

-- |Pure function to convert a 'LSig' to a 'LHsBind'. This does
-- nothing to any annotations that may be attached to either of the elements.
-- It is used as a utility function in 'replaceDecls'
decl2Sig :: LHsDecl GhcPs -> [LSig GhcPs]
decl2Sig (L l (SigD _ s)) = [L l s]
decl2Sig _                = []

-- ---------------------------------------------------------------------

-- |Convert a 'LSig' into a 'LHsDecl'
wrapSig :: LSig GhcPs -> LHsDecl GhcPs
wrapSig (L l s) = L l (SigD NoExtField s)

-- ---------------------------------------------------------------------

-- |Convert a 'LHsBind' into a 'LHsDecl'
wrapDecl :: LHsBind GhcPs -> LHsDecl GhcPs
wrapDecl (L l s) = L l (ValD NoExtField s)

-- ---------------------------------------------------------------------

showAst :: (Data a) => a -> String
showAst ast
  = showSDocUnsafe
    $ showAstData BlankSrcSpanFile NoBlankEpAnnotations ast

-- ---------------------------------------------------------------------
-- Putting these here for the time being, to avoid import loops

ghead :: String -> [a] -> a
ghead  info []    = error $ "ghead "++info++" []"
ghead _info (h:_) = h

glast :: String -> [a] -> a
glast  info []    = error $ "glast " ++ info ++ " []"
glast _info h     = last h

gtail :: String -> [a] -> [a]
gtail  info []    = error $ "gtail " ++ info ++ " []"
gtail _info (_:t) = t

gfromJust :: String -> Maybe a -> a
gfromJust _info (Just h) = h
gfromJust  info Nothing = error $ "gfromJust " ++ info ++ " Nothing"

-- ---------------------------------------------------------------------

-- Copied from syb for the test


-- | Generic queries of type \"r\",
--   i.e., take any \"a\" and return an \"r\"
--
type GenericQ r = forall a. Data a => a -> r


-- | Make a generic query;
--   start from a type-specific case;
--   return a constant otherwise
--
mkQ :: ( Typeable a
       , Typeable b
       )
    => r
    -> (b -> r)
    -> a
    -> r
(r `mkQ` br) a = case cast a of
                        Just b  -> br b
                        Nothing -> r

-- | Make a generic monadic transformation;
--   start from a type-specific case;
--   resort to return otherwise
--
mkM :: ( Monad m
       , Typeable a
       , Typeable b
       )
    => (b -> m b)
    -> a
    -> m a
mkM = extM return

-- | Flexible type extension
ext0 :: (Typeable a, Typeable b) => c a -> c b -> c a
ext0 def ext = maybe def id (gcast ext)


-- | Extend a generic query by a type-specific case
extQ :: ( Typeable a
        , Typeable b
        )
     => (a -> q)
     -> (b -> q)
     -> a
     -> q
extQ f g a = maybe (f a) g (cast a)

-- | Flexible type extension
ext2 :: (Data a, Typeable t)
     => c a
     -> (forall d1 d2. (Data d1, Data d2) => c (t d1 d2))
     -> c a
ext2 def ext = maybe def id (dataCast2 ext)


-- | Extend a generic monadic transformation by a type-specific case
extM :: ( Monad m
        , Typeable a
        , Typeable b
        )
     => (a -> m a) -> (b -> m b) -> a -> m a
extM def ext = unM ((M def) `ext0` (M ext))

-- | Type extension of monadic transformations for type constructors
ext2M :: (Monad m, Data d, Typeable t)
      => (forall e. Data e => e -> m e)
      -> (forall d1 d2. (Data d1, Data d2) => t d1 d2 -> m (t d1 d2))
      -> d -> m d
ext2M def ext = unM ((M def) `ext2` (M ext))

-- | The type constructor for transformations
newtype M m x = M { unM :: x -> m x }

-- | Generic monadic transformations,
--   i.e., take an \"a\" and compute an \"a\"
--
type GenericM m = forall a. Data a => a -> m a

-- | Monadic variation on everywhere
everywhereM :: forall m. Monad m => GenericM m -> GenericM m

-- Bottom-up order is also reflected in order of do-actions
everywhereM f = go
  where
    go :: GenericM m
    go x = do
      x' <- gmapM go x
      f x'
