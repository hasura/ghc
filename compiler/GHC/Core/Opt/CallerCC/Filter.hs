{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TupleSections #-}

-- | Adds cost-centers to call sites selected with the @-fprof-caller=...@
-- flag.
module GHC.Core.Opt.CallerCC.Filter
    ( CallerCcFilter(..)
    , NamePattern(..)
    , parseCallerCcFilter
    ) where

import Data.Word (Word8)
import Data.Maybe

import Control.Applicative
import Data.Either
import Control.Monad
import qualified Text.ParserCombinators.ReadP as P

import GHC.Prelude
import GHC.Utils.Outputable as Outputable
import GHC.Utils.Panic
import qualified GHC.Utils.Binary as B
import Data.Char

import Language.Haskell.Syntax.Module.Name

data NamePattern
    = PChar Char NamePattern
    | PWildcard NamePattern
    | PEnd

instance Outputable NamePattern where
  ppr (PChar c rest) = char c <> ppr rest
  ppr (PWildcard rest) = char '*' <> ppr rest
  ppr PEnd = Outputable.empty

instance B.Binary NamePattern where
  get bh = do
    tag <- B.get bh
    case tag :: Word8 of
      0 -> PChar <$> B.get bh <*> B.get bh
      1 -> PWildcard <$> B.get bh
      2 -> pure PEnd
      _ -> panic "Binary(NamePattern): Invalid tag"
  put_ bh (PChar x y) = B.put_ bh (0 :: Word8) >> B.put_ bh x >> B.put_ bh y
  put_ bh (PWildcard x) = B.put_ bh (1 :: Word8) >> B.put_ bh x
  put_ bh PEnd = B.put_ bh (2 :: Word8)

type Parser = P.ReadP

parseNamePattern :: Parser NamePattern
parseNamePattern = pattern
  where
    pattern = star P.<++ wildcard P.<++ char P.<++ end
    star = PChar '*' <$ P.string "\\*" <*> pattern
    wildcard = do
      void $ P.char '*'
      PWildcard <$> pattern
    char = PChar <$> P.get <*> pattern
    end = PEnd <$ P.eof

data CallerCcFilter
    = CallerCcFilter { ccfModuleName  :: Maybe ModuleName
                     , ccfFuncName    :: NamePattern
                     }

instance Outputable CallerCcFilter where
  ppr ccf =
    maybe (char '*') ppr (ccfModuleName ccf)
    <> char '.'
    <> ppr (ccfFuncName ccf)

instance B.Binary CallerCcFilter where
  get bh = CallerCcFilter <$> B.get bh <*> B.get bh
  put_ bh (CallerCcFilter x y) = B.put_ bh x >> B.put_ bh y

parseCallerCcFilter :: String -> Either String CallerCcFilter
parseCallerCcFilter inp =
    case P.readP_to_S parseCallerCcFilter' inp of
      ((result, ""):_) -> Right result
      _ -> Left $ "parse error on " ++ inp

parseCallerCcFilter' :: Parser CallerCcFilter
parseCallerCcFilter' =
  CallerCcFilter
    <$> moduleFilter
    <*  P.char '.'
    <*> parseNamePattern
  where
    moduleFilter :: Parser (Maybe ModuleName)
    moduleFilter =
      (Just . mkModuleName <$> moduleName)
      <|>
      (Nothing <$ P.char '*')

    moduleName :: Parser String
    moduleName = do
      c <- P.satisfy isUpper
      cs <- P.munch1 (\c -> isUpper c || isLower c || isDigit c || c == '_')
      rest <- optional $ P.char '.' >> fmap ('.':) moduleName
      return $ c : (cs ++ fromMaybe "" rest)

