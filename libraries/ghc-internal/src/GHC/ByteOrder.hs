{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE Trustworthy #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  GHC.ByteOrder
-- Copyright   :  (c) The University of Glasgow, 1994-2000
-- License     :  see libraries/base/LICENSE
--
-- Maintainer  :  ghc-devs@haskell.org
-- Stability   :  internal
-- Portability :  non-portable (GHC extensions)
--
-- Target byte ordering.
--
-- @since 4.11.0.0
-----------------------------------------------------------------------------

module GHC.ByteOrder
  ( ByteOrder(..)
  , targetByteOrder
  ) where

-- Required for WORDS_BIGENDIAN
#include <ghcautoconf.h>

import GHC.Base
import GHC.Enum
import GHC.Generics (Generic)
import Text.Read
import Text.Show

-- | Byte ordering.
data ByteOrder
    = BigEndian    -- ^ most-significant-byte occurs in lowest address.
    | LittleEndian -- ^ least-significant-byte occurs in lowest address.
    deriving ( Eq      -- ^ @since 4.11.0.0
             , Ord     -- ^ @since 4.11.0.0
             , Bounded -- ^ @since 4.11.0.0
             , Enum    -- ^ @since 4.11.0.0
             , Read    -- ^ @since 4.11.0.0
             , Show    -- ^ @since 4.11.0.0
             , Generic -- ^ @since 4.15.0.0
             )

-- | The byte ordering of the target machine.
targetByteOrder :: ByteOrder
#if defined(WORDS_BIGENDIAN)
targetByteOrder = BigEndian
#else
targetByteOrder = LittleEndian
#endif
