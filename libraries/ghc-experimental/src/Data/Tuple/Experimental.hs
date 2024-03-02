{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE NoImplicitPrelude, MagicHash, UnboxedTuples, NoListTuplePuns #-}

{-
Module      :  Data.Tuple.Experimental
Copyright   :  (c) The GHC Team
License     :  see libraries/ghc-experimental/LICENSE

Maintainer  :  ghc-devs@haskell.org
Stability   :  experimental
Portability :  non-portable (GHC extensions)

This module exports the new user-syntax types for (boxed, unboxed, constraint)
tuples, which avoid the ambiguity of the old punned names.
See the proposal for motivation and explanations:
https://github.com/ghc-proposals/ghc-proposals/blob/master/proposals/0475-tuple-syntax.rst
-}
module Data.Tuple.Experimental (
  module GHC.Tuple,
  Solo (Solo, MkSolo),

  -- * Unboxed tuples
  Unit#,
  Solo#,
  Tuple0#,
  Tuple1#,
  Tuple2#,
  Tuple3#,
  Tuple4#,
  Tuple5#,
  Tuple6#,
  Tuple7#,
  Tuple8#,
  Tuple9#,
  Tuple10#,
  Tuple11#,
  Tuple12#,
  Tuple13#,
  Tuple14#,
  Tuple15#,
  Tuple16#,
  Tuple17#,
  Tuple18#,
  Tuple19#,
  Tuple20#,
  Tuple21#,
  Tuple22#,
  Tuple23#,
  Tuple24#,
  Tuple25#,
  Tuple26#,
  Tuple27#,
  Tuple28#,
  Tuple29#,
  Tuple30#,
  Tuple31#,
  Tuple32#,
  Tuple33#,
  Tuple34#,
  Tuple35#,
  Tuple36#,
  Tuple37#,
  Tuple38#,
  Tuple39#,
  Tuple40#,
  Tuple41#,
  Tuple42#,
  Tuple43#,
  Tuple44#,
  Tuple45#,
  Tuple46#,
  Tuple47#,
  Tuple48#,
  Tuple49#,
  Tuple50#,
  Tuple51#,
  Tuple52#,
  Tuple53#,
  Tuple54#,
  Tuple55#,
  Tuple56#,
  Tuple57#,
  Tuple58#,
  Tuple59#,
  Tuple60#,
  Tuple61#,
  Tuple62#,
  Tuple63#,
  Tuple64#,

  -- * Constraint tuples
  CUnit,
  CSolo,
  CTuple0,
  CTuple1,
  CTuple2,
  CTuple3,
  CTuple4,
  CTuple5,
  CTuple6,
  CTuple7,
  CTuple8,
  CTuple9,
  CTuple10,
  CTuple11,
  CTuple12,
  CTuple13,
  CTuple14,
  CTuple15,
  CTuple16,
  CTuple17,
  CTuple18,
  CTuple19,
  CTuple20,
  CTuple21,
  CTuple22,
  CTuple23,
  CTuple24,
  CTuple25,
  CTuple26,
  CTuple27,
  CTuple28,
  CTuple29,
  CTuple30,
  CTuple31,
  CTuple32,
  CTuple33,
  CTuple34,
  CTuple35,
  CTuple36,
  CTuple37,
  CTuple38,
  CTuple39,
  CTuple40,
  CTuple41,
  CTuple42,
  CTuple43,
  CTuple44,
  CTuple45,
  CTuple46,
  CTuple47,
  CTuple48,
  CTuple49,
  CTuple50,
  CTuple51,
  CTuple52,
  CTuple53,
  CTuple54,
  CTuple55,
  CTuple56,
  CTuple57,
  CTuple58,
  CTuple59,
  CTuple60,
  CTuple61,
  CTuple62,
  CTuple63,
  CTuple64,
) where

import GHC.Tuple
import GHC.Types
import GHC.Classes

-- stupid build-order workaround until #23942 is properly fixed
import GHC.Base ()
