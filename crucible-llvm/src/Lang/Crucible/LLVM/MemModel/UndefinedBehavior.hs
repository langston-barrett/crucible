-- |
-- Module           : Lang.Crucible.LLVM.MemModel.UndefinedBehavior
-- Description      : All about undefined behavior
-- Copyright        : (c) Galois, Inc 2018
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
-- This module is intended to be imported qualified.
--
-- This module serves as an ad-hoc reference for the sort of undefined behaviors
-- that Crucible is aware of. The information contained here is used in
--  * providing helpful error messages
--  * configuring which safety checks to perform
--
-- Disabling checks for undefined behavior does not change the behavior of any
-- memory operations. If it is used to enable the simulation of undefined
-- behavior, the result is that any guarantees that Crucible provides about the
-- code essentially have an additional hypothesis: that the LLVM
-- compiler/hardware platform behave identically to Crucible's simulator when
-- encountering such behavior.
--
-- The following documents were used in the writing of this module:
-- * [C++17]: http://www.open-std.org/jtc1/sc22/wg21/docs/papers/2017/n4659.pdf
-- * [C99]: http://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf
--   (text: http://www.iso-9899.info/n1570.html)
------------------------------------------------------------------------

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StrictData #-}

module Lang.Crucible.LLVM.MemModel.UndefinedBehavior
  ( UndefinedBehavior(..)
  , citeUndefinedBehavior
  , ppUndefinedBehavior

  -- ** UndefinedBehaviorConfig
  , ubStrictConfig
  , ubLaxConfig
  , ubBlacklist
  , ubWhitelist
  ) where

-- -----------------------------------------------------------------
-- ** UndefinedBehavior

-- | See 'cite' and 'explain'.
data UndefinedBehavior =
    PtrAddOffsetOutOfBounds
  | MemcpyDisjoint
  | DoubleFree
  | FreeInvalidPointer
  deriving (Eq, Enum, Ord, Show)

-- | Which section(s) of the C or C++ specifications are relevant to this
-- behavior?
cite :: UndefinedBehavior -> String
cite =
  \case
    PtrAddOffsetOutOfBounds -> "C99: 6.5.6 Additive operators"
    MemcpyDisjoint          -> "C99: 7.24.2.1 The memcpy function"
    DoubleFree              -> "C99: 7.22.3.3 The free function"
    FreeInvalidPointer      -> "C99: 7.22.3.3 The free function"

explain :: UndefinedBehavior -> String
explain = 
  \case
    PtrAddOffsetOutOfBounds -> unwords $
      [ "Addition of an offset to a pointer that resulted in a pointer to an"
      , "address outside of the allocation."
      ]
    MemcpyDisjoint     -> "Use of `memcpy` with non-disjoint regions of memory"
    DoubleFree         -> "`free` called on already-freed memory"
    FreeInvalidPointer -> "`free` called on invalid pointer"

pp :: UndefinedBehavior -> String
pp ub = unlines [ "Undefined behavior: ", "Reference: " ++ cite ub, explain ub ]

-- -----------------------------------------------------------------
-- ** UndefinedBehaviorConfig

type Config = UndefinedBehavior -> Bool

-- | Disallow all undefined behavior.
strictConfig :: Config
strictConfig = const True
{-# INLINE strictConfig #-}

-- | Allow all undefined behavior.
laxConfig :: Config
laxConfig = const False
{-# INLINE laxConfig #-}

-- | Disallow undefined behavior that appears in this list.
blacklist :: [UndefinedBehavior] -> Config
blacklist lst = not . whitelist lst
{-# INLINE blacklist #-}

-- | Allow undefined behavior that appears in this list.
whitelist :: [UndefinedBehavior] -> Config
whitelist lst = (`elem` lst)
{-# INLINE whitelist #-}
