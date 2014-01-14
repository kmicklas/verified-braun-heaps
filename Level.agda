module Level where

postulate
  Level : Set
  lzero : Level
  lsucc : Level → Level
  _⊔_   : Level → Level → Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO lzero #-}
{-# BUILTIN LEVELSUC  lsucc #-}
{-# BUILTIN LEVELMAX  _⊔_   #-}
