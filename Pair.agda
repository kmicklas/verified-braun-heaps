module Pair where

open import Level

record Σ {i} {j} (A : Set i) (B : A → Set j) : Set (i ⊔ j) where
  constructor
    _∷_
  field
    a : A
    b : B a

record _×_ {i} {j} (A : Set i) (B : Set j) : Set (i ⊔ j) where
  constructor
    _,_
  field
    a : A
    b : B

left  = _×_.a
right = _×_.b
