module Decidable where

open import Logic
open import Equality

data Decision {i} (P : Set i) : Set i where
  yes : P → Decision P
  no : ¬ P → Decision P

≡Decision : ∀ {i} → (A : Set i) → Set i
≡Decision A = ∀ {x y : A} → Decision (x ≡ y)

decide : ∀ {i} → {P : Set i} → {{d : Decision P}} → Decision P
decide {i} {P} {{d}} = d
