module Logic where

open import Level
open import Equality

data _∨_ {i} (P Q : Set i) : Set i where
  inl : P → P ∨ Q
  inr : Q → P ∨ Q

data Bool : Set where
  true false : Bool

not : Bool → Bool
not true  = false
not false = true

if_then_else_ : ∀ {i} {A : Set i} → Bool → A → A → A
if true  then r else _ = r
if false then _ else r = r

data ⊥ : Set where

¬_ : ∀ {i} → Set i -> Set i
¬ a = a → ⊥

IsProp : ∀ {i} → Set i → Set i
IsProp {i} A = (x y : A) → x ≡ y
