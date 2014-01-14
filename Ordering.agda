module Ordering where

open import Level
open import Equality
open import Logic

record Ordering {i} (A : Set i) : Set (lsucc i) where
  field
    _≤_ : A → A → Set i
    anti-sym : ∀ {x y} → x ≤ y → y ≤ x → x ≡ y
    transitive : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
    total : ∀ x y → (x ≤ y) ∨ (y ≤ x)

open Ordering {{...}}

reflexive : ∀ {i} → {A : Set i} {{o : Ordering A}} → ∀ x → x ≤ x
reflexive x with total x x
... | inl p = p
... | inr p = p
