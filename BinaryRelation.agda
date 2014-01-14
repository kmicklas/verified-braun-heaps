module BinaryRelation where

open import Level

BinaryRelation : ∀ {i} → Set i → Set (lsucc i)
BinaryRelation {i} A = A → A → Set i

Reflexive : ∀ {i} → {A : Set i} → BinaryRelation A → Set i
Reflexive r = ∀ {x} → r x x

Symmetric : ∀ {i} → {A : Set i} → BinaryRelation A → Set i
Symmetric r = ∀ {x y} → r x y → r y x

Transitive : ∀ {i} → {A : Set i} → BinaryRelation A → Set i
Transitive r = ∀ {x y z} → r x y → r y z → r x z

Congruential : ∀ {i j} → {A : Set i} {B : Set j}
                       → (a : BinaryRelation A) (b : BinaryRelation B)
                       → (A → B) → Set (i ⊔ j)
Congruential a b f = ∀ {x y} → a x y → b (f x) (f y)

record Equivalence {i} {A : Set i} (r : BinaryRelation A) : Set (lsucc i) where
  field
    reflexive  : Reflexive  r
    symmetric  : Symmetric  r
    transitive : Transitive r

open Equivalence {{...}} public
