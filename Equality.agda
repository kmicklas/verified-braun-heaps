module Equality where

open import Level
open import BinaryRelation

data _≡_ {i} {A : Set i} : BinaryRelation A where
  refl : Reflexive _≡_

sym : ∀ {i A} → Symmetric (_≡_ {i} {A})
sym refl = refl

_≈_ : ∀ {i A} → Transitive (_≡_ {i} {A})
refl ≈ refl = refl

≡-equiv : ∀ {i A} → Equivalence (_≡_ {i} {A})
≡-equiv = record {
                   reflexive  = refl;
                   symmetric  = sym;
                   transitive = _≈_
                 }

cong : ∀ {i j} → {A : Set i} {B : Set j} → (f : A → B) → Congruential _≡_ _≡_ f
cong f refl = refl

uip : ∀ {i} {A : Set i} {x y : A} (p q : x ≡ y) → p ≡ q
uip refl refl = refl

{-# BUILTIN EQUALITY _≡_  #-}
{-# BUILTIN REFL     refl #-}
