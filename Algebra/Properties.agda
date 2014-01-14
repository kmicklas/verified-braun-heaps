module Algebra.Properties where

open import Level
open import Equality

BinOp : ∀ {i} → Set i → Set i
BinOp C = C → C → C

Assoc : ∀ {i} → {C : Set i} → BinOp C → Set i
Assoc _·_ = ∀ x y z → ((x · y) · z) ≡ (x · (y · z))

Comm : ∀ {i} → {C : Set i} → BinOp C → Set i
Comm _·_ = ∀ x y → (x · y) ≡ (y · x)

LeftUnit : ∀ {i} → {C : Set i} → BinOp C → C → Set i
LeftUnit _·_ e = ∀ x → (e · x) ≡ x

RightUnit : ∀ {i} → {C : Set i} → BinOp C → C → Set i
RightUnit _·_ e = ∀ x → (x · e) ≡ x

comm-left-unit : ∀ {i} → {C : Set i} {b : BinOp C} {e : C}
                       → Comm b → RightUnit b e → LeftUnit b e
comm-left-unit {i} {C} {b} {e} c r = λ x → c e x ≈ r x

comm-right-unit : ∀ {i} → {C : Set i} {b : BinOp C} {e : C}
                        → Comm b → LeftUnit b e → RightUnit b e
comm-right-unit {i} {C} {b} {e} c l = λ x → c x e ≈ l x

LeftDistr : ∀ {i} → {C : Set i} → BinOp C → BinOp C → Set i
LeftDistr _·_ _+_ = ∀ x y z → (x · (y + z)) ≡ ((x · y) + (x · z))

RightDistr : ∀ {i} → {C : Set i} → BinOp C → BinOp C → Set i
RightDistr _·_ _+_ = ∀ x y z → ((x + y) · z) ≡ ((x · z) + (y · z))

comm-left-distr : ∀ {i} → {C : Set i} {m : BinOp C} {a : BinOp C}
                        → Comm m → RightDistr m a → LeftDistr m a
comm-left-distr {i} {C} {_·_} {_+_} c l x y z
  = (c x (y + z) ≈ l y z x) ≈
    (cong (λ a → a + (z · x)) (c y x) ≈
     cong (λ a → (x · y) + a) (c z x))

comm-right-distr : ∀ {i} → {C : Set i} {m : BinOp C} {a : BinOp C}
                         → Comm m → LeftDistr m a → RightDistr m a
comm-right-distr {i} {C} {_·_} {_+_} c l x y z
  = (c (x + y) z ≈ l z x y) ≈
    (cong (λ a → a + (z · y)) (c z x) ≈
     cong (λ a → (x · z) + a) (c z y))

LeftInverse : ∀ {i} → {C : Set i} → BinOp C → C → (C → C) → Set i
LeftInverse _·_ e inv = ∀ x → ((inv x) · x) ≡ e

RightInverse : ∀ {i} → {C : Set i} → BinOp C → C → (C → C) → Set i
RightInverse _·_ e inv = ∀ x → (x · (inv x)) ≡ e

comm-left-inverse : ∀ {i} → {C : Set i} {b : BinOp C} {e : C}
                          → {inv : C → C} {c : Comm b}
                          → RightInverse b e inv → LeftInverse b e inv
comm-left-inverse {i} {C} {_·_} {e} {inv} {c} r x = c (inv x) x ≈ r x

comm-right-inverse : ∀ {i} → {C : Set i} {b : BinOp C} {e : C}
                           → {inv : C → C} {c : Comm b}
                           → LeftInverse b e inv → RightInverse b e inv
comm-right-inverse {i} {C} {_·_} {e} {inv} {c} l x = c x (inv x) ≈ l x

LeftAnhil : ∀ {i} → {C : Set i} → BinOp C → C → Set i
LeftAnhil _·_ e = ∀ x → (e · x) ≡ e

RightAnhil : ∀ {i} → {C : Set i} → BinOp C → C → Set i
RightAnhil _·_ e = ∀ x → (x · e) ≡ e

comm-left-anhil : ∀ {i} → {C : Set i} {b : BinOp C} {e : C}
                        → Comm b → RightAnhil b e → LeftAnhil b e
comm-left-anhil {i} {C} {b} {e} c r = λ x → c e x ≈ r x

comm-right-anhil : ∀ {i} → {C : Set i} {b : BinOp C} {e : C}
                         → Comm b → LeftAnhil b e → RightAnhil b e
comm-right-anhil {i} {C} {b} {e} c l = λ x → c x e ≈ l x
