module Nat where

open import Equality
open import Decidable
open import Function
open import Algebra.Properties
open import Algebra.Structures

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC  succ #-}

pred : ℕ → ℕ
pred zero = zero
pred (succ x) = x

decideℕ≡ : (x y : ℕ) → Decision (x ≡ y)
decideℕ≡ zero zero = yes refl
decideℕ≡ zero (succ _) = no λ ()
decideℕ≡ (succ _) zero = no λ ()
decideℕ≡ (succ x) (succ y) = cong-succ x y (decideℕ≡ x y)
  where cong-succ : (x y : ℕ) → Decision (x ≡ y) → Decision (succ x ≡ succ y)
        cong-succ x y (yes e) = yes (cong succ e)
        cong-succ x y (no n) = no (n ∘ cong pred)

ℕ≡Decision : ≡Decision ℕ
ℕ≡Decision {x} {y} = decideℕ≡ x y

_+_ : ℕ → ℕ → ℕ
zero     + y = y
(succ x) + y = succ (x + y)

{-# BUILTIN NATPLUS _+_ #-}

_*_ : ℕ → ℕ → ℕ
zero     * y = zero
(succ x) * y = y + (x * y)

{-# BUILTIN NATTIMES _*_ #-}

data _≤_ : ℕ → ℕ → Set where
  z≤x : {y   : ℕ}         → zero ≤ y
  s≤s : {x y : ℕ} → (p : x ≤ y) → (succ x) ≤ (succ y)

sub : (x y : ℕ) → y ≤ x → ℕ
sub x zero _ = zero
sub .(succ x) (succ y) (s≤s .{y} {x} p) = sub x y p

+-succ-lemma : ∀ x y → (x + succ y) ≡ succ (x + y)
+-succ-lemma zero     y = refl
+-succ-lemma (succ x) y = cong succ (+-succ-lemma x y)

+-comm : Comm _+_
+-comm zero zero     = refl
+-comm zero (succ y) = cong succ (+-comm zero y)
+-comm (succ x) y    = cong succ (+-comm x y) ≈ sym (+-succ-lemma y x)

+-assoc : Assoc _+_
+-assoc zero     y z = refl
+-assoc (succ x) y z = cong succ (+-assoc x y z)

*-succ-lemma : ∀ x y → (x * succ y) ≡ (x + (x * y))
*-succ-lemma zero     y = refl
*-succ-lemma (succ x) y = cong (λ a → succ (y + a)) (*-succ-lemma x y) ≈
                          cong succ (sym
                            (+-assoc y x (x * y)) ≈
                            (cong (λ a → a + (x * y)) (sym (+-comm x y)) ≈
                             +-assoc x y (x * y)))

*-comm : Comm _*_
*-comm zero zero     = refl
*-comm zero (succ y) = *-comm zero y
*-comm (succ x) y    = cong (λ a → y + a) (*-comm x y) ≈
                       sym (*-succ-lemma y x)

*-+-right-distr : RightDistr _*_ _+_
*-+-right-distr zero y z = refl
*-+-right-distr (succ x) y z = cong (λ a → z + a) (*-+-right-distr x y z) ≈ (sym (+-assoc z (x * z) (y * z)))

*-+-left-distr : LeftDistr _*_ _+_
*-+-left-distr = comm-left-distr *-comm *-+-right-distr

*-assoc : Assoc _*_
*-assoc zero y z = refl
*-assoc (succ x) y z = *-+-right-distr y (x * y) z ≈
                       cong (λ a → (y * z) + a) (*-assoc x y z)

+-0-left-unit : LeftUnit _+_ 0
+-0-left-unit _ = refl

+-0-right-unit : RightUnit _+_ 0
+-0-right-unit = comm-right-unit +-comm +-0-left-unit

*-1-left-unit : LeftUnit _*_ 1
*-1-left-unit zero = refl
*-1-left-unit (succ y) = cong succ (*-1-left-unit y)

*-1-right-unit : RightUnit _*_ 1
*-1-right-unit = comm-right-unit *-comm *-1-left-unit

ℕ-+-comm-monoid : CommMonoidStr ℕ
ℕ-+-comm-monoid = record {
                    _·_ = _+_;
                    e = 0;
                    assoc = +-assoc;
                    comm = +-comm;
                    unit = +-0-left-unit
                  }

ℕ-*-comm-monoid : CommMonoidStr ℕ
ℕ-*-comm-monoid = record {
                    _·_ = _*_;
                    e = 1;
                    assoc = *-assoc;
                    comm = *-comm;
                    unit = *-1-left-unit
                  }

ℕ-comm-semiring-str : CommSemiRingStr ℕ
ℕ-comm-semiring-str = record {
                        add = ℕ-+-comm-monoid;
                        mul = ℕ-*-comm-monoid;
                        distr = *-+-left-distr
                      }

ℕ-comm-semiring : CommSemiRing
ℕ-comm-semiring = algebra ℕ ℕ-comm-semiring-str
