open import Level
open import Ordering using (reflexive)

module BraunHeap
  {i}
  {A : Set i}
  (o : Ordering.Ordering A)
  where

open Ordering.Ordering o
open import Equality
open import Logic
open import Pair
open import Nat hiding (_≤_)

mutual
  data BHeap : Set i where
    mt : BHeap
    node : (v : A) → (l r : BHeap)
                   → .(size : ValidSizes l r)
                   → .(heap-left : Heap v l) .(heap-right : Heap v r)
                   → BHeap
  
  data ValidSizes (l r : BHeap) : Set i where
    same-size : size l ≡ size r → ValidSizes l r
    one-more : size l ≡ succ (size r) → ValidSizes l r
  
  data Heap (v : A) : BHeap → Set i where
    empty : Heap v mt
    is-≤ : ∀ v' l r .s .hl .hr → v ≤ v' → Heap v (node v' l r s hl hr)
  
  size : BHeap → ℕ
  size mt = 0
  size (node _ l r _ _ _) = 1 + (size l + size r)

heap-trans : ∀ {x y} → (h : BHeap) → x ≤ y → Heap y h → Heap x h
heap-trans .mt _ empty = empty
heap-trans .(node v l r s hl hr) le (is-≤ v l r s hl hr p) = is-≤ v l r s hl hr (transitive le p)

singleton : A → BHeap
singleton v = node v mt mt (same-size refl) empty empty

singleton-heap : ∀ {x y} → x ≤ y → Heap x (singleton y)
singleton-heap p = is-≤ _ _ _ _ _ _ p

mutual
  insert : A → BHeap → BHeap
  insert x mt = singleton x
  insert x (node v l r s hl hr) with total x v
  ... | inl p = node x (insert v r) l
                     (insert-swap s v)
                     (insert-heap x v r p hr) (heap-trans _ p hl)
  ... | inr p = node v (insert x r) l
                       (insert-swap s x)
                       (insert-still-heap x v r p hr)
                       hl
  
  insert-swap : ∀ {l r} → ValidSizes l r → (v : A) → ValidSizes (insert v r) l
  insert-swap {_} {r} (same-size p) v = one-more  (insert-size v r ≈ cong succ (sym p))
  insert-swap {_} {r} (one-more  p) v = same-size (insert-size v r ≈ sym p)
  
  insert-size : ∀ v h → size (insert v h) ≡ succ (size h)
  insert-size _ mt = refl
  insert-size x (node v l r s hl hr) with total x v
  ... | inl p = cong succ (cong (λ a → a + size l) (insert-size v r) ≈
                           cong succ (+-comm (size r) (size l)))
  ... | inr p = cong succ (cong (λ a → a + size l) (insert-size x r) ≈
                           cong succ (+-comm (size r) (size l)))
  
  insert-heap : ∀ x v h → x ≤ v → Heap v h → Heap x (insert v h)
  insert-heap _ _ mt p _ = singleton-heap p
  insert-heap x v .(node rt l r s hl hr) le (is-≤ rt l r s hl hr hp) with total v rt
  ... | inl p = is-≤ _ _ _ _ _ _ le
  ... | inr p = is-≤ _ _ _ _ _ _ (transitive le hp)
  
  insert-still-heap : ∀ x v h → v ≤ x → Heap v h → Heap v (insert x h)
  insert-still-heap _ _ mt p _ = singleton-heap p
  insert-still-heap x v .(node rt l r s hl hr) le (is-≤ rt l r s hl hr hp) with total x rt
  ... | inl p = is-≤ _ _ _ _ _ _ le
  ... | inr p = is-≤ _ _ _ _ _ _ hp

¬0≡succ : ∀ {i n} → {T : Set i} → 0 ≡ succ n → T
¬0≡succ ()

get-min : ∀ {n} h → size h ≡ succ n → A
get-min mt p = ¬0≡succ p
get-min (node v _ _ _ _ _) _ = v

data Tri (v l r : A) : Set i where
  v-least : v ≤ l → v ≤ r → Tri v l r
  l-least : l ≤ v → l ≤ r → Tri v l r
  r-least : r ≤ v → r ≤ l → Tri v l r

decide-tri : (v l r : A) → Tri v l r
decide-tri v l r with (total l r , (total v l , total v r))
... | (_      , (inl vl , inl vr)) = v-least vl vr
... | (inl lr , (inl vl , inr rv)) = v-least vl (transitive vl lr)
... | (inl lr , (inr lv , inl vr)) = l-least lv lr
... | (inl lr , (inr lv , inr rv)) = l-least lv lr
... | (inr rl , (inl vl , inr rv)) = r-least rv rl
... | (inr rl , (inr lv , inl vr)) = v-least (transitive vr rl) vr
... | (inr rl , (inr lv , inr rv)) = r-least rv rl


mutual
  combine : A → (l r : BHeap) → .(s : ValidSizes l r) → BHeap
  combine v mt _ _ = singleton v
  combine v (node lv ll lr ls lhl lhr) mt _ with total v lv
  ... | inl p = node v  (singleton lv) mt (one-more refl) (singleton-heap p) empty
  ... | inr p = node lv (singleton v)  mt (one-more refl) (singleton-heap p) empty
  combine v (node lv ll lr ls lhl lhr) (node rv rl rr rs rhl rhr) s with decide-tri v lv rv
  ... | v-least pvl pvr = node v (node lv ll lr ls lhl lhr) (node rv rl rr rs rhl rhr)
                               s (is-≤ _ _ _ _ _ _ pvl) (is-≤ _ _ _ _ _ _ pvr)
  ... | l-least plv plr = node lv (combine v ll lr ls) (node rv rl rr rs rhl rhr)
                                  (combine-left-size s)
                                  (combine-heap plv lhl lhr) (is-≤ _ _ _ _ _ _ plr)
  ... | r-least prv prl = node rv (node lv ll lr ls lhl lhr) (combine v rl rr rs)
                                  (combine-right-size s)
                                  (is-≤ _ _ _ _ _ _ prl) (combine-heap prv rhl rhr)
  
  combine-left-size : ∀ {v lv ll lr ls lhl lhr r} → ValidSizes (node lv ll lr ls lhl lhr) r
                                                  → ValidSizes (combine v ll lr ls) r
  combine-left-size = {!!}
  
  combine-right-size : ∀ {v lv ll lr ls lhl lhr rv rl rr rs rhl rhr}
                       → ValidSizes (node lv ll lr ls lhl lhr) (node rv rl rr rs rhl rhr)
                       → ValidSizes (node lv ll lr ls lhl lhr) (combine v rl rr rs)
  combine-right-size = {!!}
  
  combine-heap : ∀ {x v l r s} → v ≤ x → Heap v l → Heap v r → Heap v (combine x l r s)
  combine-heap = {!!}

get-bottom-left : ∀ {n} → (h : BHeap) → size h ≡ succ n → A
get-bottom-left mt p = ¬0≡succ p
get-bottom-left (node v mt _ _ _ _) _ = v
get-bottom-left (node v (node lv ll lr ls lhl lhr) _ _ _ _) _
  = get-bottom-left (node lv ll lr ls lhl lhr) refl

mutual
  del-bottom-left : ∀ {n} → (h : BHeap) → size h ≡ succ n → BHeap
  del-bottom-left mt p = ¬0≡succ p
  del-bottom-left (node v mt _ _ _ _) _ = mt
  del-bottom-left (node v (node lv ll lr ls lhl lhr)  r _ hl hr) _
    = node v r (del-bottom-left (node lv ll lr ls lhl lhr) refl) {!!} hr {!!}
  
  del-bottom-left-size : ∀ {n} h → (p : size h ≡ succ n) → size (del-bottom-left h p) ≡ n
  del-bottom-left-size mt p = ¬0≡succ p
  del-bottom-left-size (node v mt r s hl hr) p = {!!}
  del-bottom-left-size (node v (node v₁ l l₁ size heap-left heap-right) r s hl hr) p = {!!}

del-min : ∀ {n} h → size h ≡ succ n → BHeap
del-min mt p = ¬0≡succ p
del-min (node v mt _ _ _ _) _ = mt
del-min (node v (node lv ll lr ls lhl lhr) r _ _ _) _ 
  = combine (get-bottom-left (node lv ll lr ls lhl lhr) refl)
            r (del-bottom-left (node lv ll lr ls lhl lhr) refl) {!!}
