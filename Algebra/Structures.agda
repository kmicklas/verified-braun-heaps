module Algebra.Structures where

open import Level
open import Algebra.Properties

record MagmaStr (C : Set) : Set where
  field
    _·_ : BinOp C

record SemiGroupStr (C : Set) : Set where
  field
    _·_ : BinOp C
    assoc : Assoc _·_

record MonoidStr (C : Set) : Set where
  field
    _·_ : BinOp C
    e : C
    assoc : Assoc _·_
    left-unit  : LeftUnit  _·_ e
    right-unit : RightUnit _·_ e

record CommMonoidStr (C : Set) : Set where
  field
    _·_ : BinOp C
    e : C
    assoc : Assoc _·_
    comm : Comm _·_
    unit  : LeftUnit  _·_ e

record GroupStr (C : Set) : Set where
  field
    _·_ : BinOp C
    e : C
    assoc : Assoc _·_
    left-unit  : LeftUnit  _·_ e
    right-unit : RightUnit _·_ e
    inv : C → C
    left-inverse  : LeftInverse  _·_ e inv
    right-inverse : RightInverse _·_ e inv

record CommGroupStr (C : Set) : Set where
  field
    _·_ : BinOp C
    e : C
    assoc : Assoc _·_
    comm  : Comm  _·_
    left-unit  : LeftUnit  _·_ e
    inv : C → C
    left-inverse  : LeftInverse  _·_ e inv

record SemiRingStr (C : Set) : Set where
  field
    add : CommMonoidStr C
    mul : MonoidStr C
  open CommMonoidStr add renaming (_·_ to _+_)
  open MonoidStr mul
  field
    left-distr  : LeftDistr  _·_ _+_
    right-distr : RightDistr _·_ _+_

record CommSemiRingStr (C : Set) : Set where
  field
    add : CommMonoidStr C
    mul : CommMonoidStr C
  open CommMonoidStr add renaming (_·_ to _+_)
  open CommMonoidStr mul
  field
    distr  : LeftDistr  _·_ _+_

record RingStr (C : Set) : Set where
  field
    add : CommGroupStr C
    mul : MonoidStr C
  open CommGroupStr add renaming (_·_ to _+_)
  open MonoidStr mul
  field
    left-distr  : LeftDistr  _·_ _+_
    right-distr : RightDistr _·_ _+_

record CommRingStr (C : Set) : Set where
  field
    add : CommGroupStr C
    mul : CommMonoidStr C
  open CommGroupStr add renaming (_·_ to _+_)
  open CommMonoidStr mul
  field
    left-distr  : LeftDistr  _·_ _+_

record Algebra {i} (Str : Set i → Set i) : Set (lsucc i) where
  constructor algebra
  field
    carrier : Set i
    structure : Str carrier

Magma        = Algebra MagmaStr
SemiGroup    = Algebra SemiGroupStr
Monoid       = Algebra MonoidStr
CommMonoid   = Algebra CommMonoidStr
Group        = Algebra GroupStr
CommGroup    = Algebra CommGroupStr
SemiRing     = Algebra SemiRingStr
CommSemiRing = Algebra CommSemiRingStr
Ring         = Algebra RingStr
CommRing     = Algebra CommRingStr
