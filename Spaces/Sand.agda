{-# OPTIONS --without-K #-}

module Spaces.Sand where

open import Base
open import Spaces.Suspension public

-- [Sp n] is the sphere of dimension n, defined by iterated suspension
Sp : ℕ → Set
Sp 0 = bool
Sp (S n) = suspension (Sp n)

-- reflexivity of equivalence at a particular point
rat : ∀ {i} {A : Set i} (a : A) → a ≡ a
rat a = refl

mutual
 ratn-tp : {X : Set} (n : ℕ) (x : X) → Set
 ratn-tp {X} 0 x = X
 ratn-tp (S n) x = ratn-tm n x ≡ ratn-tm n x

 ratn-tm : {X : Set} (n : ℕ) (x : X) → ratn-tp n x
 ratn-tm 0 x = x
 ratn-tm (S n) x = rat (ratn-tm n x)

-- [Sh n] is the sphere of dimension n, defined by having one nontrivial cell at dimension n

data Sh (n : ℕ) : Set where
  base : Sh n

postulate hoop : (n : ℕ) → ratn-tp n (base {n})

Sh-rec : (n : ℕ)
         (C : Set)
         (base* : C)
         (hoop* : ratn-tp n base*)
         -> (s : Sh n) -> C
Sh-rec C n base* hoop* sh = base*

Sh-ind : (n : ℕ)
         (C : Sh n → Set)
         (base* : C base)
         (hoop* : ratn-tp n base*)
         -> (s : Sh n) -> C
Sh-rec C n base* hoop* sh = base*

-- Sh-ind : ∀ {l} (C : Sh → Set l)
--          (north* : C north)
--          (south* : C south)
--          (paths* : (x : A) -> (transport C (paths x) north*) ≡ south*)
--          -> (s : Sh) -> C s
-- Sh-ind C north* south* nm* #north = north*
-- Sh-ind C north* south* nm* #south = south*


sp→sh : (n : ℕ) → Sp n → Sh n
sp→sh n sp = {!!}

sh→sp : (n : ℕ) → Sh n → Sp n
sh→sp n sh = {!!}
