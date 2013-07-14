{-# OPTIONS --without-K #-}

-- Given a space A, create a space that has one point "base", and a
-- freely adjoined A-shaped collection of paths from base to itself.

open import Base

module Spaces.Lift (A : Set) where

private
  data #Lift : Set where
    #base : #Lift

Lift : Set
Lift = #Lift

base : Lift
base = #base

postulate  -- HIT
  loops : (x : A) → base ≡ base

Lift-rec : ∀ {l} (C : Set l)
         (base* : C)
         (loops* : (x : A) -> (base* ≡ base*))
         -> (s : Lift) -> C
Lift-rec C base* loops* #base = base*

Lift-ind : ∀ {l} (C : Lift → Set l)
         (base* : C base)
         (loops* : (x : A) -> (transport C (loops x) base*) ≡ base*)
         -> (s : Lift) -> C s
Lift-ind C base* loops* #base = base*

postulate  -- HIT
  Lift-rec-loops : (C : Set) (b : C)
                 (m : (a : A) -> b ≡ b)
               → (a : A) → ap (Lift-rec C b m) (loops a) ≡ m a

postulate  -- HIT
  Lift-ind-loops : (C : Lift → Set) (b : C base)
                 (m : (a : A) -> (transport C (loops a) b) ≡ b)
               → (a : A) → apd (Lift-ind C b m) (loops a) ≡ m a
