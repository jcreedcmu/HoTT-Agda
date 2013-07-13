{-# OPTIONS --without-K #-}

open import Base

module Spaces.Susp (A : Set) where

private
  data #Susp : Set where
    #north : #Susp
    #south : #Susp

Susp : Set
Susp = #Susp

north : Susp
north = #north

south : Susp
south = #south

postulate  -- HIT
  paths : (x : A) → north ≡ south

Susp-rec : ∀ {l} (C : Set l)
         (north* : C)
         (south* : C)
         (paths* : (x : A) -> (north* ≡ south*))
         -> (s : Susp) -> C
Susp-rec C north* south* nm* #north = north*
Susp-rec C north* south* nm* #south = south*

Susp-ind : ∀ {l} (C : Susp → Set l)
         (north* : C north)
         (south* : C south)
         (paths* : (x : A) -> (transport C (paths x) north*) ≡ south*)
         -> (s : Susp) -> C s
Susp-ind C north* south* nm* #north = north*
Susp-ind C north* south* nm* #south = south*

postulate  -- HIT
  Susp-β-paths : (C : Susp → Set) (n : C north) (s : C south)
                 (m : (a : A) -> (transport C (paths a) n) ≡ s)
               → (a : A) → apd (Susp-ind C n s m) (paths a) ≡ m a

postulate  -- HIT
  Susp-ρ-paths : {C : Set} {n : C} {s : C}
                 (m : (a : A) -> n ≡ s)
               → (a : A) → ap (Susp-rec C n s m) (paths a) ≡ m a


Susp-ρ-paths2 : (C : Set) (n : C) (s : C)
            (m : (a : A) -> n ≡ s)
          → (a : A) → ap (Susp-rec C n s m) (paths a) ≡ m a
Susp-ρ-paths2 C n s m a = Susp-ρ-paths m a
