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
  merid : (x : A) → north ≡ south

Susp-rec : ∀ {l} {C : Set l}
         (north* : C)
         (south* : C)
         (merid* : (x : A) -> (north* ≡ south*))
         -> (s : Susp) -> C
Susp-rec north* south* nm* #north = north*
Susp-rec north* south* nm* #south = south*

Susp-ind : ∀ {l} (C : Susp → Set l)
         (north* : C north)
         (south* : C south)
         (merid* : (x : A) -> (transport C (merid x) north*) ≡ south*)
         -> (s : Susp) -> C s
Susp-ind C north* south* nm* #north = north*
Susp-ind C north* south* nm* #south = south*

postulate  -- HIT
  Susp-β-merid : (C : Susp → Set) (n : C north) (s : C south)
                 (m : (a : A) -> (transport C (merid a) n) ≡ s)
               → (a : A) → apd (Susp-ind C n s m) (merid a) ≡ m a

postulate  -- HIT
  Susp-ρ-merid : (C : Set) (n : C) (s : C)
                 (m : (a : A) -> n ≡ s)
               → (a : A) → ap (Susp-rec n s m) (merid a) ≡ m a
