{-# OPTIONS --without-K #-}

open import Base

module Spaces.EqSusp (A : Set) where

private
  data #Susp : Set where
    #north : #Susp
    #south : #Susp
    #equator : A → #Susp

Susp : Set
Susp = #Susp

north : Susp
north = #north

south : Susp
south = #south

equator : A → Susp
equator = #equator

postulate  -- HIT
  north-merid : (x : A) → north ≡ equator x
  south-merid : (x : A) → south ≡ equator x

Susp-rec : ∀ {l} {C : Set l}
         (north* : C)
         (south* : C)
         (equator* : A -> C)
         (north-merid* : (x : A) -> (north* ≡ equator* x))
         (south-merid* : (x : A) -> (south* ≡ equator* x))
         -> (s : Susp) -> C
Susp-rec north* south* equator* nm* sm* #north = north*
Susp-rec north* south* equator* nm* sm* #south = south*
Susp-rec north* south* equator* nm* sm* (#equator a) = equator* a

Susp-ind : ∀ {l} (C : Susp → Set l)
         (north* : C north)
         (south* : C south)
         (equator* : (x : A) -> C (equator x))
         (north-merid* : (x : A) -> (transport C (north-merid x) north*) ≡ equator* x)
         (south-merid* : (x : A) -> (transport C (south-merid x) south*) ≡ equator* x)
         -> (s : Susp) -> C s
Susp-ind C north* south* equator* nm* sm* #north = north*
Susp-ind C north* south* equator* nm* sm* #south = south*
Susp-ind C north* south* equator* nm* sm* (#equator a) = equator* a


postulate  -- HIT
 Susp-β-north-merid :
                   (C : Susp → Set)
                   (north* : C north)
                   (south* : C south)
                   (equator* : (x : A) -> C (equator x))
                   (north-merid* : (x : A) -> (transport C (north-merid x) north*) ≡ equator* x)
                   (south-merid* : (x : A) -> (transport C (south-merid x) south*) ≡ equator* x)
               → (x : A) → apd (Susp-ind C north* south* equator* north-merid* south-merid*)
                                (north-merid x) ≡ north-merid* x

postulate  -- HIT
 Susp-β-south-merid :
                   (C : Susp → Set)
                   (north* : C north)
                   (south* : C south)
                   (equator* : (x : A) -> C (equator x))
                   (north-merid* : (x : A) -> (transport C (north-merid x) north*) ≡ equator* x)
                   (south-merid* : (x : A) -> (transport C (south-merid x) south*) ≡ equator* x)
               → (x : A) → apd (Susp-ind C north* south* equator* north-merid* south-merid*)
                                (south-merid x) ≡ south-merid* x


postulate  -- HIT
 Susp-ρ-north-merid :
                   {C : Set}
                   {north* : C}
                   {south* : C}
                   {equator* : (x : A) -> C}
                   (north-merid* : (x : A) -> north* ≡ equator* x)
                   (south-merid* : (x : A) -> south* ≡ equator* x)
               → (x : A) → ap (Susp-rec north* south* equator* north-merid* south-merid*)
                                (north-merid x) ≡ north-merid* x

postulate  -- HIT
 Susp-ρ-south-merid :
                   {C : Set}
                   {north* : C}
                   {south* : C}
                   {equator* : (x : A) -> C}
                   (north-merid* : (x : A) -> north* ≡ equator* x)
                   (south-merid* : (x : A) -> south* ≡ equator* x)
               → (x : A) → ap (Susp-rec north* south* equator* north-merid* south-merid*)
                                (south-merid x) ≡ south-merid* x
