{-# OPTIONS --without-K #-}

open import Base

module Spaces.SInfinity where

  private
    data #S∞ : Set where
      #north : #S∞
      #south : #S∞
      #equator : #S∞ → #S∞

  S∞ : Set
  S∞ = #S∞

  north : S∞
  north = #north

  south : S∞
  south = #south

  equator : S∞ → S∞
  equator = #equator

  postulate  -- HIT
    north-merid : (x : S∞) → north ≡ equator x
    south-merid : (x : S∞) → south ≡ equator x

  S∞-ind : ∀ {l} {C : Set l}
           (north* : C)
           (south* : C)
           (equator* : C -> C)
           (north-merid* : (p : C) -> (north* ≡ equator* p))
           (south-merid* : (p : C) -> (south* ≡ equator* p))
           -> (s : S∞) -> C
  S∞-ind north* south* equator* nm* sm* #north = north*
  S∞-ind north* south* equator* nm* sm* #south = south*
  S∞-ind north* south* equator* nm* sm* (#equator x) = equator* (S∞-ind north* south* equator* nm* sm* x)

  S∞-rec : ∀ {l} (C : S∞ → Set l)
           (north* : C north)
           (south* : C south)
           (equator* : (x : S∞) -> C x -> C (equator x))
           (north-merid* : (x : S∞) (p : C x) -> (transport C (north-merid x) north*) ≡ equator* x p)
           (south-merid* : (x : S∞) (p : C x) -> (transport C (south-merid x) south*) ≡ equator* x p)
           -> (s : S∞) -> C s
  S∞-rec C north* south* equator* nm* sm* #north = north*
  S∞-rec C north* south* equator* nm* sm* #south = south*
  S∞-rec C north* south* equator* nm* sm* (#equator x) = equator* x (S∞-rec C north* south* equator* nm* sm* x)
