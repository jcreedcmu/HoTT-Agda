{-# OPTIONS --without-K #-}

open import Base

module Spaces.SInfinity where

  private
    data #S∞ : Set where
      #north : #S∞
      #south : #S∞

  S∞ : Set
  S∞ = #S∞

  north : S∞
  north = #north

  south : S∞
  south = #south

  postulate  -- HIT
    merid : S∞ → north ≡ south

  S∞-rec : ∀ {l} {C : Set l}
           (north* : C)
           (south* : C)
           (merid* : C -> (north* ≡ south*))
           -> (s : S∞) -> C
  S∞-rec north* south* merid* #north = north*
  S∞-rec north* south* merid* #south = south*

  S∞-ind : ∀ {l} (C : S∞ → Set l)
           (north* : C north)
           (south* : C south)
           (merid* : (x : S∞) → C x → (transport C (merid x) north*) ≡ south*)
           -> (s : S∞) -> C s
  S∞-ind C north* south* merid* #north = north*
  S∞-ind C north* south* merid* #south = south*

  -- also should put in β rules for recursion, induction...

  module Proof where
    {- The infinite dimensional sphere is contractible -}
    lemma0 : (x : S∞) → north ≡ x → transport (λ x → north ≡ x) (merid x) refl ≡ merid north
    lemma0 = λ x p → trans-cst≡id (merid x) refl ∘ ap merid (! p)

    S∞-is-contr : is-contr S∞
    S∞-is-contr = north , λ y → ! (S∞-ind (λ x → north ≡ x) refl (merid north) lemma0 y)
