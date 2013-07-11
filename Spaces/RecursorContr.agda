{-# OPTIONS --without-K #-}

open import Base
import Spaces.Susp as S

module Spaces.RecursorContr where

susp : Set → Set
susp = S.Susp

-- constructors
inj-S∞ : Set → Set
inj-S∞ X = susp X → X

-- induction principle
out-S∞ : (X : Set) → inj-S∞ X → Set₁
out-S∞ X inj = (C : X → Set)
           (north* : C (inj (S.north X)))
           (south* : C (inj (S.south X)))
           (paths* : (x : X) → C x → (transport C (ap inj (S.paths X x)) north*) ≡ south*)
           -> (s : X) -> C s

module Proof (X : Set) (inj : inj-S∞ X) (out : out-S∞ X inj) where

  north : X
  north = inj (S.north X)

  south : X
  south = inj (S.south X)

  paths : X → north ≡ south
  paths = λ x → ap inj (S.paths X x)

  S∞-is-contr : is-contr X
  S∞-is-contr = north , λ y → ! (out (λ x → north ≡ x) refl (paths north)
                                      (λ x p → trans-cst≡id (paths x) refl ∘ ap paths (! p)) y)
