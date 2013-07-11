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
-- out-S∞ X = (C : X → Set) → ((x : X) → susp (C x) → C x) → (s : X) → C s
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

  rc : (C : Set) (north* : C) (south* : C) → (X → C → north* ≡ south*) → X → C
  rc C n* s* p* subj = out (λ x → C) n* s* (λ x c → trans-cst (ap inj (S.paths X x)) n* ∘ p* x c) subj

  S∞-is-contr : is-contr X
  S∞-is-contr = north , λ y → ! (out (λ x → north ≡ x) refl (ap inj (S.paths X north))
                                      (λ x p → trans-cst≡id (ap inj (S.paths X x)) refl ∘
                                                ap (λ x → ap inj (S.paths X x)) (! p)) y)
--  S∞-is-contr = north , λ y → ! (out (λ x → north ≡ x) refl (paths north) ? y)

{-
  module Proof where
    {- The infinite dimensional sphere is contractible -}
    lemma0 : (x : S∞) → north ≡ x → transport (λ x → north ≡ x) (paths x) refl ≡ paths north
    lemma0 = λ x p → trans-cst≡id (paths x) refl ∘ ap paths (! p)

    S∞-is-contr : is-contr S∞
    S∞-is-contr = north , λ y → ! (S∞-ind (λ x → north ≡ x) refl (paths north) lemma0 y)
-}
