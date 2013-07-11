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
           (merid* : (x : X) → C x → (transport C (ap inj (S.paths X x)) north*) ≡ south*)
           -> (s : X) -> C s

module Proof (X : Set) (inj : inj-S∞ X) (out : out-S∞ X inj) where

  rc : (C : Set) → (susp C → C) → X → C
  rc C f subj = out (λ x → C) (λ x sp → f sp) subj

  north : X
  north = inj (S.north X)

  south : X
  south = inj (S.south X)

  paths : X → north ≡ south
  paths = λ x → ap inj (S.paths X x)

  lemma0 : susp ((x : X) → north ≡ x) → (x : X) → north ≡ x
  lemma0 sp x = S.Susp-rec ((x : X) → north ≡ x) (north ≡ x) {!!} {!!} {!!} sp

  -- S∞-is-contr : is-contr X
  -- S∞-is-contr = north , λ y → ! (out (λ x → north ≡ x)  y)
--  S∞-is-contr = north , λ y → ! (out (λ x → north ≡ x) refl (paths north) ? y)

{-
  module Proof where
    {- The infinite dimensional sphere is contractible -}
    lemma0 : (x : S∞) → north ≡ x → transport (λ x → north ≡ x) (merid x) refl ≡ merid north
    lemma0 = λ x p → trans-cst≡id (merid x) refl ∘ ap merid (! p)

    S∞-is-contr : is-contr S∞
    S∞-is-contr = north , λ y → ! (S∞-ind (λ x → north ≡ x) refl (merid north) lemma0 y)
-}
