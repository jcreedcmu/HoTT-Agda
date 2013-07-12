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
out-S∞ X inj = (C : X → Set) → ((sp : susp X) → C (inj sp)) → (x : X) → C x

module Proof (X : Set) (inj : inj-S∞ X) (out : out-S∞ X inj) where

  north : X
  north = inj (S.north X)

  south : X
  south = inj (S.south X)

  paths : X → north ≡ south
  paths = λ x → ap inj (S.paths X x)

{-
  lemma : (x₁ : X) (C: X → Set) →
 C x₁ → transport C (ap inj (S.paths X x₁)) n* ≡ s*

 transport (C ◯ inj) (S.paths X x₁) n* ≡ s*
  lemma = ?
-}
  out2 : (C : X → Set)
         (north* : C north)
         (south* : C south)
         (paths* : (x : X) → C x → (transport C (paths x) north*) ≡ south*)
           -> (x : X) -> C x
  out2 C n* s* p* x = out C (λ sp → S.Susp-ind X (C ◯ inj) n* s* {!?!} sp) x

  S∞-is-contr : is-contr X
  S∞-is-contr = north , λ y → ! (out2 (λ x → north ≡ x) refl (paths north)
                                      (λ x p → trans-cst≡id (paths x) refl ∘ ap paths (! p)) y)
