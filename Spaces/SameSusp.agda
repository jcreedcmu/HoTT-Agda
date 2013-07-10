{-# OPTIONS --without-K #-}

open import Base
import Spaces.EqSusp
import Spaces.Susp
open import Funext

module Spaces.SameSusp (A : Set) where

  module S where
    open Spaces.Susp A public

  module E where
    open Spaces.EqSusp A public


  forward : S.Susp -> E.Susp
  forward = λ x -> S.Susp-rec E.Susp E.north E.south (λ x -> (E.north-merid x) ∘ (! (E.south-merid x))) x

  back : E.Susp -> S.Susp
  back = λ x -> E.Susp-rec S.north S.south (λ y -> S.north) (λ y -> refl) (λ y → ! (S.merid y)) x

  lemma1 : (z : A) -> ! (ap (forward ◯ back) (E.north-merid z)) ∘ E.north-merid z ≡ E.north-merid z
  lemma1 = {!!}

  lemma2 : (z : A) -> ! (ap (forward ◯ back) (E.south-merid z)) ∘ E.south-merid z ≡ E.north-merid z
  lemma2 = {!!}

  lemma3a : (z : A) -> ! (ap (back ◯ forward) (S.merid z)) ≡ ! (S.merid z)
  lemma3a = λ z → opposite-ap (back ◯ forward) (S.merid z) ∘
                   ap-compose back forward (! (S.merid z)) ∘
                   ap (ap back) (ap-opposite forward (S.merid z)) ∘
                   ap (λ x → ap back (! x)) (S.Susp-ρ-merid (λ x -> (E.north-merid x) ∘ (! (E.south-merid x))) z)  ∘
                   ap (ap back) (opposite-concat (E.north-merid z) (! (E.south-merid z))) ∘
                   ap-concat back (! (! (E.south-merid z))) (! (E.north-merid z)) ∘
                   ap (λ q → q ∘ (ap back (! (E.north-merid z)))) ((ap (ap back) (opposite-opposite (E.south-merid z))) ∘
                                                                  (E.Susp-ρ-south-merid (λ y -> refl) (λ y → ! (S.merid y)) z)) ∘
                   ap (λ q → ! (S.merid z) ∘ q) (ap-opposite back (E.north-merid z) ∘ (ap ! (E.Susp-ρ-north-merid (λ y -> refl) (λ y → ! (S.merid y)) z))) ∘
                   refl-right-unit (! (S.merid z))

-- ?2 : ap back (! (ap forward (S.merid z))) ≡ ! (S.merid z)

  lemma3 : (z : A) -> ! (ap (back ◯ forward) (S.merid z)) ∘ S.merid z ≡ refl
  lemma3 = λ z → move-right-on-right (! (ap (back ◯ forward) (S.merid z))) (S.merid z) refl (lemma3a z)


  equiv1 : (x : E.Susp) -> forward (back x) ≡ x
  equiv1 = λ y -> E.Susp-ind (λ x -> forward (back x) ≡ x) refl refl E.north-merid
                     (λ z → trans-app≡id (forward ◯ back) (E.north-merid z) refl ∘ lemma1 z)
                     (λ z → trans-app≡id (forward ◯ back) (E.south-merid z) refl ∘ lemma2 z) y

  equiv2 : (x : S.Susp) -> back (forward x) ≡ x
  equiv2 =  λ z -> S.Susp-ind (λ x -> back (forward x) ≡ x) refl refl (λ x → trans-app≡id (back ◯ forward) (S.merid x) refl ∘ lemma3 x) z
