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


  apdp : ∀ {i j} {A : Set i} (P : A → Set j) (f : (a : A) → P a) {x y : A}
    → (p : x ≡ y) → transport P p (f x) ≡ f y
  apdp P f refl = refl





  forward : S.Susp -> E.Susp
  forward = λ x -> S.Susp-rec E.north E.south (λ x -> (E.north-merid x) ∘ (! (E.south-merid x))) x

  back : E.Susp -> S.Susp
  back = λ x -> E.Susp-rec S.north S.south (λ y -> S.north) (λ y -> refl) (λ y → ! (S.merid y)) x

--  foo = (x y : S.Susp) (foo : x ≡ y) -> transport (λ x → back (forward x) ≡ x) foo refl ≡ refl

  equiv1 : (x : E.Susp) -> forward (back x) ≡ x
  equiv1 =  λ y -> E.Susp-ind (λ x -> forward (back x) ≡ x) refl refl E.north-merid {!!} {!!} y

{-
  lemma : {a b : S.Susp} (p : a ≡ b) {M : back (forward a) ≡ a}  →
             transport (λ x → back (forward x) ≡ x) p M ≡ refl
  lemma refl = {!refl!}
-}

  equiv2 : (x : S.Susp) -> back (forward x) ≡ x
  equiv2 =  λ z -> S.Susp-ind (λ x -> back (forward x) ≡ x) refl refl (λ x → {!apdp !}) z

{-

-}
