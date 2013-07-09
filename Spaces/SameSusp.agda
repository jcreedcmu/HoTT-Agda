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

  shim : {u v : S.Susp} (p : u ≡ v) (q : back(forward u) ≡ u) → back(forward v) ≡ v
  shim refl q = q

  shim-thm : {u v : S.Susp} (p : u ≡ v) (q : back(forward u) ≡ u) →
              transport (λ x → back(forward x) ≡ x) p q ≡ shim p q
  shim-thm refl q = refl

  test : {u v w : S.Susp} (f : S.Susp → S.Susp) (p : u ≡ v) (q r : f u ≡ w) → q ≡ r → ap f (! p) ∘ q ≡ ap f (! p) ∘ r
  test f refl q r e = e

  test2 : {u v w : S.Susp} (p : v ≡ w) (q r : u ≡ w) → q ≡ r → q ∘' (! p) ≡ r ∘' (! p)
  test2 refl q r e = e

  shim-ident : {u v : S.Susp} (p : u ≡ v) (q : back(forward u) ≡ u) → shim p q ≡ ap back (ap forward (! p)) ∘ q ∘' p
  shim-ident refl q = refl

  other-ident : {u v : S.Susp} (p : u ≡ v) (q : back(forward u) ≡ u) →
                transport (λ x → back(forward x) ≡ x) p q ≡ ap back (ap forward (! p)) ∘ q ∘' p
  other-ident refl q = refl

  equiv2 : (x : S.Susp) -> back (forward x) ≡ x
  equiv2 =  λ z -> S.Susp-ind (λ x -> back (forward x) ≡ x) refl refl (λ x →  shim-thm (S.merid x) refl ∘ {!!}) z

{-

-}
