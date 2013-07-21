{-# OPTIONS --without-K #-}

open import Base
open import Jcreed.Util

module Jcreed.Yoneda where

  -- apply a natural isomorphism at an object
  _·_ : {F G : Functor} (α : F ≡ G) → (A : Set) → F * A → G * A
  α · A = transport (λ H → H * A) α

  -- paths between functors are in fact natural isomorphisms
  naturality : {F G : Functor} (α : F ≡ G) → (A B : Set) (f : A → B) →
               (G ` f) ◯ (α · A) ≡ (α · B) ◯ (F ` f)
  naturality refl A B f = refl

  -- coyoneda embedding ℂ → Sets^ℂ, a contravariant functor in ℂ although we don't show it
  coyoneda : (X : Set) → Functor
  coyoneda X = functor (λ Y → X → Y) (λ f g → f ◯ g)

  -- the arrows that come out of inverse natural isos are inverses
  right-inverse : {X : Set} {F G : Functor} (α : F ≡ G) (x : G * X) →
        (α · X) ((! α · X) x) ≡ x
  right-inverse refl x = refl

  left-inverse : {X : Set} {F G : Functor} (α : F ≡ G) (x : F * X) →
        (! α · X) ((α · X) x) ≡ x
  left-inverse refl x = refl

  -- the coyoneda embedding is injective
  coyoneda-is-injective : (X Y : Set) (α : coyoneda Y ≡ coyoneda X) → X ≡ Y
  coyoneda-is-injective X Y α =
    eq-to-path (let f = (α · Y) (id Y) ; g = (! α · X) (id X) in
               f , iso-is-eq f g
               (λ y → tap (tap (naturality (! α) X Y ((α · Y) (id Y))) (id X)
                 ∘  (left-inverse α (id Y))) y)
               (λ x → tap (tap (naturality α Y X ((! α · X) (id X))) (id Y)
                 ∘ right-inverse α (id X)) x))

  -- F is a representable functor, represented by X
  Repr : (F : Functor) (X : Set) → Set₁
  Repr F X = F ≡ coyoneda X

  -- Any two representations of the same functor are equivalent
  thm : (X Y : Set) (F : Functor) → Repr F X → Repr F Y → X ≡ Y
  thm X Y F rX rY = coyoneda-is-injective X Y (! rY ∘ rX)
