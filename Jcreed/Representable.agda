{-# OPTIONS --without-K #-}

open import Base

module Jcreed.Representable where
  -- Going to try to prove a theorem that whenever you know all the
  -- homs of a type X into various other types, you know exactly what
  -- X is.


  -- "the type operator F is represented by the object X"
  repr : (F : Set → Set) (X : Set) → Set₁
  repr F X = (C : Set) → F(C) ≡ X → C

  lemma3 : (X Y : Set) (Q : ((Z : Set) → (Y → Z) ≃ (X → Z)))
          (f : Y → X) → f ◯ (Q Y ☆ id Y) ≡ (Q X) ☆ f
  lemma3 = {!!}

  lemma2 : (X Y : Set) (Q : ((Z : Set) → (Y → Z) ≃ (X → Z)))
           (f : Y → X) → (Q X ⁻¹) ☆ (f ◯ (Q Y ☆ id Y)) ≡ f
  lemma2 = {!!}

  lemma0 : (X Y : Set) (Q : ((Z : Set) → (Y → Z) ≃ (X → Z)))
           → (y : Y) → (Q Y ☆ id Y) (((Q X ⁻¹) ☆ id X) y) ≡ y
  lemma0 X Y Q y = {!π₂ (Q Y)!}
  lemma1 : (X Y : Set) (Q : ((Z : Set) → (Y → Z) ≃ (X → Z)))
           → (x : X) → ((Q X ⁻¹) ☆ id X) ((Q Y ☆ id Y) x) ≡ x
  lemma1 = {!!}

  lemma : (X Y : Set) → ((Z : Set) → (Y → Z) ≃ (X → Z)) → X ≃ Y
  lemma X Y Q = let f : X → Y ; f = Q Y ☆ (id Y) in
                  f , iso-is-eq f ((Q X)⁻¹ ☆ (id X)) (lemma0 X Y Q) (lemma1 X Y Q)

  thm : (X Y : Set) (F : Set → Set) → repr F X → repr F Y → X ≡ Y
  thm X Y F rX rY = {!rX Y!}
