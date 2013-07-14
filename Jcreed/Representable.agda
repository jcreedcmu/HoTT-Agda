{-# OPTIONS --without-K #-}

open import Base

module Jcreed.Representable where
  -- Going to try to prove a theorem that whenever you know all the
  -- homs of a type X into various other types, you know exactly what
  -- X is.

  record Functor : Set₁ where
    constructor functor
    field
      o : Set → Set
      m : {A B : Set} (f : A → B) → o A → o B

  -- "the functor F is represented by the object X"
  record Repr (F : Functor) (X : Set) : Set₂ where
    constructor repr
    field
      o : (λ C → (X → C)) ≡ (Functor.o F)
      m : {A B : Set} (f : A → B) → transport (λ z → z A → z B) o (λ g → f ◯ g) ≡ (Functor.m F) f

  what : {X Y : Set} {f g : X → Y} → f ≡ g → (x : X) → f x ≡ g x
  what refl = λ x → refl

  lemma0 : (X Y : Set)
           (Q : (C : Set) → (X → C) ≃ (Y → C))
           (eq1 : (C D : Set) (f : X → C) (g : C → D) → g ◯ (Q C ☆ f) ≡ Q D ☆ (g ◯ f))
           (eq2 : (C D : Set) (f : Y → C) (g : C → D) → g ◯ (inverse (Q C) f) ≡ inverse (Q D) (g ◯ f))
           → X ≃ Y
  lemma0 X Y Q eq1 eq2 = let f = inverse (Q Y) (id Y)
                             g = (Q X) ☆ (id X)
         in f , iso-is-eq f g (what (eq1 X Y (id X) f ∘ inverse-right-inverse (Q Y) (id Y)))
                              (what (eq2 Y X (id Y) g ∘ inverse-left-inverse (Q X) (id X)))

  thm : (X Y : Set) (F : Functor) → Repr F X → Repr F Y → X ≡ Y
  thm X Y F rX rY = {!!}

{-
  lemma3 : (X Y Z W : Set) (Q : ((Z : Set) → (Y → Z) ≃ (X → Z)))
          (f : Z → W) (g : Y → Z) → f ◯ (Q Z ☆ g) ≡ (Q W) ☆ (f ◯ g)
  lemma3 = {!!}

  lemma2 : (X Y : Set) (Q : ((Z : Set) → (Y → Z) ≃ (X → Z)))
          (f : Y → X) → f ◯ (Q Y ☆ id Y) ≡ (Q X) ☆ f
  lemma2 X Y Q f = lemma3 X Y Y X Q f (id Y)


  lemma0 : (X Y : Set) (Q : ((Z : Set) → (Y → Z) ≃ (X → Z)))
           → (y : Y) → (Q Y ☆ id Y) (((Q X ⁻¹) ☆ id X) y) ≡ y
  lemma0 X Y Q y = {!π₂ (Q Y)!}
  lemma1 : (X Y : Set) (Q : ((Z : Set) → (Y → Z) ≃ (X → Z)))
           → (x : X) → ((Q X ⁻¹) ☆ id X) ((Q Y ☆ id Y) x) ≡ x
  lemma1 = {!!}

  lemma : (X Y : Set) → ((Z : Set) → (Y → Z) ≃ (X → Z)) → X ≃ Y
  lemma X Y Q = let f : X → Y ; f = Q Y ☆ (id Y) in
                  f , iso-is-eq f ((Q X)⁻¹ ☆ (id X)) (lemma0 X Y Q) (lemma1 X Y Q)

-}
