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

  coyoneda : (X : Set) → Functor
  coyoneda X = functor (λ Y → X → Y) (λ f g → f ◯ g)

  Repr : (F : Functor) (X : Set) → Set₁
  Repr F X = F ≡ coyoneda X

  what : ∀ {i j} {X : Set i} {Y : Set j} {f g : X → Y} → f ≡ g → (x : X) → f x ≡ g x
  what refl = λ x → refl

  lemma1 : (X Y : Set)
           (Q : (C : Set) → (X → C) ≃ (Y → C))
           (eq1 : (C D : Set) (f : X → C) (g : C → D) → g ◯ (Q C ☆ f) ≡ Q D ☆ (g ◯ f))
           (eq2 : (C D : Set) (f : Y → C) (g : C → D) → g ◯ (inverse (Q C) f) ≡ inverse (Q D) (g ◯ f))
           → X ≃ Y
  lemma1 X Y Q eq1 eq2 = let f = inverse (Q Y) (id Y)
                             g = (Q X) ☆ (id X)
         in f , iso-is-eq f g (what (eq1 X Y (id X) f ∘ inverse-right-inverse (Q Y) (id Y)))
                              (what (eq2 Y X (id Y) g ∘ inverse-left-inverse (Q X) (id X)))

  lemma2 : (X Y : Set)
           (Q : (λ (C : Set) → X → C) ≡ (λ C → Y → C))
           → X ≡ Y
  lemma2 X Y Q = {!!}

  lemma0 : (X Y : Set)
           (Q : coyoneda X ≡ coyoneda Y)
           → X ≡ Y
  lemma0 X Y Q = eq-to-path (lemma1 X Y (λ C → path-to-eq (what (ap Functor.o Q) C))
                 {!!}
                 {!!})

  thm : (X Y : Set) (F : Functor) → Repr F X → Repr F Y → X ≡ Y
  thm X Y F rX rY = lemma0 X Y (! rX ∘ rY)

{-
  -- "the functor F is represented by the object X"
  record Repr (F : Functor) (X : Set) : Set₁ where
    constructor repr
    field
      o : (λ C → (X → C)) ≡ (Functor.o F)
      m : {A B : Set} (f : A → B) → transport (λ z → z A → z B) o (λ g → f ◯ g) ≡ (Functor.m F) f

                              (what (eq2 Y X (id Y) g ∘ inverse-left-inverse (Q X) (id X)))

  thm : (X Y : Set) (F : Functor) → Repr F X → Repr F Y → X ≡ Y
  thm X Y F rX rY = eq-to-path (lemma0 X Y (λ C → path-to-eq (what (Repr.o rX ∘ ! (Repr.o rY)) C)) {!!} {!!})
-}





{-
(C D : Set) (f : X → C) (g : C → D) →
g ◯ (path-to-eq (what (Repr.o rX ∘ ! (Repr.o rY)) C) ☆ f)
≡ path-to-eq (what (Repr.o rX ∘ ! (Repr.o rY)) D) ☆ (g ◯ f)
-}

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
