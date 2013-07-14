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

  _•_ : {X Y : Set} → X ≡ Y → X → Y
  refl • x = x

  tap : ∀ {i j} {X : Set i} {Y : Set j} {f g : X → Y} → f ≡ g → (x : X) → f x ≡ g x
  tap refl = λ x → refl

  _*_ : (F : Functor) (A : Set) → Set
  F * A = Functor.o F A

  _`_ : (F : Functor) {A B : Set} (f : A → B) → F * A → F * B
  F ` f = Functor.m F f

  _·_ : {F G : Functor} (α : F ≡ G) → (A : Set) → F * A → G * A
  α · A = λ x → (ap (λ H → H * A) α) • x

  naturality : {F G : Functor} (α : F ≡ G) → (A B : Set) (f : A → B) →
               (G ` f) ◯ (α · A) ≡ (α · B) ◯ (F ` f)
  naturality refl A B f = refl

  coyoneda : (X : Set) → Functor
  coyoneda X = functor (λ Y → X → Y) (λ f g → f ◯ g)

  win : {X Y : Set} (α : coyoneda X ≡ coyoneda Y) → (A B : Set) (f : A → B) →
               (λ (g : Y → A) → f ◯ g) ◯ (λ x → (ap (λ H → H * A) α) • x) ≡ (λ x → (ap (λ H → H * B) α) • x) ◯ (λ (h : X → A) → f ◯ h)
  win α A B f = naturality α A B f

  xm : (F : Functor) (A B : Set) (f : A → B) → Functor.o F A → Functor.o F B
  xm F A B f x = Functor.m F {A} {B} f x

  sb : (A : Set) (B : A → Set) (p q : Σ A B) → p ≡ q → π₁ p ≡ π₁ q
  sb A B p q α = ap π₁ α

  sb2 : (A : Set) (B : A → Set) (p q : Σ A B) → (α : p ≡ q) → transport B (sb A B p q α) (π₂ p) ≡ π₂ q
  sb2 A B p q α = (trans-ap B π₁ α (π₂ p)) ∘ apd π₂ α


  zzz : (X Y : Set) (Q : coyoneda Y ≡ coyoneda X) →  transport
        (λ z → (A B : Set) → (A → B) → Functor.o z A → Functor.o z B) Q
        (λ A B f g x → f (g x)) ≡ (λ A B f g x → f (g x))
  zzz X Y Q = apd xm Q

  Repr : (F : Functor) (X : Set) → Set₁
  Repr F X = F ≡ coyoneda X



  -- XXX : could probably prove this from trans-→ and trans-cst
  trans-cst→ : {Z : Set} {z1 z2 : Z} (Q : z1 ≡ z2) (A : Set) (B : Z → Set) (F : A → B z1) (G : A → B z2)   →
     (transport (λ z → A → (B z)) Q F ≡ G) → (a : A) → transport B Q (F a) ≡ G a
  trans-cst→ refl A B F G p = tap p

{-
transport : ∀ {i j} {A : Set i} (P : A → Set j) {x y : A}
  → (x ≡ y → P x → P y)
transport P refl t = t
-}

  trans-head : ∀ {i} {C : Set i} {x y : C → Set} (Q : x ≡ y) (c : C) (T : x c) → transport (λ f → f c) Q T ≡ tap Q c • T
  trans-head refl c T = refl

  lift-transport-ctx-binders :
          (X Y : Set)
          (Q : (λ (C : Set) → Y → C) ≡ (λ C → X → C)) →
          (transport (λ z → (A B : Set) → (A → B) → z A → z B) Q (λ A B (f : A → B) (g : Y → A) y → f (g y))
          ≡ (λ A B (f : A → B) (g : X → A) x → f (g x)))
          → (A B : Set) (f : A → B) →
          transport (λ z → z A → z B) Q (λ (g : Y → A) y → f (g y)) ≡ (λ (g : X → A) x → f (g x))
  lift-transport-ctx-binders X Y Q M A B f = {! !}

  mine : (X Y : Set) (A B : Set)
       (Q : (λ (C : Set) → Y → C) ≡ (λ C → X → C))
       (a : X → A) (f : A → B)
    → transport (λ x → x A → x B) Q (λ g y → f (g y)) a
      ≡ transport (λ z → z B) Q (λ y → f ((transport (λ z → z A) (! Q) a) y))
  mine X Y A B Q a f = trans-→ (λ z → z A) (λ z → z B) Q (λ g y → f (g y)) a

  mine2 : (X Y : Set) (A B : Set)
       (Q : (λ (C : Set) → Y → C) ≡ (λ C → X → C))
       (a : X → A) (f : A → B)
    → transport (λ x → x A → x B) Q (λ g y → f (g y)) a
      ≡ tap Q B • (λ y → f ((transport (λ z → z A) (! Q) a) y))
  mine2 X Y A B Q a f = mine X Y A B Q a f ∘ trans-head Q B (λ y → f ((transport (λ z → z A) (! Q) a) y))


  lemma2 : (X Y : Set)
           (Q : (λ (C : Set) → Y → C) ≡ (λ C → X → C))
           (M : (A B : Set) (f : A → B) →
                  transport (λ z → z A → z B) Q (λ (g : Y → A) y → f (g y)) ≡ (λ (g : X → A) x → f (g x)))
           → X ≡ Y
  lemma2 X Y Q M = eq-to-path (let f = (tap Q Y) • (id Y) ; g = (! (tap Q X)) • (id X) in
                               f , iso-is-eq f g {!!} {!!}  )

  lemma0 : (X Y : Set)
           (Q : coyoneda Y ≡ coyoneda X)
           → X ≡ Y
  lemma0 X Y Q = lemma2 X Y (ap Functor.o Q) (lift-transport-ctx-binders X Y (ap Functor.o Q) ((trans-ap (λ z → (A B : Set) → (A → B) → z A → z B)
                                                         Functor.o Q (λ A B f x y → f (x y))) ∘ apd xm Q ))

  thm : (X Y : Set) (F : Functor) → Repr F X → Repr F Y → X ≡ Y
  thm X Y F rX rY = lemma0 X Y (! rY ∘ rX)

{-
  -- "the functor F is represented by the object X"
  record Repr (F : Functor) (X : Set) : Set₁ where
    constructor repr
    field
      o : (λ C → (X → C)) ≡ (Functor.o F)
      m : {A B : Set} (f : A → B) → transport (λ z → z A → z B) o (λ g → f ◯ g) ≡ (Functor.m F) f

                              (tap (eq2 Y X (id Y) g ∘ inverse-left-inverse (Q X) (id X)))

  thm : (X Y : Set) (F : Functor) → Repr F X → Repr F Y → X ≡ Y
  thm X Y F rX rY = eq-to-path (lemma0 X Y (λ C → path-to-eq (tap (Repr.o rX ∘ ! (Repr.o rY)) C)) {!!} {!!})
-}





{-
(C D : Set) (f : X → C) (g : C → D) →
g ◯ (path-to-eq (tap (Repr.o rX ∘ ! (Repr.o rY)) C) ☆ f)
≡ path-to-eq (tap (Repr.o rX ∘ ! (Repr.o rY)) D) ☆ (g ◯ f)
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
