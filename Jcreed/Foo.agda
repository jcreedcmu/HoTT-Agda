{-# OPTIONS --without-K  #-}
open import Base
open import Jcreed.Util
open import Jcreed.Yoneda using (coyoneda)

module Jcreed.Foo where

module Hom {A : Set} where
  postulate
    _≤_ : A → A → Set
    ≤defn : {x y : A} → x ≤ y ≡ ({z : A} → y ≤ z → x ≤ z)

  ≤refl : {x : A} → x ≤ x
  ≤refl = (! ≤defn) • id _

  ≤trans : {x y z : A} → x ≤ y → y ≤ z → x ≤ z
  ≤trans = λ p q → (≤defn • p) q

-- accept : {x y : Set₁} → ({z : Set} → (y → z) → (x → z)) ≡ (x → y)
-- accept = {!iso-to-path ? ? ? ?!}

module What (x y : Set) where
  into : ((z : Set) → (y → z) → (x → z)) → x → y
  into f = f y (id y)

  outo : (x → y) → ((z : Set) → (y → z) → (x → z))
  outo g = λ _ h → h ◯ g

  io : (g : x → y) → into (outo g) ≡ g
  io = {!λ g → iso-to-path ? ? ? ?!}

  oi : (f : ((z : Set) → (y → z) → (x → z))) → outo (into f) ≡ f
  oi = {!!}

{-
  I-rep : Functor
  I-rep = functor F map where
     F : Set → Set
     F X = Σ X (λ a → Σ X (λ b → a ≡ b))
     map : {A B : Set} → (A → B) → F A → F B
     map f (x , (y , z)) = (f x , (f y , ap f z))

--  F X = Σ X (λ a → Σ X (λ b → a ≡ b))

  -- apply a natural isomorphism at an object
  _·_ : {F G : Functor} (α : F ≡ G) → (A : Set) → F * A → G * A
  refl · A = id _

  -- paths between functors are in fact natural isomorphisms
  naturality : {F G : Functor} (α : F ≡ G) → (A B : Set) (f : A → B) →
               (G ` f) ◯ (α · A) ≡ (α · B) ◯ (F ` f)
  naturality refl A B f = refl

  postulate
    I : Set
    I-d : coyoneda I ≡ I-rep

  I-def : (X : Set) → (I → X) ≡ Σ X (λ a → Σ X (λ b → a ≡ b))
  I-def X = tap (ap _*_ I-d) X

  bundle = (I-d · I) (id I)
  a : I
  a = π₁ (bundle)

  b : I
  b = π₁ (π₂ bundle)

  p : a ≡ b
  p = π₂ (π₂ bundle)

  I-rec : (C : Set) (a* b* : C) (p* : a* ≡ b*) (x : I) → C
  I-rec C a* b* p* = ((! I-d) · C) ((a* , (b* , p*)))

  I-rec-β-a : (C : Set) (a* b* : C) (p* : a* ≡ b*) →
                 I-rec C a* b* p* a ≡ a*
  I-rec-β-a = {!naturality (! I-d)!}

-- (A B : Set) (f : A → B) →
-- (λ x →
--    f (π₁ ((I-d · A) x)) ,
--    (f (π₁ (π₂ ((I-d · A) x))) , ap f (π₂ (π₂ ((I-d · A) x)))))
-- ≡ (λ x → (I-d · B) (λ x₁ → f (x x₁)))


-- (C : Set) (a* b* : C) (p* : a* ≡ b*) →
-- (! I-d · C) (a* , (b* , p*)) (π₁ ((I-d · I) (λ x → x))) ≡ a*

-- (C : Set) (a* b* : C) (p* : a* ≡ b*) →
-- (! (tap (ap _*_ I-d) C) • (a* , (b* , p*)))
-- (π₁ (tap (ap _*_ I-d) I • (λ x → x)))
-- ≡ a*
-}
