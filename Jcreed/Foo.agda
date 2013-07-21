{-# OPTIONS --without-K  #-}
open import Base
open import Jcreed.Util hiding (_*_ ; _`_)

open import Jcreed.Yoneda using (coyoneda)

module Jcreed.Foo where

postulate
  _≤_ : ∀ {i} {A : Set i} → A → A → Set i
  ≤defn : {A : Set} {x y : A} → x ≤ y ≡ ((z : A) → y ≤ z → x ≤ z)

_⊂_ : Set → Set → Set
A ⊂ B = Σ (A → B) (λ f → (x y : A) → x ≤ y → f x ≤ f y)

_*_ : {A B : Set} → (A ⊂ B) → A → B
(f , ℓ) * x = f x

_`_ : {A B : Set} (f : A ⊂ B) {x y : A} → x ≤ y → (f * x) ≤ (f * y)
(f , ℓ) ` p = ℓ _ _ p

postulate
  univ : (A B : Set) → (A ≤ B) ≃ (A ⊂ B)

module thm-for-→ where
  into : {A B : Set} → (A ⊂ B) → ((C : Set) → (B ⊂ C) → (A ⊂ C))
  into f C g = (λ x → g * (f * x)) , (λ _ _ p → g ` (f ` p))

  I : (A : Set) → A ⊂ A
  I A = (id _) , (λ _ _ p → p)

  outo : {A B : Set} → ((C : Set) → (B ⊂ C) → (A ⊂ C)) → (A ⊂ B)
  outo {A} {B} h = h B (I B)

  result : {A B : Set} → (A ⊂ B) ≃ ((C : Set) → (B ⊂ C) → (A ⊂ C))
  result = into , iso-is-eq into outo {!!} (λ x → refl)

module thm-for-≡ where
  into : {A : Set} {a b : A} → (a ≡ b) → ((c : A) → b ≡ c → a ≡ c)
  into refl = λ x → id _

  outo : {A : Set} {a b : A} → ((c : A) → b ≡ c → a ≡ c) → (a ≡ b)
  outo f = f _ refl

  into-outo : {A : Set} {a b : A} → (g : a ≡ b) → outo (into g) ≡ g
  into-outo refl = refl

  outo-into : {A : Set} {a b : A} → (f : ((c : A) → (b ≡ c) → (a ≡ c))) → into (outo f) ≡ f
  outo-into f = funext (λ x → funext (λ y → lemma1 (f _ refl) y ∘ lemma2 refl y f)) where
    lemma1 : {A : Set} {a b c : A} (g : a ≡ b) (h : b ≡ c) → into g _ h ≡ g ∘ h
    lemma1 refl h = refl

    lemma2 : {A : Set} {a b c d : A} (p : b ≡ c) (q : c ≡ d) (f : (c : A) → b ≡ c → a ≡ c)
              → (f _ p) ∘ q ≡ f _ (p ∘ q)
    lemma2 refl refl f = refl-right-unit _

  result : {A : Set} {a b : A} → (a ≡ b) ≡ ((c : A) → b ≡ c → a ≡ c)
  result = iso-to-path into outo outo-into into-outo

  -- into-outo : {A : Set} {a b : A} → (g : a ≡ b) → outo (into g) ≡ g
  -- into-outo refl = refl

  -- outo-into : {A : Set} {a b : A} → (f : ((c : A) → (b ≡ c) → (a ≡ c))) → into (outo f) ≡ f
  -- outo-into f = funext (λ x → funext (λ y → lemma1 (f _ refl) y ∘ lemma2 refl y f)) where
  --   lemma1 : {A : Set} {a b c : A} (g : a ≡ b) (h : b ≡ c) → into g _ h ≡ g ∘ h
  --   lemma1 refl h = refl

  --   lemma2 : {A : Set} {a b c d : A} (p : b ≡ c) (q : c ≡ d) (f : (c : A) → b ≡ c → a ≡ c)
  --             → (f _ p) ∘ q ≡ f _ (p ∘ q)
  --   lemma2 refl refl f = refl-right-unit _

  -- result : {A : Set} {a b : A} → (a ≡ b) ≡ ((c : A) → b ≡ c → a ≡ c)
  -- result = iso-to-path into outo outo-into into-outo


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

-- module Hom {A : Set} where

--   ≤refl : {x : A} → x ≤ x
--   ≤refl = (! ≤defn) • (λ _ → id _)

--   ≤trans : {x y z : A} → x ≤ y → y ≤ z → x ≤ z
--   ≤trans = λ p q → (≤defn • p) _ q

--   alt-into : {x y : A} → x ≤ y → ((w : A) → w ≤ x → w ≤ y)
--   alt-into p _ q = ≤trans q p

--   alt-outo : {x y : A} → ((w : A) → w ≤ x → w ≤ y) → x ≤ y
--   alt-outo p = p _ ≤refl

--   lemma : {x y : A} (f : (w : A) → w ≤ x → w ≤ y) (w : A) (q : w ≤ x) →
--    (≤defn • q) _ (f _ (! ≤defn • (λ _ x → x))) ≡ f w q
--   lemma = {!!}

--   alt-into-outo : {x y : A} (f : (w : A) → w ≤ x → w ≤ y) → (alt-into (alt-outo f)) ≡ f
--   alt-into-outo f = {!!}

--   alt-outo-into : {x y : A} (f : x ≤ y) → (alt-outo (alt-into f)) ≡ f
--   alt-outo-into f = {!!}
