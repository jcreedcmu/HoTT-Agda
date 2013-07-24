{-# OPTIONS --without-K  #-}
open import Base
open import Jcreed.Util hiding (_*_ ; _`_)

open import Jcreed.Yoneda using (coyoneda)

module Jcreed.Foo where


postulate
  _≤_ : ∀ {i} {A : Set i} → A → A → Set i

yon : ∀ {i j} {A : Set i} → ({Z : Set j} (x y : Z) → Set i) → (a b : A) → Set (max (suc j) i)
yon {i} {j} {A} _⊂_ a b = ((Z : Set j) (f : A → Z) (z : Z) → (f b) ⊂ z → f a ⊂ z)

postulate
  ≤defn : {A : Set} {a b : A} → (a ≤ b) ≃ yon _≤_ a b
  univ : (A B : Set) → (A ≤ B) ≃ (A → B)

module thm-for-≡ where
  into : {A : Set} {a b : A} → (a ≡ b) → yon _≡_ a b
  into refl = λ _ _ _ → id _

  outo : {A : Set} {a b : A} → yon _≡_ a b → (a ≡ b)
  outo f = f _ (id _) _ refl

  into-outo : {A : Set} {a b : A} → (g : a ≡ b) → outo (into g) ≡ g
  into-outo refl = refl

  outo-into : {A : Set} {a b : A} → (f : yon _≡_ a b) → into (outo f) ≡ f
  outo-into f = funext (λ _ → funext (λ g → funext (λ _ → funext (λ q →
                          lemma1 (outo f) q ∘ lemma2 f (id _) g refl q)))) where
    lemma1 : {A Z : Set} {a b : A} {f : A → Z} {z : Z} (g : a ≡ b) (h : f b ≡ z) → into g _ f _ h ≡ (ap f g) ∘ h
    lemma1 refl h = refl

    lemma2 : {A K Z : Set} {a b : A} → (f : yon _≡_ a b)
           → (h : A → K) (g : K → Z) {k : K} {z : Z} (p : h b ≡ k) (q : g k ≡ z)
           → ap g (f K h k p) ∘ q ≡ f Z (g ◯ h) z (ap g p ∘ q)
-- ap g (f K h k p) ∘ q ≡ f Z (g ◯ h) z (ap g p ∘ q)
-- ap g (f .A (λ x → x) .b refl) ∘ m4 ≡ f m1 g m3 m4
    lemma2 f h g p q = {!!}

{-
  outo-into f = funext (λ x → funext (λ y → lemma1 (f _ refl) y ∘ lemma2 refl y f)) where
    lemma1 : {A : Set} {a b c : A} (g : a ≡ b) (h : b ≡ c) → into g _ h ≡ g ∘ h
    lemma1 refl h = refl

    lemma2 : {A : Set} {a b c d : A} (p : b ≡ c) (q : c ≡ d) (f : (c : A) → b ≡ c → a ≡ c)
              → (f _ p) ∘ q ≡ f _ (p ∘ q)
    lemma2 refl refl f = refl-right-unit _
-}

--   result : {A : Set} {a b : A} → (a ≡ b) ≡ ((c : A) → b ≡ c → a ≡ c)
--   result = iso-to-path into outo outo-into into-outo

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
