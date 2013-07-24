{-# OPTIONS --without-K  #-}
open import Base
open import Jcreed.Util hiding (_*_ ; _`_)

module Jcreed.Grothendieck where

grot : {B : Set} → (B → Set) → Σ Set (λ A → A → B)
grot {B} F = Σ B F , π₁

grot⁻¹ : {B : Set} → Σ Set (λ A → A → B) → B → Set
grot⁻¹ (A , π) b = Σ A (λ a → π a ≡ b)

lemma0' : {B : Set} (F : B → Set) (b : B)
         (y : Σ (Σ B F) (λ a → π₁ a ≡ b)) →
         (b , transport F (π₂ y) (π₂ (π₁ y))) , refl ≡ y
lemma0' F b ((.b , yf) , refl) = refl

lemma0 : {B : Set} (F : B → Set) (b : B) → F b ≡ Σ (Σ B F) (λ a → π₁ a ≡ b)
lemma0 F b = iso-to-path (λ x → (b , x) , refl)
                         (λ y → transport F (π₂ y) (π₂ (π₁ y)))
                         (lemma0' F b) (λ x → refl)

gig : {B : Set} (F : B → Set) → F ≡ grot⁻¹ (grot F)
gig F = funext (lemma0 F)

lemma1' : {A B : Set} (p : A → B) → (y : Σ B (λ v → Σ A (λ a → p a ≡ v))) →
         p (π₁ (π₂ y)) , (π₁ (π₂ y) , refl) ≡ y
lemma1' p (.(p y) , (y , refl)) = refl

lemma1 : {A B : Set} (p : A → B) → A ≡ Σ B (λ b → Σ A (λ a → p a ≡ b))
lemma1 p = iso-to-path (λ a → p a , (a , refl))
                       (λ x → π₁ (π₂ x)) (lemma1' p) (λ x → refl)

ggi : {B : Set} (Q : Σ Set (λ A → A → B)) → Q ≡ grot (grot⁻¹ Q)
ggi {B} (A , p) =  Σ-eq (lemma1 p)
  (trans-iso-to-path p
  (λ a → p a , (a , refl))
  (λ x → π₁ (π₂ x)) (lemma1' p) (λ x → refl) ∘ funext (λ x → π₂ (π₂ x)))

-- Correctness of the Grothendieck construction
grotc : {B : Set} → (B → Set) ≡ Σ Set (λ A → A → B)
grotc = iso-to-path grot grot⁻¹ (! ◯ ggi) (! ◯ gig)
