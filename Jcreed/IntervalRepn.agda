{-# OPTIONS --without-K #-}

open import Base
open import Jcreed.Yoneda
open import Spaces.Interval

module Jcreed.IntervalRepn where

  -- Here's the functor that we claim the interval represents
  F = functor (λ A → Σ A (λ a → Σ A (λ b → a ≡ b)))
              (λ f pkg → (f (π₁ pkg)) , ((f (π₁ (π₂ pkg))) , (ap f (π₂ (π₂ pkg)))))

  _• : {X Y : Set} → X ≡ Y → (X → Y)
  refl • = λ x → x

  natl-iso : (F G : Functor) (α : (C : Set) → F * C ≡ G * C) →
             ((A B : Set) (f : A → B) → (G ` f) ◯ (α A •) ≡ (α B •) ◯ (F ` f))
             → F ≡ G
  natl-iso F G = {!!}

  interval-represents-F : coyoneda I ≡ F
  interval-represents-F = {!!}

{-

constructors:

inj : F X → X

generic induction principle:

ind : (C : X → Set) ((q : F (Σ X C)) → C (inj ((F π₁) q))) → (x : X) → C x

generic beta law:

β : (C : X → Set) (Q : (q : F (Σ X C)) → C (inj ((F π₁) q))) →
    (f : F X) → ind C Q (inj f) ≡ Q (F (λ x → (x , ind C Q x)) f)

if F is constant:

constructors:

inj : F → X

generic induction principle:

ind : (C : X → Set) ((q : F) → C (inj q)) → (x : X) → C x

generic beta law:

β : (C : X → Set) (Q : (q : F) → C (inj q)) →
    (f : F) → ind C Q (inj f) ≡ Q f

-}
