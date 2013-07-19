{-# OPTIONS --without-K #-}

open import Base
open import Jcreed.Susp
open import Jcreed.Util
import Funext

module Jcreed.Pullback where

  record pb {A B C : Set} (f : A → C) (g : B → C) : Set where
    constructor pbc
    field
      xa : A
      xb : B
      xm : f xa ≡ g xb
  open pb

  thm : {A B C D : Set} (f : A → C) (g : B → C) →
        (D → pb f g) ≡ Σ (D → A) (λ ff → Σ (D → B) (λ gg → f ◯ ff ≡ g ◯ gg))
  thm f g = iso-to-path (λ h → (λ x → xa (h x)) , ((λ x → xb (h x)) , funext (λ x → xm (h x))))
             (λ bundle d → pbc (π₁ bundle d) (π₁ (π₂ bundle) d) (tap (π₂ (π₂ bundle)) d))
             {!!} {!!}
