{-# OPTIONS --without-K #-}

open import Base
import Spaces.Suspension

module Spaces.SInf where

data S∞ : Set where
   # : Spaces.Suspension.suspension S∞ → S∞

open Spaces.Suspension S∞

reach-north : (y : S∞) → y ≡ # north
reach-north (# y) = ! (ap # (suspension-rec (λ x → north ≡ x) refl (paths (# north))
                      (λ x → trans-cst≡id (paths x) refl ∘ (ap paths (reach-north x))) y))

S∞-is-contr : is-contr S∞
S∞-is-contr = # north , reach-north
