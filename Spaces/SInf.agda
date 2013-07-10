{-# OPTIONS --without-K #-}

open import Base
import Spaces.Suspension

module Spaces.SInf where

data S∞ : Set where
   # : Spaces.Suspension.suspension S∞ → S∞

open Spaces.Suspension S∞

{-
   Even though it is, the Agda termination check can't tell that the x in
   (λ x → trans-cst≡id (paths x) refl ∘ (ap paths (reach-north x)))
   is smaller than the y in reach-north (# y).
   This is because suspension-rec is hand-built recursor, rather than
   an agda-native inductive function definition.
-}

{-# NO_TERMINATION_CHECK #-}
reach-north : (y : S∞) → y ≡ # north
reach-north (# y) = ! (ap # (suspension-rec (λ x → north ≡ x) refl (paths (# north))
                      (λ x → trans-cst≡id (paths x) refl ∘ (ap paths (reach-north x))) y))

S∞-is-contr : is-contr S∞
S∞-is-contr = # north , reach-north
