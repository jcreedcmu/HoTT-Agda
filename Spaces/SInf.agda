{-# OPTIONS --without-K #-}

open import Base
import Spaces.Susp

module Spaces.SInf where

  foo : ℕ
  foo = 0

  module Attempt where
    data S∞ : ℕ → Set where
       # : {n : ℕ} → Spaces.Susp.Susp (S∞ n) → S∞ (S n)

    module S where
      open Spaces.Susp public


      -- loop : (x : S∞) → refl ∘ S.merid x ≡ S.merid (# (S.north))
      -- loop = λ x → ap S.merid (reach-north x)

      -- reach-north-susp : (y : S.Susp) → S.north ≡ y
      -- reach-north-susp y = S.Susp-ind (λ x → S.north ≡ x) refl (S.merid (# S.north)) (λ x → trans-cst≡id (S.merid x) refl ∘ loop x) y

      -- reach-north : (y : S∞) → y ≡ # S.north
      -- reach-north (# y) = ! (ap # (reach-north-susp y))

    S∞-is-contr : (n : ℕ) → is-contr (S∞ n)
    S∞-is-contr = λ n → {!# ?!} , {!!}

  module Term where
    data S∞ : Set where
       # : Spaces.Susp.Susp S∞ → S∞

    module S where
      open Spaces.Susp S∞ public

    mutual
      loop : (x : S∞) → refl ∘ S.merid x ≡ S.merid (# (S.north))
      loop = λ x → ap S.merid (reach-north x)

      reach-north-susp : (y : S.Susp) → S.north ≡ y
      reach-north-susp y = S.Susp-ind (λ x → S.north ≡ x) refl (S.merid (# S.north)) (λ x → trans-cst≡id (S.merid x) refl ∘ loop x) y

      reach-north : (y : S∞) → y ≡ # S.north
      reach-north (# y) = ! (ap # (reach-north-susp y))

    S∞-is-contr : is-contr S∞
    S∞-is-contr = # S.north , reach-north
