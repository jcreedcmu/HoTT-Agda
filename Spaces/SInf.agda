{-# OPTIONS --without-K #-}

open import Base
import Spaces.Suspension as S

module Spaces.SInf where

data S∞ : Set where
   # : S.suspension S∞ → S∞

open S S∞

-- I can't see these subscripts on my mac
fst = π₁
snd = π₂

-- some abbrevs
#n = # north
#s = # south

cells : ℕ → Set
cells 0 = S∞
cells (S n) = Σ (cells n × cells n) (λ p → fst p ≡ snd p)

pred : (n : ℕ) → cells n → Set
pred 0 s = s ≡ #n
pred (S n) p = {!!}

srec : (P : suspension → Set)
  (north* : P north)
  (south* : P south)
  (paths* : (x : S∞) → transport P (paths x) north* ≡ south*)
  → ((x : suspension) → P x)
srec P north* south* paths* = suspension-rec P north* south* paths*

-- outrec : (Q : S∞ → Set)  ((x : suspension) →  Q (# x)) → (y : S∞) → Q y
-- outrec Q ## (# y) = ## y

smap : (X Y : Set) → (X → Y) → (S.suspension X → S.suspension Y)
smap X Y f sx = S.suspension-rec-nondep X (S.suspension Y) (S.north Y) (S.south Y) (λ x → S.paths Y (f x)) sx

S∞-ind : (C : S∞ → Set)
           (north* : C (# north))
           (south* : C (# south))
           (merid* : (x : S∞) → C x → (transport C (ap # (paths x)) north*) ≡ south*)
           -> (s : S∞) -> C s
S∞-ind C north* south* merid* s = {!s!}

mutual
  loop : (x : S∞) → refl ∘ (paths x) ≡ paths (# (north))
  loop = λ x → ap paths (reach-north x)

  thing : (x : S∞) → transport (λ y → north ≡ y) (paths x) refl ≡ paths #n
  thing x = trans-cst≡id (paths x) refl ∘ loop x

  reach-north-susp : (y : suspension) → north ≡ y
  reach-north-susp y = suspension-rec (λ x → north ≡ x) refl (paths #n) thing y

  reach-north : (y : S∞) → y ≡ #n
  reach-north (# y) = ! (ap # (reach-north-susp y))

S∞-is-contr : is-contr S∞
S∞-is-contr = #n , reach-north

{-
lemma0 : (C : S∞ → Set)
           (north* : C #n) →
  ((x : S∞) → C x → (transport C (ap # (paths x)) north*) ≡ transport (λ p → C (# p)) (paths x) north*)
lemma0 = {!!}

blend : (C : S∞ → Set)
           (north* : C #n)
           (south* : C #s) →
  ((x : S∞) → C x → (transport C (ap # (paths x)) north*) ≡ south*) →
  ((x : S∞) → transport (λ p → C (# p)) (paths x) north* ≡ south*)
blend = {!!}

S∞-ind : (C : S∞ → Set)
           (north* : C #n)
           (south* : C #s)
           (paths* : (x : S∞) → C x → (transport C (ap # (paths x)) north*) ≡ south*)
           -> (s : S∞) -> C s
S∞-ind C north* south* paths* (# s) = suspension-rec (λ p → C (# p)) north* south* (blend C north* south* paths*) s
-}
