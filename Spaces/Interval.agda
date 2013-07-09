{-# OPTIONS --without-K #-}

open import Base

module Spaces.Interval where

private
  data #I : Set where
    #zer : #I
    #one : #I

I : Set
I = #I

zer : I
zer = #zer

one : I
one = #one

postulate  -- HIT
  seg : zer ≡ one

I-rec : ∀ {i} (P : I → Set i) (x1 : P zer) (x2 : P one)
  (p : transport P seg x1 ≡ x2)
  → ((t : I) → P t)
I-rec P x1 x2 p #zer = x1
I-rec P x1 x2 p #one = x2

postulate  -- HIT
  β : ∀ {i} (P : I → Set i) (x1 : P zer) (x2 : P one)
      (p : transport P seg x1 ≡ x2)
      → apd (I-rec P x1 x2 p) seg ≡ p

I-rec-nondep : ∀ {i} (C : Set i) (x1 x2 : C) (p : x1 ≡ x2) → (I → C)
I-rec-nondep C x1 x2 p #zer = x1
I-rec-nondep C x1 x2 p #one = x2

postulate  -- HIT
  β-nondep : ∀ {i} (C : Set i) (x1 x2 : C) (p : x1 ≡ x2)
             → ap (I-rec-nondep C x1 x2 p) seg ≡ p
