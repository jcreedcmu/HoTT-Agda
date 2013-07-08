{-# OPTIONS --without-K #-}

open import Base
open import Funext
open import Spaces.SInfinity

module Spaces.SInfinityIsContr where

  -- Here I have my hands on concrete paths that I can induct over:
  lemma1 : (p q : north ≡ north) →
         transport (λ x2 → north ≡ x2) q (! q)
         ≡ transport (λ x2 → north ≡ x2) p (! p)
  lemma1 refl refl = refl

  -- in order to prove this:
  lemma2 : (y : S∞)
         (p q : y ≡ north) →
         transport (λ x2 → north ≡ x2) q (! q)
         ≡ transport (λ x2 → north ≡ x2) p (! p)
  lemma2 y p q = transport
                 (λ y -> (p q : y ≡ north) →
                   transport (λ x2 → north ≡ x2) q (! q)
                 ≡ transport (λ x2 → north ≡ x2) p (! p)) (! p) lemma1 p q

  -- Here's a slightly involved transport context, for converting uses
  -- of the constant-north function to uses of equator.
  -- The fact that we know λ_.north = equator is immediate
  -- from extensionality and north-merid.
  ctx3 : (S∞ → S∞) → Set
  ctx3 = λ e →
         (y : S∞)
         (p q : y ≡ e y) →
         transport (λ x2 → e x2 ≡ x2) q (! q)
         ≡ transport (λ x2 → e x2 ≡ x2) p (! p)

  lemma3 : (y : S∞)
         (p q : y ≡ equator y) →
         transport (λ x2 → equator x2 ≡ x2) q (! q)
         ≡ transport (λ x2 → equator x2 ≡ x2) p (! p)
  lemma3 = transport ctx3 (funext north-merid) lemma2

  -- The gap from lemma4 to lemma3 is noticing that merid only gets used at one argument,
  -- namely y.

  lemma4 : (y : S∞) (merid : (x : S∞) → y ≡ equator x) ->
         (p : y ≡ equator y) →
         transport (λ x2 → equator x2 ≡ x2) (merid y) (! (merid y))
         ≡ transport (λ x2 → equator x2 ≡ x2) p (! p)
  lemma4 y merid p = lemma3 y p (merid y)


  -- The gap from lemma5 to lemma4 is realizing that we can identify x1 and pole via (merid x1 ∘ (! p))

  lemma5 : (pole : S∞) (merid : (x : S∞) → pole ≡ equator x) ->
         (x1 : S∞) (p : x1 ≡ equator x1) →
         transport (λ x2 → equator x2 ≡ x2) (merid x1) (! (merid pole))
         ≡ transport (λ x2 → equator x2 ≡ x2) p (! p)
  lemma5 pole merid x1 p = transport
                              (λ x1 -> (p : x1 ≡ equator x1) → transport (λ x2 → equator x2 ≡ x2) (merid x1) (! (merid pole))
                                                                    ≡ transport (λ x2 → equator x2 ≡ x2) p (! p))
                             (merid x1 ∘ (! p)) (lemma4 pole merid) p

  -- The gap from lemma6 to lemma5 is just flipping around the path p and cancelling two !'s
  -- What lemma6 does is uniformly handle the two cases of path-reasoning required in the induction, one around the north pole, and the other around the south.

  lemma6 : (pole : S∞) (merid : (x : S∞) → pole ≡ equator x) ->
         (x1 : S∞) (p : equator x1 ≡ x1) →
         transport (λ x2 → equator x2 ≡ x2) (merid x1) (! (merid pole))
         ≡ transport (λ x2 → equator x2 ≡ x2) (! p) p
  lemma6 pole merid x p = transport (λ ζ -> transport (λ x2 → equator x2 ≡ x2) (merid x) (! (merid pole))
                                         ≡ transport (λ x2 → equator x2 ≡ x2) (! p) ζ)
         (opposite-opposite p) (lemma5 pole merid x (! p))

  -- Here's the place where we recurse over S∞, to find that the
  -- equatorial embedding and the identity function from S∞ to itself
  -- are identical

  equator≡id : (x : S∞) -> equator x ≡ x
  equator≡id = λ x → S∞-rec (λ x -> equator x ≡ x) (! (north-merid north)) (! (south-merid south))
                         (λ x1 p → transport (λ x -> equator x ≡ x) (! p) p) (lemma6 north north-merid) (lemma6 south south-merid) x

  -- Desired final result: the infinite dimensional sphere is
  -- contractible We get this because by the above recursion, every
  -- point is (uniformly) connected to its equatorial embedding, and
  -- by definition every point in the equator is (uniformly) connected
  -- to the north pole, so every point is (uniformly) connected to the
  -- north pole.

  S∞-is-contr : is-contr S∞
  S∞-is-contr = north , (λ y → transport (λ y -> y ≡ north) (equator≡id y) (! (north-merid y)))
