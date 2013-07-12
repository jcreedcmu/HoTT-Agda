{-# OPTIONS --without-K #-}

open import Base
import Spaces.Susp as S

module Spaces.RecursorContr where

susp : Set → Set
susp = S.Susp

-- I can't see these
fst = π₁
snd = π₂

-- constructors
inj-S∞ : Set → Set
inj-S∞ X = susp X → X

-- Functoriality of susp
smap : {X Y : Set} → (X → Y) → susp X → susp Y
smap {X} {Y} f sp = S.Susp-rec X (susp Y) (S.north Y) (S.south Y) (λ x → S.paths Y (f x) ) sp

-- induction principle
out-S∞ : (X : Set) → inj-S∞ X → Set₁
out-S∞ X inj = (C : X → Set) → ((q : susp (Σ X C)) → C (inj ((smap fst) q))) → (x : X) → C x

module Proof (X : Set) (inj : inj-S∞ X) (out : out-S∞ X inj) where

  north : X
  north = inj (S.north X)

  south : X
  south = inj (S.south X)

  paths : X → north ≡ south
  paths = λ x → ap inj (S.paths X x)

  lemma1 : (C : X → Set)
           (n* : C north)
           (s* : C south) →
           (xc : Σ X C) →
           transport C (ap inj (S.paths X (fst xc))) n* ≡ transport (λ qq → C (inj (smap fst qq))) (S.paths (Σ X C) xc) n*
  lemma1 = {!!}

  lemma0 : (C : X → Set)
           (n* : C north)
           (s* : C south) →
           ((xc : X) → C xc → transport C (ap inj (S.paths X xc)) n* ≡ s*)
           → (xc : Σ X C) → transport (λ qq → C (inj (smap fst qq))) (S.paths (Σ X C) xc) n* ≡ s*
  lemma0 C n* s* p* xc = ! (lemma1 C n* s* xc) ∘ p* (fst xc) (snd xc)

  out2 : (C : X → Set)
         (north* : C north)
         (south* : C south)
         (paths* : (x : X) → C x → (transport C (paths x) north*) ≡ south*)
           -> (x : X) -> C x
  out2 C n* s* p* x = out C ((λ (q : susp (Σ X C)) → S.Susp-ind (Σ X C) (λ qq → C (inj (smap fst qq)))
                               n* s* (lemma0 C n* s* p*) q)) x
{-
need
?2 :

have
-}
  S∞-is-contr : is-contr X
  S∞-is-contr = north , λ y → ! (out2 (λ x → north ≡ x) refl (paths north)
                                      (λ x p → trans-cst≡id (paths x) refl ∘ ap paths (! p)) y)
