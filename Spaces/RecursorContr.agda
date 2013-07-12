{-# OPTIONS --without-K #-}

open import Base
import Spaces.Suspension as S

module Spaces.RecursorContr where

susp : Set → Set

susp = S.suspension
susp-ind = S.suspension-rec
susp-rec = S.suspension-rec-nondep
β = S.suspension-β-paths-nondep

{-
susp = S.Susp
susp-ind = S.Susp-ind
susp-rec = S.Susp-rec
-}

-- I can't see these
fst = π₁
snd = π₂

-- constructors
inj-S∞ : Set → Set
inj-S∞ X = susp X → X

-- Functoriality of susp
smap : {X Y : Set} → (X → Y) → susp X → susp Y
smap {X} {Y} f sp = susp-rec X (susp Y) (S.north Y) (S.south Y) (λ x → S.paths Y (f x) ) sp

{- smap fst : susp (Σ X C) → susp X -}

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

  lemma2 : (C : X → Set)
           (xc : Σ X C) →
           S.paths X (fst xc) ≡ ap (smap fst) (S.paths (Σ X C) xc)
  lemma2 C xc = ! (β (Σ X C) (susp X) (S.north X) (S.south X) (λ x → S.paths X (fst x)) xc)

  lemma1 : (C : X → Set)
           (n* : C north)
           (xc : Σ X C) →
           transport C (ap inj (S.paths X (fst xc))) n* ≡ transport (λ qq → C (inj (smap fst qq))) (S.paths (Σ X C) xc) n*
  lemma1 C n* xc = trans-ap C inj (S.paths X (fst xc)) n* ∘
                   ap (λ w → transport (C ◯ inj) w n*) (lemma2 C xc) ∘
                   trans-ap (C ◯ inj) (smap fst) (S.paths (Σ X C) xc) n*

  lemma0 : (C : X → Set)
           (n* : C north)
           (s* : C south) →
           ((xc : X) → C xc → transport C (ap inj (S.paths X xc)) n* ≡ s*)
           → (xc : Σ X C) → transport (λ qq → C (inj (smap fst qq))) (S.paths (Σ X C) xc) n* ≡ s*
  lemma0 C n* s* p* xc = ! (lemma1 C n* xc) ∘ p* (fst xc) (snd xc)

  {- a more comfortable induction principle -}
  out2 : (C : X → Set)
         (north* : C north)
         (south* : C south)
         (paths* : (x : X) → C x → (transport C (paths x) north*) ≡ south*)
           -> (x : X) -> C x
  out2 C n* s* p* x = out C ((λ (q : susp (Σ X C)) → susp-ind (Σ X C) (λ qq → C (inj (smap fst qq)))
                               n* s* (lemma0 C n* s* p*) q)) x

  S∞-is-contr : is-contr X
  S∞-is-contr = north , λ y → ! (out2 (λ x → north ≡ x) refl (paths north)
                                      (λ x p → trans-cst≡id (paths x) refl ∘ ap paths (! p)) y)
