{-# OPTIONS --without-K #-}

open import Base

module Spaces.MySpheres where

-- reflexivity of equivalence at a particular point
rat : {A : Set} (a : A) → a ≡ a
rat a = refl

data S0 : Set where
  base0 : S0
  loop0 : S0

S0-rec : (C : Set) (base* : C) (loop* : C) → S0 → C
S0-rec C base* loop* base0 = base*
S0-rec C base* loop* loop0 = loop*

S0-ind : (C : S0 → Set) (base* : C base0) (loop* : C loop0) → (x : S0) → C x
S0-ind C base* loop* base0 = base*
S0-ind C base* loop* loop0 = loop*

data S1 : Set where
  base1 : S1

postulate loop1 : base1 ≡ base1

S1-rec : (C : Set) (base* : C) (loop* : base* ≡ base*) → S1 → C
S1-rec C base* loop* base1 = base*

postulate
 S1-rec-β-loop1 : (C : Set) (base* : C) (loop* : base* ≡ base*) →
                  ap (S1-rec C base* loop*) loop1 ≡ loop*

S1-ind : (C : S1 → Set) (base* : C base1)
         (loop* : transport C loop1 base* ≡ base*) →
         (x : S1) → C x
S1-ind C base* loop* base1 = base*

postulate
 S1-ind-β-loop1 : (C : S1 → Set) (base* : C base1)
                 (loop* : transport C loop1 base* ≡ base*) →
                 apd (S1-ind C base* loop*) loop1 ≡ loop*

module B2 where

  data X : Set where
    a : X
    b : X

  postulate p1a : a ≡ b
  postulate p1b : a ≡ b

  postulate p2 : p1a ≡ p1b

  rec : (C : Set) (a* b* : C) (p1a* p1b* : a* ≡ b*) (p2* : p1a* ≡ p1b*) → X → C
  rec C a* b* p1a* p1b* p2* a = a*
  rec C a* b* p1a* p1b* p2* b = b*

  postulate
   rec-β-p1a : (C : Set) (a* b* : C) (p1a* p1b* : a* ≡ b*) (p2* : p1a* ≡ p1b*) →
                    ap (rec C a* b* p1a* p1b* p2*) p1a ≡ p1a*

  postulate
   rec-β-p1b : (C : Set) (a* b* : C) (p1a* p1b* : a* ≡ b*) (p2* : p1a* ≡ p1b*) →
                    ap (rec C a* b* p1a* p1b* p2*) p1b ≡ p1b*

  postulate
   rec-β-p2 : (C : Set) (a* b* : C) (p1a* p1b* : a* ≡ b*) (p2* : p1a* ≡ p1b*) →
                    ap (ap (rec C a* b* p1a* p1b* p2*)) p2 ≡ rec-β-p1a C a* b* p1a* p1b* p2* ∘ p2* ∘ !(rec-β-p1b C a* b* p1a* p1b* p2*)
{-
  ind : (C : X → Set) (a* : C a) (b* : C b)
           (p* : transport C p a* ≡ b*) →
           (x : X) → C x
  ind C a* b* p* a = a*
  ind C a* b* p* b = b*

  postulate
   ind-β-p1 : (C : X → Set) (a* : C a) (b* : C b)
                   (p* : transport C p a* ≡ b*) →
                   apd (ind C a* b* p*) p ≡ p*

-}
module B1 where

  data X : Set where
    a : X
    b : X

  postulate p : a ≡ b

  rec : (C : Set) (a* : C) (b* : C) (p* : a* ≡ b*) → X → C
  rec C a* b* p* a = a*
  rec C a* b* p* b = b*

  postulate
   rec-β-p1 : (C : Set) (a* b* : C) (p* : a* ≡ b*) →
                    ap (rec C a* b* p*) p ≡ p*

  ind : (C : X → Set) (a* : C a) (b* : C b)
           (p* : transport C p a* ≡ b*) →
           (x : X) → C x
  ind C a* b* p* a = a*
  ind C a* b* p* b = b*

  postulate
   ind-β-p1 : (C : X → Set) (a* : C a) (b* : C b)
                   (p* : transport C p a* ≡ b*) →
                   apd (ind C a* b* p*) p ≡ p*

data S2 : Set where
  base2 : S2

-- rat base2 : base2 ≡ base2
postulate loop2 : rat base2 ≡ rat base2

data S3 : Set where
  base3 : S3

-- rat base3 : base3 ≡ base3
-- rat (rat base3) : rat base3 ≡ rat base3
postulate loop3 : rat (rat base3) ≡ rat (rat base3)


data S4 : Set where
  base4 : S4

-- rat base4 : base4 ≡ base4
-- rat (rat base4) : rat base4 ≡ rat base4
-- rat (rat (rat base4)) : rat (rat base4) ≡ rat (rat base4)
postulate loop4 : rat (rat (rat base4)) ≡ rat (rat (rat base4))
