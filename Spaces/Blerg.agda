{-# OPTIONS --without-K #-}

open import Base

module Spaces.Blerg where

data Unit : Set where
  * : Unit

data I : Set where
  a b : I

postulate  -- HIT
  go : a ≡ b

I-rec : {C : Set} (a* b* : C) (go* : a* ≡ b*) -> I -> C
I-rec a* b* go* a = a*
I-rec a* b* go* b = b*

I-ind : (C : I → Set) (a* : C a) (b* : C b) (go* : (transport C go a*) ≡ b*) -> (x : I) -> C x
I-ind C a* b* go* a = a*
I-ind C a* b* go* b = b*

postulate
 I-rec-go : {C : Set} (a* b* : C) (go* : a* ≡ b*) -> ap (I-rec a* b* go*) go ≡ go*

to : Unit → I
to * = a

fro : I → Unit
fro x = *


_then_ : {A : Set} {a u v : A} (p : u ≡ v) (q : a ≡ u) → a ≡ v
refl then q = q

surprise : {A : Set} {a u v : A} (p : u ≡ v) (q : a ≡ u) →
              (transport (λ x → a ≡ x)) p q ≡ (p then q)
surprise refl q = refl

rightunit : {A : Set} {u v : A} (p : u ≡ v) -> p then refl ≡ p
rightunit refl = refl

round1 : (x : I) → a ≡ x
round1 = λ y → I-ind (λ x → a ≡ x) refl go (surprise go refl ∘ rightunit go) y

{-
Susp : Set
Susp = #Susp

north : Susp
north = #north

south : Susp
south = #south

postulate  -- HIT
  merid : (x : A) → north ≡ south

Susp-rec : ∀ {l} {C : Set l}
         (north* : C)
         (south* : C)
         (merid* : (x : A) -> (north* ≡ south*))
         -> (s : Susp) -> C
Susp-rec north* south* nm* #north = north*
Susp-rec north* south* nm* #south = south*

Susp-ind : ∀ {l} (C : Susp → Set l)
         (north* : C north)
         (south* : C south)
         (merid* : (x : A) -> (transport C (merid x) north*) ≡ south*)
         -> (s : Susp) -> C s
Susp-ind C north* south* nm* #north = north*
Susp-ind C north* south* nm* #south = south*

postulate  -- HIT
  Susp-β-merid : (C : Susp → Set) (n : C north) (s : C south)
                 (m : (a : A) -> (transport C (merid a) n) ≡ s)
               → (a : A) → apd (Susp-ind C n s m) (merid a) ≡ m a

postulate  -- HIT
  Susp-ρ-merid : (C : Set) (n : C) (s : C)
                 (m : (a : A) -> n ≡ s)
               → (a : A) → ap (Susp-rec n s m) (merid a) ≡ m a
-}
