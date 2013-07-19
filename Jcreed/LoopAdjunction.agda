{-# OPTIONS --without-K #-}

open import Base hiding (Σ)
open import Jcreed.Susp
import Funext

module Jcreed.LoopAdjunction where

  {- The goal here is to show the suspension is left adjoint to loops -}

  record 2Pointed : Set₁ where
    constructor pointed
    field
      space : Set
      pn : space
      ps : space

  open 2Pointed public

  record _⇒_ (X Y : 2Pointed) : Set where
    constructor pmap
    field
      map : space X → space Y
      pn-map : map (pn X) ≡ pn Y
      ps-map : map (ps X) ≡ ps Y

  open _⇒_ public

  -- -- pointed maps compose
  -- _⊚_ : {P Q R : Pointed} → (Q ⇒ R) → (P ⇒ Q) → (P ⇒ R)
  -- _⊚_ {P} {Q} {R} F G = pmap (space-map F ◯ space-map G)
  --                            (ap (space-map F) (point-map G) ∘ point-map F)

  -- -- pointed maps have identities
  -- pid : (P : Pointed) → (P ⇒ P)
  -- pid P = pmap (id (space P)) refl

  -- pointed-eq : (P Q : Pointed) (p : space P ≡ space Q)
  --              (q : transport (id _) p (point P) ≡ point Q) → P ≡ Q
  -- pointed-eq P Q p q = ap2 pointed p q

  ap3 : {A D : Set} {B C : A → Set}
        (f : (a : A) → B a → C a → D) {a1 a2 : A}
        (p : a1 ≡ a2) →
        {u1 : B a1} {u2 : B a2}
        {v1 : C a1} {v2 : C a2} →
        transport B p u1 ≡ u2 →
        transport C p v1 ≡ v2 →
        f a1 u1 v1 ≡ f a2 u2 v2
  ap3 f refl refl refl = refl

  iso-to-path : {A B : Set} (f : A → B) (g : B → A) (h : (y : B) → f (g y) ≡ y)
    (h' : (x : A) → g (f x) ≡ x) → A ≡ B
  iso-to-path f g h h' = eq-to-path (f , iso-is-eq f g h h')

  pmap-eq : {P Q : 2Pointed} (F G : P ⇒ Q)
            (p : map F ≡ map G) →
            transport (λ z → z (pn P) ≡ pn Q) p (pn-map F) ≡ pn-map G →
            transport (λ z → z (ps P) ≡ ps Q) p (ps-map F) ≡ ps-map G →
          F ≡ G
  pmap-eq F G p q r = ap3 pmap p q r

  tap : ∀ {j} {A B : Set j} {x y : A → B} (p : x ≡ y) (k : A) → x k ≡ y k
  tap refl k = refl

  trans-fapp≡cst : ∀ {j} {A B : Set j} {k : A} {a : B} {x y : A → B}
    (p : x ≡ y) (q : x k ≡ a)
    → transport (λ x → x k ≡ a) p q ≡ ! (tap p k) ∘ q
  trans-fapp≡cst refl q = refl

  Σ : Set → 2Pointed
  Σ P = pointed (Susp P) (north P) (south P)

  Ω : 2Pointed → Set
  Ω Q = pn Q ≡ ps Q

  claim : (P : Set) (Q : 2Pointed) → (Σ P ⇒ Q) ≡ (P → Ω Q)
  claim P Q = iso-to-path
            (λ f x → ! (pn-map f) ∘ ap (map f) (paths P x) ∘ ps-map f)
            (λ g → pmap (Susp-rec P (space Q) (pn Q) (ps Q) g) refl refl)
            (λ y → funext (λ x →
              refl-right-unit (ap (Susp-rec P (space Q) (pn Q) (ps Q) y) (paths P x))
              ∘ Susp-ρ-paths P y x))
            (λ x → pmap-eq
              (pmap
              (Susp-rec P (space Q) (pn Q) (ps Q)
              (λ x₁ → ! (pn-map x) ∘ ap (map x) (paths P x₁) ∘ ps-map x))
              refl refl) x
              {!!} {!!} {!!})

  -- Ω : (Q : Set) (a b : Q) → Set
  -- Ω Q a b = a ≡ b

  -- Ωum :  (P Q : Set) (a b : Q) (m : P → a ≡ b) → P → Ω Q a b
  -- Ωum P Q a b m = m

  -- Ωum : (P : Set) (Q : 2Pointed) (m : (x : P) → pn Q ≡ ps Q)
  --       → P → Ω Q
  -- Ωump : (P Q : Set) (a b : Q) (m : P → a ≡ b)
  --        (h : P → Ω Q a b) → h ≡ Ωum P Q a b m
  -- Ωump = {!!}

  -- Ωum : (P : Set) (Q : Pointed) → Σ P ⇒ Q
  -- Σum P Q = pmap (Susp-rec P (space Q) (point Q) (point Q) (λ x → refl)) refl

{-

  Σ : Pointed → Pointed
  Σ P = pointed (Susp (space P)) (north (space P))

  Ωmap : (P Q : Pointed) → P ⇒ Q → Ω P ⇒ Ω Q
  Ωmap P Q f = pmap (λ p → (! (point-map f)) ∘ ap (space-map f) p ∘ point-map f)
                    (opposite-left-inverse (point-map f))

  Susp-map : {X Y : Set} → (X → Y) → Susp X → Susp Y
  Susp-map {X} {Y} f sp = Susp-rec X (Susp Y) (north Y) (south Y) (λ x → paths Y (f x) ) sp

  Σmap : (P Q : Pointed) → P ⇒ Q → Σ P ⇒ Σ Q
  Σmap P Q f = pmap (Susp-map (space-map f)) refl

  -- ap : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) {x y : A}
  --   → (x ≡ y → f x ≡ f y)
  -- ap f refl = refl

  η : (P : Pointed) → P ⇒ Ω (Σ P)
  η P = pmap (λ x → paths (space P) x ∘ ! (paths (space P) (point P)))
        (opposite-right-inverse (paths (space P) (point P)))

  adj : (P Q : Pointed) → P ⇒ Ω Q → Σ P ⇒ Q
  adj P Q f = pmap (λ x → Susp-rec (space P) (space Q) (point Q) (point Q)
                          (space-map f) x) refl

  -- adj : hom(-, Ω Q) → hom(Σ -, Q) covariant in Q

  --                                   adj
  -- adj : y : Q ⇒ R -->  hom(P, Ω Q) → hom(Σ P, Q)
  --                            |             |
  --             hom(P, Ω y)    |             | hom(Σ P, y)
  --                            v             v
  --                      hom(P, Ω R) → hom(Σ P, R)
  --                                   adj

  -- let x : P ⇒ Ω Q.     y ⊚ adj x ≡ adj (Ω y ⊚ x)

  -- adj : hom(P, Ω -) → hom(Σ P, -) contravariant in P

  -- adj-nat1 : {P Q R : Pointed} (y : Q ⇒ R) (x : P ⇒ Ω Q) →
  --            y ⊚ adj P Q x ≡ adj P R (Ωmap Q R y ⊚ x)
  -- adj-nat1 {P} {Q} {R} y x = pmap-eq (y ⊚ adj _ _ x) (adj _ _ (Ωmap _ _ y ⊚ x))
  --          {!!} {!!}

  jda : (P Q : Pointed) → Σ P ⇒ Q → P ⇒ Ω Q
  jda P Q f =  Ωmap (Σ P) Q f ⊚ η P


  what : (P Q : Pointed) (f : Σ P ⇒ Q) (x : space P) → point Q ≡ space-map f (south (space P))
  what P Q f x = ! (point-map f) ∘ ap (space-map f) (paths (space P) x)

  jda2 : (P Q : Pointed) → Σ P ⇒ Q → P ⇒ Ω Q
  jda2 P Q f =  pmap (λ x → what P Q f x ∘ ! (what P Q f (point P)))
                     (opposite-right-inverse (what P Q f (point P)))

  ε : (P : Pointed) → Σ (Ω P) ⇒ P
  ε P = adj (Ω P) P (pmap (id (space (Ω P))) refl)

  -- beta-normalized
  ε2 : (P : Pointed) → Σ (Ω P) ⇒ P
  ε2 P = pmap (Susp-rec (space (Ω P)) (space P) (point P) (point P)
              (λ x → x)) refl

  _≡[_]_ : {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
  _ ≡[ p1 ] p2 = (p1 ∘ p2)

  _■ : ∀ {A : Set} (x : A) → x ≡ x
  _■ _ = refl

  infix  2 _■
  infixr 2 _≡[_]_

  par : {A B C : Set} {p1 q1 : A} {p2 q2 : B} (F : A → B → C) → p1 ≡ q1 → p2 ≡ q2 →  F p1 p2 ≡ F q1 q2
  par F refl refl = refl

{-
  -- Here's an experiment in shoving around the basepoint

  type-ctx : (P Q : Pointed) (f : P ⇒ Ω Q) (pm : space-map f (point P) ≡ refl)
              → Set
  type-ctx P Q f pm =
    (transport (λ z → z (point P) ≡ point (Ω Q))
    (funext
     (λ x →
        par (λ p q → p ∘ ! q) (Susp-ρ-paths (space P) (space-map f) x)
        (Susp-ρ-paths (space P) (space-map f) (point P) ∘ pm)
        ∘ refl-right-unit (space-map f x)))
    (point-map (jda2 P Q (adj P Q f)))
    ≡ pm)

  # : (Q : Pointed) (x : space Q) → Pointed
  # Q x = pointed (space Q) x

  altspace : {Q : Pointed} (x : space Q) (p : x ≡ point Q) → Q ≡ # Q x
  altspace {Q} x p = pointed-eq Q (# Q x) refl (! p)

  altmap : (P Q : Pointed) (f : P ⇒ Q) → P ⇒ # Q (space-map f (point P))
  altmap P Q f = transport (λ Q → P ⇒ Q) (altspace (space-map f (point P)) (point-map f)) f

  altmap-thm : (P Q : Pointed) (f : P ⇒ Q) → (point-map (altmap P Q f)) ≡ {!!}
  altmap-thm P Q f = {!!}

  lemma-setup : (P Q : Pointed) (C : Set) (f : P ⇒ Q)
                (X1 X2 : space-map f (point P) ≡ (point Q) → C) → (X1 (point-map f) ≡ X2 (point-map f))
                → P ⇒ # Q (space-map f (point P))
  lemma-setup P Q C f X1 X2 q = altmap P Q f
-}


  -- This is my first substantial subgoal that I don't know how to prove

{-
  lemma0 : (P Q : Pointed) (f : P ⇒ Ω Q) →
    transport (λ z → z (point P) ≡ point (Ω Q))
    (funext
     (λ x →
        par (λ p q → p ∘ ! q) (Susp-ρ-paths (space P) (space-map f) x)
        (Susp-ρ-paths (space P) (space-map f) (point P) ∘ point-map f)
        ∘ refl-right-unit (space-map f x)))
    (point-map (jda2 P Q (adj P Q f)))
  test P Q f = {!point-map f!}
-}

  lemma0 : {P Q : Pointed} (f : P ⇒ Ω Q) →
         space-map (jda2 P Q (adj P Q f)) ≡ space-map f
  abstract lemma0 {P} {Q} f = funext (λ x →  par (λ p q → p ∘ ! q)
               (Susp-ρ-paths (space P) (space-map f) x)
               (Susp-ρ-paths (space P) (space-map f) (point P) ∘ point-map f)
               ∘ refl-right-unit (space-map f x))

  lemma1 : {P Q : Pointed} (f : P ⇒ Ω Q) (y : space P) →
         (λ x →
         ap (Susp-rec (space P) (space Q) (point Q) (point Q) (space-map f))
            (paths (space P) x)
         ∘ ! (ap
             (Susp-rec (space P) (space Q) (point Q) (point Q) (space-map f))
             (paths (space P) y)))
         ≡ space-map f
  abstract lemma1 {P} {Q} f x = {!!}

  blob : (P Q : Pointed) (f : P ⇒ Ω Q) (x : space P) → (ap (Susp-rec (space P) (space Q) (point Q) (point Q) (space-map f))
    (paths (space P) x) ∘ ! (ap (Susp-rec (space P) (space Q) (point Q) (point Q) (space-map f)) (paths (space P) x))
    ≡ refl)
  blob P Q f x = opposite-right-inverse
    (ap
     (Susp-rec (space P) (space Q) (point Q) (point Q) (space-map f))
     (paths (space P) x))

  --       (ap
  --       (Susp-rec (space P) (space Q) (point Q) (point Q) (space-map f))
  --       (paths (space P) x))

 -- f : (\x → M x) ≡ (λ x → N x)
 -- E x : M x ≡ N x
 -- tap f x = E x
  think : (A B : Set) (M N : A → B) (f : M ≡ N) (E : (x : A) → M x ≡ N x) (x : A) → funext (tap f)  ≡ f
  think A B M .M refl E x = {!refl!}

  attempt : (P Q : Pointed) (f : P ⇒ Ω Q)  (x : space P) (pmf : space-map f x ≡ point (Ω Q)) →
    tap (lemma1 f x) x  ≡ blob P Q f x ∘ ! pmf

  attempt P Q f x = {! tap (lemma0 f) ∘ !}

  forw : (P Q : Pointed) (f : P ⇒ Ω Q) → jda2 P Q (adj P Q f) ≡ f
  forw P Q f = pmap-eq (jda2 P Q (adj P Q f)) f
               (lemma0 f)
               (trans-fapp≡cst (lemma0 f) (point-map (jda2 P Q (adj P Q f))) ∘ {!!})


  back : (P Q : Pointed) (f : Σ P ⇒ Q) → adj P Q (jda2 P Q f) ≡ f
  back P Q f = pmap-eq (adj P Q (jda2 P Q f)) f
               {!!}
               {!!}


{-
  forw-core0 : (P Q : Pointed)
        (f : space P → space (Ω Q))
        (fm : f (point P) ≡ refl)
        (x : space P) →
        ap (Susp-rec (space P) (space Q) (point Q) (point Q) f)
        (paths (space P) x ∘ ! (paths (space P) (point P)))
        ≡ f x
  forw-core0 P Q f fm x =
   ap (Susp-rec (space P) (space Q) (point Q) (point Q) f)
        (paths (space P) x ∘ ! (paths (space P) (point P)))
   ≡[ ap-concat (Susp-rec (space P) (space Q) (point Q) (point Q) f)
        (paths (space P) x) (! (paths (space P) (point P))) ]
   ap (Susp-rec (space P) (space Q) (point Q) (point Q) f)
     (paths (space P) x)
     ∘
     ap (Susp-rec (space P) (space Q) (point Q) (point Q) f)
     (! (paths (space P) (point P)))
   ≡[  ap (λ w →
     w ∘
     ap (Susp-rec (space P) (space Q) (point Q) (point Q) f)
     (! (paths (space P) (point P))))
     (Susp-ρ-paths (space P) f x) ]
   f x ∘
     ap (Susp-rec (space P) (space Q) (point Q) (point Q) f)
     (! (paths (space P) (point P)))
   ≡[  ap (λ w → f x ∘ w) (ap-opposite ((Susp-rec (space P) (space Q) (point Q) (point Q) f))
                                       ((paths (space P) (point P)))) ]
   f x ∘
     !
     (ap (Susp-rec (space P) (space Q) (point Q) (point Q) f)
      (paths (space P) (point P)))
   ≡[ ap (λ w → f x ∘ ! w) (Susp-ρ-paths (space P) f (point P) ∘ fm) ]
   f x ∘ refl
   ≡[ refl-right-unit (f x) ]
   f x ■

  forw-lemma1 : (P Q : Pointed)
           (f : space P → space (Ω Q))
           (fm : f (point P) ≡ refl) →
           (λ x → ap (Susp-rec (space P) (space Q) (point Q) (point Q) f)
           (paths (space P) x ∘ ! (paths (space P) (point P))) ∘ refl)
           ≡ f
  forw-lemma1 P Q f fm = Funext.funext (λ x →
           refl-right-unit (ap (Susp-rec (space P) (space Q) (point Q) (point Q) f)
                    (paths (space P) x ∘ ! (paths (space P) (point P)))) ∘
           forw-core0 P Q f fm x)

  forw-lemma0 : (P Q : Pointed) (f : P ⇒ Ω Q) →
           space-map (jda P Q (adj P Q f)) ≡ space-map f
  forw-lemma0 P Q f = forw-lemma1 P Q (space-map f) (point-map f)

  test : (P Q : Pointed) (f : P ⇒ Ω Q) →
   (ap (λ z → z (point P)) (forw-lemma0 P Q f)) ≡ {!!}
  test = {!!}

  forw-lemma2 : (P Q : Pointed) (f : P ⇒ Ω Q) →
    transport (λ z → z (point P) ≡ point (Ω Q)) (forw-lemma0 P Q f)
    (point-map (jda P Q (adj P Q f))) ≡ point-map f
  forw-lemma2 P Q f =
    transport (λ z → z (point P) ≡ point (Ω Q)) (forw-lemma0 P Q f)
    (point-map (jda P Q (adj P Q f)))
      ≡[ trans-app≡cst (λ z → z (point P)) (point (Ω Q)) (forw-lemma0 P Q f)
         (point-map (jda P Q (adj P Q f))) ]
    ! (ap (λ z → z (point P)) (forw-lemma0 P Q f)) ∘ (point-map (jda P Q (adj P Q f)))
      ≡[ {!(point-map (jda P Q (adj P Q f)))!} ]
    point-map f ■

  forw : (P Q : Pointed) (f : P ⇒ Ω Q) → jda P Q (adj P Q f) ≡ f
  forw P Q f = pmap-eq (jda P Q (adj P Q f)) f
               (forw-lemma0 P Q f) {!forw-lemma2!}

  back : (P Q : Pointed) (f : Σ P ⇒ Q) → adj P Q (jda P Q f) ≡ f
  back P Q f = {!!}
-}
-}
