{-# OPTIONS --without-K #-}

open import Base hiding (Σ)
open import Jcreed.Susp
import Funext

module Jcreed.LoopAdjunction where

  {- The goal here is to show the suspension is left adjoint to loops -}

  record Pointed : Set₁ where
    constructor pointed
    field
      space : Set
      point : space

  open Pointed public

  record _⇒_ (X Y : Pointed) : Set where
    constructor pmap
    field
      space-map : space X → space Y
      point-map : space-map (point X) ≡ point Y

  open _⇒_ public

  -- pointed maps compose
  _⊚_ : {P Q R : Pointed} → (Q ⇒ R) → (P ⇒ Q) → (P ⇒ R)
  _⊚_ {P} {Q} {R} F G = pmap (space-map F ◯ space-map G)
                             (ap (space-map F) (point-map G) ∘ point-map F)

  -- pointed maps have identities
  pid : (P : Pointed) → (P ⇒ P)
  pid P = pmap (id (space P)) refl


  Ω : Pointed → Pointed
  Ω P = pointed (point P ≡ point P) refl

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

  pmap-eq : {P Q : Pointed} (F G : P ⇒ Q) (p : space-map F ≡ space-map G) →
          transport (λ z → z (point P) ≡ point Q) p (point-map F) ≡ point-map G →
          F ≡ G
  pmap-eq F G p q = ap2 pmap p q

  fwd : (P : Pointed) → ε2 (Σ P) ⊚ Σmap P (Ω (Σ P)) (η P) ≡ pid (Σ P)
  fwd P = pmap-eq (ε2 (Σ P) ⊚ Σmap P (Ω (Σ P)) (η P)) (pid (Σ P))
      (Funext.funext (λ x → (
      space-map (ε2 (Σ P) ⊚ Σmap P (Ω (Σ P)) (η P)) x
      ≡[ {!space-map (ε2 (Σ P) ⊚ Σmap P (Ω (Σ P)) (η P)) x!} ]
      x ■)))
      {!!}

  -- substf : {X C A : Set} {n : C} {s : C}
  --                (m : (a : A) -> n ≡ s)
  --                (f : ((a : A) -> n ≡ s) → X)
  --              → (a : A) → ap (Susp-rec A C n s m) (f (paths A)) ≡ f m
  -- substf = ?



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
