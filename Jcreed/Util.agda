open import Base

module Jcreed.Util where

iso-to-path : ∀ {i} {A B : Set i} (f : A → B) (g : B → A) (h : (y : B) → f (g y) ≡ y)
  (h' : (x : A) → g (f x) ≡ x) → A ≡ B
iso-to-path f g h h' = eq-to-path (f , iso-is-eq f g h h')

-- converse of function extensionality
tap : ∀ {i j} {X : Set i} {Y : Set j} {f g : X → Y} → f ≡ g → (x : X) → f x ≡ g x
tap refl = λ x → refl

trans-fapp≡cst : ∀ {j} {A B : Set j} {k : A} {a : B} {x y : A → B}
  (p : x ≡ y) (q : x k ≡ a)
  → transport (λ x → x k ≡ a) p q ≡ ! (tap p k) ∘ q
trans-fapp≡cst refl q = refl

ap3 : {A D : Set} {B C : A → Set}
      (f : (a : A) → B a → C a → D) {a1 a2 : A}
      (p : a1 ≡ a2) →
      {u1 : B a1} {u2 : B a2}
      {v1 : C a1} {v2 : C a2} →
      transport B p u1 ≡ u2 →
      transport C p v1 ≡ v2 →
      f a1 u1 v1 ≡ f a2 u2 v2
ap3 f refl refl refl = refl

_•_ : ∀ {i} {A B : Set i} (F : A ≡ B) → A → B
refl • x = x

record Functor : Set₁ where
  constructor functor
  field
    _*_ : Set → Set
    _`_ : {A B : Set} (f : A → B) → _*_ A → _*_ B

open Functor public

trans-id→cst : ∀ {i k} (P : Set k)
    {b c : Set  i} (p : b ≡ c) (q : b → P) (a : c)
    → transport (λ x → x → P) p q a ≡ q (transport (λ x → x) (! p) a)
trans-id→cst P refl q a = refl

-- XXX Probably should pull out the transport at λ A → A → B and generalize
trans-iso-to-path : {A1 A2 B : Set} (p : A1 → B) (f : A1 → A2) (g : A2 → A1)
          (fg : (y : A2) → f (g y) ≡ y) (gf : (y : A1) → g (f y) ≡ y) →
    transport (λ A → A → B) (iso-to-path f g fg gf) p ≡ p ◯ g
trans-iso-to-path {B = B} p f g fg gf = funext (λ x →
        trans-id→cst B (iso-to-path f g fg gf) p x
        ∘ ap p (trans-id! (iso-to-path f g fg gf) x
        ∘ tap (ap inverse (eq-to-path-right-inverse (f , iso-is-eq f g fg gf))) x))
