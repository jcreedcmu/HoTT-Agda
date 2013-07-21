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
