open import Base

module Jcreed.Util where
  iso-to-path : {A B : Set} (f : A → B) (g : B → A) (h : (y : B) → f (g y) ≡ y)
    (h' : (x : A) → g (f x) ≡ x) → A ≡ B
  iso-to-path f g h h' = eq-to-path (f , iso-is-eq f g h h')

  tap : ∀ {j} {A B : Set j} {x y : A → B} (p : x ≡ y) (k : A) → x k ≡ y k
  tap refl k = refl

  trans-fapp≡cst : ∀ {j} {A B : Set j} {k : A} {a : B} {x y : A → B}
    (p : x ≡ y) (q : x k ≡ a)
    → transport (λ x → x k ≡ a) p q ≡ ! (tap p k) ∘ q
  trans-fapp≡cst refl q = refl
