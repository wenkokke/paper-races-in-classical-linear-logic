open import Algebra
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Pos as ℕ⁺
open import Data.List as L using (List; []; _∷_; _++_)
open import Data.List.Any as LA using (Any; here; there)
open import Data.List.Any.BagAndSetEquality as B
open import Data.Product as PR using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_$_; flip)
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse as I using ()
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_)

open import Logic.Context
open import nodcap.Base
open import nodcap.NF.Typing
open import nodcap.NF.Contract
open import nodcap.NF.Expand
open import nodcap.NF.Redistribute

module nodcap.NF.Cut where

open I.Inverse using (to; from)
private module ++ {a} {A : Set a} = Monoid (L.monoid A)

{-# TERMINATING #-}
-- Theorem:
--   Cut elimination.
mutual
  cut : {Γ Δ : Context} {A : Type} →

    ⊢ⁿᶠ A ∷ Γ → ⊢ⁿᶠ A ^ ∷ Δ →
    ---------------------
    ⊢ⁿᶠ Γ ++ Δ

  cut {_} {Δ} {𝟏} halt (wait y)
    = y
  cut {Γ} {_} {⊥} (wait x) halt
    = P.subst ⊢ⁿᶠ_ (P.sym (proj₂ ++.identity Γ)) x
  cut {_} {Θ} {A ⊗ B} (send {Γ} {Δ} x y) (recv z)
    = P.subst ⊢ⁿᶠ_ (P.sym (++.assoc Γ Δ Θ))
    $ exch (swp [] Γ Δ)
    $ cut y
    $ exch (fwd [] Γ)
    $ cut x z
  cut {Θ} {_} {A ⅋ B} (recv x) (send {Γ} {Δ} y z)
    = P.subst ⊢ⁿᶠ_ (++.assoc Θ Γ Δ)
    $ cut (cut x y) z
  cut {Γ} {Δ} {A ⊕ B} (sel₁ x) (case y z)
    = cut x y
  cut {Γ} {Δ} {A ⊕ B} (sel₂ x) (case y z)
    = cut x z
  cut {Γ} {Δ} {A & B} (case x y) (sel₁ z)
    = cut x z
  cut {Γ} {Δ} {A & B} (case x y) (sel₂ z)
    = cut y z
  cut {Γ} {Δ} {⊗[ ._ ] A} (mk⊗₁ x) y
    = cut x (expand y)
  cut {_} {Θ} {⊗[ ._ ] _} (pool {Γ} {Δ} x y) z
    = P.subst ⊢ⁿᶠ_ (P.sym (++.assoc Γ Δ Θ))
    $ exch (swp [] Γ Δ)
    $ cut y
    $ exch (fwd [] Γ)
    $ cut x
    $ redistribute z
  cut {Γ} {Δ} {⅋[ ._ ] A} x (mk⊗₁ y)
    = cut (expand x) y
  cut {Θ} {_} {⅋[ ._ ] A} x (pool {Γ} {Δ} y z)
    = P.subst ⊢ⁿᶠ_ (++.assoc Θ Γ Δ)
    $ flip cut z
    $ flip cut y
    $ redistribute x
  cut {Γ} {Δ} {A} (exch b x) y
    = exch (B.++-cong {ys₁ = Δ} (del-from b (here P.refl)) I.id)
    $ cutIn (from b ⟨$⟩ here P.refl) (here P.refl) x y
  cut {Γ} {Δ} {A} x (exch b y)
    = exch (B.++-cong {xs₁ = Γ} I.id (del-from b (here P.refl)))
    $ cutIn (here P.refl) (from b ⟨$⟩ here P.refl) x y


  cutIn : {Γ Δ : Context} {A : Type} (i : A ∈ Γ) (j : A ^ ∈ Δ) →

    ⊢ⁿᶠ Γ → ⊢ⁿᶠ Δ →
    ----------------
    ⊢ⁿᶠ Γ - i ++ Δ - j

  cutIn (here P.refl) (here P.refl) x y = cut x y

  cutIn {_} {Θ} (there i) j (send {Γ} {Δ} x y) z
    with split Γ i
  ... | inj₁ (k , p) rewrite p
      = P.subst ⊢ⁿᶠ_ (P.sym (++.assoc (_ ∷ Γ - k) Δ (Θ - j)))
      $ exch (swp₃ (_ ∷ Γ - k) Δ)
      $ P.subst ⊢ⁿᶠ_ (++.assoc (_ ∷ Γ - k) (Θ - j) Δ)
      $ flip send y
      $ cutIn (there k) j x z
  ... | inj₂ (k , p) rewrite p
      = P.subst ⊢ⁿᶠ_ (P.sym (++.assoc (_ ∷ Γ) (Δ - k) (Θ - j)))
      $ send x
      $ cutIn (there k) j y z
  cutIn (there i) j (recv x) y
    = recv
    $ cutIn (there (there i)) j x y
  cutIn (there i) j (sel₁ x) y
    = sel₁
    $ cutIn (there i) j x y
  cutIn (there i) j (sel₂ x) y
    = sel₂
    $ cutIn (there i) j x y
  cutIn (there i) j (case x y) z
    = case
    ( cutIn (there i) j x z )
    ( cutIn (there i) j y z )
  cutIn (there ()) j halt y
  cutIn (there i) j (wait x) y
    = wait
    $ cutIn i j x y
  cutIn (there i) j loop y
    = loop
  cutIn {Γ} {Δ} (there i) j (mk⅋₁ x) y
    = mk⅋₁
    $ cutIn (there i) j x y
  cutIn {Γ} {Δ} (there i) j (mk⊗₁ x) y
    = mk⊗₁
    $ cutIn (there i) j x y
  cutIn {Γ} {Δ} (there i) j (cont x) y
    = cont
    $ cutIn (there (there i)) j x y
  cutIn {_} {Θ} (there i) j (pool {Γ} {Δ} x y) z
    with split Γ i
  ... | inj₁ (k , p) rewrite p
      = P.subst ⊢ⁿᶠ_ (P.sym (++.assoc (_ ∷ Γ - k) Δ (Θ - j)))
      $ exch (swp₃ (_ ∷ Γ - k) Δ)
      $ P.subst ⊢ⁿᶠ_ (++.assoc (_ ∷ Γ - k) (Θ - j) Δ)
      $ flip pool y
      $ cutIn (there k) j x z
  ... | inj₂ (k , p) rewrite p
      = P.subst ⊢ⁿᶠ_ (P.sym (++.assoc (_ ∷ Γ) (Δ - k) (Θ - j)))
      $ pool x
      $ cutIn (there k) j y z

  cutIn {Θ} {_} i (there j) x (send {Γ} {Δ} y z)
    with split Γ j
  ... | inj₁ (k , p) rewrite p
      = exch (bwd [] (Θ - i))
      $ P.subst ⊢ⁿᶠ_ (++.assoc (_ ∷ Θ - i) (Γ - k) Δ)
      $ flip send z
      $ exch (fwd [] (Θ - i))
      $ cutIn i (there k) x y
  ... | inj₂ (k , p) rewrite p
      = exch (swp [] (Θ - i) (_ ∷ Γ))
      $ send y
      $ exch (fwd [] (Θ - i))
      $ cutIn i (there k) x z
  cutIn {Γ} i (there j) x (recv {Δ} y)
    = exch (bwd [] (Γ - i))
    $ recv
    $ exch (swp [] (_ ∷ _ ∷ []) (Γ - i))
    $ cutIn i (there (there j)) x y
  cutIn {Γ} {Δ} i (there j) x (sel₁ y)
    = exch (bwd [] (Γ - i))
    $ sel₁
    $ exch (fwd [] (Γ - i))
    $ cutIn i (there j) x y
  cutIn {Γ} {Δ} i (there j) x (sel₂ y)
    = exch (bwd [] (Γ - i))
    $ sel₂
    $ exch (fwd [] (Γ - i))
    $ cutIn i (there j) x y
  cutIn {Γ} {Δ} i (there j) x (case y z)
    = exch (bwd [] (Γ - i))
    $ case
    ( exch (fwd [] (Γ - i)) $ cutIn i (there j) x y )
    ( exch (fwd [] (Γ - i)) $ cutIn i (there j) x z )
  cutIn {Γ} i (there ()) x halt
  cutIn {Γ} {Δ} i (there j) x (wait y)
    = exch (bwd [] (Γ - i))
    $ wait
    $ cutIn i j x y
  cutIn {Γ} {Δ} i (there j) x loop
    = exch (bwd [] (Γ - i)) loop
  cutIn {Γ} {Δ} i (there j) x (mk⅋₁ y)
    = exch (bwd [] (Γ - i))
    $ mk⅋₁
    $ exch (fwd [] (Γ - i))
    $ cutIn i (there j) x y
  cutIn {Γ} {Δ} i (there j) x (mk⊗₁ y)
    = exch (bwd [] (Γ - i))
    $ mk⊗₁
    $ exch (fwd [] (Γ - i))
    $ cutIn i (there j) x y
  cutIn {Γ} {Δ} i (there j) x (cont y)
    = exch (bwd [] (Γ - i))
    $ cont
    $ exch (swp [] (_ ∷ _ ∷ []) (Γ - i))
    $ cutIn i (there (there j)) x y
  cutIn {Θ} {_} i (there j) x (pool {Γ} {Δ} y z)
    with split Γ j
  ... | inj₁ (k , p) rewrite p
      = exch (bwd [] (Θ - i))
      $ P.subst ⊢ⁿᶠ_ (++.assoc (_ ∷ Θ - i) (Γ - k) Δ)
      $ flip pool z
      $ exch (fwd [] (Θ - i))
      $ cutIn i (there k) x y
  ... | inj₂ (k , p) rewrite p
      = exch (swp [] (Θ - i) (_ ∷ Γ))
      $ pool y
      $ exch (fwd [] (Θ - i))
      $ cutIn i (there k) x z

  cutIn {Γ} {Δ} i j (exch b x) y
    = exch (B.++-cong {ys₁ = Δ - j} (del-from b i ) I.id)
    $ cutIn (from b ⟨$⟩ i) j x y
  cutIn {Γ} {Δ} i j x (exch b y)
    = exch (B.++-cong {xs₁ = Γ - i} I.id (del-from b j))
    $ cutIn i (from b ⟨$⟩ j) x y
