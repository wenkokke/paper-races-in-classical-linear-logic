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

module nodcap.NF.Expand where

open I.Inverse using (to; from)
private module ++ {a} {A : Set a} = Monoid (L.monoid A)

{-# TERMINATING #-}
-- Lemma:
--   We can expand an instance of ⅋[ n ] A into n repetitions of A,
--   by induction on n.
--
-- Problematic calls:
--   * in the recursive call under cont, the index n is split as
--     n₁ + n₂, for which we have n₁, n₂ < n, but not definitionally.
mutual
  expand : {Γ : Context} {A : Type} {n : ℕ⁺} →

    ⊢ⁿᶠ ⅋[ n ] A ∷ Γ →
    --------------------
    ⊢ⁿᶠ replicate⁺ n A ++ Γ

  expand (mk⅋₁ x) = x
  expand (cont {Γ} {A} {m} {n} x)
    = P.subst (λ Δ → ⊢ⁿᶠ Δ ++ Γ) (replicate⁺-++-commute m n)
    $ P.subst ⊢ⁿᶠ_ (P.sym (++.assoc (replicate⁺ m A) (replicate⁺ n A) Γ))
    $ exch (swp [] (replicate⁺ m A) (replicate⁺ n A))
    $ expand {n = n}
    $ exch (fwd [] (replicate⁺ m A))
    $ expand {n = m} x
  expand {Γ} {A} {n} (exch b x)
    = exch (B.++-cong {xs₁ = replicate⁺ n A} I.id (del-from b (here P.refl)))
    $ expandIn (from b ⟨$⟩ here P.refl) x

  expandIn : {Γ : Context} {A : Type} {n : ℕ⁺} (i : ⅋[ n ] A ∈ Γ) →

    ⊢ⁿᶠ Γ →
    ----------------------------
    ⊢ⁿᶠ replicate⁺ n A ++ Γ - i

  expandIn (here P.refl) x = expand x
  expandIn {_} {A} {n} (there i) (send {Γ} {Δ} x h)
    with split Γ i
  ... | inj₁ (j , p) rewrite p
      = exch (swp [] (replicate⁺ n A) (_ ∷ []))
      $ P.subst ⊢ⁿᶠ_ (++.assoc (_ ∷ replicate⁺ n A) (Γ - j) Δ)
      $ flip send h
      $ exch (swp [] (_ ∷ []) (replicate⁺ n A))
      $ expandIn (there j) x
  ... | inj₂ (j , p) rewrite p
      = exch (swp [] (replicate⁺ n A) (_ ∷ Γ))
      $ send x
      $ exch (swp [] (_ ∷ []) (replicate⁺ n A))
      $ expandIn (there j) h
  expandIn {Γ} {A} {n} (there i) (recv x)
    = exch (swp [] (replicate⁺ n A) (_ ∷ []))
    $ recv
    $ exch (swp [] (_ ∷ _ ∷ []) (replicate⁺ n A))
    $ expandIn (there (there i)) x
  expandIn {Γ} {A} {n} (there i) (sel₁ x)
    = exch (swp [] (replicate⁺ n A) (_ ∷ []))
    $ sel₁
    $ exch (swp [] (_ ∷ []) (replicate⁺ n A))
    $ expandIn (there i) x
  expandIn {Γ} {A} {n} (there i) (sel₂ x)
    = exch (swp [] (replicate⁺ n A) (_ ∷ []))
    $ sel₂
    $ exch (swp [] (_ ∷ []) (replicate⁺ n A))
    $ expandIn (there i) x
  expandIn {Γ} {A} {n} (there i) (case x h)
    = exch (swp [] (replicate⁺ n A) (_ ∷ []))
    $ case
      ( exch (swp [] (_ ∷ []) (replicate⁺ n A))
      $ expandIn (there i) x )
      ( exch (swp [] (_ ∷ []) (replicate⁺ n A))
      $ expandIn (there i) h )
  expandIn (there ()) halt
  expandIn {Γ} {A} {n} (there i) (wait x)
    = exch (swp [] (replicate⁺ n A) (_ ∷ []))
    $ wait
    $ expandIn i x
  expandIn {Γ} {A} {n} (there i)  loop
    = exch (swp [] (replicate⁺ n A) (_ ∷ []))
    $ loop
  expandIn {Γ} {A} {n} (there i) (mk⅋₁ x)
    = exch (swp [] (replicate⁺ n A) (_ ∷ []))
    $ mk⅋₁
    $ exch (swp [] (_ ∷ []) (replicate⁺ n A))
    $ expandIn (there i) x
  expandIn {Γ} {A} {n} (there i) (mk⊗₁ x)
    = exch (swp [] (replicate⁺ n A) (_ ∷ []))
    $ mk⊗₁
    $ exch (swp [] (_ ∷ []) (replicate⁺ n A))
    $ expandIn (there i) x
  expandIn {Γ} {A} {n} (there i) (cont x)
    = exch (swp [] (replicate⁺ n A) (_ ∷ []))
    $ cont
    $ exch (swp [] (_ ∷ _ ∷ []) (replicate⁺ n A))
    $ expandIn (there (there i)) x
  expandIn {_} {A} {n} (there i) (pool {Γ} {Δ} x y)
    with split Γ i
  ... | inj₁ (j , p) rewrite p
      = exch (swp [] (replicate⁺ n A) (_ ∷ []))
      $ P.subst ⊢ⁿᶠ_ (++.assoc (_ ∷ replicate⁺ n A) (Γ - j) Δ)
      $ flip pool y
      $ exch (swp [] (_ ∷ []) (replicate⁺ n A))
      $ expandIn (there j) x
  ... | inj₂ (j , p) rewrite p
      = exch (swp [] (replicate⁺ n A) (_ ∷ Γ))
      $ pool x
      $ exch (swp [] (_ ∷ []) (replicate⁺ n A))
      $ expandIn (there j) y
  expandIn {Γ} {A} {n} i (exch b x)
    = exch (B.++-cong {xs₁ = replicate⁺ n A} I.id (del-from b i))
    $ expandIn (from b ⟨$⟩ i) x
