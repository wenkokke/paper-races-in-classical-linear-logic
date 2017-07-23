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
open import nodcap.Typing as FF using (⊢_)
open import nodcap.WHNF.Typing

module nodcap.WHNF.Expand where

open I.Inverse using (to; from)
private module ++ {a} {A : Set a} = Monoid (L.monoid A)

private
  serve_of_ : ℕ⁺ → Type → Context
  serve n of A = replicate⁺ n (?[ suc 0 ] A)

{-# TERMINATING #-}
-- Lemma:
--   We can expand an instance of ?[ n ] A into n repetitions of A,
--   by induction on n.
--
-- Problematic calls:
--   * in the recursive call under cont, the index n is split as
--     n₁ + n₂, for which we have n₁, n₂ < n, but not definitionally.
mutual
  expand : {Γ : Context} {A : Type} {n : ℕ⁺} →

    ⊢ʷʰⁿᶠ ?[ n ] A ∷ Γ →
    --------------------
    ⊢ serve n of A ++ Γ

  expand ax = ?
  expand (mk?₁ P) = mk?₁ P
  expand (cont {Γ} {A} {m} {n} P)
    = P.subst (λ Δ → ⊢ʷʰⁿᶠ Δ ++ Γ) (replicate⁺-++-commute m n)
    $ P.subst ⊢ʷʰⁿᶠ_ (P.sym (++.assoc (serve m of A) (serve n of A) Γ))
    $ exch (swp [] (serve m of A) (serve n of A))
    $ expand {n = n}
    $ exch (fwd [] (serve m of A))
    $ expand {n = m} P
  expand {Γ} {A} {n} (exch π P)
    = exch (B.++-cong {xs₁ = serve n of A} I.id (del-from π (here P.refl)))
    $ expandIn (from π ⟨$⟩ here P.refl) P

  expandIn : {Γ : Context} {A : Type} {n : ℕ⁺} (i : ?[ n ] A ∈ Γ) →

    ⊢ʷʰⁿᶠ Γ →
    ----------------------------
    ⊢ʷʰⁿᶠ serve n of A ++ Γ - i

  expandIn (here P.refl) P = expand P
  expandIn {_} {A} {n} (there i) (send {Γ} {Δ} P R)
    with split Γ i
  ... | inj₁ (j , p) rewrite p
      = exch (swp [] (serve n of A) (_ ∷ []))
      $ P.subst ⊢ʷʰⁿᶠ_ (++.assoc (_ ∷ serve n of A) (Γ - j) Δ)
      $ flip send R
      $ exch (swp [] (_ ∷ []) (serve n of A))
      $ expandIn (there j) P
  ... | inj₂ (j , p) rewrite p
      = exch (swp [] (serve n of A) (_ ∷ Γ))
      $ send P
      $ exch (swp [] (_ ∷ []) (serve n of A))
      $ expandIn (there j) R
  expandIn {Γ} {A} {n} (there i) (recv P)
    = exch (swp [] (serve n of A) (_ ∷ []))
    $ recv
    $ exch (swp [] (_ ∷ _ ∷ []) (serve n of A))
    $ expandIn (there (there i)) P
  expandIn {Γ} {A} {n} (there i) (sel₁ P)
    = exch (swp [] (serve n of A) (_ ∷ []))
    $ sel₁
    $ exch (swp [] (_ ∷ []) (serve n of A))
    $ expandIn (there i) P
  expandIn {Γ} {A} {n} (there i) (sel₂ P)
    = exch (swp [] (serve n of A) (_ ∷ []))
    $ sel₂
    $ exch (swp [] (_ ∷ []) (serve n of A))
    $ expandIn (there i) P
  expandIn {Γ} {A} {n} (there i) (case P h)
    = exch (swp [] (serve n of A) (_ ∷ []))
    $ case
      ( exch (swp [] (_ ∷ []) (serve n of A))
      $ expandIn (there i) P )
      ( exch (swp [] (_ ∷ []) (serve n of A))
      $ expandIn (there i) h )
  expandIn (there ()) halt
  expandIn {Γ} {A} {n} (there i) (wait P)
    = exch (swp [] (serve n of A) (_ ∷ []))
    $ wait
    $ expandIn i P
  expandIn {Γ} {A} {n} (there i)  loop
    = exch (swp [] (serve n of A) (_ ∷ []))
    $ loop
  expandIn {Γ} {A} {n} (there i) (mk?₁ P)
    = exch (swp [] (serve n of A) (_ ∷ []))
    $ mk?₁
    $ exch (swp [] (_ ∷ []) (serve n of A))
    $ expandIn (there i) P
  expandIn {Γ} {A} {n} (there i) (mk!₁ P)
    = exch (swp [] (serve n of A) (_ ∷ []))
    $ mk!₁
    $ exch (swp [] (_ ∷ []) (serve n of A))
    $ expandIn (there i) P
  expandIn {Γ} {A} {n} (there i) (cont P)
    = exch (swp [] (serve n of A) (_ ∷ []))
    $ cont
    $ exch (swp [] (_ ∷ _ ∷ []) (serve n of A))
    $ expandIn (there (there i)) P
  expandIn {_} {A} {n} (there i) (pool {Γ} {Δ} P Q)
    with split Γ i
  ... | inj₁ (j , p) rewrite p
      = exch (swp [] (serve n of A) (_ ∷ []))
      $ P.subst ⊢ʷʰⁿᶠ_ (++.assoc (_ ∷ serve n of A) (Γ - j) Δ)
      $ flip pool Q
      $ exch (swp [] (_ ∷ []) (serve n of A))
      $ expandIn (there j) P
  ... | inj₂ (j , p) rewrite p
      = exch (swp [] (serve n of A) (_ ∷ Γ))
      $ pool P
      $ exch (swp [] (_ ∷ []) (serve n of A))
      $ expandIn (there j) Q
  expandIn {Γ} {A} {n} i (exch b P)
    = exch (B.++-cong {xs₁ = serve n of A} I.id (del-from b i))
    $ expandIn (from b ⟨$⟩ i) P
