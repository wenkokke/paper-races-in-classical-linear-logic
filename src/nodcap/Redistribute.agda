open import Algebra
open import Function using (_$_)
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Pos as ℕ⁺
open import Data.List as L using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_)

open import Logic.Context
open import nodcap.Base
open import nodcap.Contract
open import nodcap.Expand

module nodcap.Redistribute where

private module ++ {a} {A : Set a} = Monoid (L.monoid A)

-- Lemma:
--   A formula of the form ⅋[ m + n ] is introduced by a contraction on two
--   formulas of the form ⅋[ p ] A and ⅋[ q ] A. While we know p + q = m + n,
--   it isn't necessarily true that p = m or p = n.
--   Using expansion and contraction, we can redistribute the subproofs, such
--   that we get exactly two formulas with p and q where p = m and q = n.
redistribute : {Γ : Context} {A : Type} {m n : ℕ⁺} →

  ⊢ ⅋[ m + n ] A ∷ Γ →
  ----------------------------
  ⊢ ⅋[ m ] A ∷ ⅋[ n ] A ∷ Γ

redistribute {Γ} {A} {m} {n} x
  = exch (bbl [])
  $ contract {n = n}
  $ exch (bwd [] (replicate⁺ n A))
  $ contract {n = m}
  $ P.subst ⊢_ (++.assoc (replicate⁺ m A) (replicate⁺ n A) Γ)
  $ P.subst (λ Γ' → ⊢ Γ' ++ Γ) (P.sym (replicate⁺-++-commute m n))
  $ expand x
