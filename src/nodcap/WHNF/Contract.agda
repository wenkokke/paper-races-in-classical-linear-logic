open import Function using (_$_)
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Pos as ℕ⁺
open import Data.List as L using (List; []; _∷_; _++_)

open import Logic.Context
open import nodcap.Base
open import nodcap.Typing as FF using (⊢_)
open import nodcap.WHNF.Typing

module nodcap.WHNF.Contract where

-- Lemma:
--   We can contract n repetitions of A to an instance of ?[ n ] A,
--   by induction on n.
contract : {Γ : Context} {A : Type} {n : ℕ⁺} →

  ⊢ʷʰⁿᶠ replicate⁺ n A ++ Γ →
  --------------------------
  ⊢ʷʰⁿᶠ ?[ n ] A ∷ Γ

contract {n = suc zero}    P
  = mk?₁
  $ fromWHNF P
contract {n = suc (suc n)} P
  = cont {m = suc zero}
  $ exch (fwd [] (_ ∷ []))
  $ contract
  $ exch (bwd [] (replicate⁺ (suc n) _))
  $ mk?₁
  $ fromWHNF P
