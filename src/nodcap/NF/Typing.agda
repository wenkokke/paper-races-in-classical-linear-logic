module nodcap.NF.Typing where

open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Pos as ℕ⁺ using (ℕ⁺; suc; _+_)
open import Data.Environment
open import Data.List as L using (List; []; _∷_; _++_)
open import Data.List.Any as LA using (Any; here; there)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import nodcap.Base
open import nodcap.Typing as FF using (⊢_)


-- Typing Rules.

infix 1 ⊢ⁿᶠ_

data ⊢ⁿᶠ_ : Environment → Set where

  send : {Γ Δ : Environment} {A B : Type} →

       ⊢ⁿᶠ A ∷ Γ → ⊢ⁿᶠ B ∷ Δ →
       -------------------
       ⊢ⁿᶠ A ⊗ B ∷ Γ ++ Δ

  recv : {Γ : Environment} {A B : Type} →

       ⊢ⁿᶠ A ∷ B ∷ Γ →
       -------------
       ⊢ⁿᶠ A ⅋ B ∷ Γ

  sel₁ : {Γ : Environment} {A B : Type} →

       ⊢ⁿᶠ A ∷ Γ →
       -----------
       ⊢ⁿᶠ A ⊕ B ∷ Γ

  sel₂ : {Γ : Environment} {A B : Type} →

       ⊢ⁿᶠ B ∷ Γ →
       -----------
       ⊢ⁿᶠ A ⊕ B ∷ Γ

  case : {Γ : Environment} {A B : Type} →

       ⊢ⁿᶠ A ∷ Γ → ⊢ⁿᶠ B ∷ Γ →
       -------------------
       ⊢ⁿᶠ A & B ∷ Γ

  halt :

       --------
       ⊢ⁿᶠ 𝟏 ∷ []

  wait : {Γ : Environment} →

       ⊢ⁿᶠ Γ →
       -------
       ⊢ⁿᶠ ⊥ ∷ Γ

  loop : {Γ : Environment} →

       -------
       ⊢ⁿᶠ ⊤ ∷ Γ

  mk?₁ : {Γ : Environment} {A : Type} →

       ⊢ⁿᶠ A ∷ Γ →
       ---------------------
       ⊢ⁿᶠ ?[ 1 ] A ∷ Γ

  mk!₁ : {Γ : Environment} {A : Type} →

       ⊢ⁿᶠ A ∷ Γ →
       ---------------------
       ⊢ⁿᶠ ![ 1 ] A ∷ Γ

  cont : {Γ : Environment} {A : Type} {m n : ℕ⁺} →

       ⊢ⁿᶠ ?[ m ] A ∷ ?[ n ] A ∷ Γ →
       ------------------------------
       ⊢ⁿᶠ ?[ m + n ] A ∷ Γ

  pool : {Γ Δ : Environment} {A : Type} {m n : ℕ⁺} →

       ⊢ⁿᶠ ![ m ] A ∷ Γ → ⊢ⁿᶠ ![ n ] A ∷ Δ →
       -------------------------------------
       ⊢ⁿᶠ ![ m + n ] A ∷ Γ ++ Δ

  exch : {Γ Δ : Environment} →

       Γ ∼[ bag ] Δ → ⊢ⁿᶠ Γ →
       --------------------
       ⊢ⁿᶠ Δ

fromNF : {Γ : Environment} → ⊢ⁿᶠ Γ → ⊢ Γ
fromNF (send x y) = FF.send (fromNF x) (fromNF y)
fromNF (recv x)   = FF.recv (fromNF x)
fromNF (sel₁ x)   = FF.sel₁ (fromNF x)
fromNF (sel₂ x)   = FF.sel₂ (fromNF x)
fromNF (case x y) = FF.case (fromNF x) (fromNF y)
fromNF  halt      = FF.halt
fromNF (wait x)   = FF.wait (fromNF x)
fromNF  loop      = FF.loop
fromNF (mk?₁ x)   = FF.mk?₁ (fromNF x)
fromNF (mk!₁ x)   = FF.mk!₁ (fromNF x)
fromNF (cont x)   = FF.cont (fromNF x)
fromNF (pool x y) = FF.pool (fromNF x) (fromNF y)
fromNF (exch x y) = FF.exch x (fromNF y)

-- -}
-- -}
-- -}
-- -}
-- -}
