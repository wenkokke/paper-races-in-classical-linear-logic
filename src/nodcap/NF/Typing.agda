open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Pos as ℕ⁺ using (ℕ⁺; suc; _+_)
open import Data.List as L using (List; []; _∷_; _++_)
open import Data.List.Any as LA using (Any; here; there)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality as P using (_≡_)


open import nodcap.Base


module nodcap.NF.Typing where


-- Typing Rules.

infix 1 ⊢ⁿᶠ_

data ⊢ⁿᶠ_ : Context → Set where

  send : {Γ Δ : Context} {A B : Type} →

       ⊢ⁿᶠ A ∷ Γ → ⊢ⁿᶠ B ∷ Δ →
       -------------------
       ⊢ⁿᶠ A ⊗ B ∷ Γ ++ Δ

  recv : {Γ : Context} {A B : Type} →

       ⊢ⁿᶠ A ∷ B ∷ Γ →
       -------------
       ⊢ⁿᶠ A ⅋ B ∷ Γ

  sel₁ : {Γ : Context} {A B : Type} →

       ⊢ⁿᶠ A ∷ Γ →
       -----------
       ⊢ⁿᶠ A ⊕ B ∷ Γ

  sel₂ : {Γ : Context} {A B : Type} →

       ⊢ⁿᶠ B ∷ Γ →
       -----------
       ⊢ⁿᶠ A ⊕ B ∷ Γ

  case : {Γ : Context} {A B : Type} →

       ⊢ⁿᶠ A ∷ Γ → ⊢ⁿᶠ B ∷ Γ →
       -------------------
       ⊢ⁿᶠ A & B ∷ Γ

  halt :

       --------
       ⊢ⁿᶠ 𝟏 ∷ []

  wait : {Γ : Context} →

       ⊢ⁿᶠ Γ →
       -------
       ⊢ⁿᶠ ⊥ ∷ Γ

  loop : {Γ : Context} →

       -------
       ⊢ⁿᶠ ⊤ ∷ Γ

  mk?₁ : {Γ : Context} {A : Type} →

       ⊢ⁿᶠ A ∷ Γ →
       ---------------------
       ⊢ⁿᶠ ?[ suc zero ] A ∷ Γ

  mk!₁ : {Γ : Context} {A : Type} →

       ⊢ⁿᶠ A ∷ Γ →
       ---------------------
       ⊢ⁿᶠ ![ suc zero ] A ∷ Γ

  cont : {Γ : Context} {A : Type} {m n : ℕ⁺} →

       ⊢ⁿᶠ ?[ m ] A ∷ ?[ n ] A ∷ Γ →
       ------------------------------
       ⊢ⁿᶠ ?[ m + n ] A ∷ Γ

  pool : {Γ Δ : Context} {A : Type} {m n : ℕ⁺} →

       ⊢ⁿᶠ ![ m ] A ∷ Γ → ⊢ⁿᶠ ![ n ] A ∷ Δ →
       -------------------------------------
       ⊢ⁿᶠ ![ m + n ] A ∷ Γ ++ Δ

  exch : {Γ Δ : Context} →

       Γ ∼[ bag ] Δ → ⊢ⁿᶠ Γ →
       --------------------
       ⊢ⁿᶠ Δ

-- -}
-- -}
-- -}
-- -}
-- -}
