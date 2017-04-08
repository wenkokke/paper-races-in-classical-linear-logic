open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Pos as ℕ⁺ using (ℕ⁺; suc; _+_)
open import Data.List as L using (List; []; _∷_; _++_)
open import Data.List.Any as LA using (Any; here; there)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open import Logic.Context
open import nodcap.Base

module nodcap.Typing where


-- Typing Rules.

infix 1 ⊢_

data ⊢_ : Context → Set where

  ax   : {A : Type} →

       -------------- 
       ⊢ A ∷ A ^ ∷ []

  cut  : {Γ Δ : Context} {A : Type} →

       ⊢ A ∷ Γ → ⊢ A ^ ∷ Δ →
       ---------------------
       ⊢ Γ ++ Δ

  send : {Γ Δ : Context} {A B : Type} →

       ⊢ A ∷ Γ → ⊢ B ∷ Δ →
       -------------------
       ⊢ A ⊗ B ∷ Γ ++ Δ

  recv : {Γ : Context} {A B : Type} →

       ⊢ A ∷ B ∷ Γ →
       -------------
       ⊢ A ⅋ B ∷ Γ

  sel₁ : {Γ : Context} {A B : Type} →

       ⊢ A ∷ Γ →
       -----------
       ⊢ A ⊕ B ∷ Γ

  sel₂ : {Γ : Context} {A B : Type} →

       ⊢ B ∷ Γ →
       -----------
       ⊢ A ⊕ B ∷ Γ

  case : {Γ : Context} {A B : Type} →

       ⊢ A ∷ Γ → ⊢ B ∷ Γ →
       -------------------
       ⊢ A & B ∷ Γ

  halt :

       --------
       ⊢ 𝟏 ∷ []

  wait : {Γ : Context} →

       ⊢ Γ →
       -------
       ⊢ ⊥ ∷ Γ

  loop : {Γ : Context} →

       -------
       ⊢ ⊤ ∷ Γ

  mk?₁ : {Γ : Context} {A : Type} →

       ⊢ A ∷ Γ →
       ---------------------
       ⊢ ?[ suc zero ] A ∷ Γ

  mk!₁ : {Γ : Context} {A : Type} →

       ⊢ A ∷ Γ →
       ---------------------
       ⊢ ![ suc zero ] A ∷ Γ

  cont : {Γ : Context} {A : Type} {m n : ℕ⁺} →

       ⊢ ?[ m ] A ∷ ?[ n ] A ∷ Γ →
       ------------------------------
       ⊢ ?[ m + n ] A ∷ Γ

  pool : {Γ Δ : Context} {A : Type} {m n : ℕ⁺} →

       ⊢ ![ m ] A ∷ Γ → ⊢ ![ n ] A ∷ Δ →
       -------------------------------------
       ⊢ ![ m + n ] A ∷ Γ ++ Δ

  exch : {Γ Δ : Context} →

       Γ ∼[ bag ] Δ → ⊢ Γ →
       --------------------
       ⊢ Δ

cutIn : {Γ Δ : Context} {A : Type} (i : A ∈ Γ) (j : A ^ ∈ Δ) →

  ⊢ Γ → ⊢ Δ →
  ----------------
  ⊢ Γ - i ++ Δ - j

cutIn {Γ} {Δ} {A} i j P Q with ∈→++ i | ∈→++ j
... | (Γ₁ , Γ₂ , P.refl , p) | (Δ₁ , Δ₂ , P.refl , q) rewrite p | q
    = cut (exch (fwd [] Γ₁) P) (exch (fwd [] Δ₁) Q)

-- -}
-- -}
-- -}
-- -}
-- -}
