open import Algebra using (Semiring)
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Vec using (Vec; _∷_; [])

module cpnd where

data Pretype : Set where
  𝟏 ⊥ : Pretype
  _⊗_ _⅋_ : Pretype → Pretype → Pretype

infixl 30 _^

_^ : Pretype → Pretype
𝟏 ^ = ⊥
⊥ ^ = 𝟏
(A ⊗ B) ^ = A ^ ⅋ B ^
(A ⅋ B) ^ = A ^ ⊗ B ^

Precontext : ℕ → Set
Precontext n = Vec Pretype n

data Usage : Set where
  0# 1# : Usage

infix 10 _⊠_

data Type : (A : Pretype) → Set where
  _⊠_ : (ρ : Usage) (A : Pretype) → Type A

infixr 5 _∷_

data Context : {n : ℕ} (Γ : Precontext n) → Set where
  [] : Context []
  _∷_ : {n : ℕ} {Γ : Precontext n} {A : Pretype} (σ : Type A) (Δ : Context Γ) → Context {suc n} (A ∷ Γ)

infix 1 _↝_∈_↝_

data _∶_↝_∈_↝_ {A B : Pretype} (σ : Type A) (σ′ : Type B) : {n : ℕ} {Γ Γ′ : Precontext n} (Δ : Context Γ) (Δ′ : Context Γ′) → Set where

  zero : {n : ℕ} {Γ : Precontext n} {Δ : Context Γ} →
         σ ↝ σ′ ∈ σ ∷ Δ ↝ σ′ ∷ Δ

  suc  : {n : ℕ} {Γ : Precontext n} {Δ Δ′ : Context Γ} {C : Pretype} {τ : Type C} →
         σ ↝ σ′ ∈ Δ ↝ Δ′ → σ ↝ σ′ ∈ τ ∷ Δ ↝ τ ∷ Δ′

infix 1 ⊢_↝_

data ⊢_↝_ {n : ℕ} : {Γ Γ′ : Precontext n} (Δ : Context Γ) (Δ′ : Context Γ′) → Set where

  link : {A : Pretype} {Γ : Precontext n} {Δ Δ′ Δ″ : Context Γ} →

    1# ⊠ A   ↝ 0# ⊠ A   ∈ Δ  ↝ Δ′ →
    1# ⊠ A ^ ↝ 0# ⊠ A ^ ∈ Δ′ ↝ Δ″ →
    --------------------------------
    ⊢ Δ ↝ Δ″

  send : {A B : Pretype} {Γ Γ′ Γ″ Γ‴ : Precontext n} {Δ : Context Γ} {Δ′ : Context Γ′} {Δ″ : Context Γ″} {Δ‴ : Context Γ‴} →

    1# ⊠ A ⊗ B ↝ 1# ⊠ A ∈ Δ ↝ Δ′ →
    ⊢ 1# ⊠ B ∷ Δ′ ↝ 0# ⊠ B ∷ Δ″ →
    ⊢ Δ″ ↝ Δ‴ →
    -------------------------------
    ⊢ Δ ↝ Δ″

--  recv : {A B C : Pretype} {ρ : Usage} {Γ Γ′ Γ″ : Precontext n} {Δ : Context Γ} {Δ′ : Context Γ′} {Δ″ : Context Γ″} →

-- -}
-- -}
-- -}
-- -}
-- -}
