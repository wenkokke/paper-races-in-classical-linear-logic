module pi where

open import Data.Pos as Pos
open import Data.List renaming (_∷_ to _,_; [] to ∅)

-- Types.

data Type : Set where
  𝟏 : Type
  ⊥ : Type
  𝟎 : Type
  ⊤ : Type
  _⊗_ : (A B : Type) → Type
  _⅋_ : (A B : Type) → Type
  _⊕_ : (A B : Type) → Type
  _&_ : (A B : Type) → Type
  ![_]_ : (n : ℕ⁺) (A : Type) → Type
  ?[_]_ : (n : ℕ⁺) (A : Type) → Type

-- Duality.

_^ : Type → Type
𝟏 ^ = ⊥
⊥ ^ = 𝟏
𝟎 ^ = ⊤
⊤ ^ = 𝟎
(A ⊗ B) ^ = (A ^) ⅋ (B ^)
(A ⅋ B) ^ = (A ^) ⊗ (B ^)
(A ⊕ B) ^ = (A ^) & (B ^)
(A & B) ^ = (A ^) ⊕ (B ^)
(![ n ] A) ^ = ?[ n ] (A ^)
(?[ n ] A) ^ = ![ n ] (A ^)

-- Environments and Structures.

Env : Set
Env = List Type

Sep : Set
Sep = List Env

-- Sequents.

infix 1 ⊢_

data ⊢_ : Sep → Set where

  ax : {A : Type} →

    --------------------
    ⊢ (A , A ^ , ∅) , ∅

  mix : {X Y : Sep} →

    ⊢ X → ⊢ Y →
    -----------
    ⊢ X ++ Y

  cut : {A : Type} {Γ Δ : Env} {X : Sep} →

    ⊢ (A , Γ) , (A ^ , Δ) , X →
    ---------------------------
    ⊢ (Γ ++ Δ) , X
