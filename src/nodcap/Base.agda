open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Pos as ℕ⁺ using (ℕ⁺; suc; _+_)
open import Data.List as L using (List; []; _∷_; _++_)
open import Data.List.Any as LA using (Any; here; there)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality as P using (_≡_)


module nodcap.Base where

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
  ⊗[_]_ : (n : ℕ⁺) (A : Type) → Type
  ⅋[_]_ : (n : ℕ⁺) (A : Type) → Type


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
(⊗[ n ] A) ^ = ⅋[ n ] (A ^)
(⅋[ n ] A) ^ = ⊗[ n ] (A ^)

^-inv : (A : Type) → A ^ ^ ≡ A
^-inv 𝟏 = P.refl
^-inv ⊥ = P.refl
^-inv 𝟎 = P.refl
^-inv ⊤ = P.refl
^-inv (A ⊗ B) = P.cong₂ _⊗_ (^-inv A) (^-inv B)
^-inv (A ⅋ B) = P.cong₂ _⅋_ (^-inv A) (^-inv B)
^-inv (A ⊕ B) = P.cong₂ _⊕_ (^-inv A) (^-inv B)
^-inv (A & B) = P.cong₂ _&_ (^-inv A) (^-inv B)
^-inv (⊗[ n ] A) = P.cong ⊗[ n ]_ (^-inv A)
^-inv (⅋[ n ] A) = P.cong ⅋[ n ]_ (^-inv A)

-- Lollipop.

_⊸_ : (A B : Type) → Type
A ⊸ B = (A ^) ⅋ B


-- Polarity.

data Pos : (A : Type) → Set where
  𝟎 : Pos 𝟎
  𝟏 : Pos 𝟏
  _⊗_ : (A B : Type) → Pos (A ⊗ B)
  _⊕_ : (A B : Type) → Pos (A ⊕ B)
  ⊗[_]_ : (n : ℕ⁺) (A : Type) → Pos (⊗[ n ] A)

data Neg : (A : Type) → Set where
  ⊥ : Neg ⊥
  ⊤ : Neg ⊤
  _⅋_ : (A B : Type) → Neg (A ⅋ B)
  _&_ : (A B : Type) → Neg (A & B)
  ⅋[_]_ : (n : ℕ⁺) (A : Type) → Neg (⅋[ n ] A)

pol? : (A : Type) → Pos A ⊎ Neg A
pol? 𝟏 = inj₁ 𝟏
pol? ⊥ = inj₂ ⊥
pol? 𝟎 = inj₁ 𝟎
pol? ⊤ = inj₂ ⊤
pol? (A ⊗ B) = inj₁ (A ⊗ B)
pol? (A ⅋ B) = inj₂ (A ⅋ B)
pol? (A ⊕ B) = inj₁ (A ⊕ B)
pol? (A & B) = inj₂ (A & B)
pol? (⊗[ n ] A) = inj₁ (⊗[ n ] A)
pol? (⅋[ n ] A) = inj₂ (⅋[ n ] A)

^-posneg : {A : Type} (P : Pos A) → Neg (A ^)
^-posneg 𝟎 = ⊤
^-posneg 𝟏 = ⊥
^-posneg (A ⊗ B) = (A ^) ⅋ (B ^)
^-posneg (A ⊕ B) = (A ^) & (B ^)
^-posneg (⊗[ n ] A) = ⅋[ n ] (A ^)

^-negpos : {A : Type} (N : Neg A) → Pos (A ^)
^-negpos ⊥ = 𝟏
^-negpos ⊤ = 𝟎
^-negpos (A ⅋ B) = (A ^) ⊗ (B ^)
^-negpos (A & B) = (A ^) ⊕ (B ^)
^-negpos (⅋[ n ] A) = ⊗[ n ] (A ^)


-- Contexts.

Context : Set
Context = List Type

open LA.Membership-≡ public


-- Typing Rules.

infix 1 ⊢_

data ⊢_ : Context → Set where

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

  mk⅋₁ : {Γ : Context} {A : Type} →

       ⊢ A ∷ Γ →
       ---------------------
       ⊢ ⅋[ suc zero ] A ∷ Γ

  mk⊗₁ : {Γ : Context} {A : Type} →

       ⊢ A ∷ Γ →
       ---------------------
       ⊢ ⊗[ suc zero ] A ∷ Γ

  cont : {Γ : Context} {A : Type} {m n : ℕ⁺} →

       ⊢ ⅋[ m ] A ∷ ⅋[ n ] A ∷ Γ →
       ------------------------------
       ⊢ ⅋[ m + n ] A ∷ Γ

  pool : {Γ Δ : Context} {A : Type} {m n : ℕ⁺} →

       ⊢ ⊗[ m ] A ∷ Γ → ⊢ ⊗[ n ] A ∷ Δ →
       -------------------------------------
       ⊢ ⊗[ m + n ] A ∷ Γ ++ Δ

  exch : {Γ Δ : Context} →

       Γ ∼[ bag ] Δ → ⊢ Γ →
       --------------------
       ⊢ Δ

-- -}
-- -}
-- -}
-- -}
-- -}
