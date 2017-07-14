open import Data.Bool using (Bool; true; false)
open import Data.List as L using (List; []; _∷_; _++_)
open import Data.List.Any.BagAndSetEquality as B
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Pos as ℕ⁺
open import Data.Product using (∃-syntax; _,_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open import Logic.Context
open import nodcap.Base

module nodcap.WHNF.Typing where

infix 1 ⊢[whnf?_]_ ⊢ʷʰⁿᶠ_ ⊢_

mutual
  ⊢ʷʰⁿᶠ_ : (Γ : Context) → Set
  ⊢ʷʰⁿᶠ Γ = ⊢[whnf? true ] Γ

  ⊢_ : (Γ : Context) → Set
  ⊢ Γ = ∃[ b ] (⊢[whnf? b ] Γ)

  data ⊢[whnf?_]_ : Bool → Context → Set where

    ax   : {A : Type} →

         ------------------
         ⊢ʷʰⁿᶠ A ∷ A ^ ∷ []

    cut  : {Γ Δ : Context} {A : Type} {b₁ b₂ : Bool} →

         ⊢[whnf? b₁ ] A ∷ Γ → ⊢[whnf? b₂ ] A ^ ∷ Δ →
         -------------------------------------------
         ⊢[whnf? false ] Γ ++ Δ

    send : {Γ Δ : Context} {A B : Type} {b₁ b₂ : Bool} →

         ⊢[whnf? b₁ ] A ∷ Γ → ⊢[whnf? b₂ ] B ∷ Δ →
         -----------------------------------------
         ⊢ʷʰⁿᶠ A ⊗ B ∷ Γ ++ Δ

    recv : {Γ : Context} {A B : Type} {b : Bool} →

         ⊢[whnf? b ] A ∷ B ∷ Γ →
         -----------------------
         ⊢ʷʰⁿᶠ A ⅋ B ∷ Γ

    sel₁ : {Γ : Context} {A B : Type} {b : Bool} →

         ⊢[whnf? b ] A ∷ Γ →
         -------------------
         ⊢ʷʰⁿᶠ A ⊕ B ∷ Γ

    sel₂ : {Γ : Context} {A B : Type} {b : Bool} →

         ⊢[whnf? b ] B ∷ Γ →
         -------------------
         ⊢ʷʰⁿᶠ A ⊕ B ∷ Γ

    case : {Γ : Context} {A B : Type} {b₁ b₂ : Bool} →

         ⊢[whnf? b₁ ] A ∷ Γ → ⊢[whnf? b₂ ] B ∷ Γ →
         -----------------------------------------
         ⊢ʷʰⁿᶠ A & B ∷ Γ

    halt :

         ------------
         ⊢ʷʰⁿᶠ 𝟏 ∷ []

    wait : {Γ : Context} {b : Bool} →

         ⊢[whnf? b ] Γ →
         ---------------
         ⊢ʷʰⁿᶠ ⊥ ∷ Γ

    loop : {Γ : Context} →

         -----------
         ⊢ʷʰⁿᶠ ⊤ ∷ Γ

    mk?₁ : {Γ : Context} {A : Type} {b : Bool} →

         ⊢[whnf? b ] A ∷ Γ →
         -------------------
         ⊢ʷʰⁿᶠ ?[ 1 ] A ∷ Γ

    mk!₁ : {Γ : Context} {A : Type} {b : Bool} →

         ⊢[whnf? b ] A ∷ Γ →
         -------------------
         ⊢ʷʰⁿᶠ ![ 1 ] A ∷ Γ

    cont : {Γ : Context} {A : Type} {m n : ℕ⁺} {b : Bool} →

         ⊢[whnf? b ] ?[ m ] A ∷ ?[ n ] A ∷ Γ →
         -------------------------------------
         ⊢[whnf? b ] ?[ m + n ] A ∷ Γ

    pool : {Γ Δ : Context} {A : Type} {m n : ℕ⁺} {b : Bool} →

         ⊢[whnf? b ] ![ m ] A ∷ Γ → ⊢[whnf? b ] ![ n ] A ∷ Δ →
         -----------------------------------------------------
         ⊢[whnf? b ] ![ m + n ] A ∷ Γ ++ Δ

    exch : {Γ Δ : Context} {b : Bool} →

         Γ ∼[ bag ] Δ → ⊢[whnf? b ] Γ →
         ------------------------------
         ⊢[whnf? b ] Δ

cutIn : {Γ Δ : Context} {A : Type} {b₁ b₂ : Bool} (i : A ∈ Γ) (j : A ^ ∈ Δ) →

        ⊢[whnf? b₁ ] Γ → ⊢[whnf? b₂ ] Δ →
        ---------------------------------
        ⊢[whnf? false ] Γ - i ++ Δ - j

cutIn {Γ} {Δ} {A} i j P Q with ∈→++ i | ∈→++ j
... | (Γ₁ , Γ₂ , P.refl , p) | (Δ₁ , Δ₂ , P.refl , q) rewrite p | q
  = cut (exch (fwd [] Γ₁) P) (exch (fwd [] Δ₁) Q)


-- -}
-- -}
-- -}
-- -}
-- -}
