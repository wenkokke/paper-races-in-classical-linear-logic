open import Data.List as L using (List; []; _∷_; _++_)
open import Data.List.Any.BagAndSetEquality as B
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Pos as ℕ⁺

open import nodcap.Base
open import nodcap.Typing as FF using (⊢_)

module nodcap.WHNF.Typing where

infix 1 ⊢ʷʰⁿᶠ_

data ⊢ʷʰⁿᶠ_ : Context → Set where

  ax   : {A : Type} →

       ------------------
       ⊢ʷʰⁿᶠ A ∷ A ^ ∷ []

  send : {Γ Δ : Context} {A B : Type} →

       ⊢ A ∷ Γ → ⊢ B ∷ Δ →
       --------------------
       ⊢ʷʰⁿᶠ A ⊗ B ∷ Γ ++ Δ

  recv : {Γ : Context} {A B : Type} →

       ⊢ A ∷ B ∷ Γ →
       ----------------
       ⊢ʷʰⁿᶠ A ⅋ B ∷ Γ

  sel₁ : {Γ : Context} {A B : Type} →

       ⊢ A ∷ Γ →
       ---------------
       ⊢ʷʰⁿᶠ A ⊕ B ∷ Γ

  sel₂ : {Γ : Context} {A B : Type} →

       ⊢ B ∷ Γ →
       ---------------
       ⊢ʷʰⁿᶠ A ⊕ B ∷ Γ

  case : {Γ : Context} {A B : Type} →

       ⊢ A ∷ Γ → ⊢ B ∷ Γ →
       -------------------
       ⊢ʷʰⁿᶠ A & B ∷ Γ

  halt :

       ------------
       ⊢ʷʰⁿᶠ 𝟏 ∷ []

  wait : {Γ : Context} →

       ⊢ Γ →
       -----------
       ⊢ʷʰⁿᶠ ⊥ ∷ Γ

  loop : {Γ : Context} →

       -----------
       ⊢ʷʰⁿᶠ ⊤ ∷ Γ

  mk?₁ : {Γ : Context} {A : Type} →

       ⊢ A ∷ Γ →
       -------------------------
       ⊢ʷʰⁿᶠ ?[ suc zero ] A ∷ Γ

  mk!₁ : {Γ : Context} {A : Type} →

       ⊢ A ∷ Γ →
       -------------------------
       ⊢ʷʰⁿᶠ ![ suc zero ] A ∷ Γ

  cont : {Γ : Context} {A : Type} {m n : ℕ⁺} →

       ⊢ʷʰⁿᶠ ?[ m ] A ∷ ?[ n ] A ∷ Γ →
       -------------------------------
       ⊢ʷʰⁿᶠ ?[ m + n ] A ∷ Γ

  pool : {Γ Δ : Context} {A : Type} {m n : ℕ⁺} →

       ⊢ʷʰⁿᶠ ![ m ] A ∷ Γ → ⊢ʷʰⁿᶠ ![ n ] A ∷ Δ →
       -----------------------------------------
       ⊢ʷʰⁿᶠ ![ m + n ] A ∷ Γ ++ Δ

  exch : {Γ Δ : Context} →

       Γ ∼[ bag ] Δ → ⊢ʷʰⁿᶠ Γ →
       ------------------------
       ⊢ʷʰⁿᶠ Δ

fromWHNF : ∀ {Γ} → ⊢ʷʰⁿᶠ Γ → ⊢ Γ
fromWHNF  ax        = FF.ax
fromWHNF (send P Q) = FF.send P Q
fromWHNF (recv P)   = FF.recv P
fromWHNF (sel₁ P)   = FF.sel₁ P
fromWHNF (sel₂ P)   = FF.sel₂ P
fromWHNF (case P Q) = FF.case P Q
fromWHNF  halt      = FF.halt
fromWHNF (wait P)   = FF.wait P
fromWHNF  loop      = FF.loop
fromWHNF (mk?₁ P)   = FF.mk?₁ P
fromWHNF (mk!₁ P)   = FF.mk!₁ P
fromWHNF (cont P)   = FF.cont (fromWHNF P)
fromWHNF (pool P Q) = FF.pool (fromWHNF P) (fromWHNF Q)
fromWHNF (exch π P) = FF.exch π (fromWHNF P)

-- -}
-- -}
-- -}
-- -}
-- -}
