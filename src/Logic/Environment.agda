open import Data.Nat
open import Data.Product
open import Data.List


module Logic.Environment where

data Env : (Γ : List Set) → Set where
  [] : Env []
  _∷_ : {A : Set} (x : A) {Γ : List Set} (xs : Env Γ) → Env (A ∷ Γ)

splitEnv : {Γ Δ : List Set} → Env (Γ ++ Δ) → Env Γ × Env Δ
splitEnv {[]}         zs  = [] , zs
splitEnv {A ∷ Γ} (x ∷ zs) with splitEnv {Γ} zs
splitEnv {A ∷ Γ} (x ∷ zs) | (xs , ys) = x ∷ xs , ys


-- -}
-- -}
-- -}
-- -}
