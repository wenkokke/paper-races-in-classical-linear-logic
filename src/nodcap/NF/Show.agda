open import Coinduction
open import Category.Monad.State using (State; StateMonadState; module RawMonadState)
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Nat.Show as ℕS using ()
open import Data.Fin as F using (Fin; suc; zero)
open import Data.Pos as ℕ⁺
open import Data.List as L using (List; []; _∷_; length)
open import Data.List.Any as LA using (Any; here; there)
open import Data.List.Any.Properties as LAP using (++ˡ; ++ʳ)
open import Data.Product as PR using (proj₁)
open import Data.String as S using (String; _++_) 
open import Data.Stream as X using (Stream; _∷_; lookup)
open import Data.Vec as V using (Vec)
open import Function using (_∘_)
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse as I using ()
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_)

open import Logic.Context
open import nodcap.Base
open import nodcap.NF.Typing
open import nodcap.Norm
import nodcap.Show as S

module nodcap.NF.Show where

showTerm : {Γ : Context} → ⊢ⁿᶠ Γ → String
showTerm {Γ} x = S.showTerm (unNorm x) 
