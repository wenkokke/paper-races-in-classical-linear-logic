open import Agda.Builtin.FromNat using (Number)
open import Data.Nat using (ℕ)
open import Data.Unit using (⊤)
open import Function using (const)

module cpnd.util where

instance
  Number-ℕ : Number ℕ
  Number-ℕ = record
    { Constraint = const ⊤
    ; fromNat    = λ{n → n}
    }

record Pluggable (C E CE : Set) : Set where
  infixl 30 _[_]
  field
    _[_] : C → E → CE
