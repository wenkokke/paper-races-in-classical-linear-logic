open import Agda.Builtin.Nat
open import Agda.Builtin.FromNat
open import Data.Unit using (⊤)
open import Function using (const)

module Data.Nat.FromNat where

instance
  NumberNat : Number Nat
  NumberNat = record { Constraint = const ⊤ ; fromNat = λ n → n }
