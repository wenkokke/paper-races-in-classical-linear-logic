open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Pos as ℕ⁺
open import Data.List as L using (List; []; _∷_; _++_)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_)

open import Logic.Context
open import nodcap.Base
open import nodcap.NF.Typing

module nodcap.NF.Axiom where

{-# TERMINATING #-}
-- Theorem:
--   Identity expansion.
--
-- Problematic calls:
--   * in the recursive calls under ⅋n and ⊗n, it is the
--     size of the resource index which is decreasing, not
--     the size of the type itself.
ax : {A : Type} → ⊢ⁿᶠ A ∷ A ^ ∷ []
ax { 𝟏 }
  = exch (bbl [])
  $ wait halt
ax { ⊥ }
  = wait halt
ax { 𝟎 }
  = exch (bbl [])
  $ loop
ax { ⊤ }
  = loop
ax { A ⊗ B }
  = exch (bbl [])
  $ recv
  $ exch (bwd [] (_ ∷ _ ∷ []))
  $ send ax ax
ax { A ⅋ B }
  = recv
  $ exch (bwd [] (_ ∷ _ ∷ []))
  $ send
  ( exch (bbl []) ax )
  ( exch (bbl []) ax )
ax { A ⊕ B }
  = exch (bbl [])
  $ case
  ( exch (bbl [])
  $ sel₁ ax
  )
  ( exch (bbl [])
  $ sel₂ ax
  )
ax { A & B }
  = case
  ( exch (bbl [])
  $ sel₁
  $ exch (bbl []) ax
  )
  ( exch (bbl [])
  $ sel₂
  $ exch (bbl []) ax
  )
ax { ![ suc zero ] A }
  = mk!₁
  $ exch (bbl [])
  $ mk?₁
  $ exch (bbl []) ax
ax { ![ suc (suc n) ] A }
  = exch (bbl [])
  $ cont {m = suc zero} {n = suc n}
  $ exch (bwd [] (_ ∷ _ ∷ []))
  $ pool {m = suc zero} {n = suc n}
  ( ax )
  ( ax )
ax { ?[ suc zero ] A }
  = mk?₁
  $ exch (bbl [])
  $ mk!₁
  $ exch (bbl []) ax
ax { ?[ suc (suc n) ] A }
  = cont {m = suc zero} {n = suc n}
  $ exch (bwd [] (_ ∷ _ ∷ []))
  $ pool {m = suc zero} {n = suc n}
  ( exch (bbl []) ax )
  ( exch (bbl []) ax )
