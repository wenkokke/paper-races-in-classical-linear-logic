open import Category.Monad
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Pos as ℕ⁺ using (ℕ⁺; suc; _+_)
open import Data.List as L using (List; []; _∷_; _++_)
open import Data.List.Any as LA using (Any; here; there)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open import nodcap.Base
open import nodcap.Typing as FF using (⊢_)
open import nodcap.NF.Typing as NF using (⊢ⁿᶠ_)
import nodcap.NF.Axiom as NFA
import nodcap.NF.Cut as NFD
import nodcap.NF.CutND as NFND

module nodcap.Norm where

private
  open module LM {ℓ} = RawMonadPlus (L.monadPlus {ℓ})

nf : {Γ : Context} → ⊢ Γ → ⊢ⁿᶠ Γ
nf  FF.ax        = NFA.ax
nf (FF.cut  x y) = NFD.cut (nf x) (nf y)
nf (FF.send x y) = NF.send (nf x) (nf y)
nf (FF.recv x)   = NF.recv (nf x)
nf (FF.sel₁ x)   = NF.sel₁ (nf x)
nf (FF.sel₂ x)   = NF.sel₂ (nf x)
nf (FF.case x y) = NF.case (nf x) (nf y)
nf  FF.halt      = NF.halt
nf (FF.wait x)   = NF.wait (nf x)
nf  FF.loop      = NF.loop
nf (FF.mk?₁ x)   = NF.mk?₁ (nf x)
nf (FF.mk!₁ x)   = NF.mk!₁ (nf x)
nf (FF.cont x)   = NF.cont (nf x)
nf (FF.pool x y) = NF.pool (nf x) (nf y)
nf (FF.exch b x) = NF.exch b (nf x)

nfND : {Γ : Context} → ⊢ Γ → List (⊢ⁿᶠ Γ)
nfND  FF.ax        = return NFA.ax
nfND (FF.cut  x y) = nfND x >>= λ x → nfND y >>= λ y → NFND.cutND x y
nfND (FF.send x y) = nfND x >>= λ x → nfND y >>= λ y → return $ NF.send x y
nfND (FF.recv x)   = nfND x >>= λ x → return $ NF.recv x
nfND (FF.sel₁ x)   = nfND x >>= λ x → return $ NF.sel₁ x
nfND (FF.sel₂ x)   = nfND x >>= λ x → return $ NF.sel₂ x
nfND (FF.case x y) = nfND x >>= λ x → nfND y >>= λ y → return $ NF.case x y
nfND  FF.halt      = return NF.halt
nfND (FF.wait x)   = nfND x >>= λ x → return (NF.wait x)
nfND  FF.loop      = return NF.loop
nfND (FF.mk?₁ x)   = nfND x >>= λ x → return $ NF.mk?₁ x
nfND (FF.mk!₁ x)   = nfND x >>= λ x → return $ NF.mk!₁ x
nfND (FF.cont x)   = nfND x >>= λ x → return $ NF.cont x
nfND (FF.pool x y) = nfND x >>= λ x → nfND y >>= λ y → return $ NF.pool x y
nfND (FF.exch b x) = nfND x >>= λ x → return $ NF.exch b x

-- -}
-- -}
-- -}
-- -}
-- -}
