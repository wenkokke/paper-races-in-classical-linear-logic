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
open import nodcap.WHNF.Typing as WHNF using (⊢ʷʰⁿᶠ_)
import nodcap.NF.Axiom as NFA
import nodcap.NF.Cut as NFD
import nodcap.NF.CutND as NFND

module nodcap.Norm where

private
  open module LM {ℓ} = RawMonadPlus (L.monadPlus {ℓ})

norm : {Γ : Context} → ⊢ Γ → ⊢ⁿᶠ Γ
norm  FF.ax        = NFA.ax
norm (FF.cut  x y) = NFD.cut (norm x) (norm y)
norm (FF.send x y) = NF.send (norm x) (norm y)
norm (FF.recv x)   = NF.recv (norm x)
norm (FF.sel₁ x)   = NF.sel₁ (norm x)
norm (FF.sel₂ x)   = NF.sel₂ (norm x)
norm (FF.case x y) = NF.case (norm x) (norm y)
norm  FF.halt      = NF.halt
norm (FF.wait x)   = NF.wait (norm x)
norm  FF.loop      = NF.loop
norm (FF.mk?₁ x)   = NF.mk?₁ (norm x)
norm (FF.mk!₁ x)   = NF.mk!₁ (norm x)
norm (FF.cont x)   = NF.cont (norm x)
norm (FF.pool x y) = NF.pool (norm x) (norm y)
norm (FF.exch b x) = NF.exch b (norm x)

normND : {Γ : Context} → ⊢ Γ → List (⊢ⁿᶠ Γ)
normND  FF.ax        = return NFA.ax
normND (FF.cut  x y) = normND x >>= λ x → normND y >>= λ y → NFND.cutND x y
normND (FF.send x y) = normND x >>= λ x → normND y >>= λ y → return $ NF.send x y
normND (FF.recv x)   = normND x >>= λ x → return $ NF.recv x
normND (FF.sel₁ x)   = normND x >>= λ x → return $ NF.sel₁ x
normND (FF.sel₂ x)   = normND x >>= λ x → return $ NF.sel₂ x
normND (FF.case x y) = normND x >>= λ x → normND y >>= λ y → return $ NF.case x y
normND  FF.halt      = return NF.halt
normND (FF.wait x)   = normND x >>= λ x → return (NF.wait x)
normND  FF.loop      = return NF.loop
normND (FF.mk?₁ x)   = normND x >>= λ x → return $ NF.mk?₁ x
normND (FF.mk!₁ x)   = normND x >>= λ x → return $ NF.mk!₁ x
normND (FF.cont x)   = normND x >>= λ x → return $ NF.cont x
normND (FF.pool x y) = normND x >>= λ x → normND y >>= λ y → return $ NF.pool x y
normND (FF.exch b x) = normND x >>= λ x → return $ NF.exch b x

-- -}
-- -}
-- -}
-- -}
-- -}
