open import Category.Monad
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Pos as ℕ⁺ using (ℕ⁺; suc; _+_)
open import Data.List as L using (List; []; _∷_; _++_)
open import Data.List.Any as LA using (Any; here; there)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open import nodcap.Base
open import nodcap.Typing
open import nodcap.NF.Typing as NF using (⊢ⁿᶠ_)
import nodcap.NF.Axiom as NFA
import nodcap.NF.Cut as NFD
import nodcap.NF.CutND as NFND

module nodcap.Norm where

private
  open module LM {ℓ} = RawMonadPlus (L.monadPlus {ℓ})

norm : {Γ : Context} → ⊢ Γ → ⊢ⁿᶠ Γ
norm  ax        = NFA.ax
norm (cut  x y) = NFD.cut (norm x) (norm y)
norm (send x y) = NF.send (norm x) (norm y)
norm (recv x)   = NF.recv (norm x)
norm (sel₁ x)   = NF.sel₁ (norm x)
norm (sel₂ x)   = NF.sel₂ (norm x)
norm (case x y) = NF.case (norm x) (norm y)
norm  halt      = NF.halt
norm (wait x)   = NF.wait (norm x)
norm  loop      = NF.loop
norm (mk⅋₁ x)   = NF.mk⅋₁ (norm x)
norm (mk⊗₁ x)   = NF.mk⊗₁ (norm x)
norm (cont x)   = NF.cont (norm x)
norm (pool x y) = NF.pool (norm x) (norm y)
norm (exch b x) = NF.exch b (norm x)

normND : {Γ : Context} → ⊢ Γ → List (⊢ⁿᶠ Γ)
normND  ax        = return NFA.ax
normND (cut  x y) = normND x >>= λ x → normND y >>= λ y → NFND.cutND x y
normND (send x y) = normND x >>= λ x → normND y >>= λ y → return $ NF.send x y
normND (recv x)   = normND x >>= λ x → return $ NF.recv x
normND (sel₁ x)   = normND x >>= λ x → return $ NF.sel₁ x
normND (sel₂ x)   = normND x >>= λ x → return $ NF.sel₂ x
normND (case x y) = normND x >>= λ x → normND y >>= λ y → return $ NF.case x y
normND  halt      = return NF.halt
normND (wait x)   = normND x >>= λ x → return (NF.wait x)
normND  loop      = return NF.loop
normND (mk⅋₁ x)   = normND x >>= λ x → return $ NF.mk⅋₁ x
normND (mk⊗₁ x)   = normND x >>= λ x → return $ NF.mk⊗₁ x
normND (cont x)   = normND x >>= λ x → return $ NF.cont x
normND (pool x y) = normND x >>= λ x → normND y >>= λ y → return $ NF.pool x y
normND (exch b x) = normND x >>= λ x → return $ NF.exch b x

unNorm : {Γ : Context} → ⊢ⁿᶠ Γ → ⊢ Γ
unNorm (NF.send x y) = send (unNorm x) (unNorm y)
unNorm (NF.recv x)   = recv (unNorm x)
unNorm (NF.sel₁ x)   = sel₁ (unNorm x)
unNorm (NF.sel₂ x)   = sel₂ (unNorm x)
unNorm (NF.case x y) = case (unNorm x) (unNorm y)
unNorm  NF.halt      = halt
unNorm (NF.wait x)   = wait (unNorm x)
unNorm  NF.loop      = loop
unNorm (NF.mk⅋₁ x)   = mk⅋₁ (unNorm x)
unNorm (NF.mk⊗₁ x)   = mk⊗₁ (unNorm x)
unNorm (NF.cont x)   = cont (unNorm x)
unNorm (NF.pool x y) = pool (unNorm x) (unNorm y)
unNorm (NF.exch x y) = exch x (unNorm y)

-- -}
-- -}
-- -}
-- -}
-- -}
