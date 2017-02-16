open import Category.Monad
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Pos as ℕ⁺ using (ℕ⁺; suc; _+_)
open import Data.List as L using (List; []; _∷_; _++_)
open import Data.List.Any as LA using (Any; here; there)
open import Data.Sum using (_⊎_; inj₁; inj₂)
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
normND (cut  x y) = normND x >>= λ x
                  → normND y >>= λ y
                  → NFND.cutND x y
normND (send x y) = NF.send <$> normND x ⊛ normND y
normND (recv x)   = NF.recv <$> normND x
normND (sel₁ x)   = NF.sel₁ <$> normND x
normND (sel₂ x)   = NF.sel₂ <$> normND x
normND (case x y) = NF.case <$> normND x ⊛ normND y
normND  halt      = return NF.halt
normND (wait x)   = NF.wait <$> normND x
normND  loop      = return NF.loop
normND (mk⅋₁ x)   = NF.mk⅋₁ <$> normND x
normND (mk⊗₁ x)   = NF.mk⊗₁ <$> normND x
normND (cont x)   = NF.cont <$> normND x
normND (pool x y) = NF.pool <$> normND x ⊛ normND y
normND (exch b x) = NF.exch b <$> normND x

⊢ⁿᶠ→⊢ : {Γ : Context} → ⊢ⁿᶠ Γ → ⊢ Γ
⊢ⁿᶠ→⊢ (NF.send x y) = send (⊢ⁿᶠ→⊢ x) (⊢ⁿᶠ→⊢ y)
⊢ⁿᶠ→⊢ (NF.recv x)   = recv (⊢ⁿᶠ→⊢ x)
⊢ⁿᶠ→⊢ (NF.sel₁ x)   = sel₁ (⊢ⁿᶠ→⊢ x)
⊢ⁿᶠ→⊢ (NF.sel₂ x)   = sel₂ (⊢ⁿᶠ→⊢ x)
⊢ⁿᶠ→⊢ (NF.case x y) = case (⊢ⁿᶠ→⊢ x) (⊢ⁿᶠ→⊢ y)
⊢ⁿᶠ→⊢  NF.halt      = halt
⊢ⁿᶠ→⊢ (NF.wait x)   = wait (⊢ⁿᶠ→⊢ x)
⊢ⁿᶠ→⊢  NF.loop      = loop
⊢ⁿᶠ→⊢ (NF.mk⅋₁ x)   = mk⅋₁ (⊢ⁿᶠ→⊢ x)
⊢ⁿᶠ→⊢ (NF.mk⊗₁ x)   = mk⊗₁ (⊢ⁿᶠ→⊢ x)
⊢ⁿᶠ→⊢ (NF.cont x)   = cont (⊢ⁿᶠ→⊢ x)
⊢ⁿᶠ→⊢ (NF.pool x y) = pool (⊢ⁿᶠ→⊢ x) (⊢ⁿᶠ→⊢ y)
⊢ⁿᶠ→⊢ (NF.exch x y) = exch x (⊢ⁿᶠ→⊢ y)
