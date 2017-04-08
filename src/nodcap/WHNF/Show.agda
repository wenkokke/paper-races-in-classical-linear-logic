open import Data.String using (String)

open import nodcap.Base
open import nodcap.WHNF.Typing

import nodcap.Show as S

module nodcap.WHNF.Show where

showTerm : {Γ : Context} → ⊢ʷʰⁿᶠ Γ → String
showTerm {Γ} x = S.showTerm (fromWHNF x)
