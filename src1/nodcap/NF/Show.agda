module nodcap.NF.Show where

open import Data.String using (String) 

open import nodcap.Base
open import nodcap.NF.Typing

import nodcap.Show as S

showTerm : {Γ : Environment} → ⊢ⁿᶠ Γ → String
showTerm {Γ} x = S.showTerm (fromNF x)
