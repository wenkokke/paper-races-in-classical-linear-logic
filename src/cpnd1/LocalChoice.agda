module LocalChoice where

open import IO using (run; putStrLn; mapM′; _>>_)
open import Coinduction using (♯_)
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Pos as ℕ⁺ using (ℕ⁺; suc)
open import Data.String using (String)
open import Data.List using (List; []; _∷_; map)
open import Data.Colist using (fromList)
open import Function using (_$_; _∘_)

open import Data.Environment
open import nodcap.Base
open import nodcap.Typing
open import nodcap.LocalChoice
open import nodcap.Norm
open import nodcap.Show renaming (showTerm to show)
open import nodcap.NF.Show renaming (showTerm to showNF)

Bit : Type
Bit = 𝟏 ⊕ 𝟏

bit₁ bit₂ : ⊢ Bit ∷ []
bit₁ = sel₁ halt
bit₂ = sel₂ halt

randomBit : ⊢ Bit ∷ []
randomBit = bit₁ or bit₂

main = run (mapM′ putStrLn (fromList strs))
  where
    strs = "Process:"
         ∷ show randomBit
         ∷ "Result:"
         ∷ map showNF (nfND randomBit)

-- -}
-- -}
-- -}
-- -}
-- -}
