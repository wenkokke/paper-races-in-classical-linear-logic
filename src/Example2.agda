open import IO using (run; putStrLn; mapM′; _>>_)
open import Coinduction using (♯_)
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Pos as ℕ⁺ using (ℕ⁺; suc)
open import Data.String using (String)
open import Data.List using (List; []; _∷_; map)
open import Data.Colist using (fromList)
open import Function using (_$_; _∘_)

open import Logic.Context
open import nodcap.Base
open import nodcap.Typing
open import nodcap.Norm
open import nodcap.Show renaming (showTerm to show)
open import nodcap.NF.Show renaming (showTerm to showNF)

module Example2 where

Ticket UserId Sale Receipt : Type
Ticket  = ⊥ ⊕ ⊥
UserId  = 𝟏 ⊕ 𝟏
Sale    = UserId ⊸ Ticket
Receipt = UserId ⊗ Ticket

ticket₁ ticket₂ : {Γ : Context} → ⊢ Γ → ⊢ Ticket ∷ Γ
ticket₁ x = sel₁ (wait x)
ticket₂ x = sel₂ (wait x)

sale₁ sale₂ : {Γ : Context} → ⊢ Γ → ⊢ Sale ∷ Receipt ∷ Γ
sale₁ x
  = recv
  $ exch (bbl [])
  $ ticket₁
  $ exch (bbl [])
  $ send ax (ticket₁ x)
sale₂ x
  = recv
  $ exch (bbl [])
  $ ticket₂
  $ exch (bbl [])
  $ send ax (ticket₂ x)

client₁ client₂ : ⊢ Sale ^ ∷ []
client₁ = send (sel₁ halt) (case halt halt)
client₂ = send (sel₂ halt) (case halt halt)

server : ⊢ ⅋[ suc (suc zero) ] Sale ∷ Receipt ∷ Receipt ∷ 𝟏 ∷ []
server
  = cont
  $ mk⅋₁
  $ exch (bwd (_ ∷ []) (_ ∷ []))
  $ sale₁
  $ mk⅋₁
  $ sale₂
  $ halt

clients : ⊢ ⊗[ suc (suc zero) ] (Sale ^) ∷ []
clients
  = pool (mk⊗₁ client₁) (mk⊗₁ client₂)


main = run (mapM′ putStrLn (fromList strs))
  where
    strs : List String
    strs = "Server:"
         ∷ show server
         ∷ "Clients:"
         ∷ show clients
         ∷ "Result:"
         ∷ map showNF (normND (cut server clients))

-- -}
-- -}
-- -}
-- -}
-- -}
