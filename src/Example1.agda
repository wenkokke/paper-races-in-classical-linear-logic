open import IO using (run; putStrLn)
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Pos as ℕ⁺ using (ℕ⁺; suc)
open import Data.List using (List; []; _∷_)

open import nodcap.Base
open import nodcap.Cut
open import nodcap.Show

module Example1 where

Ticket  : Type
Ticket  = ⊥ ⊕ ⊥
ticket₁ : {Γ : Context} → ⊢ Γ → ⊢ Ticket ∷ Γ
ticket₁ x = sel₁ (wait x)
ticket₂ : {Γ : Context} → ⊢ Γ → ⊢ Ticket ∷ Γ
ticket₂ x = sel₂ (wait x)

server  : ⊢ ⅋[ suc (suc zero) ] Ticket ∷ 𝟏 ∷ []
server  = cont (mk⅋₁ (ticket₁ (mk⅋₁ (ticket₂ halt))))

Client  = Ticket ^
client₁ : ⊢ Client ∷ []
client₁ = case halt halt
client₂ : ⊢ Client ∷ []
client₂ = case halt halt
clients : ⊢ ⊗[ suc (suc zero) ] Client ∷ []
clients = pool (mk⊗₁ client₁) (mk⊗₁ client₂)

main = run (putStrLn (showTerm (cut server clients)))

