open import IO using (run; putStrLn)
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Pos as ℕ⁺ using (ℕ⁺; suc)
open import Data.List using (List; []; _∷_)

open import nodcap.Base
open import nodcap.Show
open import nodcap.NF.Typing
open import nodcap.NF.Cut

module Example1 where

Ticket  : Type
Ticket  = ⊥ ⊕ ⊥
ticket₁ : {Γ : Context} → ⊢ⁿᶠ Γ → ⊢ⁿᶠ Ticket ∷ Γ
ticket₁ x = sel₁ (wait x)
ticket₂ : {Γ : Context} → ⊢ⁿᶠ Γ → ⊢ⁿᶠ Ticket ∷ Γ
ticket₂ x = sel₂ (wait x)

server  : ⊢ⁿᶠ ⅋[ suc (suc zero) ] Ticket ∷ 𝟏 ∷ []
server  = cont (mk⅋₁ (ticket₁ (mk⅋₁ (ticket₂ halt))))

Client  = Ticket ^
client₁ : ⊢ⁿᶠ Client ∷ []
client₁ = case halt halt
client₂ : ⊢ⁿᶠ Client ∷ []
client₂ = case halt halt
clients : ⊢ⁿᶠ ⊗[ suc (suc zero) ] Client ∷ []
clients = pool (mk⊗₁ client₁) (mk⊗₁ client₂)

main = run (putStrLn (showTerm (cut server clients)))

