open import Coinduction
open import Category.Monad.State using (State; StateMonadState; module RawMonadState)
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Nat.Show as ℕS using ()
open import Data.Fin as F using (Fin; suc; zero)
open import Data.Pos as ℕ⁺
open import Data.List as L using (List; []; _∷_; length)
open import Data.List.Any as LA using (Any; here; there)
open import Data.List.Any.Properties as LAP using (++ˡ; ++ʳ)
open import Data.Product as PR using (proj₁)
open import Data.String as S using (String; _++_) 
open import Data.Stream as X using (Stream; _∷_; lookup)
open import Data.Vec as V using (Vec)
open import Function using (_∘_)
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse as I using ()
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_)

open import Logic.Context
open import nodcap.Base
open import nodcap.Typing

module nodcap.Show where

open I.Inverse using (to; from)

showTerm : {Γ : Context} → ⊢ Γ → String
showTerm {Γ} x = proj₁ (go bound x state)
  where
    open RawMonadState (StateMonadState (Stream String))

    names : Stream String
    names = X.map (("x" S.++_) ∘ ℕS.show) (naturals 0)
      where
        naturals : ℕ → Stream ℕ
        naturals n = n ∷ ♯ naturals (suc n)

    fresh : State (Stream String) String
    fresh = get >>= λ{(x ∷ xs) → put (♭ xs) >> return x}

    go : {Γ : Context} (bound : {w : Type} → w ∈ Γ → String) → ⊢ Γ → State (Stream String) String
    go bound ax
      = return (boundˣ ++ "↔" ++ boundʸ)
      where
        boundˣ = bound (here P.refl)
        boundʸ = bound (there (here P.refl))
    go bound (cut {Γ} {Δ} {A} x y) = fresh >>= withFresh
      where
        withFresh : String → State (Stream String) String
        withFresh boundˣ
          = go bound₁ x >>= λ x'
          → go bound₂ y >>= λ y'
          → return ("ν" ++ boundˣ ++ ".(" ++ x' ++ "|" ++ y' ++ ")")
          where
            bound₁ : {w : Type} → w ∈ A ∷ Γ → String
            bound₁ (here px) = boundˣ
            bound₁ (there i) = bound (++ˡ i)
            bound₂ : {w : Type} → w ∈ A ^ ∷ Δ → String
            bound₂ (here px) = boundˣ
            bound₂ (there i) = bound (++ʳ Γ i)
    go bound (send {Γ} {Δ} {A} {B} x y) = fresh >>= withFresh
      where
        withFresh : String → State (Stream String) String
        withFresh boundʸ
          = go bound₁ x >>= λ x'
          → go bound₂ y >>= λ y'
          → return (boundˣ ++ "[" ++ boundʸ ++ "].(" ++ x' ++ "|" ++ y' ++ ")")
          where
            boundˣ = bound (here P.refl)
            bound₁ : {w : Type} → w ∈ A ∷ Γ → String
            bound₁ (here px) = boundʸ
            bound₁ (there i) = bound (there (++ˡ i))
            bound₂ : {w : Type} → w ∈ B ∷ Δ → String
            bound₂ (here px) = bound (here P.refl)
            bound₂ (there i) = bound (there (++ʳ Γ i))
    go bound (recv {Γ} {A} {B} x) = fresh >>= withFresh
      where
        withFresh : String → State (Stream String) String
        withFresh boundʸ
          = go bound₁ x >>= λ x'
          → return (boundˣ ++ "(" ++ boundʸ ++ ")." ++ x')
          where
            boundˣ = bound (here P.refl)
            bound₁ : {w : Type} → w ∈ A ∷ B ∷ Γ → String
            bound₁ (here px) = boundʸ
            bound₁ (there (here px)) = boundˣ
            bound₁ (there (there i)) = bound (there i)
    go bound (sel₁ {Γ} {A} {B} x)
      = go bound₁ x >>= λ x'
      → return (boundˣ ++ "[inl]." ++ x')
      where
        boundˣ = bound (here P.refl)
        bound₁ : {w : Type} → w ∈ A ∷ Γ → String
        bound₁ (here px) = boundˣ
        bound₁ (there i) = bound (there i)
    go bound (sel₂ {Γ} {A} {B} x)
      = go bound₁ x >>= λ x'
      → return (boundˣ ++ "[inr]." ++ x')
      where
        boundˣ = bound (here P.refl)
        bound₁ : {w : Type} → w ∈ B ∷ Γ → String
        bound₁ (here px) = boundˣ
        bound₁ (there i) = bound (there i)
    go bound (case {Γ} {A} {B} x y)
      = go bound₁ x >>= λ x'
      → go bound₂ y >>= λ y'
      → return ("case " ++ boundˣ ++ " {" ++ x' ++ ";" ++ y' ++ "}")
      where
        boundˣ = bound (here P.refl)
        bound₁ : {w : Type} → w ∈ A ∷ Γ → String
        bound₁ (here px) = boundˣ
        bound₁ (there i) = bound (there i)
        bound₂ : {w : Type} → w ∈ B ∷ Γ → String
        bound₂ (here px) = boundˣ
        bound₂ (there i) = bound (there i)
    go bound halt
      = return (boundˣ ++ "[].0")
      where
        boundˣ = bound (here P.refl)
    go bound (wait x)
      = go (bound ∘ there) x >>= λ x'
      → return (boundˣ ++ "()." ++ x')
      where
        boundˣ = bound (here P.refl)
    go bound loop
      = return ("case " ++ boundˣ ++ " {;}")
      where
        boundˣ = bound (here P.refl)
    go bound (mk⅋₁ {Γ} {A} x) = fresh >>= withFresh
      where
        withFresh : String → State (Stream String) String
        withFresh boundʸ
          = go bound₁ x >>= λ x'
          → return ("?" ++ boundˣ ++ "[" ++ boundʸ ++ "]." ++ x')
          where
            boundˣ = bound (here P.refl)
            bound₁ : {w : Type} → w ∈ A ∷ Γ → String
            bound₁ (here px) = boundʸ
            bound₁ (there i) = bound (there i)
    go bound (mk⊗₁ {Γ} {A} x) = fresh >>= withFresh
      where
        withFresh : String → State (Stream String) String
        withFresh boundʸ
          = go bound₁ x >>= λ x'
          → return ("!" ++ boundˣ ++ "(" ++ boundʸ ++ ")." ++ x')
          where
            boundˣ = bound (here P.refl)
            bound₁ : {w : Type} → w ∈ A ∷ Γ → String
            bound₁ (here px) = boundʸ
            bound₁ (there i) = bound (there i)
    go bound (cont {Γ} {A} {m} {n} x)
      = go bound₁ x
      where
        boundˣ = bound (here P.refl)
        bound₁ : {w : Type} → w ∈ ⅋[ m ] A ∷ ⅋[ n ] A ∷ Γ → String
        bound₁ (here px) = boundˣ
        bound₁ (there (here px)) = boundˣ
        bound₁ (there (there i)) = bound (there i)
    go bound (pool {Γ} {Δ} {A} {m} {n} x y)
      = go bound₁ x >>= λ x'
      → go bound₂ y >>= λ y'
      → return ("(" ++ x' ++ "|" ++ y' ++ ")")
      where
        boundˣ = bound (here P.refl)
        bound₁ : {w : Type} → w ∈ ⊗[ m ] A ∷ Γ → String
        bound₁ (here px) = boundˣ
        bound₁ (there i) = bound (there (++ˡ i))
        bound₂ : {w : Type} → w ∈ ⊗[ n ] A ∷ Δ → String
        bound₂ (here px) = boundˣ
        bound₂ (there i) = bound (there (++ʳ Γ i))
    go bound (exch b x) = go (bound ∘ (to b ⟨$⟩_)) x

    bound : {w : Type} → w ∈ Γ → String
    bound i = V.lookup (toFin i) (X.take (length Γ) names)
      where
        toFin : {Γ : Context} {w : Type} → w ∈ Γ → Fin (length Γ)
        toFin (here px) = zero
        toFin (there i) = suc (toFin i)

    state : Stream String
    state = X.drop (length Γ) names
