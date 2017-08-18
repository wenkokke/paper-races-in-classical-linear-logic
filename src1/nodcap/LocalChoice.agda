module nodcap.LocalChoice where

open import Algebra
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Pos as ℕ⁺
open import Data.List as L using (List; []; _∷_; _++_)
open import Data.List.Any as LA using (Any; here; there)
open import Data.List.Any.BagAndSetEquality as B
open import Data.Product as PR using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_$_; flip)
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse as I using ()
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_)

open import Data.Environment
open import nodcap.Base
open import nodcap.Typing

open I.Inverse using (to; from)
private module ++ {a} {A : Set a} = Monoid (L.monoid A)


-- We define local choice as follows:
_or_ : {A : Type} → ⊢ A ∷ [] → ⊢ A ∷ [] → ⊢ A ∷ []
x or y = cut (pool (in? x) (in? y)) out
  where
    in? : ∀ {A} → ⊢ A ∷ [] → ⊢ ![ suc 0 ] (𝟏 & A) ∷ []
    in? x = mk!₁ $ case halt x
    out : ∀ {A} → ⊢ ?[ suc 1 ] (⊥ ⊕ (A ^)) ∷ A ∷ []
    out = cont $ mk?₁ $ sel₁ $ wait $ mk?₁ $ sel₂ $ exch (bbl []) $ ax

-- However, Luís Caires defines local choice with contexts. For this to work we
-- need an additional trick: conversion between contexts and types.

-- We can represent a context as a sequence of pars.
⅋[_] : Environment → Type
⅋[ [] ]    = ⊥
⅋[ A ∷ Γ ] = A ⅋ ⅋[ Γ ]

-- See:
recv⋆ : {Γ Δ : Environment} →

  ⊢ Γ ++ Δ →
  ------------
  ⊢ ⅋[ Γ ] ∷ Δ

recv⋆ {[]}    x = wait x
recv⋆ {A ∷ Γ} x = recv $ exch (bbl []) $ recv⋆ $ exch (bwd [] Γ) $ x

-- In order to reverse this, we need to show that the `recv` rule is invertible.
-- Fortunately, it is:
recv⁻¹ : {Γ : Environment} {A B : Type} →

  ⊢ A ⅋ B ∷ Γ →
  -------------
  ⊢ A ∷ B ∷ Γ

recv⁻¹ {Γ} {A} {B} x
  = exch (swp₂ (A ∷ B ∷ []))
  $ cut {Γ} {A ∷ B ∷ []} x
  $ send
  ( exch (bbl []) ax )
  ( exch (bbl []) ax )

-- It should come as no surprise that the repeated application of `recv` is also
-- invertible.
recv⋆⁻¹ : {Γ Δ : Environment} →

  ⊢ ⅋[ Γ ] ∷ Δ →
  --------------
  ⊢ Γ ++ Δ

recv⋆⁻¹ {[]}    x = cut halt x
recv⋆⁻¹ {A ∷ Γ} x = exch (fwd [] Γ) $ recv⋆⁻¹ {Γ} $ exch (bbl []) $ recv⁻¹ x

-- Using these additional derivable operators, we can represent the version of
-- local choice as used by Luís Caires:
_or⋆_ : {Γ : Environment} → ⊢ Γ → ⊢ Γ → ⊢ Γ
_or⋆_ {Γ} x y
  = P.subst ⊢_ (proj₂ ++.identity Γ)
  $ recv⋆⁻¹ {Γ}
  $  ( recv⋆ $ P.subst ⊢_ (P.sym $ proj₂ ++.identity Γ) x )
  or ( recv⋆ $ P.subst ⊢_ (P.sym $ proj₂ ++.identity Γ) y )

-- -}
-- -}
-- -}
-- -}
-- -}
