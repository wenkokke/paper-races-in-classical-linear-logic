open import Algebra                  using (module Monoid)
open import Data.List                using (List; _∷_; []; _++_)
open import Data.List.Any            using (here; there)
open import Data.List.Any.BagAndSetEquality as B
open import Data.Sum                 using (_⊎_; inj₁; inj₂)
open import Data.Product             using (Σ-syntax; _,_; proj₁; proj₂)
open import Function                 using (flip; _$_)
open import Function.Equality        using (_⟨$⟩_)
open import Function.Inverse         using (id; sym; _∘_)
open        Function.Inverse.Inverse using (to; from)
open import Logic.Context
open import Relation.Binary.PropositionalEquality as P using (_≡_)


module RCP where


data Type : Set where
  𝟏 : Type
  ⊥ : Type
  𝟎 : Type
  ⊤ : Type
  _⊗_ : (A B : Type) → Type
  _⅋_ : (A B : Type) → Type
  _⊕_ : (A B : Type) → Type
  _&_ : (A B : Type) → Type


-- Duality.

_^ : Type → Type
𝟏 ^ = ⊥
⊥ ^ = 𝟏
𝟎 ^ = ⊤
⊤ ^ = 𝟎
(A ⊗ B) ^ = (A ^) ⅋ (B ^)
(A ⅋ B) ^ = (A ^) ⊗ (B ^)
(A ⊕ B) ^ = (A ^) & (B ^)
(A & B) ^ = (A ^) ⊕ (B ^)

^-inv : ∀ A →  A ^ ^ ≡ A
^-inv 𝟏 = P.refl
^-inv ⊥ = P.refl
^-inv 𝟎 = P.refl
^-inv ⊤ = P.refl
^-inv (A ⊗ B) = P.cong₂ _⊗_ (^-inv A) (^-inv B)
^-inv (A ⅋ B) = P.cong₂ _⅋_ (^-inv A) (^-inv B)
^-inv (A ⊕ B) = P.cong₂ _⊕_ (^-inv A) (^-inv B)
^-inv (A & B) = P.cong₂ _&_ (^-inv A) (^-inv B)


-- Polarities.

data Pos : Type → Set where
  𝟏 : Pos 𝟏
  𝟎 : Pos 𝟎
  _⊗_ : (A B : Type) → Pos (A ⊗ B)
  _⊕_ : (A B : Type) → Pos (A ⊕ B)

data Neg : Type → Set where
  ⊥ : Neg ⊥
  ⊤ : Neg ⊤
  _⅋_ : (A B : Type) → Neg (A ⅋ B)
  _&_ : (A B : Type) → Neg (A & B)

pol : ∀ A → Pos A ⊎ Neg A
pol 𝟏 = inj₁ 𝟏
pol ⊥ = inj₂ ⊥
pol 𝟎 = inj₁ 𝟎
pol ⊤ = inj₂ ⊤
pol (A ⊗ B) = inj₁ (A ⊗ B)
pol (A ⅋ B) = inj₂ (A ⅋ B)
pol (A ⊕ B) = inj₁ (A ⊕ B)
pol (A & B) = inj₂ (A & B)

^-posneg : ∀ {A} → Pos A → Neg (A ^)
^-posneg 𝟏 = ⊥
^-posneg 𝟎 = ⊤
^-posneg (A ⊗ B) = (A ^) ⅋ (B ^)
^-posneg (A ⊕ B) = (A ^) & (B ^)

^-negpos : ∀ {A} → Neg A → Pos (A ^)
^-negpos ⊥ = 𝟏
^-negpos ⊤ = 𝟎
^-negpos (A ⅋ B) = (A ^) ⊗ (B ^)
^-negpos (A & B) = (A ^) ⊕ (B ^)


-- Contexts.

Context : Set
Context = List Type

open Data.List.Any.Membership-≡
private
  module ++ {a} {A : Set a} = Monoid (Data.List.monoid A)


-- Typing Rules.

infix 1 ⊢_

data ⊢_ : Context → Set where

  send : {Γ Δ : Context} {A B : Type} →

         ⊢ A ∷ Γ → ⊢ B ∷ Δ →
         -------------------
         ⊢ A ⊗ B ∷ Γ ++ Δ

  recv : {Γ : Context} {A B : Type} →

         ⊢ A ∷ B ∷ Γ →
         -------------
         ⊢ A ⅋ B ∷ Γ

  sel₁ : {Γ : Context} {A B : Type} →

         ⊢ A ∷ Γ →
         -----------
         ⊢ A ⊕ B ∷ Γ

  sel₂ : {Γ : Context} {A B : Type} →

         ⊢ B ∷ Γ →
         -----------
         ⊢ A ⊕ B ∷ Γ

  case : {Γ : Context} {A B : Type} →

         ⊢ A ∷ Γ → ⊢ B ∷ Γ →
         -------------------
         ⊢ A & B ∷ Γ

  halt : --------
         ⊢ 𝟏 ∷ []

  wait : {Γ : Context} →

         ⊢ Γ →
         -------
         ⊢ ⊥ ∷ Γ

  loop : {Γ : Context} →

         -------
         ⊢ ⊤ ∷ Γ

  exch : {Γ Δ : Context} →

         Γ ∼[ bag ] Δ → ⊢ Γ →
         --------------------
         ⊢ Δ

mutual

  -- Principal Cuts.
  cut : {Γ Δ : Context} {A : Type} →

        ⊢ A ∷ Γ → ⊢ A ^ ∷ Δ →
        ---------------------
        ⊢ Γ ++ Δ

  cut {.[]} {Δ} {𝟏} halt (wait g) = g
  cut {Γ} {.[]} {⊥} (wait f) halt rewrite proj₂ ++.identity Γ = f
  cut {.(Γ₁ ++ Γ₂)} {Δ} {A = A₁ ⊗ A₂} (send {Γ₁} {Γ₂} f h) (recv g)
    rewrite ++.assoc Γ₁ Γ₂ Δ
      = exch (swp [] Γ₁ Γ₂)
      $ cut h
      $ exch (fwd [] Γ₁)
      $ cut f g
  cut {Γ} {.(Δ₁ ++ Δ₂)} {A = A₁ ⅋ A₂} (recv f) (send {Δ₁} {Δ₂} g h)
    rewrite P.sym (++.assoc Γ Δ₁ Δ₂)
      = flip cut h
      $ cut f g
  cut {Γ} {Δ} {A₁ ⊕ A₂} (sel₁ f) (case g h) = cut f g
  cut {Γ} {Δ} {A₁ ⊕ A₂} (sel₂ f) (case g h) = cut f h
  cut {Γ} {Δ} {A₁ & A₂} (case f h) (sel₁ g) = cut f g
  cut {Γ} {Δ} {A₁ & A₂} (case f h) (sel₂ g) = cut h g

  cut {Γ} {Δ} {A} f (exch eq g)
      = exch (B.++-cong {xs₁ = Γ} id (del-from eq (here P.refl)))
      $ cutIn (here P.refl) (from eq ⟨$⟩ here P.refl) f g
  cut {Γ} {Δ} {A} (exch eq f) g
      = exch (B.++-cong {ys₁ = Δ} (del-from eq (here P.refl)) id)
      $ cutIn (from eq ⟨$⟩ here P.refl) (here P.refl) f g

  -- Permutation Cuts,
  cutIn : {Γ Δ : Context} {A : Type} →
         (i : A ∈ Γ) (j : A ^ ∈ Δ) →

         ⊢ Γ → ⊢ Δ →
         ------------------
         ⊢ Γ - i ++ Δ - j

  cutIn (here P.refl) (here P.refl) f g = cut f g

  -- Left.
  cutIn {.(A ⊗ B ∷ Γ₁ ++ Γ₂)} {Δ} (there i) j (send {Γ₁} {Γ₂} {A} {B} f h) g
    with split Γ₁ i
  ... | inj₁ (k , p) rewrite p
      = exch (ass  (A ⊗ B ∷ Γ₁ - k)  Γ₂ ∘
              swp' (A ⊗ B ∷ Γ₁ - k)  Γ₂ ∘ sym (
              ass  (A ⊗ B ∷ Γ₁ - k) (Δ - j)))
      $ send (cutIn (there k) j f g) h
  ... | inj₂ (k , p) rewrite p
      | ++.assoc (A ⊗ B ∷ Γ₁) (Γ₂ - k) (Δ - j)
      = send f (cutIn (there k) j h g)
  cutIn (there i) j (recv f) g
      = recv (cutIn (there (there i)) j f g)
  cutIn (there i) j (sel₁ f) g
      = sel₁ (cutIn (there i) j f g)
  cutIn (there i) j (sel₂ f) g
      = sel₂ (cutIn (there i) j f g)
  cutIn (there i) j (case f h) g
      = case (cutIn (there i) j f g)
             (cutIn (there i) j h g)
  cutIn (there ()) j halt g
  cutIn (there i) j (wait f) g
      = wait (cutIn i j f g)
  cutIn (there i) j loop g
      = loop
  cutIn {Γ} {Δ} i j (exch eq f) g
      = exch (B.++-cong {ys₁ = Δ - j} (del-from eq i) id)
      $ cutIn (from eq ⟨$⟩ i) j f g

  -- Right.
  cutIn {Γ} {.(A ⊗ B ∷ Δ₁ ++ Δ₂)} i (there j) f (send {Δ₁} {Δ₂} {A} {B} g h)
    with split Δ₁ j
  ... | inj₁ (k , p) rewrite p
      = exch (sym (ass (A ⊗ B ∷ Γ - i) (Δ₁ - k) ∘ fwd [] (Γ - i)))
      $ flip send h
      $ exch (fwd [] (Γ - i))
      $ cutIn i (there k) f g
  ... | inj₂ (k , p) rewrite p
      = exch (sym (swp [] (A ⊗ B ∷ Δ₁) (Γ - i)))
      $ send g
      $ exch (fwd [] (Γ - i))
      $ cutIn i (there k) f h
  cutIn {Γ} {.(A ⅋ B ∷ Δ)} i (there j) f (recv {Δ} {A} {B} g)
      = exch (sym (fwd [] (Γ - i)))
      $ recv
      $ exch (swp [] (A ∷ B ∷ []) (Γ - i))
      $ cutIn i (there (there j)) f g
  cutIn {Γ} {Δ} i (there j) f (sel₁ g)
      = exch (sym (fwd [] (Γ - i)))
      $ sel₁
      $ exch (fwd [] (Γ - i))
      $ cutIn i (there j) f g
  cutIn {Γ} {Δ} i (there j) f (sel₂ g)
      = exch (sym (fwd [] (Γ - i)))
      $ sel₂
      $ exch (fwd [] (Γ - i))
      $ cutIn i (there j) f g
  cutIn {Γ} {Δ} i (there j) f (case g h)
      = exch (sym (fwd [] (Γ - i)))
      $ case (exch (fwd [] (Γ - i)) $ cutIn i (there j) f g)
             (exch (fwd [] (Γ - i)) $ cutIn i (there j) f h)
  cutIn {Γ} {.(𝟏 ∷ [])} i (there ()) f halt
  cutIn {Γ} {Δ} i (there j) f (wait g)
      = exch (sym (fwd [] (Γ - i)))
      $ wait
      $ cutIn i j f g
  cutIn {Γ} {Δ} i (there j) f loop
      = exch (sym (fwd [] (Γ - i))) loop
  cutIn {Γ} {Δ} i j f (exch eq g)
      = exch (B.++-cong {xs₁ = Γ - i} id (del-from eq j))
      $ cutIn i (from eq ⟨$⟩ j) f g

-- -}
-- -}
-- -}
-- -}
-- -}
