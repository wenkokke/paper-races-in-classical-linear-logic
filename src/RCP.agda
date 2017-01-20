open import Level as ℓ
open import Algebra
open import Category.Monad
open import Data.List using (List; _∷_; []; _++_)
open import Data.List.Any using (Any; here; there)
open import Data.List.Any.Properties using (++↔)
open import Data.List.Any.BagAndSetEquality as B
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Function using (flip; _$_)
open import Function.Equality using (module Π; Π; _⟶_; _⟨$⟩_)
open import Function.Inverse as I using (Inverse; module Inverse; _∘_; _↔_)
open import Logic.Context using (bbl; fwd; swp)
open import Relation.Binary
open import Relation.Binary.HeterogeneousEquality as H using (_≅_; refl)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)

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

_-_ : (Γ : Context) {A : Type} (i : A ∈ Γ) → Context
(B ∷ Γ) - (here  _) = Γ
(B ∷ Γ) - (there i) = B ∷ Γ - i


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

  cut {Γ} {Δ} {A} f (exch x g)
      = exch (B.++-cong {xs₁ = Γ} I.id (del x (here refl)))
      $ cutIn (here refl) (x ⟨⇐⟩ here refl) f g
  cut {Γ} {Δ} {A} (exch x f) g
      = exch (B.++-cong {ys₁ = Δ} (del x (here refl)) I.id)
      $ cutIn (x ⟨⇐⟩ here refl) (here refl) f g

  -- Permutation Cuts,
  cutIn : {Γ Δ : Context} {A : Type} →
         (i : A ∈ Γ) (j : A ^ ∈ Δ) →

         ⊢ Γ → ⊢ Δ →
         ------------------
         ⊢ Γ - i ++ Δ - j

  cutIn (here refl) (here refl) f g = cut f g

  -- Left.
  cutIn {.(A ⊗ B ∷ Γ₁ ++ Γ₂)} {Δ} (there i) j (send {Γ₁} {Γ₂} {A} {B} f h) g
    with split Γ₁ i
  ... | inj₁ (k , p) rewrite p
      = exch (ass  (A ⊗ B ∷ Γ₁ - k)  Γ₂ ∘
              swp' (A ⊗ B ∷ Γ₁ - k)  Γ₂ ∘ I.sym (
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
  cutIn {Γ} {Δ} i j (exch x f) g
      = exch (B.++-cong {ys₁ = Δ - j} (del x i) I.id)
      $ cutIn (x ⟨⇐⟩ i) j f g

  -- Right.
  cutIn {Γ} {.(A ⊗ B ∷ Δ₁ ++ Δ₂)} i (there j) f (send {Δ₁} {Δ₂} {A} {B} g h)
    with split Δ₁ j
  ... | inj₁ (k , p) rewrite p
      = exch (I.sym (ass (A ⊗ B ∷ Γ - i) (Δ₁ - k) ∘ fwd [] (Γ - i)))
      $ flip send h
      $ exch (fwd [] (Γ - i))
      $ cutIn i (there k) f g
  ... | inj₂ (k , p) rewrite p
      = exch (I.sym (swp [] (A ⊗ B ∷ Δ₁) (Γ - i)))
      $ send g
      $ exch (fwd [] (Γ - i))
      $ cutIn i (there k) f h
  cutIn {Γ} {.(A ⅋ B ∷ Δ)} i (there j) f (recv {Δ} {A} {B} g)
      = exch (I.sym (fwd [] (Γ - i)))
      $ recv
      $ exch (swp [] (A ∷ B ∷ []) (Γ - i))
      $ cutIn i (there (there j)) f g
  cutIn {Γ} {Δ} i (there j) f (sel₁ g)
      = exch (I.sym (fwd [] (Γ - i)))
      $ sel₁
      $ exch (fwd [] (Γ - i))
      $ cutIn i (there j) f g
  cutIn {Γ} {Δ} i (there j) f (sel₂ g)
      = exch (I.sym (fwd [] (Γ - i)))
      $ sel₂
      $ exch (fwd [] (Γ - i))
      $ cutIn i (there j) f g
  cutIn {Γ} {Δ} i (there j) f (case g h)
      = exch (I.sym (fwd [] (Γ - i)))
      $ case (exch (fwd [] (Γ - i)) $ cutIn i (there j) f g)
             (exch (fwd [] (Γ - i)) $ cutIn i (there j) f h)
  cutIn {Γ} {.(𝟏 ∷ [])} i (there ()) f halt
  cutIn {Γ} {Δ} i (there j) f (wait g)
      = exch (I.sym (fwd [] (Γ - i)))
      $ wait
      $ cutIn i j f g
  cutIn {Γ} {Δ} i (there j) f loop
      = exch (I.sym (fwd [] (Γ - i))) loop
  cutIn {Γ} {Δ} i j f (exch x g)
      = exch (B.++-cong {xs₁ = Γ - i} I.id (del x j))
      $ cutIn i (x ⟨⇐⟩ j) f g

  -- Helper functions.

  -- Transport a membership proof along a bag equality.
  _⟨⇐⟩_ : {Γ Δ : Context} (x : Δ ∼[ bag ] Γ) {A : Type} (i : A ∈ Γ) → A ∈ Δ
  x ⟨⇐⟩ i = Inverse.from x ⟨$⟩ i

  _⟨⇒⟩_ : {Γ Δ : Context} (x : Δ ∼[ bag ] Γ) {A : Type} (i : A ∈ Δ) → A ∈ Γ
  x ⟨⇒⟩ i = Inverse.to x ⟨$⟩ i

  -- Split a context based on a proof of membership (used as index).
  split : ∀ (Γ {Δ} : Context) {A : Type} →
          (i : A ∈ Γ ++ Δ) →
          Σ[ j ∈ A ∈ Γ ] ((Γ ++ Δ) - i ≡ Γ - j ++ Δ) ⊎
          Σ[ j ∈ A ∈ Δ ] ((Γ ++ Δ) - i ≡ Γ ++ Δ - j)
  split [] i = inj₂ (i , refl)
  split (_ ∷ Γ) (here px) = inj₁ (here px , refl)
  split (_ ∷ Γ) (there i) with split Γ i
  ... | inj₁ (j , p) = inj₁ (there j , P.cong (_ ∷_) p)
  ... | inj₂ (j , p) = inj₂ (j , P.cong (_ ∷_) p)


  postulate
    -- If there is a bijection between Γ and Δ, then there
    -- is a bijection between Γ minus i, and Δ minus the
    -- image of i across the bijection.
    del : {Γ Δ : Context} {A : Type} →
          (x : Δ ∼[ bag ] Γ) (i : A ∈ Γ) →
          Δ - (x ⟨⇐⟩ i) ∼[ bag ] Γ - i


  -- Move a context forwards over another context (w/ prefix).
  swp' : (Γ Δ {Θ} : Context) → Γ ++ Θ ++ Δ ∼[ bag ] Γ ++ Δ ++ Θ
  swp' Γ Δ {Θ} = P.subst₂ (λ Δ' Θ' → Γ ++ Θ ++ Δ' ∼[ bag ] Γ ++ Δ ++ Θ')
                 (proj₂ ++.identity Δ)
                 (proj₂ ++.identity Θ)
                 (swp Γ Δ Θ {[]})

  -- Rewrite by associativity.
  ass : (Γ Δ {Θ} : Context) → Γ ++ (Δ ++ Θ) ∼[ bag ] (Γ ++ Δ) ++ Θ
  ass Γ Δ {Θ} rewrite ++.assoc Γ Δ Θ = I.id


-- -}
-- -}
-- -}
-- -}
-- -}
