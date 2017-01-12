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
open import Function.Related.TypeIsomorphisms
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)

module RCP where

data Type : Set where
  𝟏 : Type
  ⊥ : Type
  𝟎 : Type
  ⊤ : Type
  _⊗_ : (S₁ S₂ : Type) → Type
  _⅋_ : (S₁ S₂ : Type) → Type
  _⊕_ : (S₁ S₂ : Type) → Type
  _&_ : (S₁ S₂ : Type) → Type

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
^-inv 𝟏 = refl
^-inv ⊥ = refl
^-inv 𝟎 = refl
^-inv ⊤ = refl
^-inv (S₁ ⊗ S₂) rewrite ^-inv S₁ | ^-inv S₂ = refl
^-inv (S₁ ⅋ S₂) rewrite ^-inv S₁ | ^-inv S₂ = refl
^-inv (S₁ ⊕ S₂) rewrite ^-inv S₁ | ^-inv S₂ = refl
^-inv (S₁ & S₂) rewrite ^-inv S₁ | ^-inv S₂ = refl

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


Context : Set
Context = List Type

open Data.List.Any.Membership-≡
private
  module Eq         {k a} {A : Set a} = Setoid ([ k ]-Equality A)
  module Ord        {k a} {A : Set a} = Preorder ([ k ]-Order A)
  module ×⊎         {k ℓ}             = CommutativeSemiring (×⊎-CommutativeSemiring k ℓ)
  module ListMonad  {ℓ}               = RawMonad (Data.List.monad {ℓ = ℓ})
  module ListMonoid {a} {A : Set a}   = Monoid (Data.List.monoid A)
  open ListMonoid using (identity; assoc)

bagEq : {Γ Δ : Context}
        (to   : ∀ {A} → A ∈ Γ → A ∈ Δ)
        (from : ∀ {A} → A ∈ Δ → A ∈ Γ)
        (inv₁ : ∀ {A} (i : A ∈ Γ) → from (to i) ≡ i)
        (inv₂ : ∀ {A} (i : A ∈ Δ) → to (from i) ≡ i)
        → Γ ∼[ bag ] Δ
bagEq to from inv₁ inv₂ = record
  { to         = P.→-to-⟶ to
  ; from       = P.→-to-⟶ from
  ; inverse-of = record { left-inverse-of = inv₁ ; right-inverse-of = inv₂ }
  }


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


_-_ : (Γ : Context) {A : Type} (i : A ∈ Γ) → Context
(B ∷ Γ) - (here  _) = Γ
(B ∷ Γ) - (there i) = B ∷ Γ - i

postulate
  inv : {Γ Δ : Context} {A : Type} →
        (x : Δ ∼[ bag ] Γ) (i : A ∈ Γ) →
        Δ - (Inverse.from x ⟨$⟩ i) ∼[ bag ] Γ - i
  swp : (Γ Δ Σ {Π} : Context) →
        Γ ++ Σ ++ Δ ++ Π ∼[ bag ] Γ ++ Δ ++ Σ ++ Π

mutual
  cut : {Γ Δ : Context} {A : Type} →

        ⊢ A ∷ Γ → ⊢ A ^ ∷ Δ →
        ---------------------
        ⊢ Γ ++ Δ

  cut f g = cutAt (here refl) (here refl) f g

  cutAt : {Γ Δ : Context} {A : Type} →
         (i : A ∈ Γ) (j : A ^ ∈ Δ) →

         ⊢ Γ → ⊢ Δ →
         ------------------
         ⊢ Γ - i ++ Δ - j

  -- Principal Cuts.
  cutAt (here refl) (here refl) f g = principal f g
    where
      principal : {Γ Δ : Context} {A : Type} → ⊢ A ∷ Γ → ⊢ A ^ ∷ Δ → ⊢ Γ ++ Δ
      principal {Γ} {Δ} {𝟏} halt (wait g)
          = g
      principal {Γ} {Δ} {⊥} (wait f) halt rewrite proj₂ identity Γ
          = f
      principal {.(Γ₁ ++ Γ₂)} {Δ} {A = A₁ ⊗ A₂} (send {Γ₁} {Γ₂} f h) (recv g)
        rewrite assoc Γ₁ Γ₂ Δ
          = exch (swp [] Γ₁ Γ₂)
          $ cut h
          $ exch (fwd Γ₁)
          $ cut f g
      principal {Γ} {.(Δ₁ ++ Δ₂)} {A = A₁ ⅋ A₂} (recv f) (send {Δ₁} {Δ₂} g h)
        rewrite P.sym (assoc Γ Δ₁ Δ₂)
          = flip cut h
          $ cut f g
      principal {Γ} {Δ} {A₁ ⊕ A₂} (sel₁ f) (case g h)
          = cut f g
      principal {Γ} {Δ} {A₁ ⊕ A₂} (sel₂ f) (case g h)
          = cut f h
      principal {Γ} {Δ} {A₁ & A₂} (case f h) (sel₁ g)
          = cut f g
      principal {Γ} {Δ} {A₁ & A₂} (case f h) (sel₂ g)
          = cut h g

  -- Permutation Cases.

      -- Principal.
      principal {Γ} {Δ} {A} f (exch x g)
          = exch (B.++-cong {xs₁ = Γ} I.id (inv x (here refl)))
          $ cutAt (here refl) (Inverse.from x ⟨$⟩ here refl) f g
      principal {Γ} {Δ} {A} (exch x f) g
          = exch (B.++-cong {ys₁ = Δ} (inv x (here refl)) I.id)
          $ cutAt (Inverse.from x ⟨$⟩ here refl) (here refl) f g

  -- Left.
  cutAt {.(A ⊗ B ∷ Γ₁ ++ Γ₂)} {Δ} (there i) j (send {Γ₁} {Γ₂} {A} {B} f h) g
    with ++-split Γ₁ i
  ... | inj₁ (k , p) rewrite p
      = exch (ass  (A ⊗ B ∷ Γ₁ - k)  Γ₂ ∘
              swp' (A ⊗ B ∷ Γ₁ - k)  Γ₂ ∘ I.sym (
              ass  (A ⊗ B ∷ Γ₁ - k) (Δ - j)))
      $ send (cutAt (there k) j f g) h
  ... | inj₂ (k , p) rewrite p
      | assoc (A ⊗ B ∷ Γ₁) (Γ₂ - k) (Δ - j)
      = send f (cutAt (there k) j h g)
  cutAt (there i) j (recv f) g
      = recv (cutAt (there (there i)) j f g)
  cutAt (there i) j (sel₁ f) g
      = sel₁ (cutAt (there i) j f g)
  cutAt (there i) j (sel₂ f) g
      = sel₂ (cutAt (there i) j f g)
  cutAt (there i) j (case f h) g
      = case (cutAt (there i) j f g)
             (cutAt (there i) j h g)
  cutAt (there ()) j halt g
  cutAt (there i) j (wait f) g
      = wait (cutAt i j f g)
  cutAt (there i) j loop g
      = loop
  cutAt {Γ} {Δ} i j (exch x f) g
      = exch (B.++-cong {ys₁ = Δ - j} (inv x i) I.id)
      $ cutAt (Inverse.from x ⟨$⟩ i) j f g

  -- Right.
  cutAt {Γ} {.(A ⊗ B ∷ Δ₁ ++ Δ₂)} i (there j) f (send {Δ₁} {Δ₂} {A} {B} g h)
    with ++-split Δ₁ j
  ... | inj₁ (k , p) rewrite p
      = exch (I.sym (ass (A ⊗ B ∷ Γ - i) (Δ₁ - k) ∘ fwd (Γ - i)))
      $ flip send h
      $ exch (fwd (Γ - i))
      $ cutAt i (there k) f g
  ... | inj₂ (k , p) rewrite p
      = exch (I.sym (swp [] (A ⊗ B ∷ Δ₁) (Γ - i)))
      $ send g
      $ exch (fwd (Γ - i))
      $ cutAt i (there k) f h
  cutAt {Γ} {.(A ⅋ B ∷ Δ)} i (there j) f (recv {Δ} {A} {B} g)
      = exch (I.sym (fwd (Γ - i)))
      $ recv
      $ exch (swp [] (A ∷ B ∷ []) (Γ - i))
      $ cutAt i (there (there j)) f g
  cutAt {Γ} {Δ} i (there j) f (sel₁ g)
      = exch (I.sym (fwd (Γ - i)))
      $ sel₁
      $ exch (fwd (Γ - i))
      $ cutAt i (there j) f g
  cutAt {Γ} {Δ} i (there j) f (sel₂ g)
      = exch (I.sym (fwd (Γ - i)))
      $ sel₂
      $ exch (fwd (Γ - i))
      $ cutAt i (there j) f g
  cutAt {Γ} {Δ} i (there j) f (case g h)
      = exch (I.sym (fwd (Γ - i)))
      $ case (exch (fwd (Γ - i)) $ cutAt i (there j) f g)
             (exch (fwd (Γ - i)) $ cutAt i (there j) f h)
  cutAt {Γ} {.(𝟏 ∷ [])} i (there ()) f halt
  cutAt {Γ} {Δ} i (there j) f (wait g)
      = exch (I.sym (fwd (Γ - i)))
      $ wait
      $ cutAt i j f g
  cutAt {Γ} {Δ} i (there j) f loop
      = exch (I.sym (fwd (Γ - i))) loop
  cutAt {Γ} {Δ} i j f (exch x g)
      = exch (B.++-cong {xs₁ = Γ - i} I.id (inv x j))
      $ cutAt i (Inverse.from x ⟨$⟩ j) f g

  -- Helper functions.

  -- Swap two contexts occurring after Γ.
  swp' : (Γ Δ {Θ} : Context) → Γ ++ Θ ++ Δ ∼[ bag ] Γ ++ Δ ++ Θ
  swp' Γ Δ {Θ}
      = P.subst₂ (λ Δ' Θ' → Γ ++ Θ ++ Δ' ∼[ bag ] Γ ++ Δ ++ Θ')
        (proj₂ identity Δ)
        (proj₂ identity Θ)
        (swp Γ Δ Θ {[]})

  -- Rewrite by associativity as a permutation.
  ass : (Γ Δ {Θ} : Context) → Γ ++ (Δ ++ Θ) ∼[ bag ] (Γ ++ Δ) ++ Θ
  ass Γ Δ {Θ} rewrite assoc Γ Δ Θ = I.id

  -- Move a type forwards in a context.
  fwd : (Γ {Θ} : Context) {A : Type} → Γ ++ A ∷ Θ ∼[ bag ] A ∷ Γ ++ Θ
  fwd Γ = swp [] (_ ∷ []) Γ

  -- Split a contexts based on a proof of inclusion.
  ++-split : ∀ (Γ {Δ} : Context) {A : Type} →
             (i : A ∈ Γ ++ Δ) →
             Σ[ j ∈ A ∈ Γ ] ((Γ ++ Δ) - i ≡ Γ - j ++ Δ) ⊎
             Σ[ j ∈ A ∈ Δ ] ((Γ ++ Δ) - i ≡ Γ ++ Δ - j)
  ++-split [] i = inj₂ (i , refl)
  ++-split (_ ∷ Γ) (here px) = inj₁ (here px , refl)
  ++-split (_ ∷ Γ) (there i) with ++-split Γ i
  ... | inj₁ (j , p) = inj₁ (there j , P.cong (_ ∷_) p)
  ... | inj₂ (j , p) = inj₂ (j , P.cong (_ ∷_) p)


-- -}
-- -}
-- -}
-- -}
-- -}
