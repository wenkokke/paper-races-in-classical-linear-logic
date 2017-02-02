open import Algebra
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Pos as ℕ⁺
open import Data.List as L
open import Data.List.Properties as LP
open import Data.List.Any as LA using (Any; here; there)
open import Data.List.Any.BagAndSetEquality as B
open import Data.Product as PR using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; _$_; flip)
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse as I using ()
open import Induction.Nat
open import Logic.Context
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_)


module nodcap where


open I.Inverse using (to; from)
private module ++ {a} {A : Set a} = Monoid (L.monoid A)


-- Types.

data Type : Set where
  𝟏 : Type
  ⊥ : Type
  𝟎 : Type
  ⊤ : Type
  _⊗_ : (A B : Type) → Type
  _⅋_ : (A B : Type) → Type
  _⊕_ : (A B : Type) → Type
  _&_ : (A B : Type) → Type
  ⊗[_]_ : (n : ℕ⁺) (A : Type) → Type
  ⅋[_]_ : (n : ℕ⁺) (A : Type) → Type


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
(⊗[ n ] A) ^ = ⅋[ n ] (A ^)
(⅋[ n ] A) ^ = ⊗[ n ] (A ^)

^-inv : (A : Type) → A ^ ^ ≡ A
^-inv 𝟏 = P.refl
^-inv ⊥ = P.refl
^-inv 𝟎 = P.refl
^-inv ⊤ = P.refl
^-inv (A ⊗ B) = P.cong₂ _⊗_ (^-inv A) (^-inv B)
^-inv (A ⅋ B) = P.cong₂ _⅋_ (^-inv A) (^-inv B)
^-inv (A ⊕ B) = P.cong₂ _⊕_ (^-inv A) (^-inv B)
^-inv (A & B) = P.cong₂ _&_ (^-inv A) (^-inv B)
^-inv (⊗[ n ] A) = P.cong ⊗[ n ]_ (^-inv A)
^-inv (⅋[ n ] A) = P.cong ⅋[ n ]_ (^-inv A)


-- Contexts.

Context : Set
Context = List Type

open LA.Membership-≡


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

  halt :

       --------
       ⊢ 𝟏 ∷ []

  wait : {Γ : Context} →

       ⊢ Γ →
       -------
       ⊢ ⊥ ∷ Γ

  loop : {Γ : Context} →

       -------
       ⊢ ⊤ ∷ Γ

  mk⅋₁ : {Γ : Context} {A : Type} →

       ⊢ A ∷ Γ →
       ---------------------
       ⊢ ⅋[ suc zero ] A ∷ Γ

  mk⊗₁ : {Γ : Context} {A : Type} →

       ⊢ A ∷ Γ →
       ---------------------
       ⊢ ⊗[ suc zero ] A ∷ Γ

  cont : {Γ : Context} {A : Type} {m n : ℕ⁺} →

       ⊢ ⅋[ m ] A ∷ ⅋[ n ] A ∷ Γ →
       ------------------------------
       ⊢ ⅋[ m + n ] A ∷ Γ

  pool : {Γ Δ : Context} {A : Type} {m n : ℕ⁺} →

       ⊢ ⊗[ m ] A ∷ Γ → ⊢ ⊗[ n ] A ∷ Δ →
       -------------------------------------
       ⊢ ⊗[ m + n ] A ∷ Γ ++ Δ

  exch : {Γ Δ : Context} →

       Γ ∼[ bag ] Δ → ⊢ Γ →
       --------------------
       ⊢ Δ


-- Contract A*n into ⅋[n]A.
contract : {Γ : Context} {A : Type} {n : ℕ⁺} →

  ⊢ replicate⁺ n A ++ Γ →
  ----------------------
  ⊢ ⅋[ n ] A ∷ Γ

contract {n = suc zero}    x
  = mk⅋₁ x
contract {n = suc (suc n)} x
  = cont {m = suc zero}
  $ exch (fwd [] (_ ∷ []))
  $ contract
  $ exch (bwd [] (replicate⁺ (suc n) _))
  $ mk⅋₁ x



-- Expand ⅋[n]A into A*n.
{-# TERMINATING #-}
expandIn : {Γ : Context} {A : Type} {n : ℕ⁺} (i : ⅋[ n ] A ∈ Γ) →

  ⊢ Γ →
  ----------------------------
  ⊢ replicate⁺ n A ++ Γ - i

expandIn (here P.refl) (mk⅋₁ x) = x
expandIn (here P.refl) (cont {Γ} {A} {m} {n} x)
  = P.subst (λ Δ → ⊢ Δ ++ Γ) (replicate⁺-++-commute m n)
  $ P.subst ⊢_ (P.sym (++.assoc (replicate⁺ m A) (replicate⁺ n A) Γ))
  $ exch (swp [] (replicate⁺ m A) (replicate⁺ n A))
  $ expandIn {n = n} (here P.refl)
  $ exch (fwd [] (replicate⁺ m A))
  $ expandIn {n = m} (here P.refl) x
expandIn {_} {A} {n} (there i) (send {Γ} {Δ} x h)
  with split Γ i
... | inj₁ (j , p) rewrite p
    = exch (swp [] (replicate⁺ n A) (_ ∷ []))
    $ P.subst ⊢_ (++.assoc (_ ∷ replicate⁺ n A) (Γ - j) Δ)
    $ flip send h
    $ exch (swp [] (_ ∷ []) (replicate⁺ n A))
    $ expandIn (there j) x
... | inj₂ (j , p) rewrite p
    = exch (swp [] (replicate⁺ n A) (_ ∷ Γ))
    $ send x
    $ exch (swp [] (_ ∷ []) (replicate⁺ n A))
    $ expandIn (there j) h
expandIn {Γ} {A} {n} (there i) (recv x)
  = exch (swp [] (replicate⁺ n A) (_ ∷ []))
  $ recv
  $ exch (swp [] (_ ∷ _ ∷ []) (replicate⁺ n A))
  $ expandIn (there (there i)) x
expandIn {Γ} {A} {n} (there i) (sel₁ x)
  = exch (swp [] (replicate⁺ n A) (_ ∷ []))
  $ sel₁
  $ exch (swp [] (_ ∷ []) (replicate⁺ n A))
  $ expandIn (there i) x
expandIn {Γ} {A} {n} (there i) (sel₂ x)
  = exch (swp [] (replicate⁺ n A) (_ ∷ []))
  $ sel₂
  $ exch (swp [] (_ ∷ []) (replicate⁺ n A))
  $ expandIn (there i) x
expandIn {Γ} {A} {n} (there i) (case x h)
  = exch (swp [] (replicate⁺ n A) (_ ∷ []))
  $ case
    ( exch (swp [] (_ ∷ []) (replicate⁺ n A))
    $ expandIn (there i) x )
    ( exch (swp [] (_ ∷ []) (replicate⁺ n A))
    $ expandIn (there i) h )
expandIn (there ()) halt
expandIn {Γ} {A} {n} (there i) (wait x)
  = exch (swp [] (replicate⁺ n A) (_ ∷ []))
  $ wait
  $ expandIn i x
expandIn {Γ} {A} {n} (there i)  loop
  = exch (swp [] (replicate⁺ n A) (_ ∷ []))
  $ loop
expandIn {Γ} {A} {n} (there i) (mk⅋₁ x)
  = exch (swp [] (replicate⁺ n A) (_ ∷ []))
  $ mk⅋₁
  $ exch (swp [] (_ ∷ []) (replicate⁺ n A))
  $ expandIn (there i) x
expandIn {Γ} {A} {n} (there i) (mk⊗₁ x)
  = exch (swp [] (replicate⁺ n A) (_ ∷ []))
  $ mk⊗₁
  $ exch (swp [] (_ ∷ []) (replicate⁺ n A))
  $ expandIn (there i) x
expandIn {Γ} {A} {n} (there i) (cont x)
  = exch (swp [] (replicate⁺ n A) (_ ∷ []))
  $ cont
  $ exch (swp [] (_ ∷ _ ∷ []) (replicate⁺ n A))
  $ expandIn (there (there i)) x
expandIn {_} {A} {n} (there i) (pool {Γ} {Δ} x h)
  with split Γ i
... | inj₁ (j , p) rewrite p
    = exch (swp [] (replicate⁺ n A) (_ ∷ []))
    $ P.subst ⊢_ (++.assoc (_ ∷ replicate⁺ n A) (Γ - j) Δ)
    $ flip pool h
    $ exch (swp [] (_ ∷ []) (replicate⁺ n A))
    $ expandIn (there j) x
... | inj₂ (j , p) rewrite p
    = exch (swp [] (replicate⁺ n A) (_ ∷ Γ))
    $ pool x
    $ exch (swp [] (_ ∷ []) (replicate⁺ n A))
    $ expandIn (there j) h
expandIn {Γ} {A} {n} i (exch b x)
  = exch (B.++-cong {xs₁ = replicate⁺ n A} I.id (del-from b i))
  $ expandIn (from b ⟨$⟩ i) x


expand : {Γ : Context} {A : Type} {n : ℕ⁺} →

  ⊢ ⅋[ n ] A ∷ Γ →
  --------------------
  ⊢ replicate⁺ n A ++ Γ

expand = expandIn (here P.refl)


split-⅋ : {Γ : Context} {A : Type} {m n : ℕ⁺} →

  ⊢ ⅋[ m + n ] A ∷ Γ →
  ----------------------------
  ⊢ ⅋[ m ] A ∷ ⅋[ n ] A ∷ Γ

split-⅋ {Γ} {A} {m} {n} x
  = exch (bbl [])
  $ contract {n = n}
  $ exch (bwd [] (replicate⁺ n A))
  $ contract {n = m}
  $ P.subst ⊢_ (++.assoc (replicate⁺ m A) (replicate⁺ n A) Γ)
  $ P.subst (λ Γ' → ⊢ Γ' ++ Γ) (P.sym (replicate⁺-++-commute m n))
  $ expand x


{-# TERMINATING #-}
mutual
  cut : {Γ Δ : Context} {A : Type} →

    ⊢ A ∷ Γ → ⊢ A ^ ∷ Δ →
    ---------------------
    ⊢ Γ ++ Δ

  cut {_} {Δ} {𝟏} halt (wait y)
    = y
  cut {Γ} {_} {⊥} (wait x) halt
    = P.subst ⊢_ (P.sym (proj₂ ++.identity Γ)) x
  cut {_} {Θ} {A ⊗ B} (send {Γ} {Δ} x y) (recv z)
    = P.subst ⊢_ (P.sym (++.assoc Γ Δ Θ))
    $ exch (swp [] Γ Δ)
    $ cut y
    $ exch (fwd [] Γ)
    $ cut x z
  cut {Θ} {_} {A ⅋ B} (recv x) (send {Γ} {Δ} y z)
    = P.subst ⊢_ (++.assoc Θ Γ Δ)
    $ cut (cut x y) z
  cut {Γ} {Δ} {A ⊕ B} (sel₁ x) (case y z)
    = cut x y
  cut {Γ} {Δ} {A ⊕ B} (sel₂ x) (case y z)
    = cut x z
  cut {Γ} {Δ} {A & B} (case x y) (sel₁ z)
    = cut x z
  cut {Γ} {Δ} {A & B} (case x y) (sel₂ z)
    = cut y z
  cut {Γ} {Δ} {⊗[ ._ ] A} (mk⊗₁ x) y
    = cut x (expand y)
  cut {_} {Θ} {⊗[ ._ ] _} (pool {Γ} {Δ} x y) z
    = P.subst ⊢_ (P.sym (++.assoc Γ Δ Θ))
    $ exch (swp [] Γ Δ)
    $ cut y
    $ exch (fwd [] Γ)
    $ cut x
    $ split-⅋ z
  cut {Γ} {Δ} {⅋[ ._ ] A} x (mk⊗₁ y)
    = cut (expand x) y
  cut {Θ} {_} {⅋[ ._ ] A} x (pool {Γ} {Δ} y z)
    = P.subst ⊢_ (++.assoc Θ Γ Δ)
    $ flip cut z
    $ flip cut y
    $ split-⅋ x
  cut {Γ} {Δ} {A} (exch b x) y
    = exch (B.++-cong {ys₁ = Δ} (del-from b (here P.refl)) I.id)
    $ cutIn (from b ⟨$⟩ here P.refl) (here P.refl) x y
  cut {Γ} {Δ} {A} x (exch b y)
    = exch (B.++-cong {xs₁ = Γ} I.id (del-from b (here P.refl)))
    $ cutIn (here P.refl) (from b ⟨$⟩ here P.refl) x y


  cutIn : {Γ Δ : Context} {A : Type} (i : A ∈ Γ) (j : A ^ ∈ Δ) →

    ⊢ Γ → ⊢ Δ →
    ----------------
    ⊢ Γ - i ++ Δ - j

  cutIn (here P.refl) (here P.refl) x y = cut x y

  cutIn {_} {Θ} (there i) j (send {Γ} {Δ} x y) z
    with split Γ i
  ... | inj₁ (k , p) rewrite p
      = P.subst ⊢_ (P.sym (++.assoc (_ ∷ Γ - k) Δ (Θ - j)))
      $ exch (swp₃ (_ ∷ Γ - k) Δ)
      $ P.subst ⊢_ (++.assoc (_ ∷ Γ - k) (Θ - j) Δ)
      $ flip send y
      $ cutIn (there k) j x z
  ... | inj₂ (k , p) rewrite p
      = P.subst ⊢_ (P.sym (++.assoc (_ ∷ Γ) (Δ - k) (Θ - j)))
      $ send x
      $ cutIn (there k) j y z
  cutIn (there i) j (recv x) y
    = recv
    $ cutIn (there (there i)) j x y
  cutIn (there i) j (sel₁ x) y
    = sel₁
    $ cutIn (there i) j x y
  cutIn (there i) j (sel₂ x) y
    = sel₂
    $ cutIn (there i) j x y
  cutIn (there i) j (case x y) z
    = case
    ( cutIn (there i) j x z )
    ( cutIn (there i) j y z )
  cutIn (there ()) j halt y
  cutIn (there i) j (wait x) y
    = wait
    $ cutIn i j x y
  cutIn (there i) j loop y
    = loop
  cutIn {Γ} {Δ} (there i) j (mk⅋₁ x) y
    = mk⅋₁
    $ cutIn (there i) j x y
  cutIn {Γ} {Δ} (there i) j (mk⊗₁ x) y
    = mk⊗₁
    $ cutIn (there i) j x y
  cutIn {Γ} {Δ} (there i) j (cont x) y
    = cont
    $ cutIn (there (there i)) j x y
  cutIn {_} {Θ} (there i) j (pool {Γ} {Δ} x y) z
    with split Γ i
  ... | inj₁ (k , p) rewrite p
      = P.subst ⊢_ (P.sym (++.assoc (_ ∷ Γ - k) Δ (Θ - j)))
      $ exch (swp₃ (_ ∷ Γ - k) Δ)
      $ P.subst ⊢_ (++.assoc (_ ∷ Γ - k) (Θ - j) Δ)
      $ flip pool y
      $ cutIn (there k) j x z
  ... | inj₂ (k , p) rewrite p
      = P.subst ⊢_ (P.sym (++.assoc (_ ∷ Γ) (Δ - k) (Θ - j)))
      $ pool x
      $ cutIn (there k) j y z

  cutIn {Θ} {_} i (there j) x (send {Γ} {Δ} y z)
    with split Γ j
  ... | inj₁ (k , p) rewrite p
      = exch (bwd [] (Θ - i))
      $ P.subst ⊢_ (++.assoc (_ ∷ Θ - i) (Γ - k) Δ)
      $ flip send z
      $ exch (fwd [] (Θ - i))
      $ cutIn i (there k) x y
  ... | inj₂ (k , p) rewrite p
      = exch (swp [] (Θ - i) (_ ∷ Γ))
      $ send y
      $ exch (fwd [] (Θ - i))
      $ cutIn i (there k) x z
  cutIn {Γ} i (there j) x (recv {Δ} y)
    = exch (bwd [] (Γ - i))
    $ recv
    $ exch (swp [] (_ ∷ _ ∷ []) (Γ - i))
    $ cutIn i (there (there j)) x y
  cutIn {Γ} {Δ} i (there j) x (sel₁ y)
    = exch (bwd [] (Γ - i))
    $ sel₁
    $ exch (fwd [] (Γ - i))
    $ cutIn i (there j) x y
  cutIn {Γ} {Δ} i (there j) x (sel₂ y)
    = exch (bwd [] (Γ - i))
    $ sel₂
    $ exch (fwd [] (Γ - i))
    $ cutIn i (there j) x y
  cutIn {Γ} {Δ} i (there j) x (case y z)
    = exch (bwd [] (Γ - i))
    $ case
    ( exch (fwd [] (Γ - i)) $ cutIn i (there j) x y )
    ( exch (fwd [] (Γ - i)) $ cutIn i (there j) x z )
  cutIn {Γ} i (there ()) x halt
  cutIn {Γ} {Δ} i (there j) x (wait y)
    = exch (bwd [] (Γ - i))
    $ wait
    $ cutIn i j x y
  cutIn {Γ} {Δ} i (there j) x loop
    = exch (bwd [] (Γ - i)) loop
  cutIn {Γ} {Δ} i (there j) x (mk⅋₁ y)
    = exch (bwd [] (Γ - i))
    $ mk⅋₁
    $ exch (fwd [] (Γ - i))
    $ cutIn i (there j) x y
  cutIn {Γ} {Δ} i (there j) x (mk⊗₁ y)
    = exch (bwd [] (Γ - i))
    $ mk⊗₁
    $ exch (fwd [] (Γ - i))
    $ cutIn i (there j) x y
  cutIn {Γ} {Δ} i (there j) x (cont y)
    = exch (bwd [] (Γ - i))
    $ cont
    $ exch (swp [] (_ ∷ _ ∷ []) (Γ - i))
    $ cutIn i (there (there j)) x y
  cutIn {Θ} {_} i (there j) x (pool {Γ} {Δ} y z)
    with split Γ j
  ... | inj₁ (k , p) rewrite p
      = exch (bwd [] (Θ - i))
      $ P.subst ⊢_ (++.assoc (_ ∷ Θ - i) (Γ - k) Δ)
      $ flip pool z
      $ exch (fwd [] (Θ - i))
      $ cutIn i (there k) x y
  ... | inj₂ (k , p) rewrite p
      = exch (swp [] (Θ - i) (_ ∷ Γ))
      $ pool y
      $ exch (fwd [] (Θ - i))
      $ cutIn i (there k) x z

  cutIn {Γ} {Δ} i j (exch b x) y
    = exch (B.++-cong {ys₁ = Δ - j} (del-from b i ) I.id)
    $ cutIn (from b ⟨$⟩ i) j x y
  cutIn {Γ} {Δ} i j x (exch b y)
    = exch (B.++-cong {xs₁ = Γ - i} I.id (del-from b j))
    $ cutIn i (from b ⟨$⟩ j) x y



-- -}
-- -}
-- -}
-- -}
-- -}
