module cpnd.typing-judgement where

open import Data.List using (List; _++_) renaming (_∷_ to _,_; [] to ∅)
open import Data.List.Any.Membership.Propositional using (_∼[_]_; bag)
open import Data.Nat as Nat using (ℕ; suc; zero; _≤?_)
open import Data.Nat.Properties.Simple using (+-comm; +-assoc)
open import Function.Inverse using (id; sym; _∘_)
open        Function.Inverse.Inverse using (to; from)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; cong; cong₂; subst)
open import Logic.Context
open import cpnd.term

data Pos : Set where
  suc : ℕ → Pos

_+_ : Pos → Pos → Pos
suc m + suc n = suc (suc (m Nat.+ n))

instance
  PosNumber : Number Pos
  PosNumber = record
    { Constraint = λ{n → True (1 ≤? n)}
    ; fromNat    = λ{zero {{()}}; (suc n) → suc n}
    }


data Type : Set where
  _⊗_ : Type → Type → Type
  _⅋_ : Type → Type → Type
  𝟏 ⊥ : Type
  _⊕_ : Type → Type → Type
  _&_ : Type → Type → Type
  𝟎 ⊤ : Type
  ![_]_ : Pos → Type → Type
  ?[_]_ : Pos → Type → Type


infixl 30 _^

_^ : Type → Type
(A ⊗ B) ^ = A ^ ⅋ B ^
(A ⅋ B) ^ = A ^ ⊗ B ^
𝟏 ^ = ⊥
⊥ ^ = 𝟏
(A ⊕ B) ^ = A ^ & B ^
(A & B) ^ = A ^ ⊕ B ^
𝟎 ^ = ⊤
⊤ ^ = 𝟎
(![ n ] A) ^ = ?[ n ] A ^
(?[ n ] A) ^ = ![ n ] A ^

^-inv : (A : Type) → A ^ ^ ≡ A
^-inv 𝟏 = refl
^-inv ⊥ = refl
^-inv 𝟎 = refl
^-inv ⊤ = refl
^-inv (A ⊗ B) = cong₂ _⊗_ (^-inv A) (^-inv B)
^-inv (A ⅋ B) = cong₂ _⅋_ (^-inv A) (^-inv B)
^-inv (A ⊕ B) = cong₂ _⊕_ (^-inv A) (^-inv B)
^-inv (A & B) = cong₂ _&_ (^-inv A) (^-inv B)
^-inv (![ n ] A) = cong ![ n ]_ (^-inv A)
^-inv (?[ n ] A) = cong ?[ n ]_ (^-inv A)


infix 10 _⦂_

data NameType : Set where
  _⦂_ : (x : Name) (A : Type) → NameType

infix 3 _⊢_

data _⊢_ : Term → List NameType → Set where

  ax : ∀{A x y} →

    ----------------------------
    x ↔ y ⊢ x ⦂ A , y ⦂ A ^ , ∅

  cut : ∀{Γ Δ A x P Q} →

    P ⊢ x ⦂ A , Γ → Q ⊢ x ⦂ A ^ , Δ →
    ---------------------------------
    ν x (P ∣ Q) ⊢ Γ ++ Δ

  ⊢-⊗ : ∀{Γ Δ A B x y P Q} →

    P ⊢ y ⦂ A , Γ → Q ⊢ x ⦂ B , Δ →
    ------------------------------------
    x [ y ] (P ∣ Q) ⊢ x ⦂ A ⊗ B , Γ ++ Δ

  ⊢-⅋ : ∀{Γ A B x y P} →

    P ⊢ y ⦂ A , x ⦂ B , Γ →
    -------------------------
    x ⟨ y ⟩ P ⊢ x ⦂ A ⅋ B , Γ

  ⊢-⊕₁ : ∀{Γ A B x P} →

    P ⊢ x ⦂ A , Γ →
    -----------------------
    x [L] P ⊢ x ⦂ A ⊕ B , Γ

  ⊢-⊕₂ : ∀{Γ A B x P} →

    P ⊢ x ⦂ B , Γ →
    -----------------------
    x [R] P ⊢ x ⦂ A ⊕ B , Γ

  ⊢-& : ∀{Γ A B x P Q} →

    P ⊢ x ⦂ A , Γ → Q ⊢ x ⦂ B , Γ →
    -------------------------------
    case x (P , Q) ⊢ x ⦂ A & B , Γ

  ⊢-𝟏 : ∀{x} →

    ------------------
    x [] 0 ⊢ x ⦂ 𝟏 , ∅

  ⊢-⊥ : ∀{Γ x P} →

    P ⊢ Γ →
    -------------
    x ⟨⟩ P ⊢ x ⦂ ⊥ , Γ

  ⊢-⊤ : ∀{Γ x} →

    -------------------
    crash x ⊢ x ⦂ ⊤ , Γ

  ⊢-?₁ : ∀{Γ A x y P} →

    P ⊢ y ⦂ A , Γ →
    ------------------------------
    ⋆ x ⟨ y ⟩ P ⊢ x ⦂ ?[ 1 ] A , Γ

  ⊢-!₁ : ∀{Γ A x y P} →

    P ⊢ y ⦂ A , Γ →
    ------------------------------
    ⋆ x [ y ] P ⊢ x ⦂ ![ 1 ] A , Γ

  ⊢-| : ∀{Γ Δ A m n x P Q} →

    P ⊢ x ⦂ ![ m ] A , Γ → Q ⊢ x ⦂ ![ n ] A , Δ →
    ---------------------------------------------
    (P ∣ Q) ⊢ x ⦂ ![ m + n ] A , Γ ++ Δ

  cont : ∀{Γ A m n x y P} →

    P ⊢ x ⦂ ?[ m ] A , y ⦂ ?[ n ] A , Γ →
    --------------------------------------
    P [ x / y , ∅ ] ⊢ x ⦂ ?[ m + n ] A , Γ

  exch : ∀{Γ Δ P} →

    Γ ∼[ bag ] Δ → P ⊢ Γ →
    ----------------------
    P ⊢ Δ


data ExchCut (x : Name) (P Q : Term) (Θ : List NameType) : Set where
  exchCut : ∀{Γ Δ A}
          (π : Γ ++ Δ ∼[ bag ] Θ)
          (P⊢Γ : P ⊢ x ⦂ A , Γ)
          (Q⊢Δ : Q ⊢ x ⦂ A ^ , Δ)
          → ExchCut x P Q Θ

findCut : ∀{x P Q Θ} → ν x (P ∣ Q) ⊢ Θ → ExchCut x P Q Θ
findCut (cut P⊢Γ Q⊢Δ) = exchCut id P⊢Γ Q⊢Δ
findCut (exch π νx[P∣Q]⊢πΘ) with findCut νx[P∣Q]⊢πΘ
...| exchCut π′ P⊢Γ Q⊢Δ = exchCut (π ∘ π′) P⊢Γ Q⊢Δ

data ExchPool (P Q : Term) (Θ : List NameType) : Set where
  exchPool : ∀{Γ Δ x A m n}
           (π : x ⦂ ![ m + n ] A , Γ ++ Δ ∼[ bag ] Θ)
           (P⊢Γ : P ⊢ x ⦂ ![ m ] A , Γ)
           (Q⊢Δ : Q ⊢ x ⦂ ![ n ] A , Δ)
           → ExchPool P Q Θ

{-
⊢-resp-≈ : ∀{Γ P Q} →

  P ≈ Q → P ⊢ Γ →
  ---------------
  Q ⊢ Γ

⊢-resp-≈  refl P⊢Γ = P⊢Γ
⊢-resp-≈ (trans P≈Q Q≈R) P⊢Γ = ⊢-resp-≈ Q≈R (⊢-resp-≈ P≈Q P⊢Γ)
⊢-resp-≈  P≈Q (exch π P⊢Γ) = exch π (⊢-resp-≈ P≈Q P⊢Γ)
⊢-resp-≈ (ν-cong P≈P′) (cut P⊢Γ Q⊢Δ) = cut (⊢-resp-≈ P≈P′ P⊢Γ) Q⊢Δ
⊢-resp-≈  ν-swap (cut {Γ} {Δ} {A} {x} {P} P⊢Γ Q⊢Δ) = exch (swp₂ Γ) (cut Q⊢Δ (P.subst (λ A → P ⊢ x ⦂ A , Γ) (P.sym (^-inv A)) P⊢Γ))
⊢-resp-≈ (ν-assoc₁ c₁ c₂) (cut P⊢Γ QR⊢ΔΘ) with findCut QR⊢ΔΘ
...| exchCut π Q⊢Δ R⊢Θ = {!cut P⊢Γ Q⊢Δ!}
⊢-resp-≈ (ν-assoc₂ c₁ c₂) (cut PQ⊢ΓΔ R⊢Θ) with findCut PQ⊢ΓΔ
...| exchCut π P⊢Γ Q⊢Δ = {!!}
⊢-resp-≈  |-swap (⊢-| P⊢Γ Q⊢Δ) = {!!}
⊢-resp-≈  |-assoc₁ (⊢-| P⊢Γ QR⊢ΔΘ) = {!!}
⊢-resp-≈  |-assoc₂ (⊢-| PQ⊢ΓΔ R⊢Θ) = {!!}
-- -}
