module cpnd.term where

open import Agda.Builtin.FromNat public using (Number)
open import Data.Nat using (ℕ; _+_)
open import Data.List using (List) renaming (_∷_ to _,_; [] to ∅)
open import Data.Vec using (Vec; splitAt) renaming (_∷_ to _,_; [] to ∅)
open import Data.String public renaming (String to Name) using ()
open import Data.Product using ()
open import Function using (const)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import cpnd.util

infixr  5 _,_
infixr  8 _∣_
infix   9 _↔_
infixr 10 _[_]_ _[]_ _[L]_ _[R]_
infixr 10 _⟨_⟩_ _⟨⟩_
infixl 30 _[_]

data End : Set where
  zero : End

instance
  Number-End : Number End
  Number-End = record
    { Constraint = λ{n → n ≡ 0}
    ; fromNat    = λ{n → zero}
    }

data Subst : Set where
  _/_ : (w z : Name) → Subst

mutual
  data Term : Set where
    _↔_    : (x y : Name) → Term
    ν      : (x : Name) (PQ : Parr) → Term
    _[_]_  : (x y : Name) (PQ : Parr) → Term
    _⟨_⟩_  : (x y : Name) (P : Term) → Term
    _[]_   : (x : Name) (P : End) → Term
    _⟨⟩_   : (x : Name) (P : Term) → Term
    _[L]_  : (x : Name) (P : Term) → Term
    _[R]_  : (x : Name) (P : Term) → Term
    case   : (x : Name) (PQ : Case) → Term
    crash  : (x : Name) → Term
    ⋆_[_]_ : (x y : Name) (P : Term) → Term
    ⋆_⟨_⟩_ : (x y : Name) (P : Term) → Term
    _∣_     : (P Q : Term) → Term
    _[_]   : (P : Term) (σ : List Subst) → Term

  data Parr : Set where
    _∣_ : (P Q : Term) → Parr

  data Case : Set where
    _,_ : (P Q : Term) → Case


instance
  Pluggable-Subst : Pluggable Term (List Subst) Term
  Pluggable-Subst = record { _[_] = _[_] }


-- One-holed Terms

mutual
  data OhTerm : Set where
    □      : OhTerm
    ν      : (x : Name) (PQ : OhParr) → OhTerm
    _[_]_  : (x y : Name) (PQ : OhParr) → OhTerm
    _⟨_⟩_  : (x y : Name) (P : OhTerm) → OhTerm
    _⟨⟩_   : (x : Name) (P : OhTerm) → OhTerm
    _[L]_  : (x : Name) (P : OhTerm) → OhTerm
    _[R]_  : (x : Name) (P : OhTerm) → OhTerm
    case   : (x : Name) (PQ : OhCase) → OhTerm
    ⋆_[_]_ : (x y : Name) (P : OhTerm) → OhTerm
    ⋆_⟨_⟩_ : (x y : Name) (P : OhTerm) → OhTerm
    _<∣_    : (P : OhTerm) (Q : Term) → OhTerm
    _∣>_    : (P : Term) (Q : OhTerm) → OhTerm
    _[_]   : (P : OhTerm) (σ : List Subst) → OhTerm

  data OhParr : Set where
    _<∣_ : (P : OhTerm) (Q : Term) → OhParr
    _∣>_ : (P : Term) (Q : OhTerm) → OhParr

  data OhCase : Set where
    _<,_ : (P : OhTerm) (Q : Term) → OhCase
    _,>_ : (P : Term) (Q : OhTerm) → OhCase

plugOhTerm : OhTerm → Term → Term
plugOhTerm □ R = R
plugOhTerm (ν x (P <∣ Q)) R = ν x (plugOhTerm P R ∣ Q)
plugOhTerm (ν x (P ∣> Q)) R = ν x (P ∣ plugOhTerm Q R)
plugOhTerm (x [ y ] (P <∣ Q)) R = x [ y ] (plugOhTerm P R ∣ Q)
plugOhTerm (x [ y ] (P ∣> Q)) R = x [ y ] (P ∣ plugOhTerm Q R)
plugOhTerm (x ⟨ y ⟩ P) R = x ⟨ y ⟩ plugOhTerm P R
plugOhTerm (x ⟨⟩ P) R = x ⟨⟩ plugOhTerm P R
plugOhTerm (x [L] P) R = x [L] plugOhTerm P R
plugOhTerm (x [R] P) R = x [R] plugOhTerm P R
plugOhTerm (case x (P <, Q)) R = case x (plugOhTerm P R , Q)
plugOhTerm (case x (P ,> Q)) R = case x (P , plugOhTerm Q R)
plugOhTerm (⋆ x [ y ] P) R = ⋆ x [ y ] plugOhTerm P R
plugOhTerm (⋆ x ⟨ y ⟩ P) R = ⋆ x ⟨ y ⟩ plugOhTerm P R
plugOhTerm (P <∣ Q) R = (plugOhTerm P R ∣ Q)
plugOhTerm (P ∣> Q) R = (P ∣ plugOhTerm Q R)
plugOhTerm (P [ σ ]) R = plugOhTerm P R [ σ ]

instance
  Pluggable-OhTerm : Pluggable OhTerm Term Term
  Pluggable-OhTerm = record { _[_] = plugOhTerm }

-- Evaluation Prefix

mutual
  data EPParr : ℕ → Set where
    _∣_ : ∀{m n} → (G : EPTerm m) (H : EPTerm n) → EPParr (m + n)

  data EPTerm : ℕ → Set where
    □ : EPTerm 1
    ν : ∀{n} → (x : Name) (G : EPParr n) → EPTerm n

plugEPTerm : ∀{n} → EPTerm n → Vec Term n → Term
plugEPTerm □ (P , ∅) = P
plugEPTerm (ν x (_∣_ {m} {n} G H)) Ps with splitAt m Ps
... | (Ps₁ , Ps₂ , _) = {!!}

-- Evaluation Context

mutual
  data ECParr : Set where
    _<∣_ : (E : ECTerm) (Q : Term) → ECParr
    _∣>_ : (P : Term) (E : ECTerm) → ECParr

  data ECTerm : Set where
    □ : ECTerm
    ν : (x : Name) (E : ECParr) → ECTerm

plugECTerm : ECTerm → Term → Term
plugECTerm □ R = R
plugECTerm (ν x (E <∣ Q)) R = ν x (plugECTerm E R ∣ Q)
plugECTerm (ν x (P ∣> E)) R = ν x (P ∣ plugECTerm E R)

instance
  Pluggable-ECTerm : Pluggable ECTerm Term Term
  Pluggable-ECTerm = record { _[_] = plugECTerm }

-- Free Variables

infixr 5 _∈_

data _∈_ (w : Name) : (P : Term) → Set where
  ∈-↔₁     : ∀{y} → w ∈ w ↔ y
  ∈-↔₂     : ∀{x} → w ∈ x ↔ w
  ∈-ν₁     : ∀{x P Q} → w ≢ x → w ∈ P → w ∈ ν x (P ∣ Q)
  ∈-ν₂     : ∀{x P Q} → w ≢ x → w ∈ Q → w ∈ ν x (P ∣ Q)
  ∈-[·]₀   : ∀{y P Q} → w ∈ w [ y ] (P ∣ Q)
  ∈-[·]₁   : ∀{x y P Q} → w ≢ y → w ∈ P → w ∈ x [ y ] (P ∣ Q)
  ∈-[·]₂   : ∀{x y P Q} → w ∈ Q → w ∈ x [ y ] (P ∣ Q)
  ∈-[]     : w ∈ w [] 0
  ∈-⟨·⟩₀   : ∀{y P} → w ∈ w ⟨ y ⟩ P
  ∈-⟨·⟩₁   : ∀{x y P} → w ≢ y → w ∈ P → w ∈ x ⟨ y ⟩ P
  ∈-⟨⟩₀    : ∀{y P} → w ∈ w ⟨ y ⟩ P
  ∈-⟨⟩₁    : ∀{x y P} → w ≢ y → w ∈ P → w ∈ x ⟨ y ⟩ P
  ∈-[L]₀   : ∀{P} → w ∈ w [L] P
  ∈-[L]₁   : ∀{x P} → w ∈ P → w ∈ x [L] P
  ∈-[R]₀   : ∀{P} → w ∈ w [R] P
  ∈-[R]₁   : ∀{x P} → w ∈ P → w ∈ x [R] P
  ∈-case₀  : ∀{P Q} → w ∈ case w (P , Q)
  ∈-case₁  : ∀{x P Q} → w ∈ P → w ∈ case x (P , Q)
  ∈-case₂  : ∀{x P Q} → w ∈ Q → w ∈ case x (P , Q)
  ∈-crash₀ : w ∈ crash w
  ∈-⋆[·]₀  : ∀{y P} → w ∈ ⋆ w ⟨ y ⟩ P
  ∈-⋆[·]₁  : ∀{x y P} → w ≢ y → w ∈ P → w ∈ ⋆ x ⟨ y ⟩ P
  ∈-⋆⟨·⟩₀  : ∀{y P} → w ∈ ⋆ w ⟨ y ⟩ P
  ∈-⋆⟨·⟩₁  : ∀{x y P} → w ≢ y → w ∈ P → w ∈ ⋆ x ⟨ y ⟩ P
  ∈-|₀     : ∀{P Q} → w ∈ P → w ∈ (P ∣ Q)
  ∈-|₁     : ∀{P Q} → w ∈ Q → w ∈ (P ∣ Q)
  ∈-[∅]    : ∀{P} → w ∈ P → w ∈ P [ ∅ ]
  ∈-[/]₀   : ∀{x y σ P} → w ≢ y → w ∈ P [ σ ] → w ∈ P [ x / y , σ ]
  ∈-[/]₁   : ∀{x y σ P} → w ≡ x → y ∈ P [ σ ] → w ∈ P [ x / y , σ ]

_∉_ : (w : Name) (P : Term) → Set
w ∉ P = ¬ (w ∈ P)


