module cpnd.term where

open import Agda.Builtin.FromNat public using (Number)
open import Data.List using (List) renaming (_∷_ to _,_; [] to ∅)
open import Data.List.Any using (Any; here; there)
open import Data.Product using (_×_)
open import Data.String public renaming (String to Name) using (_≟_)
open import Data.Sum using (_⊎_)
open import Data.Nat using (ℕ)
open import Data.Unit using (⊤)
open import Function using (const; _$_)
open import Relation.Binary using (IsEquivalence; Reflexive; Symmetric; Transitive)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (¬_)


instance
  Number-ℕ : Number ℕ
  Number-ℕ = record
    { Constraint = const ⊤
    ; fromNat    = λ{n → n}
    }

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

plug : OhTerm → Term → Term
plug □ R = R
plug (ν x (P <∣ Q)) R = ν x (plug P R ∣ Q)
plug (ν x (P ∣> Q)) R = ν x (P ∣ plug Q R)
plug (x [ y ] (P <∣ Q)) R = x [ y ] (plug P R ∣ Q)
plug (x [ y ] (P ∣> Q)) R = x [ y ] (P ∣ plug Q R)
plug (x ⟨ y ⟩ P) R = x ⟨ y ⟩ plug P R
plug (x ⟨⟩ P) R = x ⟨⟩ plug P R
plug (x [L] P) R = x [L] plug P R
plug (x [R] P) R = x [R] plug P R
plug (case x (P <, Q)) R = case x (plug P R , Q)
plug (case x (P ,> Q)) R = case x (P , plug Q R)
plug (⋆ x [ y ] P) R = ⋆ x [ y ] plug P R
plug (⋆ x ⟨ y ⟩ P) R = ⋆ x ⟨ y ⟩ plug P R
plug (P <∣ Q) R = (plug P R ∣ Q)
plug (P ∣> Q) R = (P ∣ plug Q R)
plug (P [ σ ]) R = plug P R [ σ ]

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


-- Structural Congruence

infix 5 _≈_

data _≈_ : (P Q : Term) → Set where

  refl    : Reflexive _≈_
  trans   : Transitive _≈_
  cong    : ∀{P P′} (C : OhTerm) →

    P ≈ P′ →
    --------------------
    plug C P ≈ plug C P′

  ν-swap  : ∀{x P Q} →

    ------------------------
    ν x (P ∣ Q) ≈ ν x (Q ∣ P)

  ν-assoc₁ : ∀{x y P Q R} →

    y ∉ P  →  x ∉ R  →
    -------------------------------------------
    ν x (P ∣ ν y (Q ∣ R)) ≈ ν y (ν x (P ∣ Q) ∣ R)

  |-swap  : ∀{P Q} →

    ----------------
    (P ∣ Q) ≈ (Q ∣ P)

  |-assoc₁ : ∀{P Q R} →

    --------------------------
    (P ∣ (Q ∣ R)) ≈ ((P ∣ Q) ∣ R)


ν-assoc₂ : ∀{x y P Q R} →

  y ∉ P  →  x ∉ R  →
  -------------------------------------------
  ν y (ν x (P ∣ Q) ∣ R) ≈ ν x (P ∣ ν y (Q ∣ R))

ν-assoc₂ {x} {y} {P} {Q} {R} c₁ c₂
  = trans (cong (ν y (□ <∣ R)) ν-swap)
  $ trans ν-swap
  $ trans (ν-assoc₁ c₂ c₁)
  $ trans ν-swap
  $ cong (ν x (P ∣> □)) ν-swap


|-assoc₂ : ∀{P Q R} →

  --------------------------
  ((P ∣ Q) ∣ R) ≈ (P ∣ (Q ∣ R))

|-assoc₂ {P} {Q} {R}
  = trans (cong (□ <∣ R) |-swap)
  $ trans |-swap
  $ trans |-assoc₁
  $ trans |-swap
  $ cong (P ∣> □) |-swap


sym : Symmetric _≈_
sym  refl            = refl
sym (trans p₁ p₂)    = trans (sym p₂) (sym p₁)
sym (cong C p)       = cong C (sym p)
sym  ν-swap          = ν-swap
sym (ν-assoc₁ cx cy) = ν-assoc₂ cx cy
sym  |-swap          = |-swap
sym  |-assoc₁        = |-assoc₂


IsEquivalence-≈ : IsEquivalence _≈_
IsEquivalence-≈ = record
  { refl  = refl
  ; sym   = sym
  ; trans = trans
  }
