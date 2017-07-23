open import Agda.Builtin.FromNat using (Number)
open import Data.List using (List; _++_) renaming (_∷_ to _,_; [] to ∅)
open import Data.List.Any.Membership.Propositional using (_∼[_]_; bag)
open import Data.Nat as Nat using (ℕ; suc; zero; _≤?_; _≤_; s≤s)
open import Data.String using (String; _≟_)
open import Data.Unit as Unit using ()
open import Function using (const)
open import Relation.Binary using (Reflexive; Symmetric; Transitive)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_; refl)
open import Logic.Context


instance
  Number-ℕ : Number ℕ
  Number-ℕ = record
    { Constraint = const Unit.⊤
    ; fromNat    = λ{n → n}
    }

Name : Set
Name = String

infixr 5 _,_
infixr 8 _∣_
infix 9 _↔_
infixr 10 _[_]_ _[]_ _[L]_ _[R]_
infixr 10 _⟨_⟩_ _⟨⟩_


data End : Set where
  zero : End

instance
  EndNumber : Number End
  EndNumber = record
    { Constraint = λ{n → n ≡ 0}
    ; fromNat    = λ{n → zero}
    }

mutual
  data Parr : Set where
    _∣_ : (P Q : Term) → Parr

  data Case : Set where
    _,_ : (P Q : Term) → Case

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

_∉_ : (w : Name) (P : Term) → Set
w ∉ P = ¬ (w ∈ P)

infix 5 _≈_

data _≈_ : (P Q : Term) → Set where

  refl    : Reflexive _≈_
  trans   : Transitive _≈_

  ↔-cong  : ∀{x y x′ y′} →

    x ≡ x′ → y ≡ y′ →
    -----------------
    x ↔ y ≈ x′ ↔ y′

  ν-cong : ∀{x x′ P Q P′ Q′} →

    x ≡ x′ → P ≈ P′ → Q ≈ Q′ →
    --------------------------
    ν x (P ∣ Q) ≈ ν x′ (P′ ∣ Q′)

  ν-swap  : ∀{x P Q} →

    ------------------------
    ν x (P ∣ Q) ≈ ν x (Q ∣ P)

  ν-assoc₁ : ∀{x y P Q R} →

    y ∉ P  →  x ∉ R  →
    -------------------------------------------
    ν x (P ∣ ν y (Q ∣ R)) ≈ ν y (ν x (P ∣ Q) ∣ R)

  ν-assoc₂ : ∀{x y P Q R} →

    y ∉ P  →  x ∉ R  →
    -------------------------------------------
    ν y (ν x (P ∣ Q) ∣ R) ≈ ν x (P ∣ ν y (Q ∣ R))

  [·]-cong : ∀{x y x′ y′ P Q P′ Q′} →

    x ≡ x′ → y ≡ y′ → P ≈ P′ → Q ≈ Q′ →
    ------------------------------------
    x [ y ] (P ∣ Q) ≈ x′ [ y′ ] (P′ ∣ Q′)

  ⟨·⟩-cong : ∀{x y x′ y′ P P′} →

    x ≡ x′ → y ≡ y′ → P ≈ P′ →
    --------------------------
    x ⟨ y ⟩ P ≈ x′ ⟨ y′ ⟩ P′

  []-cong : ∀{x x′} →

    x ≡ x′ →
    -----------------
    x [] 0 ≈ x′ [] 0

  ⟨⟩-cong : ∀{x x′ P P′} →

    x ≡ x′ → P ≈ P′ →
    -----------------
    x ⟨⟩ P ≈ x′ ⟨⟩ P′

  [L]-cong : ∀{x x′ P P′} →

    x ≡ x′ → P ≈ P′ →
    -------------------
    x [L] P ≈ x′ [L] P′

  [R]-cong : ∀{x x′ P P′} →

    x ≡ x′ → P ≈ P′ →
    -------------------
    x [R] P ≈ x′ [R] P′

  case-cong : ∀{x x′ P Q P′ Q′} →

    x ≡ x′ → P ≈ P′ → Q ≈ Q′ →
    ----------------------------------
    case x (P , Q) ≈ case x′ (P′ , Q′)

  crash-cong : ∀{x x′} →

    x ≡ x′ →
    ------------------
    crash x ≈ crash x′

  ⋆[]-cong : ∀{x x′ y y′ P P′} →

    x ≡ x′ → y ≡ y′ → P ≈ P′ →
    ----------------------------
    ⋆ x [ y ] P ≈ ⋆ x′ [ y′ ] P′

  ⋆⟨⟩-cong : ∀{x x′ y y′ P P′} →

    x ≡ x′ → y ≡ y′ → P ≈ P′ →
    ----------------------------
    ⋆ x ⟨ y ⟩ P ≈ ⋆ x′ ⟨ y′ ⟩ P′

  |-cong : ∀{P Q P′ Q′} →

    P ≈ P′ → Q ≈ Q′ →
    ------------------
    (P ∣ Q) ≈ (P′ ∣ Q′)

  |-swap  : ∀{P Q} →

    ----------------
    (P ∣ Q) ≈ (Q ∣ P)

  |-assoc₁ : ∀{P Q R} →

    --------------------------
    (P ∣ (Q ∣ R)) ≈ ((P ∣ Q) ∣ R)

  |-assoc₂ : ∀{P Q R} →

    --------------------------
    ((P ∣ Q) ∣ R) ≈ (P ∣ (Q ∣ R))


sym : Symmetric _≈_
sym  refl                  = refl
sym (trans p₁ p₂)          = trans (sym p₂) (sym p₁)
sym (↔-cong c₁ c₂)         = ↔-cong (P.sym c₁) (P.sym c₂)
sym (ν-cong c p₁ p₂)       = ν-cong (P.sym c) (sym p₁) (sym p₂)
sym  ν-swap                = ν-swap
sym (ν-assoc₁ c₁ c₂)       = ν-assoc₂ c₁ c₂
sym (ν-assoc₂ c₁ c₂)       = ν-assoc₁ c₁ c₂
sym ([·]-cong c₁ c₂ p₁ p₂) = [·]-cong (P.sym c₁) (P.sym c₂) (sym p₁) (sym p₂)
sym (⟨·⟩-cong c₁ c₂ p)     = ⟨·⟩-cong (P.sym c₁) (P.sym c₂) (sym p)
sym ([]-cong c₁)           = []-cong (P.sym c₁)
sym (⟨⟩-cong c₁ p)         = ⟨⟩-cong (P.sym c₁) (sym p)
sym ([L]-cong c₁ p)        = [L]-cong (P.sym c₁) (sym p)
sym ([R]-cong c₁ p)        = [R]-cong (P.sym c₁) (sym p)
sym (case-cong c₁ p₁ p₂)   = case-cong (P.sym c₁) (sym p₁) (sym p₂)
sym (crash-cong c₁)        = crash-cong (P.sym c₁)
sym (⋆[]-cong c₁ c₂ p)     = ⋆[]-cong (P.sym c₁) (P.sym c₂) (sym p)
sym (⋆⟨⟩-cong c₁ c₂ p)     = ⋆⟨⟩-cong (P.sym c₁) (P.sym c₂) (sym p)
sym (|-cong p₁ p₂)         = |-cong (sym p₁) (sym p₂)
sym  |-swap                = |-swap
sym  |-assoc₁              = |-assoc₂
sym  |-assoc₂              = |-assoc₁



infixr 30 _for_

_for_ : (w z x : Name) → Name
(w for z) x with x ≟ z
...| yes x≡z = w
...| no  x≢z = x


infixl 30 _[_/_]

_[_/_] : (P : Term) (w z : Name) → Term
(x ↔ y) [ w / z ]
             = (w for z) x ↔ (w for z) y
(ν x (P ∣ Q)) [ w / z ]
  with x ≟ z
...| yes x≡z = ν x (P           ∣ Q [ w / z ])
...| no  x≢z = ν x (P [ w / z ] ∣ Q [ w / z ])
(x [ y ] (P ∣ Q)) [ w / z ]
  with y ≟ z
...| yes y≡z = (w for z) x [ y ] (P           ∣ Q [ w / z ])
...| no  y≢z = (w for z) x [ y ] (P [ w / z ] ∣ Q [ w / z ])
(x ⟨ y ⟩ P) [ w / z ]
  with y ≟ z
...| yes y≡z = (w for z) x ⟨ y ⟩ P
...| no  y≢z = (w for z) x ⟨ y ⟩ P [ w / z ]
(x [] _) [ w / z ]
             = (w for z) x [] 0
(x ⟨⟩ P) [ w / z ]
             = (w for z) x ⟨⟩ P [ w / z ]
(x [L] P) [ w / z ]
             = (w for z) x [L] P [ w / z ]
(x [R] P) [ w / z ]
             = (w for z) x [R] P [ w / z ]
(case x (P , Q)) [ w / z ]
             = case ((w for z) x) (P [ w / z ] , Q [ w / z ])
(crash x) [ w / z ]
             = crash ((w for z) x)
(⋆ x [ y ] P) [ w / z ]
  with y ≟ z
...| yes y≡z = ⋆ (w for z) x [ y ] P
...| no  y≢z = ⋆ (w for z) x [ y ] P [ w / z ]
(⋆ x ⟨ y ⟩ P) [ w / z ]
  with y ≟ z
...| yes y≡z = ⋆ (w for z) x ⟨ y ⟩ P
...| no  y≢z = ⋆ (w for z) x ⟨ y ⟩ P [ w / z ]
(P ∣ Q) [ w / z ] = (P [ w / z ] ∣ Q [ w / z ])


infix 5 _⟹_

data _⟹_ : (P P′ : Term) → Set where
  ↔₁ : ∀{w x P} →

    ν x (w ↔ x ∣ P) ⟹ P [ w / x ]

  ↔₂ : ∀{w x P} →

    ν x (x ↔ w ∣ P) ⟹ P [ w / x ]

  β⊗⅋ : ∀{x y z P Q R} →

    ν x (x [ y ] (P ∣ Q) ∣ x ⟨ z ⟩ R) ⟹ ν y (P ∣ ν x (Q ∣ R [ y / z ]))

  β𝟏⊥ : ∀{x P} →

    ν x (x [] 0 ∣ x ⟨⟩ P) ⟹ P

  β⊕&₁ : ∀{x P Q R} →

    ν x (x [L] P ∣ case x (Q , R)) ⟹ ν x (P ∣ Q)

  β⊕&₂ : ∀{x P Q R} →

    ν x (x [R] P ∣ case x (Q , R)) ⟹ ν x (P ∣ R)

  β⋆₁ : ∀{x y z P R} →

    ν x (⋆ x [ y ] P ∣ ⋆ x ⟨ z ⟩ R) ⟹ ν y (P ∣ R [ y / z ])

  β⋆n : ∀{x y z P Q R} →

    ν x ((⋆ x [ y ] P ∣ Q) ∣ ⋆ x ⟨ z ⟩ R) ⟹ ν x (Q ∣ ν y (P ∣ R [ y / z ]))

  κ⊗₁ : ∀{x y z P Q R} →

    x ≢ y → x ≢ z → x ∉ Q →
    ---------------------------------------------------
    ν x (y [ z ] (P ∣ Q) ∣ R) ⟹ y [ z ] (ν x (P ∣ R) ∣ Q)

  κ⊗₂ : ∀{x y z P Q R} →

    x ≢ y → x ≢ z → x ∉ P →
    ---------------------------------------------------
    ν x (y [ z ] (P ∣ Q) ∣ R) ⟹ y [ z ] (P ∣ ν x (Q ∣ R))

  κ⅋ : ∀{x y z P R} →

    x ≢ y → x ≢ z →
    ----------------------------------------
    ν x (y ⟨ z ⟩ P ∣ R) ⟹ y ⟨ z ⟩ ν x (P ∣ R)

  κ⊥ : ∀{x y P R} →

    x ≢ y →
    -----------------------------------
    ν x (y ⟨⟩ P ∣ R) ⟹ y ⟨⟩ ν x (P ∣ R)

  κ⊕₁ : ∀{x y P R} →

    x ≢ y →
    -------------------------------------
    ν x (y [L] P ∣ R) ⟹ y [L] ν x (P ∣ R)

  κ⊕₂ : ∀{x y P R} →

    x ≢ y →
    -------------------------------------
    ν x (y [R] P ∣ R) ⟹ y [R] ν x (P ∣ R)

  κ& : ∀{x y P Q R} →

    x ≢ y →
    ------------------------------------------------------------
    ν x (case y (P , Q) ∣ R) ⟹ case y (ν x (P ∣ R) , ν x (Q ∣ R))

  κ⊤ : ∀{x y R} →

    x ≢ y →
    ----------------------------
    ν x (crash y ∣ R) ⟹ crash y

  κ! : ∀{x y z P R} →

    x ≢ y → x ≢ z →
    ---------------------------------------------
    ν x (⋆ y [ z ] P ∣ R) ⟹ ⋆ y [ z ] ν x (P ∣ R)

  κ? : ∀{x y z P R} →

    x ≢ y → x ≢ z →
    ---------------------------------------------
    ν x (⋆ y ⟨ z ⟩ P ∣ R) ⟹ ⋆ y [ z ] ν x (P ∣ R)

  κ| : ∀{x P Q R} →

    x ∉ P →
    ------------------------------------
    ν x ((P ∣ Q) ∣ R) ⟹ (P ∣ ν x (Q ∣ R))

  γν : ∀{x P Q P′} →

    P ⟹ P′ →
    --------------------------
    ν x (P ∣ Q) ⟹ ν x (P′ ∣ Q)

  γ| : ∀{P Q P′} →

    P ⟹ P′ →
    ------------------
    (P ∣ Q) ⟹ (P′ ∣ Q)

  γ≈ : ∀{P Q Q′ P′} →

    P ≈ Q → Q ⟹ Q′ → Q′ ≡ P′ →
    ----------------------------
    P ⟹ P′


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
    P ⊢ x ⦂ ⊥ , Γ

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
    -------------------------------------
    P [ x / y ] ⊢ x ⦂ ?[ m + n ] A , Γ

  exch : ∀{Γ Δ P} →

    Γ ∼[ bag ] Δ → P ⊢ Γ →
    ----------------------
    P ⊢ Δ

{-
⊢-resp-≈ : ∀{Γ P Q} →

  P ≈ Q → P ⊢ Γ →
  ---------------
  Q ⊢ Γ

⊢-resp-≈  refl P⊢Γ = P⊢Γ
⊢-resp-≈ (trans P≈Q Q≈R) P⊢Γ = ⊢-resp-≈ Q≈R (⊢-resp-≈ P≈Q P⊢Γ)
⊢-resp-≈ (↔-cong cx cy) P⊢Γ rewrite cx | cy = P⊢Γ
⊢-resp-≈ (ν-cong cx P≈P′ Q≈Q′) P⊢Γ rewrite cx = {!!}
⊢-resp-≈  ν-swap P⊢Γ = {!!}
⊢-resp-≈ (ν-assoc₁ cx cy) P⊢Γ = {!!}
⊢-resp-≈ (ν-assoc₂ cx cy) P⊢Γ = {!!}
⊢-resp-≈ ([·]-cong cx cy P≈Q P≈Q₁) P⊢Γ = {!!}
⊢-resp-≈ (⟨·⟩-cong cx cy P≈Q) P⊢Γ = {!!}
⊢-resp-≈ ([]-cong cx) P⊢Γ = {!!}
⊢-resp-≈ (⟨⟩-cong cx P≈Q) P⊢Γ = {!!}
⊢-resp-≈ ([L]-cong cx P≈Q) P⊢Γ = {!!}
⊢-resp-≈ ([R]-cong cx P≈Q) P⊢Γ = {!!}
⊢-resp-≈ (case-cong cx P≈Q P≈Q₁) P⊢Γ = {!!}
⊢-resp-≈ (crash-cong cx) P⊢Γ = {!!}
⊢-resp-≈ (⋆[]-cong cx cy P≈Q) P⊢Γ = {!!}
⊢-resp-≈ (⋆⟨⟩-cong cx cy P≈Q) P⊢Γ = {!!}
⊢-resp-≈ (|-cong P≈P′ Q≈Q′) P⊢Γ = {!!}
⊢-resp-≈  |-swap P⊢Γ = {!!}
⊢-resp-≈  |-assoc₁ P⊢Γ = {!!}
⊢-resp-≈  |-assoc₂ P⊢Γ = {!!}


-- -}
-- -}
-- -}
-- -}
-- -}
