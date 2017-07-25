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








infixr 30 _for_

_for_ : (w z x : Name) → Name
(w for z) x with x ≟ z
...| yes x≡z = w
...| no  x≢z = x

[/]-step : (w z : Name) (P : Term) → Term
[/]-step w z (τ P) = τ (P [ w / z ])
[/]-step w z (x ↔ y) = (w for z) x ↔ (w for z) y
[/]-step w z (ν x (P ∣ Q)) with x ≟ z
...| yes x≡z = ν x (P ∣ Q)
...| no  x≢z = ν x (P [ w / z ] ∣ Q [ w / z ])
[/]-step w z (x [ y ] (P ∣ Q)) with y ≟ z
...| yes y≡z = (w for z) x [ y ] (P ∣ Q [ w / z ])
...| no  y≢z = (w for z) x [ y ] (P [ w / z ] ∣ Q [ w / z ])
[/]-step w z (x ⟨ y ⟩ P) with y ≟ z
...| yes y≡z = (w for z) x ⟨ y ⟩ P
...| no  y≢z = (w for z) x ⟨ y ⟩ P [ w / z ]
[/]-step w z (x [] _) = (w for z) x [] 0 
[/]-step w z (x ⟨⟩ P) = (w for z) x ⟨⟩ P [ w / z ]
[/]-step w z (x [L] P) = (w for z) x [L] P [ w / z ]
[/]-step w z (x [R] P) = (w for z) x [R] P [ w / z ]
[/]-step w z (case x (P , Q)) = case ((w for z) x) (P [ w / z ] , Q [ w / z ])
[/]-step w z (crash x) = crash ((w for z) x)
[/]-step w z (⋆ x [ y ] P) with y ≟ z
...| yes y≡z = ⋆ (w for z) x [ y ] P
...| no  y≢z = ⋆ (w for z) x [ y ] P [ w / z ]
[/]-step w z (⋆ x ⟨ y ⟩ P) with y ≟ z
...| yes y≡z = ⋆ (w for z) x ⟨ y ⟩ P
...| no  y≢z = ⋆ (w for z) x ⟨ y ⟩ P [ w / z ]
[/]-step w z (P ∣ Q) = (P [ w / z ] ∣ Q [ w / z ])
[/]-step w z (P [ w′ / z′ ]) = {!!}


infix 5 _⟹_

data _⟹_ : (P P′ : Term) → Set where

  τ : ∀{P} →

    τ P ⟹ P

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
    -------------------------------------
    P [ x / y ] ⊢ x ⦂ ?[ m + n ] A , Γ

  exch : ∀{Γ Δ P} →

    Γ ∼[ bag ] Δ → P ⊢ Γ →
    ----------------------
    P ⊢ Δ


⊢-resp-≈ : ∀{Γ P Q} →

  P ≈ Q → P ⊢ Γ →
  ---------------
  Q ⊢ Γ

⊢-resp-≈  refl P⊢Γ = P⊢Γ
⊢-resp-≈ (trans P≈Q Q≈R) P⊢Γ = ⊢-resp-≈ Q≈R (⊢-resp-≈ P≈Q P⊢Γ)
⊢-resp-≈ P≈P′ (exch π P⊢Γ) = exch π (⊢-resp-≈ P≈P′ P⊢Γ)
⊢-resp-≈ (↔-cong cx cy) P⊢Γ rewrite cx | cy = P⊢Γ
⊢-resp-≈ (ν-cong cx P≈P′ Q≈Q′) (cut P⊢Γ Q⊢Δ) rewrite cx = cut (⊢-resp-≈ P≈P′ P⊢Γ) (⊢-resp-≈ Q≈Q′ Q⊢Δ)
⊢-resp-≈  ν-swap (cut P⊢Γ Q⊢Δ) = {!!}
⊢-resp-≈ (ν-assoc₁ cx cy) (cut P⊢Γ R⊢Θ) = {!!}
⊢-resp-≈ (ν-assoc₂ cx cy) (cut P⊢Γ R⊢Θ) = {!!}
⊢-resp-≈ ([·]-cong cx cy P≈P′ Q≈Q′) (⊢-⊗ P⊢Γ Q⊢Δ) rewrite cx | cy = ⊢-⊗ (⊢-resp-≈ P≈P′ P⊢Γ) (⊢-resp-≈ Q≈Q′ Q⊢Δ)
⊢-resp-≈ (⟨·⟩-cong cx cy P≈P′) (⊢-⅋ P⊢Γ) rewrite cx | cy = ⊢-⅋ (⊢-resp-≈ P≈P′ P⊢Γ)
⊢-resp-≈ ([]-cong cx) ⊢-𝟏 rewrite cx = ⊢-𝟏
⊢-resp-≈ (⟨⟩-cong cx P≈P′) (⊢-⊥ P⊢Γ) rewrite cx = ⊢-⊥ (⊢-resp-≈ P≈P′ P⊢Γ)
⊢-resp-≈ ([L]-cong cx P≈P′) (⊢-⊕₁ P⊢Γ) rewrite cx = ⊢-⊕₁ (⊢-resp-≈ P≈P′ P⊢Γ)
⊢-resp-≈ ([R]-cong cx P≈P′) (⊢-⊕₂ P⊢Γ) rewrite cx = ⊢-⊕₂ (⊢-resp-≈ P≈P′ P⊢Γ)
⊢-resp-≈ (case-cong cx P≈P′ Q≈Q′) (⊢-& P⊢Γ Q⊢Δ) rewrite cx = ⊢-& (⊢-resp-≈ P≈P′ P⊢Γ) (⊢-resp-≈ Q≈Q′ Q⊢Δ)
⊢-resp-≈ (crash-cong cx) ⊢-⊤ rewrite cx = ⊢-⊤
⊢-resp-≈ (⋆[]-cong cx cy P≈P′) (⊢-!₁ P⊢Γ) rewrite cx | cy = ⊢-!₁ (⊢-resp-≈ P≈P′ P⊢Γ)
⊢-resp-≈ (⋆⟨⟩-cong cx cy P≈P′) (⊢-?₁ P⊢Γ) rewrite cx | cy = ⊢-?₁ (⊢-resp-≈ P≈P′ P⊢Γ)
⊢-resp-≈ (|-cong P≈P′ Q≈Q′) (⊢-| P⊢Γ Q⊢Δ) = ⊢-| (⊢-resp-≈ P≈P′ P⊢Γ) (⊢-resp-≈ Q≈Q′ Q⊢Δ)
⊢-resp-≈  |-swap (⊢-| P⊢Γ Q⊢Δ) = {!⊢-| Q⊢Δ P⊢Γ!}
⊢-resp-≈  |-assoc₁ (⊢-| P⊢Γ (⊢-| Q⊢Δ R⊢Θ)) = {!!}
⊢-resp-≈  |-assoc₁ (⊢-| P⊢Γ (exch π QR⊢ΔΘ)) = {!!}
⊢-resp-≈  |-assoc₂ (⊢-| (⊢-| P⊢Γ Q⊢Δ) R⊢Θ) = {!!}
⊢-resp-≈  |-assoc₂ (⊢-| (exch π PQ⊢ΓΔ) R⊢Θ) = {!!}
⊢-resp-≈ ([/]-cong cx cy P≈P′) (cont P⊢Γ) rewrite cx | cy = cont (⊢-resp-≈ P≈P′ P⊢Γ)


-- -}
-- -}
-- -}
-- -}
-- -}
