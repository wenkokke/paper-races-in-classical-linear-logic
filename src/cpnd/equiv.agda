module cpnd.equiv where

open import Function using (_$_)
open import Relation.Binary using (IsEquivalence; Reflexive; Symmetric; Transitive; Setoid)
open import Relation.Binary.EqReasoning as EqR using ()
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import cpnd.term

-- Structural Congruence

infix 5 _≈_

data _≈_ : (P Q : Term) → Set where

  refl    : Reflexive _≈_
  trans   : Transitive _≈_
  cong    : ∀{P P′} (C : OhTerm) →

    P ≈ P′ →
    --------------------
    plugOhTerm C P ≈ plugOhTerm C P′

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

  |-extrusion₁ : ∀{x P Q R} →

    x ∉ P →
    ------------------------------------
    ν x ((P ∣ Q) ∣ R) ≈ (P ∣ ν x (Q ∣ R))

  |-extrusion₂ : ∀{x P Q R} →

    x ∉ P →
    -----------------------------------
    (P ∣ ν x (Q ∣ R)) ≈ ν x ((P ∣ Q) ∣ R)


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
sym  refl             = refl
sym (trans p₁ p₂)     = trans (sym p₂) (sym p₁)
sym (cong C p)        = cong C (sym p)
sym  ν-swap           = ν-swap
sym (ν-assoc₁ cx cy)  = ν-assoc₂ cx cy
sym  |-swap           = |-swap
sym  |-assoc₁         = |-assoc₂
sym (|-extrusion₁ cx) = |-extrusion₂ cx
sym (|-extrusion₂ cx) = |-extrusion₁ cx


isEquivalence-≈ : IsEquivalence _≈_
isEquivalence-≈ = record
  { refl  = refl
  ; sym   = sym
  ; trans = trans
  }


Setoid-Term : Setoid _ _
Setoid-Term = record
  { Carrier       = Term
  ; _≈_           = _≈_
  ; isEquivalence = isEquivalence-≈
  }

open EqR Setoid-Term

