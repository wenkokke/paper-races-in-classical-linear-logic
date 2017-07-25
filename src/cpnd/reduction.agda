module cpnd.reduction where

open import Data.List using (List; _∷ʳ_) renaming (_∷_ to _,_; [] to ∅)
open import Function using (id; _∘_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import cpnd.term

rename : Subst → Name → Name
rename (w / z) x with x ≟ z
...| yes x≡z = w
...| no  x≢z = x

renameAll : List Subst → Name → Name
renameAll ∅ = id
renameAll (w/z , σ) = renameAll σ ∘ rename w/z

α-step : Subst → Term → Term
α-step w/z@(w / z) = go
  where
    go : Term → Term
    go (x ↔ y) = rename w/z x ↔ rename w/z y
    go (ν x (P ∣ Q)) with x ≟ z
    ...| yes x≡z = ν x (P ∣ Q)
    ...| no  x≢z = ν x (P [ w/z , ∅ ] ∣ Q [ w/z , ∅ ])
    go (x [ y ] (P ∣ Q)) with y ≟ z
    ...| yes y≡z = rename w/z x [ y ] (P ∣ Q [ w/z , ∅ ])
    ...| no  y≢z = rename w/z x [ y ] (P [ w/z , ∅ ] ∣ Q [ w/z , ∅ ])
    go (x ⟨ y ⟩ P) with y ≟ z
    ...| yes y≡z = rename w/z x ⟨ y ⟩ P
    ...| no  y≢z = rename w/z x ⟨ y ⟩ P [ w/z , ∅ ]
    go (x [] _)  = rename w/z x [] 0
    go (x ⟨⟩ P)  = rename w/z x ⟨⟩ P [ w/z , ∅ ]
    go (x [L] P) = rename w/z x [L] P [ w/z , ∅ ]
    go (x [R] P) = rename w/z x [R] P [ w/z , ∅ ]
    go (case x (P , Q))
                 = case (rename w/z x) (P [ w/z , ∅ ] , Q [ w/z , ∅ ])
    go (crash x) = crash (rename w/z x)
    go (⋆ x [ y ] P) with y ≟ z
    ...| yes y≡z = ⋆ rename w/z x [ y ] P
    ...| no  y≢z = ⋆ rename w/z x [ y ] P [ w/z , ∅ ]
    go (⋆ x ⟨ y ⟩ P) with y ≟ z
    ...| yes y≡z = ⋆ rename w/z x ⟨ y ⟩ P
    ...| no  y≢z = ⋆ rename w/z x ⟨ y ⟩ P [ w/z , ∅ ]
    go (P ∣ Q) = (P [ w/z , ∅ ] ∣ Q [ w/z , ∅ ])
    go (P [ σ ]) = P [ σ ∷ʳ w/z ]


infix 5 _⟹_

data _⟹_ : (P P′ : Term) → Set where

  α : ∀{w/z σ P} →

    P [ w/z , σ ] ⟹ (α-step w/z P) [ σ ]

  ↔₁ : ∀{w x P} →

    ν x (w ↔ x ∣ P) ⟹ P [ w / x , ∅ ]

  ↔₂ : ∀{w x P} →

    ν x (x ↔ w ∣ P) ⟹ P [ w / x , ∅ ]

  β⊗⅋ : ∀{x y z P Q R} →

    ν x (x [ y ] (P ∣ Q) ∣ x ⟨ z ⟩ R) ⟹ ν y (P ∣ ν x (Q ∣ R [ y / z , ∅ ]))

  β𝟏⊥ : ∀{x P} →

    ν x (x [] 0 ∣ x ⟨⟩ P) ⟹ P

  β⊕&₁ : ∀{x P Q R} →

    ν x (x [L] P ∣ case x (Q , R)) ⟹ ν x (P ∣ Q)

  β⊕&₂ : ∀{x P Q R} →

    ν x (x [R] P ∣ case x (Q , R)) ⟹ ν x (P ∣ R)

  β⋆₁ : ∀{x y z P R} →

    ν x (⋆ x [ y ] P ∣ ⋆ x ⟨ z ⟩ R) ⟹ ν y (P ∣ R [ y / z , ∅ ])

  β⋆n : ∀{x y z P Q R} →

    ν x ((⋆ x [ y ] P ∣ Q) ∣ ⋆ x ⟨ z ⟩ R) ⟹ ν x (Q ∣ ν y (P ∣ R [ y / z , ∅ ]))

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

    P ≈ Q → Q ⟹ Q′ → Q′ ≈ P′ →
    ----------------------------
    P ⟹ P′


-- -}
-- -}
-- -}
-- -}
-- -}
