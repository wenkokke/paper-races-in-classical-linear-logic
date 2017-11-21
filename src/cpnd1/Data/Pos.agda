open import Agda.Builtin.FromNat
open import Data.Nat.Base  as ℕ using (ℕ; suc; zero; _>_; _≤?_)
open import Data.List.Base as L using (List; _∷_; []; _++_)
open import Relation.Nullary.Decidable using (True)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

module Data.Pos where

open import Data.Nat.FromNat public

data ℕ⁺ : Set where
  suc : ℕ → ℕ⁺

instance
  NumberPos : Number ℕ⁺
  NumberPos = record { Constraint = Pos; fromNat = fromℕ }
    where
      Pos : ℕ → Set
      Pos n = True (suc zero ≤? n)
      fromℕ : (n : ℕ) {{p : Pos n}} → ℕ⁺
      fromℕ zero {{()}}
      fromℕ (suc zero)    = suc zero
      fromℕ (suc (suc n)) = suc (suc n)

toℕ : ℕ⁺ → ℕ
toℕ (suc n) = suc n

_+_ : ℕ⁺ → ℕ⁺ → ℕ⁺
suc m + n = suc (m ℕ.+ toℕ n)

toℕ-+ : (m {n} : ℕ⁺) → toℕ m ℕ.+ toℕ n ≡ toℕ (m + n)
toℕ-+ (suc m) = P.refl

replicate⁺ : ∀ {a} {A : Set a} → ℕ⁺ → A → List A
replicate⁺ (suc n) x = x ∷ L.replicate n x

replicate⁺-++-commute : ∀ {a} {A : Set a} {x : A} (m n : ℕ⁺) →
  replicate⁺ m x ++ replicate⁺ n x ≡ replicate⁺ (m + n) x
replicate⁺-++-commute (suc m) (suc n)
  = P.cong (_ ∷_) (replicate-++-commute m (suc n))
  where
    replicate-++-commute : ∀ {a} {A : Set a} {x : A} (m n : ℕ) →
      L.replicate m x ++ L.replicate n x ≡ L.replicate (m ℕ.+ n) x
    replicate-++-commute  zero   n = P.refl
    replicate-++-commute (suc m) n = P.cong (_ ∷_) (replicate-++-commute m n)
