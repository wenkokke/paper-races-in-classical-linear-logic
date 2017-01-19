open import Data.Nat as ℕ using (ℕ)
open import Data.List as L using (List; _∷_; []; _++_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

module Data.Pos where


data ℤ⁺ : Set where
  one : ℤ⁺
  suc : ℤ⁺ → ℤ⁺

_+_ : ℤ⁺ → ℤ⁺ → ℤ⁺
one   + n = suc n
suc m + n = suc (m + n)

toℕ : ℤ⁺ → ℕ
toℕ  one    = ℕ.suc ℕ.zero
toℕ (suc n) = ℕ.suc (toℕ n)

toℕ-+ : (m {n} : ℤ⁺) → toℕ m ℕ.+ toℕ n ≡ toℕ (m + n)
toℕ-+  one    = P.refl
toℕ-+ (suc m) = P.cong ℕ.suc (toℕ-+ m)

replicate : ∀ {a} {A : Set a} (n : ℤ⁺) (x : A) → List A
replicate  one    x = x ∷ []
replicate (suc n) x = x ∷ replicate n x

replicate-++ : ∀ {a} {A : Set a} (m n : ℤ⁺) {x : A} →
  replicate m x ++ replicate n x ≡ replicate (m + n) x
replicate-++  one    n = P.refl
replicate-++ (suc m) n = P.cong (_ ∷_) (replicate-++ m n)
