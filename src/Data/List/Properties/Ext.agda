open import Algebra
open import Data.List
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning


module Data.List.Properties.Ext where


private
  module ++ {a} {A : Set a} = Monoid (monoid A)


concat-++ : ∀ {a} {A : Set a} (xs : List A) (xss : List (List A)) →
  concat (xs ∷ xss) ≡ xs ++ concat xss
concat-++ []       xss = refl
concat-++ (x ∷ xs) xss = cong (x ∷_) (concat-++ xs xss)

concat-++-commute : ∀ {a} {A : Set a} (xss yss : List (List A)) →
  concat xss ++ concat yss ≡ concat (xss ++ yss)
concat-++-commute []         yss = refl
concat-++-commute (xs ∷ xss) yss =
  begin
    (xs ++ concat xss) ++ concat yss
  ≡⟨ ++.assoc xs (concat xss) (concat yss) ⟩
    xs ++ concat xss ++ concat yss
  ≡⟨ cong (xs ++_) (concat-++-commute xss yss) ⟩
    xs ++ concat (xss ++ yss)
  ∎
