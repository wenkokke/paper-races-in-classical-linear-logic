open import Algebra
open import Category.Monad
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Pos as ℕ⁺
open import Data.List as L using (List; []; _∷_; _++_; map)
open import Data.List.Any as LA using (Any; here; there)
open import Data.List.Any.BagAndSetEquality as B
open import Data.Product as PR using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_$_; _∘_; flip)
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse as I using ()
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_)

open import Logic.Context
open import nodcap.Base
open import nodcap.NF.Typing
open import nodcap.NF.Contract
open import nodcap.NF.Expand
open import nodcap.NF.Cut

module nodcap.NF.CutND where

open I.Inverse using (to; from)
private
  open module LM {ℓ} = RawMonadPlus (L.monadPlus {ℓ})
private module ++ {a} {A : Set a} = Monoid (L.monoid A)

{-# TERMINATING #-}
-- Theorem:
--   Nondeterministic cut elimination.
mutual
  cutND : {Γ Δ : Context} {A : Type} →

    ⊢ⁿᶠ A ∷ Γ → ⊢ⁿᶠ A ^ ∷ Δ →
    ---------------------
    List (⊢ⁿᶠ Γ ++ Δ)

  cutND {_} {Δ} {𝟏} halt (wait y)
    = return y
  cutND {Γ} {_} {⊥} (wait x) halt
    = return
    $ P.subst ⊢ⁿᶠ_ (P.sym (proj₂ ++.identity Γ)) x
  cutND {_} {Θ} {A ⊗ B} (send {Γ} {Δ} x y) (recv z)
    = return
    ∘ P.subst ⊢ⁿᶠ_ (P.sym (++.assoc Γ Δ Θ))
    ∘ exch (swp [] Γ Δ)
    =<< cutND y
    ∘ exch (fwd [] Γ)
    =<< cutND x z
  cutND {Θ} {_} {A ⅋ B} (recv x) (send {Γ} {Δ} y z)
    = return
    ∘ P.subst ⊢ⁿᶠ_ (++.assoc Θ Γ Δ)
    =<< flip cutND z
    =<< cutND x y
  cutND {Γ} {Δ} {A ⊕ B} (sel₁ x) (case y z)
    = cutND x y
  cutND {Γ} {Δ} {A ⊕ B} (sel₂ x) (case y z)
    = cutND x z
  cutND {Γ} {Δ} {A & B} (case x y) (sel₁ z)
    = cutND x z
  cutND {Γ} {Δ} {A & B} (case x y) (sel₂ z)
    = cutND y z
  cutND {Γ} {Δ} {⊗[ n ] A} x y
    = all (replicate⁺ n (A ^)) >>= return ∘ withPerm ∘ proj₂
    where
      withPerm : {Θ : Context} → replicate⁺ n (A ^) ∼[ bag ] Θ → ⊢ⁿᶠ Γ ++ Δ
      withPerm {Θ} b
        = cut x
        $ contract
        $ exch (B.++-cong (P.subst (_ ∼[ bag ]_) (all-replicate⁺ n (I.sym b)) b) I.id)
        $ expand y
  cutND {Γ} {Δ} {⅋[ n ] A} x y
    = all (replicate⁺ n A) >>= return ∘ withPerm ∘ proj₂
    where
      withPerm : {Θ : Context} → replicate⁺ n A ∼[ bag ] Θ → ⊢ⁿᶠ Γ ++ Δ
      withPerm {Θ} b
        = exch (swp₂ Γ)
        $ cut y
        $ P.subst (λ A → ⊢ⁿᶠ ⅋[ n ] A ∷ Γ) (P.sym (^-inv A))
        $ contract
        $ exch (B.++-cong (P.subst (_ ∼[ bag ]_) (all-replicate⁺ n (I.sym b)) b) I.id)
        $ expand x
  cutND {Γ} {Δ} {A} (exch b x) y
    = return
    ∘ exch (B.++-cong {ys₁ = Δ} (del-from b (here P.refl)) I.id)
    =<< cutNDIn (from b ⟨$⟩ here P.refl) (here P.refl) x y
  cutND {Γ} {Δ} {A} x (exch b y)
    = return
    ∘ exch (B.++-cong {xs₁ = Γ} I.id (del-from b (here P.refl)))
    =<< cutNDIn (here P.refl) (from b ⟨$⟩ here P.refl) x y
 

  cutNDIn : {Γ Δ : Context} {A : Type} (i : A ∈ Γ) (j : A ^ ∈ Δ) →

    ⊢ⁿᶠ Γ → ⊢ⁿᶠ Δ →
    ----------------------- 
    List (⊢ⁿᶠ Γ - i ++ Δ - j)

  cutNDIn (here P.refl) (here P.refl) x y = cutND x y

  cutNDIn {_} {Θ} (there i) j (send {Γ} {Δ} x y) z
    with split Γ i
  ... | inj₁ (k , p) rewrite p
      = return
      ∘ P.subst ⊢ⁿᶠ_ (P.sym (++.assoc (_ ∷ Γ - k) Δ (Θ - j)))
      ∘  exch (swp₃ (_ ∷ Γ - k) Δ)
      ∘  P.subst ⊢ⁿᶠ_ (++.assoc (_ ∷ Γ - k) (Θ - j) Δ)
      ∘ flip send y
      =<< cutNDIn (there k) j x z
  ... | inj₂ (k , p) rewrite p
      = return
      ∘ P.subst ⊢ⁿᶠ_ (P.sym (++.assoc (_ ∷ Γ) (Δ - k) (Θ - j)))
      ∘ send x
      =<< cutNDIn (there k) j y z
  cutNDIn (there i) j (recv x) y
    = return
    ∘ recv
    =<< cutNDIn (there (there i)) j x y
  cutNDIn (there i) j (sel₁ x) y
    = return
    ∘ sel₁
    =<< cutNDIn (there i) j x y
  cutNDIn (there i) j (sel₂ x) y
    = return
    ∘ sel₂
    =<< cutNDIn (there i) j x y
  cutNDIn (there i) j (case x y) z
    = cutNDIn (there i) j x z >>= λ xz
    → cutNDIn (there i) j y z >>= λ yz
    → return
    $ case xz yz
  cutNDIn (there ()) j halt y
  cutNDIn (there i) j (wait x) y
    = return
    ∘ wait
    =<< cutNDIn i j x y
  cutNDIn (there i) j loop y
    = return
    $ loop
  cutNDIn {Γ} {Δ} (there i) j (mk⅋₁ x) y
    = return
    ∘ mk⅋₁
    =<< cutNDIn (there i) j x y
  cutNDIn {Γ} {Δ} (there i) j (mk⊗₁ x) y
    = return
    ∘ mk⊗₁
    =<< cutNDIn (there i) j x y
  cutNDIn {Γ} {Δ} (there i) j (cont x) y
    = return
    ∘ cont
    =<< cutNDIn (there (there i)) j x y
  cutNDIn {_} {Θ} (there i) j (pool {Γ} {Δ} x y) z
    with split Γ i
  ... | inj₁ (k , p) rewrite p
      = return
      ∘ P.subst ⊢ⁿᶠ_ (P.sym (++.assoc (_ ∷ Γ - k) Δ (Θ - j)))
      ∘ exch (swp₃ (_ ∷ Γ - k) Δ)
      ∘ P.subst ⊢ⁿᶠ_ (++.assoc (_ ∷ Γ - k) (Θ - j) Δ)
      ∘ flip pool y
      =<< cutNDIn (there k) j x z
  ... | inj₂ (k , p) rewrite p
      = return
      ∘ P.subst ⊢ⁿᶠ_ (P.sym (++.assoc (_ ∷ Γ) (Δ - k) (Θ - j)))
      ∘ pool x
      =<< cutNDIn (there k) j y z

  cutNDIn {Θ} {_} i (there j) x (send {Γ} {Δ} y z)
    with split Γ j
  ... | inj₁ (k , p) rewrite p
      = return
      ∘ exch (bwd [] (Θ - i))
      ∘ P.subst ⊢ⁿᶠ_ (++.assoc (_ ∷ Θ - i) (Γ - k) Δ)
      ∘ flip send z
      ∘ exch (fwd [] (Θ - i))
      =<< cutNDIn i (there k) x y
  ... | inj₂ (k , p) rewrite p
      = return
      ∘ exch (swp [] (Θ - i) (_ ∷ Γ))
      ∘ send y
      ∘ exch (fwd [] (Θ - i))
      =<< cutNDIn i (there k) x z
  cutNDIn {Γ} i (there j) x (recv {Δ} y)
    = return
    ∘ exch (bwd [] (Γ - i))
    ∘ recv
    ∘ exch (swp [] (_ ∷ _ ∷ []) (Γ - i))
    =<< cutNDIn i (there (there j)) x y
  cutNDIn {Γ} {Δ} i (there j) x (sel₁ y)
    = return
    ∘ exch (bwd [] (Γ - i))
    ∘ sel₁
    ∘ exch (fwd [] (Γ - i))
    =<< cutNDIn i (there j) x y
  cutNDIn {Γ} {Δ} i (there j) x (sel₂ y)
    = return
    ∘ exch (bwd [] (Γ - i))
    ∘ sel₂
    ∘ exch (fwd [] (Γ - i))
    =<< cutNDIn i (there j) x y
  cutNDIn {Γ} {Δ} i (there j) x (case y z)
    = cutNDIn i (there j) x y >>= λ xy
    → cutNDIn i (there j) x z >>= λ xz
    → return
    $ exch (bwd [] (Γ - i))
    $ case
    ( exch (fwd [] (Γ - i)) xy )
    ( exch (fwd [] (Γ - i)) xz )
  cutNDIn {Γ} i (there ()) x halt
  cutNDIn {Γ} {Δ} i (there j) x (wait y)
    = return
    ∘ exch (bwd [] (Γ - i))
    ∘ wait
    =<< cutNDIn i j x y
  cutNDIn {Γ} {Δ} i (there j) x loop
    = return
    ∘ exch (bwd [] (Γ - i))
    $ loop
  cutNDIn {Γ} {Δ} i (there j) x (mk⅋₁ y)
    = return
    ∘ exch (bwd [] (Γ - i))
    ∘ mk⅋₁
    ∘ exch (fwd [] (Γ - i))
    =<< cutNDIn i (there j) x y
  cutNDIn {Γ} {Δ} i (there j) x (mk⊗₁ y)
    = return
    ∘ exch (bwd [] (Γ - i))
    ∘ mk⊗₁
    ∘ exch (fwd [] (Γ - i))
    =<< cutNDIn i (there j) x y
  cutNDIn {Γ} {Δ} i (there j) x (cont y)
    = return
    ∘ exch (bwd [] (Γ - i))
    ∘ cont
    ∘ exch (swp [] (_ ∷ _ ∷ []) (Γ - i))
    =<< cutNDIn i (there (there j)) x y
  cutNDIn {Θ} {_} i (there j) x (pool {Γ} {Δ} y z)
    with split Γ j
  ... | inj₁ (k , p) rewrite p
      = return
      ∘ exch (bwd [] (Θ - i))
      ∘ P.subst ⊢ⁿᶠ_ (++.assoc (_ ∷ Θ - i) (Γ - k) Δ)
      ∘ flip pool z
      ∘ exch (fwd [] (Θ - i))
      =<< cutNDIn i (there k) x y
  ... | inj₂ (k , p) rewrite p
      = return
      ∘ exch (swp [] (Θ - i) (_ ∷ Γ))
      ∘ pool y
      ∘ exch (fwd [] (Θ - i))
      =<< cutNDIn i (there k) x z

  cutNDIn {Γ} {Δ} i j (exch b x) y
    = return
    ∘ exch (B.++-cong {ys₁ = Δ - j} (del-from b i ) I.id)
    =<< cutNDIn (from b ⟨$⟩ i) j x y
  cutNDIn {Γ} {Δ} i j x (exch b y)
    = return
    ∘ exch (B.++-cong {xs₁ = Γ - i} I.id (del-from b j))
    =<< cutNDIn i (from b ⟨$⟩ j) x y

-- -}
-- -}
-- -}
-- -}
-- -}
