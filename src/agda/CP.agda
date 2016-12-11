module CP (Atom : Set) where

open import Agda.Builtin.Nat using (Nat; suc; zero; _+_)
open import Category.Functor using (module RawFunctor)
open import Data.Fin using (Fin; suc; zero)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

import Relation.Binary.EqReasoning as EqReasoning

open RawFunctor {{...}} using (_<$>_)
instance
  functorMaybe = Data.Maybe.functor


thin : ∀ {n} → Fin (suc n) → Fin n → Fin (suc n)
thin  zero    y      = suc y
thin (suc x)  zero   = zero
thin (suc x) (suc y) = suc (thin x y)

thick : ∀ {n} → (x y : Fin (suc n)) → Maybe (Fin n)
thick          zero    zero   = nothing
thick          zero   (suc y) = just y
thick {zero}  (suc ()) _
thick {suc n} (suc x)  zero   = just zero
thick {suc n} (suc x) (suc y) = suc <$> (thick x y)

thick-lem₀ : ∀ {n} (x : Fin (suc n))
           → thick x x ≡ nothing
thick-lem₀ {n}      zero = refl
thick-lem₀ {zero}  (suc ())
thick-lem₀ {suc n} (suc x)
  rewrite thick-lem₀ x = refl


data Type : Set where
  +_  : Atom → Type
  -_  : Atom → Type
  _⊗_ : Type → Type → Type
  _⊕_ : Type → Type → Type
  _&_ : Type → Type → Type
  _⅋_ : Type → Type → Type

¬_ : Type → Type
¬ (+ A) = - A
¬ (- A) = + A
¬ (A ⊗ B) = A ⅋ B
¬ (A ⊕ B) = A & B
¬ (A & B) = A ⊕ B
¬ (A ⅋ B) = A ⊗ B


infixl 6 _\\_
infixl 5 _,_∶_
infixl 5 _[_∶_]
infix  4 _∶_∈_

Ctxt : Nat → Set
Ctxt n = Fin n → Type

_\\_ : ∀ {n} → Ctxt (suc n) → Fin (suc n) → Ctxt n
(Γ \\ x) y = Γ (thin x y)

_,_∶_ : ∀ {n} → Ctxt n → Fin (suc n) → Type → Ctxt (suc n)
(Γ , x ∶ A) y = maybe Γ A (thick x y)

ins-lem₀ : ∀ {n} (Γ : Ctxt n) (x : Fin (suc n)) (A : Type)
         → (Γ , x ∶ A) x ≡ A
ins-lem₀ Γ x A rewrite thick-lem₀ x = refl

_[_∶_] : ∀ {n} → Ctxt (suc n) → Fin (suc n) → Type → Ctxt (suc n)
Γ [ x ∶ A ] = Γ \\ x , x ∶ A

_∶_∈_ : ∀ {n} → Fin n → Type → Ctxt n → Set
x ∶ A ∈ Γ = Γ x ≡ A


data Term : {m n : Nat} (Γ : Ctxt m) (Δ : Ctxt n) → Set where

   link : ∀ {n} {Γ : Ctxt (suc (suc n))}
                (x : Fin  (suc (suc n)))
                (y : Fin  (suc n))
        → y ∶ ¬ Γ x ∈ (Γ \\ x)
        → Term Γ (Γ \\ x \\ y)

   send : ∀ {m} {Γ : Ctxt (suc m)}
            {n} {Δ : Ctxt      n }
            {o} {Θ : Ctxt      o }
            (A B : Type)
            (x : Fin (suc m))
            (y : Fin (suc m)) 
            (z : Fin (suc n)) 
        → x ∶ A ⊗ B ∈ Γ
        → Term (Γ \\ x , y ∶ A) Δ
        → Term (Δ      , z ∶ A) Θ
        → Term Γ Θ

   recv : ∀ {m} {Γ : Ctxt (suc m)}
            {n} {Δ : Ctxt      n }
            (A B : Type)
            (x : Fin      (suc m) ) 
            (y : Fin      (suc m) )
            (z : Fin (suc (suc m)))
        → x ∶ A ⅋ B ∈ Γ
        → Term (Γ \\ x , y ∶ A , z ∶ B) Δ
        → Term Γ Δ

   inl  : ∀ {m} {Γ : Ctxt (suc m)}
            {n} {Δ : Ctxt      n }
            (A B : Type)
            (x : Fin (suc m))
            (y : Fin (suc m))
        → x ∶ A ⊕ B ∈ Γ
        → Term (Γ \\ x , y ∶ A) Δ
        → Term Γ Δ

   inr  : ∀ {m} (Γ : Ctxt (suc m))
            {n} (Δ : Ctxt      n )
            (A B : Type)
            (x : Fin (suc m))
            (y : Fin (suc m))
        → x ∶ A ⊕ B ∈ Γ
        → Term (Γ \\ x , y ∶ A) Δ
        → Term Γ Δ

   case : ∀ {m} (Γ : Ctxt (suc m))
            {n} (Δ : Ctxt      n )
            {o} (Θ : Ctxt      o )
            (A B : Type)
            (x : Fin (suc m))
            (y : Fin (suc n))
            (z : Fin (suc o))
        → x ∶ A & B ∈ Γ
        → Term (Γ \\ x , y ∶ A) Δ
        → Term (Δ , z ∶ B) Θ
        → Term Γ Θ

-- so, this won't work because you have the option of
-- NOT consuming the new thing in the first branch,
-- while this should be consumed, so we need something
-- of an updated context which can be not consumed,
-- and a context which _has_ to be consumed
