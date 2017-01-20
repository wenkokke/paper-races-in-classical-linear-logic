open import Algebra
open import Data.List as L                             using (List; []; _∷_; [_]; _++_)
open import Data.List.Any                              using (here; there)
open import Data.List.Any.BagAndSetEquality as B       using ()
open        Data.List.Any.Membership-≡                 using (_∈_; _∼[_]_; bag)
open import Data.Product                               using (∃; ∃₂; _×_; proj₁; proj₂; _,_)
open import Function                                   using (_$_)
open import Function.Equality                          using (_⟨$⟩_)
open import Function.Inverse                           using (id; _∘_)
open        Function.Inverse.Inverse                   using (to; from)
open import Relation.Binary.PropositionalEquality as P using (_≡_)


module Logic.Context {a} {A : Set a} where


private module ++ = Monoid (L.monoid A)


bubble : (xs {ys} : List A) {x y z : A} →
         z ∈ xs ++ y ∷ x ∷ ys → z ∈ xs ++ x ∷ y ∷ ys
bubble []       (here px)         = there (here px)
bubble []       (there (here px)) = here px
bubble []       (there (there i)) = there (there i)
bubble (x ∷ xs) (here px)         = here px
bubble (x ∷ xs) (there i)         = there (bubble xs i)


-- There is a bijection between indices into the context
-- ΓBAΔ and the context ΓABΔ. This is called a 'bubble',
-- because it swaps two adjacent elements, as in bubble
-- sort.
bbl : (xs {ys} : List A) {x y : A} →
      xs ++ y ∷ x ∷ ys ∼[ bag ] xs ++ x ∷ y ∷ ys
bbl xs {ys} {x} {y} = record
  { to         = P.→-to-⟶ (bubble xs)
  ; from       = P.→-to-⟶ (bubble xs)
  ; inverse-of = record
    { left-inverse-of  = inv xs
    ; right-inverse-of = inv xs } }
  where
    inv : (xs {ys} : List A) {x y z : A} →
          (i : z ∈ xs ++ y ∷ x ∷ ys) →
          bubble xs (bubble xs i) ≡ i
    inv []       (here px)         = P.refl
    inv []       (there (here px)) = P.refl
    inv []       (there (there i)) = P.refl
    inv (x ∷ xs) (here px)         = P.refl
    inv (x ∷ xs) (there i)         = P.cong there (inv xs i)


-- There is a bijection between indices into the context
-- ΓΔAΘ and the context ΓAΔΘ.
fwd : (xs ys {zs} : List A) {w : A} →
      xs ++ ys ++ w ∷ zs ∼[ bag ] xs ++ w ∷ ys ++ zs
fwd (x ∷ xs) ys = B.∷-cong P.refl (fwd xs ys)
fwd []       ys = fwd' ys
  where
    fwd' : (xs {ys} : List A) {w : A} →
           xs ++ w ∷ ys ∼[ bag ] w ∷ xs ++ ys
    fwd' []       = id
    fwd' (x ∷ xs) = bbl [] ∘ B.∷-cong P.refl (fwd' xs)


-- There is a bijection between indices into the context
-- ΓΣΔΠ and the context ΓΔΣΠ.
swp : (xs ys zs {ws} : List A) →
      xs ++ zs ++ ys ++ ws ∼[ bag ] xs ++ ys ++ zs ++ ws
swp xs []       zs = id
swp xs (y ∷ ys) zs =
  ( P.subst₂ _∼[ bag ]_ (++.assoc xs [ y ] _) (++.assoc xs [ y ] _)
  $ swp (xs ++ [ y ]) ys zs
  ) ∘ fwd xs zs


-- There is a bijection between indices into the context
-- ΓΣΔ and the context ΓΔΣ. This is mostly a convenience
-- function because of the annoyance of using ++.identity
-- in the logic proofs.
swp' : (xs ys {zs} : List A) →
       xs ++ zs ++ ys ∼[ bag ] xs ++ ys ++ zs
swp' xs ys {zs} =
  ( P.subst₂ (λ ys' zs' → xs ++ zs ++ ys' ∼[ bag ] xs ++ ys ++ zs')
             (proj₂ ++.identity ys)
             (proj₂ ++.identity zs)
  $ swp xs ys zs
  )

-- There is a bijection between indices into the context
-- Γ[ΔΘ] and the context [ΓΔ]Θ. This is trivially true, because
-- these contexts are literally equal.
ass : (xs ys {zs} : List A) →
      xs ++ (ys ++ zs) ∼[ bag ] (xs ++ ys) ++ zs
ass xs ys {zs} rewrite ++.assoc xs ys zs = id



_-_ : (xs : List A) {x : A} (i : x ∈ xs) → List A
(x ∷ xs) - (here  _) = xs
(x ∷ xs) - (there i) = x ∷ xs - i


-- TODO figure out how to prove this equivalence such that `del` falls out

lem : {xs : List A} {x : A} (i : x ∈ xs) →
      ∃₂ λ xs₁ xs₂ → xs ≡ xs₁ ++ x ∷ xs₂
                   × xs - i ≡ xs₁ ++ xs₂
lem {x ∷ xs} (here P.refl) = ([] , xs , P.refl , P.refl)
lem {x ∷ xs} (there i) with lem {xs} i
... | (xs₁ , xs₂ , p₁ , p₂) = (x ∷ xs₁ , xs₂ , P.cong (x ∷_) p₁ , P.cong (x ∷_) p₂)


del : {xs ys : List A} {x : A} →
      (eq : xs ∼[ bag ] ys) (i : x ∈ xs) →
      xs - i ∼[ bag ] ys - (to eq ⟨$⟩ i)
del {xs} {ys} eq i
  with lem {xs} i
... | (xs₁ , xs₂ , p₁ , p₂) rewrite p₁ | p₂
  with lem {ys} (to eq ⟨$⟩ i)
... | (ys₁ , ys₂ , q₁ , q₂) rewrite p₁ | q₂
    = {!!}

-- TODO getting closer but there is no guarantee now that
--      both occurrences of x are pointed at by i, which is
--      what I've lost in `lem`

-- -}
-- -}
-- -}
-- -}
-- -}
