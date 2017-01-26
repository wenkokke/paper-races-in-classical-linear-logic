open import Algebra
open import Data.Nat 
open import Data.List as L                             using (List; []; _∷_; [_]; _++_)
open import Data.List.Any                              using (here; there)
open import Data.List.Any.BagAndSetEquality as B       using ()
open        Data.List.Any.Membership-≡                 using (_∈_; _∼[_]_; bag)
open import Data.Product                               using (Σ-syntax; ∃₂; _×_; proj₁; proj₂; _,_)
open import Data.Sum                                   using (_⊎_; inj₁; inj₂)
open import Function                                   using (_$_)
open import Function.Equality                          using (_⟨$⟩_)
open import Function.Inverse                           using (id; sym; _∘_)
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

bwd : (xs ys {zs} : List A) {w : A} →
      xs ++ w ∷ ys ++ zs ∼[ bag ] xs ++ ys ++ w ∷ zs
bwd xs ys = sym (fwd xs ys)

-- There is a bijection between indices into the context
-- ΓΣΔΠ and the context ΓΔΣΠ.
swp₄ : (xs ys zs {ws} : List A) →
      xs ++ zs ++ ys ++ ws ∼[ bag ] xs ++ ys ++ zs ++ ws
swp₄ xs []       zs = id
swp₄ xs (y ∷ ys) zs =
  ( P.subst₂ _∼[ bag ]_ (++.assoc xs [ y ] _) (++.assoc xs [ y ] _)
  $ swp₄ (xs ++ [ y ]) ys zs
  ) ∘ fwd xs zs

-- Alias for swp₄.
swp = swp₄

-- There is a bijection between indices into the context
-- ΓΣΔ and the context ΓΔΣ. This is mostly a convenience
-- function because of the annoyance of using ++.identity
-- in the logic proofs.
swp₃ : (xs ys {zs} : List A) →
       xs ++ zs ++ ys ∼[ bag ] xs ++ ys ++ zs
swp₃ xs ys {zs} =
  ( P.subst₂ (λ ys' zs' → xs ++ zs ++ ys' ∼[ bag ] xs ++ ys ++ zs')
             (proj₂ ++.identity ys)
             (proj₂ ++.identity zs)
  $ swp₄ xs ys zs
  )

-- There is a bijection between indices into the context
-- ΓΣΔ and the context ΓΔΣ. This is mostly a convenience
-- function because of the annoyance of using ++.identity
-- in the logic proofs.
swp₂ : (xs {ys} : List A) →
       ys ++ xs ∼[ bag ] xs ++ ys
swp₂ = swp₃ []


_-_ : (xs : List A) {x : A} (i : x ∈ xs) → List A
(x ∷ xs) - (here  _) = xs
(x ∷ xs) - (there i) = x ∷ xs - i


del-[] : {x y : A} (i : y ∈ x ∷ []) → (x ∷ []) - i ≡ []
del-[] (here px) = P.refl
del-[] (there ())

private
  -- Given a proof of membership x ∈ xs, we can be sure that
  -- there are two lists xs₁ and xs₂ s.t.
  --
  --   (1) xs = xs₁ ++ x ∷ xs₂; and
  --   (2) xs - i = xs₁ ++ xs₂.
  --
  -- That is to say, that we can break the list xs into a prefix,
  -- the element x, and a suffix, and that if we delete that occurrence
  -- of x, we are left with the prefix and the suffix.
  lem : {xs : List A} {x : A} (i : x ∈ xs) →
        ∃₂ λ xs₁ xs₂ → xs ≡ xs₁ ++ x ∷ xs₂ × xs - i ≡ xs₁ ++ xs₂
  lem {x ∷ xs} (here P.refl) = ([] , xs , P.refl , P.refl)
  lem {x ∷ xs} (there i) with lem {xs} i
  ... | (xs₁ , xs₂ , p₁ , p₂) = (x ∷ xs₁ , xs₂ , P.cong (x ∷_) p₁ , P.cong (x ∷_) p₂)


-- Given two lists which are bag-equal, we can prove that if we delete
-- the same element from both lists, the resulting lists are also bag-equal.
del-to : {xs ys : List A} {x : A} →
         (eq : xs ∼[ bag ] ys) (i : x ∈ xs) →
         xs - i ∼[ bag ] ys - (to eq ⟨$⟩ i)
del-to {xs} {ys} {x} eq i
  with lem {xs} i
... | (xs₁ , xs₂ , p₁ , p₂) rewrite p₁ | p₂
  with lem {ys} (to eq ⟨$⟩ i)
... | (ys₁ , ys₂ , q₁ , q₂) rewrite q₁ | q₂
    = B.drop-cons (fwd [] ys₁ ∘ eq ∘ sym (fwd [] xs₁))


del-from : {xs ys : List A} {x : A} →
           (eq : ys ∼[ bag ] xs) (i : x ∈ xs) →
           ys - (from eq ⟨$⟩ i) ∼[ bag ] xs - i
del-from {xs} {ys} {x} eq i
  with lem {xs} i
... | (xs₁ , xs₂ , p₁ , p₂) rewrite p₁ | p₂
  with lem {ys} (from eq ⟨$⟩ i)
... | (ys₁ , ys₂ , q₁ , q₂) rewrite q₁ | q₂
    = B.drop-cons (fwd [] xs₁ ∘ eq ∘ sym (fwd [] ys₁))

-- Split a context based on a proof of membership (used as index).
split : ∀ (xs {ys} : List A) {x : A} →
        (i : x ∈ xs ++ ys) →
        Σ[ j ∈ x ∈ xs ] ((xs ++ ys) - i ≡ xs - j ++ ys) ⊎
        Σ[ j ∈ x ∈ ys ] ((xs ++ ys) - i ≡ xs ++ ys - j)
split []       i         = inj₂ (i , P.refl)
split (_ ∷ xs) (here px) = inj₁ (here px , P.refl)
split (_ ∷ xs) (there i) with split xs i
... | inj₁ (j , p) = inj₁ (there j , P.cong (_ ∷_) p)
... | inj₂ (j , p) = inj₂ (j , P.cong (_ ∷_) p)


-- -}
-- -}
-- -}
-- -}
-- -}
