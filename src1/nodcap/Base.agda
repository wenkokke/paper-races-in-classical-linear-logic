open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Pos as ℕ⁺ using (ℕ⁺; suc; _+_)
open import Data.List as L using (List; []; _∷_; _++_)
open import Data.List.Any using (Any; here; there)
open import Data.List.Any.Membership.Propositional using (_∈_; _∼[_]_; bag)
open import Data.Product using (_×_; _,_; uncurry; map)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (id; _$_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)


module nodcap.Base where

-- Types.

data Type : Set where
  𝟏 : Type
  ⊥ : Type
  𝟎 : Type
  ⊤ : Type
  _⊗_ : (A B : Type) → Type
  _⅋_ : (A B : Type) → Type
  _⊕_ : (A B : Type) → Type
  _&_ : (A B : Type) → Type
  ![_]_ : (n : ℕ⁺) (A : Type) → Type
  ?[_]_ : (n : ℕ⁺) (A : Type) → Type


-- Duality.

_^ : Type → Type
𝟏 ^ = ⊥
⊥ ^ = 𝟏
𝟎 ^ = ⊤
⊤ ^ = 𝟎
(A ⊗ B) ^ = (A ^) ⅋ (B ^)
(A ⅋ B) ^ = (A ^) ⊗ (B ^)
(A ⊕ B) ^ = (A ^) & (B ^)
(A & B) ^ = (A ^) ⊕ (B ^)
(![ n ] A) ^ = ?[ n ] (A ^)
(?[ n ] A) ^ = ![ n ] (A ^)

^-inv : (A : Type) → A ^ ^ ≡ A
^-inv 𝟏 = P.refl
^-inv ⊥ = P.refl
^-inv 𝟎 = P.refl
^-inv ⊤ = P.refl
^-inv (A ⊗ B) = P.cong₂ _⊗_ (^-inv A) (^-inv B)
^-inv (A ⅋ B) = P.cong₂ _⅋_ (^-inv A) (^-inv B)
^-inv (A ⊕ B) = P.cong₂ _⊕_ (^-inv A) (^-inv B)
^-inv (A & B) = P.cong₂ _&_ (^-inv A) (^-inv B)
^-inv (![ n ] A) = P.cong ![ n ]_ (^-inv A)
^-inv (?[ n ] A) = P.cong ?[ n ]_ (^-inv A)

-- Lollipop.

_⊸_ : (A B : Type) → Type
A ⊸ B = (A ^) ⅋ B


-- Polarity.

data Pos : (A : Type) → Set where
  𝟎 : Pos 𝟎
  𝟏 : Pos 𝟏
  _⊗_ : (A B : Type) → Pos (A ⊗ B)
  _⊕_ : (A B : Type) → Pos (A ⊕ B)
  ![_]_ : (n : ℕ⁺) (A : Type) → Pos (![ n ] A)

data Neg : (A : Type) → Set where
  ⊥ : Neg ⊥
  ⊤ : Neg ⊤
  _⅋_ : (A B : Type) → Neg (A ⅋ B)
  _&_ : (A B : Type) → Neg (A & B)
  ?[_]_ : (n : ℕ⁺) (A : Type) → Neg (?[ n ] A)

pol? : (A : Type) → Pos A ⊎ Neg A
pol? 𝟏 = inj₁ 𝟏
pol? ⊥ = inj₂ ⊥
pol? 𝟎 = inj₁ 𝟎
pol? ⊤ = inj₂ ⊤
pol? (A ⊗ B) = inj₁ (A ⊗ B)
pol? (A ⅋ B) = inj₂ (A ⅋ B)
pol? (A ⊕ B) = inj₁ (A ⊕ B)
pol? (A & B) = inj₂ (A & B)
pol? (![ n ] A) = inj₁ (![ n ] A)
pol? (?[ n ] A) = inj₂ (?[ n ] A)

^-posneg : {A : Type} (P : Pos A) → Neg (A ^)
^-posneg 𝟎 = ⊤
^-posneg 𝟏 = ⊥
^-posneg (A ⊗ B) = (A ^) ⅋ (B ^)
^-posneg (A ⊕ B) = (A ^) & (B ^)
^-posneg (![ n ] A) = ?[ n ] (A ^)

^-negpos : {A : Type} (N : Neg A) → Pos (A ^)
^-negpos ⊥ = 𝟏
^-negpos ⊤ = 𝟎
^-negpos (A ⅋ B) = (A ^) ⊗ (B ^)
^-negpos (A & B) = (A ^) ⊕ (B ^)
^-negpos (?[ n ] A) = ![ n ] (A ^)


-- Environments.

Environment : Set
Environment = List Type

-- Injectivity.

private
  infix 10 _≈_

  _≈_ : Type → Type → Set
  A ≈ B = A ≡ B

⊗-inj : {A B C D : Type} → A ⊗ B ≈ C ⊗ D → A ≈ C × B ≈ D
⊗-inj P.refl = P.refl , P.refl

⅋-inj : {A B C D : Type} → A ⅋ B ≈ C ⅋ D → A ≈ C × B ≈ D
⅋-inj P.refl = P.refl , P.refl

⊕-inj : {A B C D : Type} → A ⊕ B ≈ C ⊕ D → A ≈ C × B ≈ D
⊕-inj P.refl = P.refl , P.refl

&-inj : {A B C D : Type} → A & B ≈ C & D → A ≈ C × B ≈ D
&-inj P.refl = P.refl , P.refl

!-inj : {A B : Type} {m n : ℕ⁺} → ![ m ] A ≈ ![ n ] B → m ≡ n × A ≈ B
!-inj P.refl = P.refl , P.refl

?-inj : {A B : Type} {m n : ℕ⁺} → ?[ m ] A ≈ ?[ n ] B → m ≡ n × A ≈ B
?-inj P.refl = P.refl , P.refl

-- This is one of those proofs for which I wish Agda had tactics.

^-inj : {A B : Type} → A ^ ≈ B ^ → A ≈ B
^-inj {A = 𝟏}        {B = 𝟏}         p = P.refl
^-inj {A = 𝟏}        {B = ⊥}         ()
^-inj {A = 𝟏}        {B = 𝟎}         ()
^-inj {A = 𝟏}        {B = ⊤}         ()
^-inj {A = 𝟏}        {B = C ⊗ D}     ()
^-inj {A = 𝟏}        {B = C ⅋ D}     ()
^-inj {A = 𝟏}        {B = C ⊕ D}     ()
^-inj {A = 𝟏}        {B = C & D}     ()
^-inj {A = 𝟏}        {B = ![ n ] C}  ()
^-inj {A = 𝟏}        {B = ?[ n ] C}  ()
^-inj {A = ⊥}        {B = 𝟏}         ()
^-inj {A = ⊥}        {B = ⊥}         p = P.refl
^-inj {A = ⊥}        {B = 𝟎}         ()
^-inj {A = ⊥}        {B = ⊤}         ()
^-inj {A = ⊥}        {B = C ⊗ D}     ()
^-inj {A = ⊥}        {B = C ⅋ D}     ()
^-inj {A = ⊥}        {B = C ⊕ D}     ()
^-inj {A = ⊥}        {B = C & D}     ()
^-inj {A = ⊥}        {B = ![ n ] C}  ()
^-inj {A = ⊥}        {B = ?[ n ] C}  ()
^-inj {A = 𝟎}        {B = 𝟏}         ()
^-inj {A = 𝟎}        {B = ⊥}         ()
^-inj {A = 𝟎}        {B = 𝟎}         p = P.refl
^-inj {A = 𝟎}        {B = ⊤}         ()
^-inj {A = 𝟎}        {B = C ⊗ D}     ()
^-inj {A = 𝟎}        {B = C ⅋ D}     ()
^-inj {A = 𝟎}        {B = C ⊕ D}     ()
^-inj {A = 𝟎}        {B = C & D}     ()
^-inj {A = 𝟎}        {B = ![ n ] C}  ()
^-inj {A = 𝟎}        {B = ?[ n ] C}  ()
^-inj {A = ⊤}        {B = 𝟏}         ()
^-inj {A = ⊤}        {B = ⊥}         ()
^-inj {A = ⊤}        {B = 𝟎}         ()
^-inj {A = ⊤}        {B = ⊤}         p = P.refl
^-inj {A = ⊤}        {B = C ⊗ D}     ()
^-inj {A = ⊤}        {B = C ⅋ D}     ()
^-inj {A = ⊤}        {B = C ⊕ D}     ()
^-inj {A = ⊤}        {B = C & D}     ()
^-inj {A = ⊤}        {B = ![ n ] C}  ()
^-inj {A = ⊤}        {B = ?[ n ] C}  ()
^-inj {A = A ⊗ B}    {B = 𝟏}         ()
^-inj {A = A ⊗ B}    {B = ⊥}         ()
^-inj {A = A ⊗ B}    {B = 𝟎}         ()
^-inj {A = A ⊗ B}    {B = ⊤}         ()
^-inj {A = A ⊗ B}    {B = C ⊗ D}     p = uncurry (P.cong₂ _⊗_) (map ^-inj ^-inj (⅋-inj p))
^-inj {A = A ⊗ B}    {B = C ⅋ D}     ()
^-inj {A = A ⊗ B}    {B = C ⊕ D}     ()
^-inj {A = A ⊗ B}    {B = C & D}     ()
^-inj {A = A ⊗ B}    {B = ![ n ] C}  ()
^-inj {A = A ⊗ B}    {B = ?[ n ] C}  ()
^-inj {A = A ⅋ B}    {B = 𝟏}         ()
^-inj {A = A ⅋ B}    {B = ⊥}         ()
^-inj {A = A ⅋ B}    {B = 𝟎}         ()
^-inj {A = A ⅋ B}    {B = ⊤}         ()
^-inj {A = A ⅋ B}    {B = C ⊗ D}     ()
^-inj {A = A ⅋ B}    {B = C ⅋ D}     p = uncurry (P.cong₂ _⅋_) (map ^-inj ^-inj (⊗-inj p))
^-inj {A = A ⅋ B}    {B = C ⊕ D}     ()
^-inj {A = A ⅋ B}    {B = C & D}     ()
^-inj {A = A ⅋ B}    {B = ![ n ] C}  ()
^-inj {A = A ⅋ B}    {B = ?[ n ] C}  ()
^-inj {A = A ⊕ B}    {B = 𝟏}         ()
^-inj {A = A ⊕ B}    {B = ⊥}         ()
^-inj {A = A ⊕ B}    {B = 𝟎}         ()
^-inj {A = A ⊕ B}    {B = ⊤}         ()
^-inj {A = A ⊕ B}    {B = C ⊗ D}     ()
^-inj {A = A ⊕ B}    {B = C ⅋ D}     ()
^-inj {A = A ⊕ B}    {B = C ⊕ D}     p = uncurry (P.cong₂ _⊕_) (map ^-inj ^-inj (&-inj p))
^-inj {A = A ⊕ B}    {B = C & D}     ()
^-inj {A = A ⊕ B}    {B = ![ n ] C}  ()
^-inj {A = A ⊕ B}    {B = ?[ n ] C}  ()
^-inj {A = A & B}    {B = 𝟏}         ()
^-inj {A = A & B}    {B = ⊥}         ()
^-inj {A = A & B}    {B = 𝟎}         ()
^-inj {A = A & B}    {B = ⊤}         ()
^-inj {A = A & B}    {B = C ⊗ D}     ()
^-inj {A = A & B}    {B = C ⅋ D}     ()
^-inj {A = A & B}    {B = C ⊕ D}     ()
^-inj {A = A & B}    {B = C & D}     p = uncurry (P.cong₂ _&_) (map ^-inj ^-inj (⊕-inj p))
^-inj {A = A & B}    {B = ![ n ] C}  ()
^-inj {A = A & B}    {B = ?[ n ] C}  ()
^-inj {A = ![ m ] A} {B = 𝟏}         ()
^-inj {A = ![ m ] A} {B = ⊥}         ()
^-inj {A = ![ m ] A} {B = 𝟎}         ()
^-inj {A = ![ m ] A} {B = ⊤}         ()
^-inj {A = ![ m ] A} {B = C ⊗ D}     ()
^-inj {A = ![ m ] A} {B = C ⅋ D}     ()
^-inj {A = ![ m ] A} {B = C ⊕ D}     ()
^-inj {A = ![ m ] A} {B = C & D}     ()
^-inj {A = ![ m ] A} {B = ![ n ] C}  p = uncurry (P.cong₂ ![_]_) (map id ^-inj (?-inj p))
^-inj {A = ![ m ] A} {B = ?[ n ] C}  ()
^-inj {A = ?[ m ] A} {B = 𝟏}         ()
^-inj {A = ?[ m ] A} {B = ⊥}         ()
^-inj {A = ?[ m ] A} {B = 𝟎}         ()
^-inj {A = ?[ m ] A} {B = ⊤}         ()
^-inj {A = ?[ m ] A} {B = C ⊗ D}     ()
^-inj {A = ?[ m ] A} {B = C ⅋ D}     ()
^-inj {A = ?[ m ] A} {B = C ⊕ D}     ()
^-inj {A = ?[ m ] A} {B = C & D}     ()
^-inj {A = ?[ m ] A} {B = ![ n ] C}  ()
^-inj {A = ?[ m ] A} {B = ?[ n ] C}  p = uncurry (P.cong₂ ?[_]_) (map id ^-inj (!-inj p))
