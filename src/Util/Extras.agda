-- ↓ All utilities *not* in the agda standard library

module Util.Extras where

open import Util.Stdlib

open import Agda.Primitive
private variable
    ℓa ℓb ℓc ℓd ℓf ℓg ℓp ℓq : Level
    A : Set ℓa
    B : Set ℓb
    C : Set ℓc
    D : Set ℓd
    P P' : A → Set ℓp
    Q Q' : B → Set ℓq
    a a' : A
    l : List A
    F : A → Set ℓf
    G : A → Set ℓg

------------------
-- Control Flow --
------------------

-- ↓ Non-dependent function composition (right-to-left)
_∘_ : (B → C) → (A → B) → A → C
(g ∘ f) x = g (f x)

infixr 15 _∘_

-- ↓ Identity monad (non-dependent)
module Do-id where
    _>>_ : A → B → B
    _ >> x = x
    _>>=_ : A → (A -> B) → B
    x >>= f = f x

-------------------
-- Proof-related --
-------------------

pattern yes! = yes refl -- for proving "Dec (x ≡ x)"

-- Wrap a both sides of an equality with some function
_under_ : {a a' : A} → (a ≡ a') → (f : A → B) → f a ≡ f a'
refl under _ = refl

-- '_under_' for binary functions
_and_under_
    : {a a' : A} {b b' : B}
    → (a ≡ a') → (b ≡ b')
    → (f : A → B → C) → f a b ≡ f a' b'
refl and refl under _ = refl

-- Flip an equality proof
_flipped : {a a' : A} → (a ≡ a') → (a' ≡ a)
refl flipped = refl

-- Compose two equalities
_then_ : {a₁ a₂ a₃ : A} → (a₁ ≡ a₂) → (a₂ ≡ a₃) → (a₁ ≡ a₃)
refl then refl = refl

-- ↓ Safe coercion via type equality
_∵_ : A → A ≡ B → B
a ∵ refl = a

infixl 16 _under_ _and_under_ _then_
infixr 15 _∵_

explode : {A : Set ℓa} → ⊥ → A
explode ()

-- Like Relation.Nullary.Decidable.map′, but combines
-- *two* decidable relations
map′′ : (A → B → C) → (C → A × B) → Dec A  → Dec B → Dec C
does  (map′′ _     _     a?                   b?)
    = does a? 𝔹.∧ does b?
proof (map′′ _     C→A×B (𝔹.false because [¬a]) b?)
    = ofⁿ (invert [¬a] ∘ fst ∘ C→A×B)
proof (map′′ A→B→C C→A×B (𝔹.true  because  [a]) b?)
    = proof $ map′
        (A→B→C (invert [a]))
        (snd ∘ C→A×B)
        b?

-- Dependent version of map′′
map′′d
    : ((a : A) → F a → C) → (C → A × ((a : A) → F a))
    → Dec A → (∀ a → Dec (F a)) → Dec C
map′′d A→Fa→C C→A×A→Fa (𝔹.true because [a]) A→Fa?
    = let a = invert [a] in
    map′ (A→Fa→C a) ((_$ a) ∘ snd ∘ C→A×A→Fa) (A→Fa? a)
map′′d A→Fa→C C→A×A→Fa (𝔹.false because [¬a]) A→Fa?
    = no $ invert [¬a] ∘ fst ∘ C→A×A→Fa

_≢_ : {A : Set ℓa} → A → A → Set ℓa
a ≢ a' = ¬' (a ≡ a')

no≢yes : ∀ {a : A} {¬a} → no ¬a ≢ yes a
no≢yes ()

true≢false : 𝔹.true ≢ 𝔹.false
true≢false ()

-- 'yes' is injective
inj-yes : yes a ≡ yes a' → a ≡ a'
inj-yes refl = refl

-- 'fst' and 'snd' are injective
inj-fst-snd
    : {B : A → Set ℓb} {a a' : A} {b : B a} {b' : B a'}
    → (a , b) ≡ (a' , b') → Σ (a ≡ a') λ{refl → b ≡ b'}
inj-fst-snd refl = refl , refl

thm-&&-true : ∀ {b} → b 𝔹.∧ 𝔹.true ≡ b
thm-&&-true {𝔹.false} = refl
thm-&&-true {𝔹.true} = refl

---------------
-- Σ-related --
---------------

-- Usual syntactic sugar
Dep-Sum = Σ
syntax Dep-Sum A (λ a → B) = a ∈ A ∙ B

-- Map over the second element of a Σ
map-snd : (∀{a} → F a → G a) → Σ A F → Σ A G
map-snd h (a , f) = a , h f

------------------
-- List helpers --
------------------

-- ↓ remove "nothing"s from a list
filter : List (Maybe A) → List A
filter [] = []
filter (just x ∷ l) = x ∷ filter l
filter (nothing ∷ l) = filter l

_∈ₗ_ : {A : Set ℓa} → A → List A → Set ℓa
a ∈ₗ l = Any (a ≡_) l

pattern ↑0 = here refl
pattern ↑1 = there ↑0
pattern ↑2 = there ↑1
pattern ↑3 = there ↑2
pattern ↑4 = there ↑3
pattern ↑5 = there ↑4
pattern ↑6 = there ↑5
pattern ↑7 = there ↑6
pattern ↑8 = there ↑7
pattern ↑9 = there ↑8

-- ↓ Given a pointer into a list l, and an auxilarly list l' on l,
-- use the pointer to lookup a value *in l'*
follow_into
    : a ∈ₗ l
    → All F l
    → F a
follow ↑0 into (b ∷ _) = b
follow there p into (_ ∷ bs) = follow p into bs

-- Pointers are preserved when a list is mapped over

map-Any
    : {l : List A} {f : A → B}
    → (∀ {a} → P a → Q (f a))
    → Any P l
    → Any Q (map f l)
map-Any h (here p) = here (h p)
map-Any h (there ptr) = there (map-Any h ptr)

-- Special case: mapping over _∈ₗ_
map-∈ₗ
    : {l : List A} {f : A → B} {a : A}
    → a ∈ₗ l
    → f a ∈ₗ map f l
map-∈ₗ ptr = map-Any (_under _) ptr

-- Bi-implications

record _↔_ {ℓa} {ℓb} (A : Set ℓa) (B : Set ℓb) : Set (ℓa ⊔ ℓb) where
    constructor Bi
    field fwd : A → B
    field bck : B → A
    -- not necessarilty inverses!

-- Bi-implications
module Bi-Impl where
    open _↔_ public

    -- Identiy bi-implications
    id-↔ : A ↔ A
    id-↔  = Bi id id

    -- Bi-implications compose
    _∘∘_ : A ↔ B → B ↔ C → A ↔ C
    (Bi A→B A←B) ∘∘ (Bi B→C B←C) = Bi (B→C ∘ A→B) (A←B ∘ B←C)

    infixl 20 _∘∘_

--------------------------
-- Overlaoded constants --
--------------------------

record From-Nat {ℓ} (A : Set ℓ) : Set ℓ where field fromNat : ℕ → A
record From-Neg {ℓ} (A : Set ℓ) : Set ℓ where field fromNeg : ℕ → A
record From-Str {ℓ} (A : Set ℓ) : Set ℓ where field fromStr : 𝕊 → A
open From-Nat {{...}} public
open From-Neg {{...}} public
open From-Str {{...}} public
{-# BUILTIN FROMNAT fromNat #-}
{-# BUILTIN FROMNEG fromNeg #-}
{-# BUILTIN FROMSTRING fromStr #-}
instance    -- obvious instances
    nat-to-ℤ : From-Nat ℤ
    nat-to-ℤ .fromNat = ℤ.pos
    nat-to-ℕ : From-Nat ℕ
    nat-to-ℕ .fromNat n = n
    neg-to-ℤ : From-Neg ℤ
    neg-to-ℤ .fromNeg = -_ ∘ ℤ.pos
        where open import Data.Integer using (-_)
    str-to-𝕊 : From-Str 𝕊
    str-to-𝕊 .fromStr s = s
