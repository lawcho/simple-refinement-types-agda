-- Grammar of Lang-λ types
-- (as in fig 3.1)
-- Un-Typed and Un-Scoped

module Lang-λ.Type where
open import Util.All

open import Lang-λ.Refinement

Var = 𝕊

-- ↓ "Primitive Types" are for expressions *inside* refinements.
data Prim-Type : Set where
    bool int : Prim-Type

-- ↓ "Base Types" are for expressions *outside* refinements.
data Base-Type : Set where
    int : Base-Type

-- ↓ However, base types translate easily to primitive types
b2p : Base-Type → Prim-Type
b2p int = int

-- ↓ Base types can be compared for equality
_≟-Base-Type_ : DecidableEquality Base-Type
int ≟-Base-Type int = yes!

-- ↓ Some types are not base types.
data Type : Set where
    -- ↓ Refined base types
    _⟨_∣_⟩ : Base-Type → Var → Refinement → Type
    -- ↓ Dependent function types
    _⦂_→'_ : Var → Type → Type → Type

infixl 35 _⟨_∣_⟩ _⟨⟩
infixr 30 _⦂_→'_

-- Helper: write types with trivial refinements
_⟨⟩ : Base-Type → Type
_⟨⟩ = _⟨ "v" ∣ true ⟩

infix 50 _[_]ₜ
-- ↓ Capture-avoiding α-ops in types
-- (from §3.3.1, with bug patched)
_[_]ₜ : Type → α-Op → Type
(b ⟨ x ∣ r ⟩) [ op ]ₜ = b ⟨ x [ op ]ᵇ ∣ r [ x / op ]ᵣ ⟩
(x ⦂ s →' t) [ op ]ₜ = x [ op ]ᵇ ⦂ s →' t [ x / op ]ₜ

----------------
-- Unit Tests --
----------------

private
    -- Helpers for tests
    open import Agda.Builtin.Equality
    pattern _⇛_ v e = (v ⦂ int ⟨ "v" ∣ true ⟩ →' e)
    pattern % v = int ⟨ "a" ∣ var "a" ▹ == ◃ var v ⟩
    pattern %% v1 v2 = int ⟨ "a" ∣ (var "a" ▹ == ◃ var v1) ▹ ∨ ◃ (var "a" ▹ == ◃ var v2) ⟩
    pattern %%% v1 v2 v3 =
        int ⟨ "a" ∣ (var "a" ▹ == ◃ var v1)
        ▹ ∨ ◃ ((var "a" ▹ == ◃ var v2)
        ▹ ∨ ◃ (var "a" ▹ == ◃ var v3)) ⟩
    infixr 50 _⇛_
    y = "y"
    x = "x"
    z = "z"

    -- Tests

    test-1 : (x ⇛ % x) [ y := x ]ₜ ≡ (y ⇛ % y)
    test-2 : (x ⇛ % y) [ y := x ]ₜ ≡ (y ⇛ % x)
    test-3 : (x ⇛ y ⇛ % x) [ y := x ]ₜ ≡ (y ⇛ x ⇛ % y)
    test-4 : (x ⇛ y ⇛ %% x y) [ y := x ]ₜ ≡ (y ⇛ x ⇛ %% y x)
    test-5 : (x ⇛ y ⇛ %%% x y z) [ z := x ]ₜ ≡ (z ⇛ y ⇛ %%% z y x)
    test-6 : (x ⇛ y ⇛ %%% x y z) [ z := y ]ₜ ≡ (x ⇛ z ⇛ %%% x z y)
    test-1 = refl
    test-2 = refl
    test-3 = refl
    test-4 = refl
    test-5 = refl
    test-6 = refl
