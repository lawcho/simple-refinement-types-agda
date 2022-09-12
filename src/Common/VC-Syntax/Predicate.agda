-- ↓ Syntax of SMT predicates
-- (roughly defined in fig 2.1)
-- (with integated scoping & simple types)
-- (without UFs)

module Common.VC-Syntax.Predicate where
open import Util.All

-- ↓ Predicates are sort-indexed
open import Common.VC-Syntax.Type

-- ↓ "Variables" are strings
Var = 𝕊

-- ↓ Scoping contexts are flat for the language
Context = List Type

data Interp-Op : Type → Type → Type → Set where
    > < : Interp-Op int int bool
    ∧ ∨ : Interp-Op bool bool bool
    + - : Interp-Op int int int
    == : ∀ {ty} → Interp-Op ty ty bool

-- ↓ Syntax defined in fig 2.1
-- (a small expression language)
data Predicate (Γ : Context) : Type → Set where
    -- ↓ variables
    var
        : ∀ {t}
        → t ∈ₗ Γ
        → Predicate Γ t
    -- ↓ booleans
    true false
        : Predicate Γ bool
    -- ↓ numbers
    num
        : ℤ
        → Predicate Γ int
    -- ↓ interpreted operations
    _▹_◃_
        : ∀{t₁ t₂ t₃}
        → Predicate Γ t₁
        → Interp-Op t₁ t₂ t₃
        → Predicate Γ t₂
        → Predicate Γ t₃
    -- ↓ negation
    ¬_
        : Predicate Γ bool
        → Predicate Γ bool
    -- ↓ conditonal
    if_then_else_
        : ∀ {pt}
        → Predicate Γ bool
        → Predicate Γ pt
        → Predicate Γ pt
        → Predicate Γ pt
