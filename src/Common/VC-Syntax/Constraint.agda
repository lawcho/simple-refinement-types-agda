-- ↓ Syntax of SMT constraints (a.k.a. "VC"s)
-- (roughly defined in fig 2.1)
-- (with integated scoping)
-- (without UFs)

module Common.VC-Syntax.Constraint where
open import Util.All

-- ↓ Constraints contain types & predicates

open import Common.VC-Syntax.Type
open import Common.VC-Syntax.Predicate

data Constraint (Γ : Context) : Set where
    pred
        : Predicate Γ bool
        → Constraint Γ
    _∧_
        : Constraint Γ
        → Constraint Γ
        → Constraint Γ
    ∀∀_∙_
        : (t : Type)
        → Constraint (t ∷ Γ)
        → Constraint Γ
    _⇒_
        : Predicate Γ bool
        → Constraint Γ
        → Constraint Γ

infixr 15 ∀∀_∙_ _⇒_

-- ↓ "Verification conditions" are constraints with no free variables
VC = Constraint []
