
-- ↓ Denotational semantics of QF-LIA verification conditions

-- (i.e. functions to transalte constraints into Agda types
-- which are inhabited iff the constraints are "valid"
-- (as defined in the paper))

-- This is described a bit in the paper (see §2.2)
-- (but UFs are omitted here)

module Common.VC-Semantics.Constraint where
open import Util.All

open import Common.VC-Syntax.Type
open import Common.VC-Syntax.Predicate
open import Common.VC-Syntax.Constraint

open import Common.VC-Semantics.Type
open import Common.VC-Semantics.Predicate

-- ↓ Finally, the main exhibit of §2.2: the _⊨_ relation!
-- (The type "Σ ⊨ c" contains proofs that "under Σ, c is valid")
-- §2.2:
--  >   We define the notion that
--  >   Σ models a constraint c, written Σ ⊨ c as follows. Σ ⊨ p if p has no free variables and
--  >   p is a tautology under Σ (i.e. Σ(p) ≡ true). Σ ⊨ c₁ ∧ c₂ if if Σ ⊨ c₁ and Σ ⊨ c₂. Finally,
--  >   Σ ⊨ ∀x :b. p ⇒ c if for every constant v of sort b such that Σ ⊨ p [x := v] we have
--  >   Σ ⊨ c [x := v]

⊨_  : VC → Set

-- ↓ Implementation of ⊨_ with interpretation-passing
-- for variables (rather than substitution)
go
    : ∀ {Γ}
    → All ⟦_⟧ₜ Γ
    → Constraint Γ
    → Set
go Δ (pred p) = Δ ⊢ p ⇓ 𝔹.true
go Δ (c₁ ∧ c₂) = go Δ c₁ × go Δ c₂
go Δ (∀∀ t ∙ c) = (v : ⟦ t ⟧ₜ) → go (v ∷ Δ) c
go Δ (p ⇒ c) = go Δ (pred p) → go Δ c

⊨ c = go [] c

-- ↓ §2.2:
--  >   A constraint c is valid if Σ ⊨ c for all interpretations Σ.
Valid : VC → Set
Valid c = ⊨ c
