
-- ↓ Mixed Big-step/Denotational semantics of SMT predicates

-- This is described hardly at all in the paper (see §2.2),
-- but needed for the semantics of "Condition"s

-- (without UFs)

module Common.VC-Semantics.Predicate where
open import Util.All

open import Common.VC-Syntax.Type
open import Common.VC-Syntax.Predicate

open import Common.VC-Semantics.Type

module Fixed-Δ
    -- ↓ §2.2:  Substitution (...)
    -- To avoid subsitution,
    -- I introduce "context interpretation"s
    -- (which map variables in a given context onto types)
    {Γ : Context}
    (Δ : All ⟦_⟧ₜ Γ)
    -- (this doesn't change during recursion into predicates,
    -- so is a module-level parameter)
    where
    variable
      τ τ₁ τ₂ τ₃ : Type
      p p₁ p₂ p₃ : Predicate Γ τ
      b b₁ b₂ : 𝔹
      z z₁ z₂ : ℤ
      v : ⟦ τ ⟧ₜ
      v₁ : ⟦ τ₁ ⟧ₜ
      v₂ : ⟦ τ₂ ⟧ₜ
      v₃ : ⟦ τ₃ ⟧ₜ

    -- Denotational semantics of operators
    ⟦_⟧ₒₚ : Interp-Op τ₁ τ₂ τ₃ → ⟦ τ₁ ⟧ₜ → ⟦ τ₂ ⟧ₜ → ⟦ τ₃ ⟧ₜ
    ⟦ > ⟧ₒₚ x y = does (y ℤ.<? x)
    ⟦ < ⟧ₒₚ x y = does (x ℤ.<? y)
    ⟦ ∧ ⟧ₒₚ x y = x 𝔹.∧ y
    ⟦ ∨ ⟧ₒₚ x y = x 𝔹.∨ y
    ⟦ == {ty = int}  ⟧ₒₚ x y = does (x ℤ.≟ y)
    ⟦ == {ty = bool} ⟧ₒₚ x y = does (x 𝔹.≟ y)
    ⟦ + ⟧ₒₚ x y = x ℤ.+ y
    ⟦ - ⟧ₒₚ x y = x ℤ.- y


    -- Big-step semantics of predicates
    data _⇓_ : Predicate Γ τ → ⟦ τ ⟧ₜ → Set where
      ⇓true  : true  ⇓ 𝔹.true
      ⇓false : false ⇓ 𝔹.false
      ⇓num : num z ⇓ z
      ⇓var : ∀{ptr : τ ∈ₗ Γ} → v ≡ follow ptr into Δ → var ptr ⇓ v
      ⇓¬   : p ⇓ b → v ≡ 𝔹.not b → (¬ p) ⇓ v
      ⇓op  : {o : Interp-Op τ₁ τ₂ τ₃}
           → p₁ ⇓ v₁ → p₂ ⇓ v₂
           → v₃ ≡ ⟦ o ⟧ₒₚ v₁ v₂
           → (p₁ ▹ o ◃ p₂) ⇓ v₃
      ⇓if : {a₁ a₂ : ⟦ τ ⟧ₜ} → p ⇓ b → p₁ ⇓ a₁ → p₂ ⇓ a₂
          → v ≡ (𝔹.if b then a₁ else a₂)
          → (if p then p₁ else p₂) ⇓ v

open Fixed-Δ renaming (_⇓_ to _⊢_⇓_) public
