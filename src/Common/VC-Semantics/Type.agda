
-- ↓ Mapping SMT types onto Agda types

module Common.VC-Semantics.Type where
open import Util.All

open import Common.VC-Syntax.Type

-- ↓ Mapping the sorts onto Agda datatypes
⟦_⟧ₜ : Type -> Set
⟦ int ⟧ₜ = ℤ
⟦ bool ⟧ₜ = 𝔹

-- ↓ Mapping lists of sorts onto agda datatypes
-- (needed when calling unintepreted functions)
⟦_⟧ₜₛ : List Type → Set
⟦ [] ⟧ₜₛ = ⊤
⟦ t ∷ ts ⟧ₜₛ = ⟦ t ⟧ₜ × ⟦ ts ⟧ₜₛ
