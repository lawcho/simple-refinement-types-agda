-- Examples demonstrating algorithmic typing of Lang-λβ

module Lang-λβ.Examples where
open import Util.All

open import Lang-λβ.Sugar
open import Lang-λβ.Typing

open import Common.SMT-API

open import Common.VC-Syntax.Type
open import Common.VC-Syntax.Predicate
open import Common.VC-Syntax.Constraint
open import Common.VC-Semantics.Constraint hiding (go)

open import Common.Example-Solver using (solver)

open With-SMT solver
open import Lang-λβ.Algorithmic-Typing solver


-- Abbreviations
nat = int ⟨ "v" ∣ -1 <ᵣ "v" ⟩
int→int = "x" ⦂ int ⟨⟩ →' int ⟨⟩
int→nat = "x" ⦂ int ⟨⟩ →' nat

-- Example 1
-- absolute-value function
---------------------------

abs : Term
abs = letₑ "zero" := 0 inₑ
      λλ "x" ∙
        letₑ "c" := "zero" ≤ₑ "x" inₑ
        ifₑ "c"
        thenₑ "x"
        elseₑ "zero" -ₑ "x"

abs:int→int : [] ⊢ abs ⇐ᵗ int→int
abs:int→int with ofʸ der ← proof $ check [] abs int→int
  = der


-- 'abs' has type int → nat
abs:int→nat : [] ⊢ abs ⇐ᵗ int→nat
abs:int→nat with ofʸ der ← proof $ check [] abs int→nat
    = der
