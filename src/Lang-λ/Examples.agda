-- Examples demonstrating algorithmic typing of Lang-λ

module Lang-λ.Examples where
open import Util.All

open import Common.SMT-API
open import Common.Example-Solver using (solver)
open import Lang-λ.Algorithmic-Typing solver
    hiding (neg)

-- Abbreviations
----------------

-- The value four
four = (con ∘ int ∘ ℤ.pos) 4

-- Type of (non-)negative integers
nat = int ⟨ "v" ∣ var "v" ▹ > ◃ num (ℤ.negsuc 0) ⟩
neg = int ⟨ "v" ∣ var "v" ▹ < ◃ num (ℤ.pos 0) ⟩

-- Non-dependent functions
int→int = "x" ⦂ int ⟨⟩ →' int ⟨⟩
nat→nat = "x" ⦂ nat →' nat
neg→neg = "x" ⦂ neg →' neg


-- Example 1
--
-- the types of 4
-----------------

open import Common.VC-Syntax.Type
open import Common.VC-Syntax.Predicate
open import Common.VC-Syntax.Constraint
open import Common.Example-Solver

-- 4 is an int
four:int : [] ⊢ four ⇐ᵗ int ⟨⟩
four:int with ofʸ der ← proof $ check [] four (int ⟨⟩)
    = der
-- 4 is *also* a natural number
four:nat : [] ⊢ four ⇐ᵗ nat
four:nat with ofʸ der ← proof $ check [] four nat
    = der
-- However, 4 is *not* a function
¬four:int→int : [] ⊢ four ⇍ᵗ int→int
¬four:int→int with ofⁿ der ← proof $ check [] four int→int
    = der


-- Example 2
--
-- the +4 function
------------------

+4 : Term
+4 =
  λλ "x" ∙
  lett "four" := four inn
  con add [ "x" ] [ "four" ]

-- +4 is a function from ints to ints
+4:int→int : [] ⊢ +4 ⇐ᵗ int→int
+4:int→int with ofʸ der ← proof $ check [] +4 int→int
    = der

-- +4 is *also* function from nats to nats
+4:nat→nat : [] ⊢ +4 ⇐ᵗ nat→nat
+4:nat→nat with ofʸ der ← proof $ check [] +4 nat→nat
    = der

-- However, +4 is *not* function from negative ints to negative ints
¬+4:neg→neg : [] ⊢ +4 ⇍ᵗ neg→neg
¬+4:neg→neg with ofⁿ der ← proof $ check [] +4 neg→neg
    = der

-- Example 3
--
-- The "apply twice" function
-----------------------------

twice : Term
twice =
  λλ "f" ∙
  λλ "x" ∙
  lett "fx" := var "f" [ "x"] inn
  var "f" [ "fx" ]

[int→int]→[int→int] = "f" ⦂ int→int →' int→int

-- twice is an int→int transformer
-- (N.B. this uses the 'ent-ext' rule missing from the original paper)
twice:[int→int]→[int→int] : [] ⊢ twice ⇐ᵗ [int→int]→[int→int]
twice:[int→int]→[int→int] with ofʸ der  ← proof $ check [] twice [int→int]→[int→int]
    = der
 