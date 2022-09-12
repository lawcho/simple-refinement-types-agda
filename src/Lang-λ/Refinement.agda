-- Grammar of Lang-λ type refinements
--
-- Almost identical to the language of refinement predicates
-- (fig 2.1), but:
--  * Un-Scoped and Un-Typed
--  * Missing Uninterpreted Functions.

module Lang-λ.Refinement where
open import Util.All

data Interp-Op : Set where
    + - > < == ∧ ∨ : Interp-Op

data Refinement : Set where
    -- ↓ variables
    var
        : 𝕊 → Refinement
    -- ↓ booleans
    true false
        : Refinement
    -- ↓ numbers
    num
        : ℤ → Refinement
    -- ↓ interpreted operations
    _▹_◃_
        : Refinement → Interp-Op → Refinement → Refinement
    ¬_
        : Refinement → Refinement
    -- ↓ conditonal
    if_then_else_
        : Refinement → Refinement → Refinement → Refinement

open import Agda.Builtin.String
open import Common.α-Renaming 𝕊 primStringEquality public

-- ↓ Capture avoiding α-ops in refinements
-- (implicit in §3.3.1)
infix 21 _[_]ᵣ
_[_]ᵣ : Refinement → α-Op → Refinement
var x [ op ]ᵣ = var (x [ op ]ᵛ)
(r₁ ▹ bo ◃ r₂) [ op ]ᵣ = r₁ [ op ]ᵣ ▹ bo ◃ r₂ [ op ]ᵣ
(¬ r) [ op ]ᵣ = ¬ r [ op ]ᵣ
(if r then r₁ else r₂) [ op ]ᵣ = if r [ op ]ᵣ then r₁ [ op ]ᵣ else r₂ [ op ]ᵣ
r [ _ ]ᵣ = r
