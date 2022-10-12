-- See Lang-λ.Refinement for general notes,
-- comments in this file emphasize how Lang-λβ differs from Lang-λ

module Lang-λβ.Refinement where
open import Util.All

data Interp-Op : Set where
    + - > < == ∧ ∨ : Interp-Op

data Refinement : Set where
    var
        : 𝕊 → Refinement
    true false
        : Refinement
    num
        : ℤ → Refinement
    _▹_◃_
        : Refinement → Interp-Op → Refinement → Refinement
    ¬_
        : Refinement → Refinement
    if_then_else_
        : Refinement → Refinement → Refinement → Refinement


open import Agda.Builtin.String
open import Common.α-Renaming 𝕊 primStringEquality public

infix 21 _[_]ᵣ
_[_]ᵣ : Refinement → α-Op → Refinement
var x [ op ]ᵣ = var (x [ op ]ᵛ)
(r₁ ▹ bo ◃ r₂) [ op ]ᵣ = r₁ [ op ]ᵣ ▹ bo ◃ r₂ [ op ]ᵣ
(¬ r) [ op ]ᵣ = ¬ r [ op ]ᵣ
(if r then r₁ else r₂) [ op ]ᵣ = if r [ op ]ᵣ then r₁ [ op ]ᵣ else r₂ [ op ]ᵣ
r [ _ ]ᵣ = r
