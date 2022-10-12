-- See Lang-λ.Type for general notes,
-- comments in this file emphasize how Lang-λβ differs from Lang-λ

module Lang-λβ.Type where
open import Util.All

open import Lang-λβ.Refinement

Var = 𝕊

data Prim-Type : Set where
    bool int : Prim-Type

data Base-Type : Set where
    bool int : Base-Type    -- NEW: boolean expression type

b2p : Base-Type → Prim-Type
b2p int = int
b2p bool = bool

_≟-Base-Type_ : DecidableEquality Base-Type
int ≟-Base-Type int   = yes!
bool ≟-Base-Type bool = yes!
int ≟-Base-Type bool = no λ ()
bool ≟-Base-Type int = no λ ()

data Type : Set where
    _⟨_∣_⟩ : Base-Type → Var → Refinement → Type
    _⦂_→'_ : Var → Type → Type → Type

infixl 35 _⟨_∣_⟩ _⟨⟩
infixr 30 _⦂_→'_

_⟨⟩ : Base-Type → Type
_⟨⟩ = _⟨ "v" ∣ true ⟩

infix 50 _[_]ₜ
_[_]ₜ : Type → α-Op → Type
(b ⟨ x ∣ r ⟩) [ op ]ₜ = b ⟨ x [ op ]ᵇ ∣ r [ x / op ]ᵣ ⟩
(x ⦂ s →' t) [ op ]ₜ = x [ op ]ᵇ ⦂ s →' t [ x / op ]ₜ
