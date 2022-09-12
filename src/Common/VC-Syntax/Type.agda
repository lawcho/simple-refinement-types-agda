
-- ↓ Syntax of low-level types ("sorts") for SMT solvers
-- (never stated explicitly in the paper)

module Common.VC-Syntax.Type where
open import Util.All

-- ↓ We only need two sorts: int and bool
data Type : Set where
    int bool : Type

_≟-Type_ : (t1 t2 : Type) → Dec (t1 ≡ t2)
int ≟-Type int = yes!
bool ≟-Type bool = yes!
int ≟-Type bool = no λ ()
bool ≟-Type int = no λ ()
