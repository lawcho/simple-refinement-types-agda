
-- ↓ Abstract interface to SMT solvers

module Common.SMT-API where
open import Util.All

open import Common.VC-Semantics.Constraint

-- ↓ An (SMT) Solver is a function that decides
-- whether a given VC is valid
Solver = Decidable Valid
