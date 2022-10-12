-- See Lang-λ.Term for general notes,
-- comments in this file emphasize how Lang-λβ differs from Lang-λ

module Lang-λβ.Term where
open import Util.All

open import Lang-λβ.Type

data Constant : Set where
    int : ℤ → Constant
    add sub : Constant
    true false : Constant   -- NEW: boolean expressions
    leq : Constant          -- NEW: comparison operator

data Term : Set where
    con
        : Constant → Term
    var
        : Var → Term
    lett_:=_inn_
        : Var → Term → Term → Term
    λλ_∙_
        : Var → Term → Term
    _[_]
        : Term → Var → Term
    _⦂_
        : Term → Type → Term
    if_then_else_   -- NEW: branches
        : Var → Term → Term → Term
    rec_:=_⦂_inn_   -- NEW: recursive let
        : Var → Term → Type → Term → Term

infixr 105 lett_:=_inn_ λλ_∙_ if_then_else_ rec_:=_⦂_inn_
infixl 106 _[_]
