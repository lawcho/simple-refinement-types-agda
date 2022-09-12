-- Grammar of Lang-λ terms
-- (as defined in fig 3.2)
-- Un-typed and un-scoped.

module Lang-λ.Term where
open import Util.All

-- ↓ Terms depend on types
open import Lang-λ.Type

data Constant : Set where
    int : ℤ → Constant
    add sub : Constant

data Term : Set where
    -- ↓ constants
    con
        : Constant → Term

    -- ↓ variables
    var
        : Var → Term

    -- ↓ let-binding
    lett_:=_inn_
        : Var → Term → Term → Term

    -- ↓ functions
    λλ_∙_
        : Var → Term → Term

    -- ↓ application
    _[_]
        : Term → Var → Term

    -- ↓ type-annotation
    _⦂_
        : Term → Type → Term

infixr 105 lett_:=_inn_ λλ_∙_
infixl 106 _[_]
