-- â Syntax of SMT predicates
-- (roughly defined in fig 2.1)
-- (with integated scoping & simple types)
-- (without UFs)

module Common.VC-Syntax.Predicate where
open import Util.All

-- â Predicates are sort-indexed
open import Common.VC-Syntax.Type

-- â "Variables" are strings
Var = ğ

-- â Scoping contexts are flat for the language
Context = List Type

data Interp-Op : Type â Type â Type â Set where
    > < : Interp-Op int int bool
    â§ â¨ : Interp-Op bool bool bool
    + - : Interp-Op int int int
    == : â {ty} â Interp-Op ty ty bool

-- â Syntax defined in fig 2.1
-- (a small expression language)
data Predicate (Î : Context) : Type â Set where
    -- â variables
    var
        : â {t}
        â t ââ Î
        â Predicate Î t
    -- â booleans
    true false
        : Predicate Î bool
    -- â numbers
    num
        : â¤
        â Predicate Î int
    -- â interpreted operations
    _â¹_â_
        : â{tâ tâ tâ}
        â Predicate Î tâ
        â Interp-Op tâ tâ tâ
        â Predicate Î tâ
        â Predicate Î tâ
    -- â negation
    Â¬_
        : Predicate Î bool
        â Predicate Î bool
    -- â conditonal
    if_then_else_
        : â {pt}
        â Predicate Î bool
        â Predicate Î pt
        â Predicate Î pt
        â Predicate Î pt
