
-- Utilities for implementing capture-avoiding α-renaming

open import Data.Bool using (Bool ; true ; false)

module Common.α-Renaming
    (Var : Set)
    (_==_ : Var → Var → Bool)
    where

---------
-- API --
---------

data α-Op : Set where
    nop  : α-Op                 -- Do-nothing
    _:=_ : Var → Var → α-Op     -- Capture-avoiding α-renaming
    _←→_ : Var → Var → α-Op     -- Capture-avoiding α-swapping

_[_]ᵛ : Var → α-Op → Var    -- Apply an α-Op to variable
_[_]ᵇ : Var → α-Op → Var    -- Apply an α-Op to binder
_/_ : Var → α-Op → α-Op     -- Calculate an α-Op to apply recursively under binder

infix 50 _[_]ᵛ _[_]ᵇ _/_

--------------------
-- Implementation --
--------------------

private
    infixr 1 _if_∣_
    _if_∣_ : {ℓ : _} {A : Set ℓ} → A → Bool → A → A
    _ if false ∣ y = y
    x if true  ∣ _ = x

    record Result : Set where
        constructor _,_∙_
        field v' : Var
        field b' : Var
        field op' : α-Op
    open Result
    infix 15 _,_∙_

    go : Var → α-Op → Result
    go v nop        = v  , v  ∙ nop
    go v (x₁ ←→ x₂) = x₂ , x₂ ∙ x₁ ←→ x₂ if v == x₁
                    ∣ x₁ , x₁ ∙ x₁ ←→ x₂ if v == x₂
                    ∣ v  , v  ∙ x₁ ←→ x₂
    go v (x₁ := x₂) = x₂ , v  ∙ nop      if v == x₁
                    ∣ v  , x₁ ∙ x₁ ←→ x₂ if v == x₂
                    ∣ v  , v  ∙ x₁ := x₂
    -- Columns:       ⇑    ⇑      ⇑
    -- v [ op ]ᵛ = ═══╝    ║      ║
    -- b [ op ]ᵇ = ════════╝      ║
    -- b / op    = ═══════════════╝

v [ op ]ᵛ = v' (go v op)
v [ op ]ᵇ = b' (go v op)
v / op    = op' (go v op)
