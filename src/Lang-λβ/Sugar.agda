
-- Syntactic sugar for Lang-λβ

module Lang-λβ.Sugar where
open import Util.All

-- Sugared Refinement Language
open import Lang-λβ.Refinement
open import Lang-λβ.Refinement
    hiding (_▹_◃_; Interp-Op; + ; - ; > ; < ; == ; ∧ ; ∨ ; num)
    public

instance
    nat-to-Refinement : From-Nat Refinement
    nat-to-Refinement .fromNat = num ∘  fromNat
    neg-to-Refinement : From-Neg Refinement
    neg-to-Refinement .fromNeg = num ∘ fromNeg
    str-to-Refinement : From-Str Refinement
    str-to-Refinement .fromStr = var

_+ᵣ_ _-ᵣ_ _>ᵣ_ _<ᵣ_ _==ᵣ_ _∧ᵣ_ _∨ᵣ_ : Refinement → Refinement → Refinement
_+ᵣ_ =  _▹ + ◃_
_-ᵣ_ =  _▹ - ◃_
_>ᵣ_ =  _▹ > ◃_
_<ᵣ_ =  _▹ < ◃_
_==ᵣ_ = _▹ == ◃_
_∧ᵣ_ =  _▹ ∧ ◃_
_∨ᵣ_ =  _▹ ∨ ◃_
infixl 25 _+ᵣ_ _-ᵣ_
infix 24 _>ᵣ_ _<ᵣ_
infixr 23 _==ᵣ_
infixr 15 _∧ᵣ_
infixr 14 _∨ᵣ_

-- No sugar for rest of Type language
open import Lang-λβ.Type
    public

-- Sugared Term language
open import Lang-λβ.Term
open import Lang-λβ.Term
    using (Term; true ; false ; λλ_∙_; _⦂_; _[_]; con)
    renaming (if_then_else_ to ifₑ_thenₑ_elseₑ_ ; lett_:=_inn_ to letₑ_:=_inₑ_)
    public

instance
    nat-to-Term : From-Nat Term
    nat-to-Term .fromNat = con ∘ int ∘ fromNat
    neg-to-Term : From-Neg Term
    neg-to-Term .fromNeg = con ∘ int ∘ fromNeg
    str-to-Term : From-Str Term
    str-to-Term .fromStr = var

recursive_⦂_:=_ : Var → Type → Term → Term
recursive x ⦂ ty := body
    = rec x := body ⦂ ty inn var x

infixr 105 recursive_⦂_:=_

_≤ₑ_ = λ x y → con leq [ x ] [ y ]
_+ₑ_ = λ x y → con add [ x ] [ y ]
_-ₑ_ = λ x y → con sub [ x ] [ y ]

infix 200 _≤ₑ_ _+ₑ_ _-ₑ_
