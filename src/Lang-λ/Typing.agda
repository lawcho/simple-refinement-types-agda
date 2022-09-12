-- Typing relations for Lang-λ
-- (as defined in figs 3.{3,4,5,6})

module Lang-λ.Typing where
open import Util.All

open import Common.VC-Syntax.Type as SMT hiding (Type)
open import Common.VC-Syntax.Predicate as SMT hiding (Var; Context; Interp-Op)
open import Common.VC-Syntax.Constraint as SMT hiding (Constraint)

open import Lang-λ.Refinement
open import Lang-λ.Type
open import Lang-λ.Term

-- ↓ §3.3.2:
-- >    A context Γ is a sequence
-- >    of variable-type bindings x₁:t₁,...,xₙ:tₙ .
data Bind : Set where
    _⦂_ : Var → Type → Bind

data Prim-Bind : Set where
    _⦂_ : Var → Prim-Type → Prim-Bind

Context      = List      Bind
Prim-Context = List Prim-Bind

lookup : (s : 𝕊) (Γ : Context) → Dec (t ∈ Type ∙ ((s ⦂ t) ∈ₗ Γ))
lookup s [] = no λ ()
lookup s (x ⦂ t ∷ Γ)
    with s 𝕊.≟ x
... | yes! = yes $ t , ↑0
... | no s≢x = map′ (λ{(t , ptr) → t , there ptr}) (λ{ (_ , ↑0) → explode (s≢x refl) ; (t , there ptr) → t , ptr}) (lookup s Γ)

prim-lookup : (s : 𝕊) (Δ : Prim-Context) → Dec (t ∈ Prim-Type ∙ ((s ⦂ t) ∈ₗ Δ))
prim-lookup s [] = no λ ()
prim-lookup s (x ⦂ t ∷ Δ)
    with s 𝕊.≟ x
... | yes! = yes $ t , ↑0
... | no s≢x = map′ (λ{(t , ptr) → t , there ptr}) (λ{ (_ , ↑0) → explode (s≢x refl) ; (t , there ptr) → t , ptr}) (prim-lookup s Δ)



-- "normal" ⇀ "primitive" conversion of {types, binding, contexts}
------------------------------------------------------------------

-- (this is very implicit in the paper, -- e.g. the first rule in fig 3.3
-- puts a raw base/primitive type into a 'context')

n2pᶜ : Context  → Prim-Context
n2pᶜ = filter ∘ map λ where
    (x ⦂ b ⟨ _ ∣ _ ⟩) → just $ x ⦂ b2p b
    _               → nothing


-- "primitive" → "SMT" conversion of {types, binding, contexts}
---------------------------------------------------------------

-- These translate trivially to their SMT counterparts

p2sᵗ : Prim-Type        → SMT.Type
p2sᵇ : Prim-Bind        → SMT.Type
p2sᶜ : Prim-Context     → SMT.Context

p2sᵗ bool = bool
p2sᵗ int  = int
p2sᵇ (_ ⦂ pt) = p2sᵗ pt
p2sᶜ = map p2sᵇ

-- Well-formedness of refinements
-- (used without definition in fig 3.3)
---------------------------------------

data _⇒ᵒ_
    : Interp-Op
    → ∀ {t₁ t₂ t₃}
    → SMT.Interp-Op t₁ t₂ t₃
    → Set where
    + : + ⇒ᵒ +
    - : - ⇒ᵒ -
    > : > ⇒ᵒ >
    < : < ⇒ᵒ <
    == : ∀ {t} → == ⇒ᵒ == {t}
    ∨ : ∨ ⇒ᵒ ∨
    ∧ : ∧ ⇒ᵒ ∧

data _⊢_⇒ᵖ_
    (Δ : Prim-Context)
    : Refinement
    → {t : SMT.Type}
    → Predicate (p2sᶜ Δ) t
    → Set where
    var
        : ∀ {s t ptr}
        → prim-lookup s Δ ≡ yes (t , ptr)
        ---------------------------------
        → Δ ⊢ var s ⇒ᵖ var (map-∈ₗ ptr)
    true
        -------------------
        : Δ ⊢ true  ⇒ᵖ true
    false
        -------------------
        : Δ ⊢ false ⇒ᵖ false
    num
        : ∀ {n}
        -------------------
        → Δ ⊢ num n ⇒ᵖ num n

    op
        : ∀ {r₁ r₂ op t₁ t₂ t₃}
            {r₁' : SMT.Predicate _ t₁}
            {r₂' : SMT.Predicate _ t₂}
            {op' : SMT.Interp-Op t₁ t₂ t₃}
        → Δ ⊢ r₁ ⇒ᵖ r₁'
        → Δ ⊢ r₂ ⇒ᵖ r₂'
        → op ⇒ᵒ op'
        ---------------------------------------
        → Δ ⊢ r₁ ▹ op ◃ r₂ ⇒ᵖ (r₁' ▹ op' ◃ r₂')
    neg
        : ∀ {r r'}
        → Δ ⊢ r ⇒ᵖ r'
        -------------------
        → Δ ⊢ ¬ r ⇒ᵖ (¬ r')
    if
        : ∀ {r₁ r₂ r₃ r₁' t}
            {r₂' r₃' : SMT.Predicate _ t}
        → Δ ⊢ r₁ ⇒ᵖ r₁'
        → Δ ⊢ r₂ ⇒ᵖ r₂'
        → Δ ⊢ r₃ ⇒ᵖ r₃'
        ---------------------------------
        → Δ ⊢ if r₁ then r₂ else r₃
            ⇒ᵖ (if r₁' then r₂' else r₃')

-- Well-formedness of constraints
---------------------------------

-- ↓ Untyped version of SMT constraints...
data Untyped-Constraint : Set where
    pred : Refinement → Untyped-Constraint
    ∀∀_∙_
        : Prim-Bind
        → Untyped-Constraint
        → Untyped-Constraint
    _⇒_
        : Refinement
        → Untyped-Constraint
        → Untyped-Constraint

-- ↓ ... and their well-formedness-relation

data _⊢_⇒ᵛᶜ_
    (Δ : Prim-Context)
    : Untyped-Constraint
    → SMT.Constraint (p2sᶜ Δ)
    → Set where
    pred
        : ∀ {p p'}
        → Δ ⊢ p ⇒ᵖ p'
        ------------------------
        → Δ ⊢ pred p ⇒ᵛᶜ pred p'
    quant
        : ∀ {v t c c'}
        → (v ⦂ t ∷ Δ) ⊢ c ⇒ᵛᶜ c'
        -----------------------------------------
        → Δ ⊢ (∀∀ v ⦂ t ∙ c) ⇒ᵛᶜ (∀∀ p2sᵗ t ∙ c')
    impl
        : ∀{p c p' c'}
        → Δ ⊢ p ⇒ᵖ  p'
        → Δ ⊢ c ⇒ᵛᶜ c'
        ---------------------------
        → Δ ⊢ (p ⇒ c) ⇒ᵛᶜ (p' ⇒ c')

-- ↓ "Kinds" from fig 3.1
data Kind : Set where
    B * : Kind

-- ↓ "Has kind" reation from fig 3.3
-- (note that the kind is never used outside this relation)
data _⊢_:ᵏ_ (Γ : Context) : Type → Kind → Set where
    wf-base
        : ∀ {b x p c}
        → (x ⦂ b2p b ∷ n2pᶜ Γ) ⊢ (pred p) ⇒ᵛᶜ c
        ----------------------------------------
        → Γ ⊢ (b ⟨ x ∣ p ⟩) :ᵏ B
    wf-fun
        : ∀ {x s t kₛ kₜ}
        → Γ ⊢ s :ᵏ kₛ
        → (x ⦂ s ∷ Γ) ⊢ t :ᵏ kₜ
        -----------------------
        → Γ ⊢ (x ⦂ s →' t) :ᵏ *

-- ↓ Direct from §3.3.3
prim : Constant → Type
prim (int x) = int ⟨ "v" ∣ var "v" ▹ == ◃ num x ⟩
prim add = "x" ⦂ int ⟨⟩ →' "y" ⦂ int ⟨⟩ →' int ⟨ "v" ∣ var "v" ▹ == ◃ (var "x" ▹ + ◃ var "y") ⟩
prim sub = "x" ⦂ int ⟨⟩ →' "y" ⦂ int ⟨⟩ →' int ⟨ "v" ∣ var "v" ▹ == ◃ (var "x" ▹ - ◃ var "y") ⟩


-- ↓ These relations require an SMT solver
open import Common.SMT-API
module With-SMT (smt : Solver) where

    -- ↓ "Entailment" from fig 3.4 (and missing a rule!)
    data _⊢_ : Context → Untyped-Constraint → Set where
        -- ↓ dependency on SMT here
        ent-emp
            : ∀{c c'}
            → [] ⊢ c ⇒ᵛᶜ c'
            → does (smt c') ≡ 𝔹.true
            ----------------------
            → [] ⊢ c
        -- ↓ "ent-ext" in paper
        ent-base
            : ∀{Γ c x v b p}
            → Γ ⊢ (∀∀ x ⦂ b2p b ∙ ((p [ v := x ]ᵣ) ⇒ c))
            --------------------------------------------
            → (x ⦂ b ⟨ v ∣ p ⟩ ∷ Γ) ⊢ c
        -- ↓ NOT IN PAPER (but it should be -- needed for higher-order functions)
        ent-fun
            : ∀{Γ c x y s t}
            → Γ ⊢ c
            ---------------------------
            → (x ⦂ (y ⦂ s →' t) ∷ Γ) ⊢ c

    -- ↓ "Subtyping" from fig 3.4
    data _⊢_≺:_ (Γ : Context) : Type → Type → Set where
        sub-base
            : ∀{b v₁ p₁ v₂ p₂}
            → Γ ⊢ (∀∀ (v₁ ⦂ b2p b) ∙ (p₁ ⇒ pred (p₂ [ v₂ := v₁ ]ᵣ)))
            --------------------------------------------------------
            → Γ ⊢ b ⟨ v₁ ∣ p₁ ⟩ ≺: b ⟨ v₂ ∣ p₂ ⟩
        sub-fun
            : ∀{x₁ s₁ t₁ x₂ s₂ t₂}
            → Γ ⊢ s₂ ≺: s₁
            → (x₂ ⦂ s₂ ∷ Γ) ⊢ t₁ [ x₁ := x₂ ]ₜ ≺: t₂
            ----------------------------------------
            → Γ ⊢ (x₁ ⦂ s₁ →' t₁) ≺: (x₂ ⦂ s₂ →' t₂)

    -- ↓ Type Synthesis and Checking (figs 3.5 and 3.6 resp.)
    data _⊢_⇒ᵗ_ Context : Term → Type → Set
    data _⊢_⇐ᵗ_ Context : Term → Type → Set

    data _⊢_⇒ᵗ_ Γ where
        syn-var
            : ∀ {x t ptr}
            → lookup x Γ ≡ yes (t , ptr)
            ---------------------------
            → Γ ⊢ var x ⇒ᵗ t
        syn-con
            : ∀{c t}
            → prim c ≡ t
            ---------------
            → Γ ⊢ con c ⇒ᵗ t
        syn-ann
            : ∀{e t k}
            → Γ ⊢ t :ᵏ k
            → Γ ⊢ e ⇐ᵗ t
            ---------------
            → Γ ⊢ e ⦂ t ⇒ᵗ t
        syn-app
            : ∀ {e x s t y}
            → Γ ⊢ e ⇒ᵗ (x ⦂ s →' t)
            → Γ ⊢ var y ⇐ᵗ s
            -------------------------------
            → Γ ⊢ e [ y ] ⇒ᵗ (t [ x := y ]ₜ)

    data _⊢_⇐ᵗ_ Γ where
        chk-syn
            : ∀ {e s t}
            → Γ ⊢ e ⇒ᵗ s
            → Γ ⊢ s ≺: t
            ------------
            → Γ ⊢ e ⇐ᵗ t
        chk-lam
            : ∀ {x t₁ e t₂}
            → (x ⦂ t₁ ∷ Γ) ⊢ e ⇐ᵗ t₂
            ----------------------------
            → Γ ⊢ λλ x ∙ e ⇐ᵗ x ⦂ t₁ →' t₂
        chk-let
            : ∀ {e₁ t₁ x e₂ t₂}
            → Γ ⊢ e₁ ⇒ᵗ t₁
            → (x ⦂ t₁ ∷ Γ) ⊢ e₂ ⇐ᵗ t₂
            -----------------------------
            → Γ ⊢ lett x := e₁ inn e₂ ⇐ᵗ t₂

    -- Negated forms
    _⊢_⇏ᵗ_ _⊢_⇍ᵗ_ : Context → Term → Type → Set
    Γ ⊢ e ⇏ᵗ t = ¬' (Γ ⊢ e ⇒ᵗ t)
    Γ ⊢ e ⇍ᵗ t = ¬' (Γ ⊢ e ⇐ᵗ t)
