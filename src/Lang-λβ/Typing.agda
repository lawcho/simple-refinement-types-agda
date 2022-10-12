-- See Lang-λ.Typing for general notes,
-- comments in this file emphasize how Lang-λβ differs from Lang-λ

module Lang-λβ.Typing where
open import Util.All

open import Common.VC-Syntax.Type as SMT hiding (Type)
open import Common.VC-Syntax.Predicate as SMT hiding (Var; Context; Interp-Op)
open import Common.VC-Syntax.Constraint as SMT hiding (Constraint)

open import Lang-λβ.Refinement
open import Lang-λβ.Type
open import Lang-λβ.Term

data Bind : Set where
    _⦂_ : Var → Type → Bind
    raw : Refinement → Bind

data Prim-Bind : Set where
    _⦂_ : Var → Prim-Type → Prim-Bind

Context      = List      Bind
Prim-Context = List Prim-Bind

lookup : (s : 𝕊) (Γ : Context) → Dec (t ∈ Type ∙ ((s ⦂ t) ∈ₗ Γ))
lookup s [] = no λ ()
lookup s (raw _ ∷ Γ) = map′ (λ{(t , ptr) → t , there ptr}) (λ{(t , there ptr) → t , ptr}) (lookup s Γ)
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


n2pᶜ : Context  → Prim-Context
n2pᶜ = filter ∘ map λ where
    (x ⦂ b ⟨ _ ∣ _ ⟩) → just $ x ⦂ b2p b
    _               → nothing

p2sᵗ : Prim-Type        → SMT.Type
p2sᵇ : Prim-Bind        → SMT.Type
p2sᶜ : Prim-Context     → SMT.Context

p2sᵗ bool = bool
p2sᵗ int  = int
p2sᵇ (_ ⦂ pt) = p2sᵗ pt
p2sᶜ = map p2sᵇ

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

data Kind : Set where
    B * : Kind

data _⊢_:ᵏ_ (Γ : Context) : Type → Kind → Set where
    wf-base
        : ∀ {b x p c}
        → (x ⦂ b2p b ∷ n2pᶜ Γ) ⊢ (pred p) ⇒ᵛᶜ c
        ---------------------------------------
        → Γ ⊢ (b ⟨ x ∣ p ⟩) :ᵏ B
    wf-fun
        : ∀ {x s t kₛ kₜ}
        → Γ ⊢ s :ᵏ kₛ
        → (x ⦂ s ∷ Γ) ⊢ t :ᵏ kₜ
        -----------------------
        → Γ ⊢ (x ⦂ s →' t) :ᵏ *

prim : Constant → Type
prim (int x) = int ⟨ "v" ∣ var "v" ▹ == ◃ num x ⟩
prim add = "x" ⦂ int ⟨⟩ →' "y" ⦂ int ⟨⟩ →' int ⟨ "v" ∣ var "v" ▹ == ◃ (var "x" ▹ + ◃ var "y") ⟩
prim sub = "x" ⦂ int ⟨⟩ →' "y" ⦂ int ⟨⟩ →' int ⟨ "v" ∣ var "v" ▹ == ◃ (var "x" ▹ - ◃ var "y") ⟩
prim true = bool ⟨ "v" ∣ var "v" ▹ == ◃ true ⟩
prim false = bool ⟨ "v" ∣ var "v" ▹ == ◃ false ⟩
prim leq = "x" ⦂ int ⟨⟩ →' "y" ⦂ int ⟨⟩ →' bool ⟨ "b" ∣ (var "b" ▹ == ◃
    ((var "x" ▹ < ◃ var "y") ▹ ∨ ◃ (var "x" ▹ == ◃ var "y"))) ⟩


open import Common.SMT-API
module With-SMT (smt : Solver) where

    data _⊢_ : Context → Untyped-Constraint → Set where
        ent-emp
            : ∀{c c'}
            → [] ⊢ c ⇒ᵛᶜ c'
            → does (smt c') ≡ 𝔹.true
            ----------------------
            → [] ⊢ c
        ent-base
            : ∀{Γ c x v b p}
            → Γ ⊢ (∀∀ x ⦂ b2p b ∙ ((p [ v := x ]ᵣ) ⇒ c))
            --------------------------------------------
            → (x ⦂ b ⟨ v ∣ p ⟩ ∷ Γ) ⊢ c
        ent-raw
            : ∀{Γ c r}
            → Γ ⊢ (r ⇒ c)
            -----------------
            → (raw r ∷ Γ) ⊢ c
        ent-fun
            : ∀{Γ c x y s t}
            → Γ ⊢ c
            ---------------------------
            → (x ⦂ (y ⦂ s →' t) ∷ Γ) ⊢ c

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

    data _⊢_⇒ᵗ_ Context : Term → Type → Set
    data _⊢_⇐ᵗ_ Context : Term → Type → Set

    -- NEW: "selfification" from fig 4.3
    self : 𝕊 → Type → Type
    self x (b ⟨ v ∣ r ⟩) = b ⟨ v ∣ (var x ▹ == ◃ var v) ▹ ∧ ◃ r ⟩
    self x t = t

    data _⊢_⇒ᵗ_ Γ where
        syn-var
            : ∀ {x t ptr}
            → lookup x Γ ≡ yes (t , ptr)
            ---------------------------
            → Γ ⊢ var x ⇒ᵗ self x t
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
        -- NEW: typing rule for branches
        chk-if
            : ∀ {x e₁ e₂ t}
            → Γ ⊢ var x ⇐ᵗ (bool ⟨⟩)
            → (raw (var x ▹ == ◃ true ) ∷ Γ) ⊢ e₁ ⇐ᵗ t
            → (raw (var x ▹ == ◃ false) ∷ Γ) ⊢ e₂ ⇐ᵗ t
            → Γ ⊢ if x then e₁ else e₂ ⇐ᵗ t
        -- NEW: typing rule for recursive let
        chk-rec
            : ∀ {x e₁ t₁ e₂ t₂ k}
            → Γ ⊢ t₁ :ᵏ k
            → (x ⦂ t₁ ∷ Γ) ⊢ e₁ ⇐ᵗ t₁
            → (x ⦂ t₁ ∷ Γ) ⊢ e₂ ⇐ᵗ t₂
            → Γ ⊢ rec x := e₁ ⦂ t₁ inn e₂ ⇐ᵗ t₂
