-- Algorithmic versions of {subtyping,synthesis,checking}
-- for Lang-λ
-- (as defined in figs 3.{7,8,9})

-- Correct-by-construction

open import Common.SMT-API

module Lang-λ.Algorithmic-Typing
    (smt : Solver)
    where

open import Util.All

open import Common.VC-Syntax.Type hiding (Type)
import      Common.VC-Syntax.Type       as SMT
open import Common.VC-Syntax.Constraint as SMT
import      Common.VC-Syntax.Predicate  as SMT

open import Lang-λ.Refinement   public
open import Lang-λ.Type         public
open import Lang-λ.Term         public
open import Lang-λ.Typing       public
open With-SMT smt public

open Do-id

-- All the synthesis relations are functional (in their 3rd argument)

fun-⇒ᵖ
    : ∀ {Δ r t₁ t₂} {p₁ : SMT.Predicate (p2sᶜ Δ) t₁} {p₂ : SMT.Predicate (p2sᶜ Δ) t₂}
    → (Δ ⊢ r ⇒ᵖ p₁) → (Δ ⊢ r ⇒ᵖ p₂) → Σ (t₁ ≡ t₂) λ {refl → p₁ ≡ p₂}
fun-⇒ᵖ (var eq1) (var eq2)
    with refl , pf ← inj-fst-snd $ inj-yes $ eq1 flipped then eq2
    = refl , pf under map-∈ₗ under SMT.var
fun-⇒ᵖ true true = refl , refl
fun-⇒ᵖ false false = refl , refl
fun-⇒ᵖ num num = refl , refl
fun-⇒ᵖ (op x1 y1 o1) (op x2 y2 o2)
    with refl , refl ← fun-⇒ᵖ x1 x2
    with refl , refl ← fun-⇒ᵖ y1 y2
    with o1 | o2
... | + | + = refl , refl
... | - | - = refl , refl
... | > | > = refl , refl
... | < | < = refl , refl
... | == | == = refl , refl
... | ∨ | ∨ = refl , refl
... | ∧ | ∧ = refl , refl
fun-⇒ᵖ (neg d1) (neg d2)
    with refl , refl ← fun-⇒ᵖ d1 d2
    = refl , refl
fun-⇒ᵖ (if x1 y1 z1) (if x2 y2 z2)
    with refl , refl ← fun-⇒ᵖ x1 x2
    with refl , refl ← fun-⇒ᵖ y1 y2
    with refl , refl ← fun-⇒ᵖ z1 z2
    = refl , refl

fun-⇒ᵖ'
    : ∀ {Δ r t₁ t₂} {p₁ : SMT.Predicate (p2sᶜ Δ) t₁} {p₂ : SMT.Predicate (p2sᶜ Δ) t₂}
    → (Δ ⊢ r ⇒ᵖ p₁) → (Δ ⊢ r ⇒ᵖ p₂) → (t₁ ≢ t₂) → ⊥
fun-⇒ᵖ' d1 d2 t₁≢t₂ = t₁≢t₂ $ fst $ fun-⇒ᵖ d1 d2

fun-⇒ᵛᶜ : ∀ {Δ c c'₁ c'₂} → (Δ ⊢ c ⇒ᵛᶜ c'₁) → (Δ ⊢ c ⇒ᵛᶜ c'₂) → c'₁ ≡ c'₂
fun-⇒ᵛᶜ (pred d1) (pred d2)
    with refl , pf ← fun-⇒ᵖ d1 d2
    = pf under pred
fun-⇒ᵛᶜ (impl d1 d1') (impl d2 d2')
    with refl , pf ← fun-⇒ᵖ d1 d2
    = pf and (fun-⇒ᵛᶜ d1' d2') under _⇒_
fun-⇒ᵛᶜ (quant d1) (quant d2)
    = fun-⇒ᵛᶜ d1 d2 under (∀∀ _ ∙_)

fun-⇒ : ∀ {Γ e t t'} → (Γ ⊢ e ⇒ᵗ t) → (Γ ⊢ e ⇒ᵗ t') → t ≡ t'
fun-⇒ (syn-var eq1) (syn-var eq2) =
    fst $ inj-fst-snd $ inj-yes $ eq1 flipped then eq2
fun-⇒ (syn-con eq1) (syn-con eq2) = eq1 flipped then eq2
fun-⇒ (syn-ann _ _) (syn-ann _ _) = refl
fun-⇒ (syn-app sy1 _) (syn-app sy2 _)
    with refl ← fun-⇒ sy1 sy2
    = refl

-- ↓ Algorithmic type inference for
-- {refinement, untyped constriants, types}
-- Never stated, but required for our C-by-C function.

dec-⇒ᵖ : ∀ Δ r → Dec
    $ t ∈ SMT.Type
    ∙ p ∈ SMT.Predicate (p2sᶜ Δ) t
    ∙ (Δ ⊢ r ⇒ᵖ p)
dec-⇒ᵖ Δ (var x)
    with prim-lookup x Δ in spl
... | no _ = no λ{(_ , _ , var p) → no≢yes $ spl flipped then p}
... | yes _ = yes $ _ , _ , var spl
dec-⇒ᵖ Δ true = yes $ _ , _ , true
dec-⇒ᵖ Δ false = yes $ _ , _ , false
dec-⇒ᵖ Δ (num _) = yes $ _ , _ , num
dec-⇒ᵖ Δ (r₁ ▹ bo ◃ r₂)
    with dec-⇒ᵖ Δ r₁ | dec-⇒ᵖ Δ r₂
... | no ∄sy₁ | _ = no λ{(_ , _ , op sy₁ _ _) → ∄sy₁ $ _ , _ , sy₁}
... | _ | no ∄sy₂ = no λ{(_ , _ , op _ sy₂ _) → ∄sy₂ $ _ , _ , sy₂}
... | yes (t₁ , p₁ , sy₁) | yes (t₂ , p₂ , sy₂)
    with bo | t₁ | t₂
... | + | int   | int   = yes $ _ , _ , op sy₁ sy₂ +
... | + | bool  | _     = no $ λ{(t , _ , op sy₁' _ +) → fun-⇒ᵖ' sy₁ sy₁' λ ()}
... | + | _     | bool  = no $ λ{(t , _ , op _ sy₂' +) → fun-⇒ᵖ' sy₂ sy₂' λ ()}
... | - | int   | int   = yes $ _ , _ , op sy₁ sy₂ -
... | - | bool  | _     = no $ λ{(t , _ , op sy₁' _ -) → fun-⇒ᵖ' sy₁ sy₁' λ ()}
... | - | _     | bool  = no $ λ{(t , _ , op _ sy₂' -) → fun-⇒ᵖ' sy₂ sy₂' λ ()}
... | > | int   | int   = yes $ _ , _ , op sy₁ sy₂ >
... | > | bool  | _     = no $ λ{(t , _ , op sy₁' _ >) → fun-⇒ᵖ' sy₁ sy₁' λ ()}
... | > | _     | bool  = no $ λ{(t , _ , op _ sy₂' >) → fun-⇒ᵖ' sy₂ sy₂' λ ()}
... | < | int   | int   = yes $ _ , _ , op sy₁ sy₂ <
... | < | bool  | _     = no $ λ{(t , _ , op sy₁' _ <) → fun-⇒ᵖ' sy₁ sy₁' λ ()}
... | < | _     | bool  = no $ λ{(t , _ , op _ sy₂' <) → fun-⇒ᵖ' sy₂ sy₂' λ ()}
... | ∧ | bool  | bool  = yes $ _ , _ , op sy₁ sy₂ ∧
... | ∧ | int   | _     = no $ λ{(t , _ , op sy₁' _ ∧) → fun-⇒ᵖ' sy₁ sy₁' λ ()}
... | ∧ | _     | int   = no $ λ{(t , _ , op _ sy₂' ∧) → fun-⇒ᵖ' sy₂ sy₂' λ ()}
... | ∨ | bool  | bool  = yes $ _ , _ , op sy₁ sy₂ ∨
... | ∨ | int   | _     = no $ λ{(t , _ , op sy₁' _ ∨) → fun-⇒ᵖ' sy₁ sy₁' λ ()}
... | ∨ | _     | int   = no $ λ{(t , _ , op _ sy₂' ∨) → fun-⇒ᵖ' sy₂ sy₂' λ ()}
... | == | int  | int   = yes $ _ , _ , op sy₁ sy₂ ==
... | == | int  | bool  = no $ λ
        {   (_ , _ , op _ syⁱ (== {int})) → fun-⇒ᵖ' sy₂ syⁱ λ ()
        ;   (_ , _ , op syᵇ _ (== {bool})) → fun-⇒ᵖ' sy₁ syᵇ λ ()}
... | == | bool | int   = no $ λ
        {   (_ , _ , op syⁱ _ (== {int})) → fun-⇒ᵖ' sy₁ syⁱ λ ()
        ;   (_ , _ , op _ syᵇ (== {bool})) → fun-⇒ᵖ' sy₂ syᵇ λ ()}
... | == | bool | bool  = yes $ _ , _ , op sy₁ sy₂ ==
dec-⇒ᵖ Δ (¬ r)
    with dec-⇒ᵖ Δ r
... | no ∄sy = no $ λ {(_ , _ , neg sy) → ∄sy $ _ , _ , sy}
... | yes (int , _ , syⁱ) = no λ {(_ , _ , neg syᵇ) → fun-⇒ᵖ' syⁱ syᵇ λ ()}
... | yes (bool , _ , sy) = yes $ _ , _ , neg sy
dec-⇒ᵖ Δ (if r then r₁ else r₂)
    with dec-⇒ᵖ Δ r
... | no ∄sy = no $ λ {(_ , _ , if sy _ _) → ∄sy $ _ , _ , sy}
... | yes (int , _ , syⁱ) = no λ { (_ , _ , if syᵇ _ _) → fun-⇒ᵖ' syⁱ syᵇ λ ()}
... | yes (bool , _ , sy)
    with dec-⇒ᵖ Δ r₁ | dec-⇒ᵖ Δ r₂
... | no ∄sy₁ | _ = no λ {(_ , _ , if _ sy₁ _) → ∄sy₁ $ _ , _ , sy₁}
... | _ | no ∄sy₂ = no λ {(_ , _ , if _ _ sy₂) → ∄sy₂ $ _ , _ , sy₂}
... | yes (t₁ , p₁ , sy₁) | yes (t₂ , p₂ , sy₂)
    with t₁ | t₂
... | int  | int  = yes $ _ , _ , if sy sy₁ sy₂
... | int  | bool = no λ
        {   (int  , _ , if _ _ syⁱ) → fun-⇒ᵖ' sy₂ syⁱ λ ()
        ;   (bool , _ , if _ syᵇ _) → fun-⇒ᵖ' sy₁ syᵇ λ ()}
... | bool | int  = no λ
        {   (int  , _ , if _ syⁱ _) → fun-⇒ᵖ' sy₁ syⁱ λ ()
        ;   (bool , _ , if _ _ syᵇ) → fun-⇒ᵖ' sy₂ syᵇ λ ()}
... | bool | bool = yes $ _ , _ , if sy sy₁ sy₂


dec-⇒ᵛᶜ : ∀ Δ c → Dec (Σ _ (Δ ⊢ c ⇒ᵛᶜ_))
dec-⇒ᵛᶜ Δ (pred r)
    with dec-⇒ᵖ Δ r
... | no ∄sy = no λ{(_ , pred sy) → ∄sy $ _ , _ , sy}
... | yes (int , _ , syⁱ) = no λ {(_ , pred syᵇ) → fun-⇒ᵖ' syⁱ syᵇ λ ()}
... | yes (bool , _ , sy) = yes $ _ , pred sy
dec-⇒ᵛᶜ Δ (∀∀ x ⦂ t ∙ c) = map′ (λ{(_ , sy) → _ , quant sy}) (λ{(_ , quant sy) → _ , sy}) (dec-⇒ᵛᶜ (x ⦂ t ∷ Δ) c)
dec-⇒ᵛᶜ Δ (p ⇒ c)
    with dec-⇒ᵖ Δ p
... | no ∄sy = no λ{(_ , impl sy _) → ∄sy $ _ , _ , sy}
... | yes (int , _ , syⁱ) = no λ {(_ , impl syᵇ _) → fun-⇒ᵖ' syⁱ syᵇ λ ()}
... | yes (bool , _ , syᵖ) = map′ (λ{(_ , syᶜ) → _ , impl syᵖ syᶜ}) (λ{(_ , impl _ syᶜ) → _ , syᶜ}) (dec-⇒ᵛᶜ Δ c)

dec-⊢ : (Γ : Context) → (c : Untyped-Constraint) → Dec (Γ ⊢ c)
dec-⊢ [] c
    with dec-⇒ᵛᶜ [] c
... | no ∄sy = no λ{(ent-emp sy _) → ∄sy $ _ , sy}
... | yes (c' , syᶜ)
    with does (smt c') in spl
... | 𝔹.false = no λ{(ent-emp syᶜ' ¬valid[c']) → true≢false $
        ¬valid[c'] flipped then (spl
            ∵ fun-⇒ᵛᶜ syᶜ syᶜ'
            under λ c' → does (smt c') ≡ 𝔹.false)}
... | 𝔹.true = yes $ ent-emp syᶜ spl
dec-⊢ ((x ⦂ b ⟨ y ∣ p ⟩) ∷ Γ) c = map′ ent-base (λ{(ent-base der) → der}) (dec-⊢ Γ (∀∀ x ⦂ b2p b ∙ ((p [ y := x ]ᵣ) ⇒ c)))
dec-⊢ (_ ⦂ (_ ⦂ _ →' _) ∷ Γ) c = map′ ent-fun (λ{(ent-fun ent) → ent}) (dec-⊢ Γ c)

-- ↓ "sub" adapted from fig 3.7
subty : ∀ Γ → (t1 t2 : Type) → Dec (Γ ⊢ t1 ≺: t2)
subty _ t1 t2 = go t1 t2 _ _ refl refl where
    -- Helpers for proving termination
    data Bt : Set where
        Leaf : Bt
        Branch : Bt → Bt → Bt

    inj-Branch : ∀ {x y x' y'} → (Branch x y ≡ Branch x' y') → (x ≡ x') × (y ≡ y')
    inj-Branch refl = refl , refl

    shape : Type → Bt
    shape (_ ⟨ _ ∣ _ ⟩) = Leaf
    shape (_ ⦂ s →' t) = Branch (shape s) (shape t)

    -- α-operations preserve shape
    ps : ∀ {t op} → shape (t [ op ]ₜ) ≡ shape t
    ps {_ ⟨ _ ∣ _ ⟩} {nop}      = refl
    ps {_ ⟨ _ ∣ _ ⟩} {_ := _}   = refl
    ps {_ ⟨ _ ∣ _ ⟩} {_ ←→ _}   = refl
    ps {_ ⦂ _ →' _} {nop}    = ps under Branch _
    ps {_ ⦂ _ →' _} {_ := _} = ps under Branch _
    ps {_ ⦂ _ →' _} {_ ←→ _} = ps under Branch _

    -- Main traversal function
    go : ∀ {Γ} → (t1 t2 : Type)
        → ∀ ~t1 ~t2
        → shape t1 ≡ ~t1
        → shape t2 ≡ ~t2
        → Dec (Γ ⊢ t1 ≺: t2)
    go (_ ⦂ _ →' _) (_ ⟨ _ ∣ _ ⟩) _ _ _ _ = no λ ()
    go (_ ⟨ _ ∣ _ ⟩) (_ ⦂ _ →' _) _ _ _ _ = no λ ()
    go {Γ} (b₁ ⟨ v₁ ∣ p₁ ⟩) (b₂ ⟨ v₂ ∣ p₂ ⟩) _ _ _ _
        with b₁ ≟-Base-Type b₂
    ... | no b₁≢b₂ = no λ{(sub-base _) → b₁≢b₂ refl}
    ... | yes! = map′ sub-base (λ{(sub-base der) → der})
                    (dec-⊢ Γ (∀∀ v₁ ⦂ b2p b₁ ∙ (p₁ ⇒ pred (p₂ [ v₂ := v₁ ]ᵣ))))
    go (x₁ ⦂ s₁ →' t₁) (x₂ ⦂ s₂ →' t₂) (Branch ~s₁ ~t₁) (Branch ~s₂ ~t₂) pf1 pf2
        with go s₂ s₁ ~s₂ ~s₁
                (fst (inj-Branch pf2)) (fst (inj-Branch pf1))
    ... | no ∄der = no λ {(sub-fun der _) → ∄der der}
    ... | yes der1
        with go (t₁ [ x₁ := x₂ ]ₜ) t₂ ~t₁ ~t₂
                (ps then snd (inj-Branch pf1)) (snd (inj-Branch pf2))
    ... | no ∄der = no λ {(sub-fun _ der) → ∄der der}
    ... | yes der2 = yes (sub-fun der1 der2)

dec-:ᵏ : ∀ Γ t → Dec (Σ Kind (Γ ⊢ t :ᵏ_))
dec-:ᵏ Γ (b ⟨ x ∣ r ⟩) = map′
    (λ {(_ , wf-r) → B , (wf-base wf-r)})
    (λ {(B , wf-base wf-r) → _ , wf-r})
    (dec-⇒ᵛᶜ _ (pred r))
dec-:ᵏ Γ (x ⦂ s →' t) = map′′
    (λ (_ , wf-s) (_ , wf-t) → * , wf-fun wf-s wf-t)
    (λ {(* , wf-fun wf-s wf-t) → (_ , wf-s) , (_ , wf-t)})
    (dec-:ᵏ Γ s) (dec-:ᵏ (x ⦂ s ∷ Γ) t)

-- ↓ Lemma: funtion types are not equal to base types
fun≠base : ∀{x s t b y r} → (x ⦂ s →' t) ≢ b ⟨ y ∣ r ⟩
fun≠base ()

-- ↓ Lemma: function type constructor is injective
inj-→'
    : ∀{s₁ x₁ t₁ s₂ x₂ t₂}
    → (x₁ ⦂ s₁ →' t₁) ≡ (x₂ ⦂ s₂ →' t₂)
    → (x₁ ≡ x₂) × (s₁ ≡ s₂) × (t₁ ≡ t₂)
inj-→' refl = refl , refl , refl

-- ↓ "synth" and "check" adapted from figs 3.8, 3.9
synth : ∀ Γ e → Dec (Σ Type (Γ ⊢ e ⇒ᵗ_))
check : ∀ Γ e t → Dec (Γ ⊢ e ⇐ᵗ t)

-- ↓ Special case needed for termination checking
check-var : ∀ Γ x t → Dec (Γ ⊢ var x ⇐ᵗ t)

synth Γ (con x) = yes (prim x , syn-con refl)
synth Γ (var x)
    with lookup x Γ in c
... | no _ = no λ {(_ , syn-var c') → no≢yes $ c flipped then c'}
... | yes (t , _) = yes (t , syn-var c)
synth Γ (e [ x ]) = do
    yes (y ⦂ s →' t , e⇒s→t) ← synth Γ e where
        no ∄d → no λ {(_ , syn-app d _) → ∄d (_ , d)}
        yes (_ ⟨ _ ∣ _ ⟩ , sy) → no λ {(_ , syn-app sy' _) → fun≠base (fun-⇒ sy' sy)}
    yes var[x]⇐s ← check-var Γ x s where
            no var[x]⇍s → no λ { (_ , syn-app e⇒s'→t' var[x]⇐s')
                        → var[x]⇍s (var[x]⇐s' ∵ (fst $ snd $ inj-→' $ fun-⇒ e⇒s'→t' e⇒s→t)
                        under (Γ ⊢ var x ⇐ᵗ_))}
    yes $ _ , syn-app e⇒s→t var[x]⇐s
synth Γ (e ⦂ t) = map′′
    (λ (_ , wf) ch → t , (syn-ann wf ch))
    (λ {(_ , syn-ann wf ch) → (_ , wf) , ch})
    (dec-:ᵏ Γ t)
    (check Γ e t)
synth Γ (lett x := e inn e') = no λ () -- these cases are "check"ed , not "synth"ed
synth Γ (λλ x ∙ e) = no λ ()

-- ↓ Binder cases are varied in how they glue together the recursive calls
check Γ (λλ x ∙ e) (_ ⟨ _ ∣ _ ⟩) = no λ {(chk-syn () _)}
check Γ (λλ x ∙ e) (y ⦂ s →' t) = map′′
    (λ {refl d → chk-lam d})
    (λ {(chk-lam d) → refl , d})
    (x 𝕊.≟ y) (check (x ⦂ s ∷ Γ) e t)
check Γ (e ⦂ t') t = map′′d
    (λ {(_ , sy) su → chk-syn sy su})
    (λ {(chk-syn sy su) → (_ , sy) , λ {(_ , sy') → su ∵ fun-⇒ sy sy' under (Γ ⊢_≺: t )}})
    (synth Γ (e ⦂ t'))
    λ {(t' , _) → subty Γ t' t}
check Γ (lett x := e₁ inn e₂) t₂ = map′′d
    (λ {(_ , sy) ch → chk-let sy ch})
    (λ {(chk-let sy ch) → (_ , sy) , λ {(_ , sy') → ch ∵ fun-⇒ sy sy' under (_ ⦂_) under (_∷ Γ) under (_⊢ e₂ ⇐ᵗ t₂)}})
    (synth Γ e₁)
    λ {(t₁ , sy) → check (x ⦂ t₁ ∷ Γ) e₂ t₂}

-- ↓ Otherwise, non-binder cases are all identical
-- (call synth, call subtyping)
check Γ e@(con _) t = do
    yes (t' , e⇒t') ← synth Γ e
        where no ∄t,sy → no λ{(chk-syn sy _) → ∄t,sy $ _ , sy}
    yes t'≺:t ← subty Γ t' t
        where no t'⊀:t → no λ{(chk-syn e⇒s s≺:t) → t'⊀:t $ s≺:t ∵ fun-⇒ e⇒s e⇒t' under (Γ ⊢_≺: t)}
    yes (chk-syn e⇒t' t'≺:t)
check Γ e@(_ [ _ ]) t = do
    yes (t' , e⇒t') ← synth Γ e
        where no ∄t,sy → no λ{(chk-syn sy _) → ∄t,sy $ _ , sy}
    yes t'≺:t ← subty Γ t' t
        where no t'⊀:t → no λ{(chk-syn e⇒s s≺:t) → t'⊀:t $ s≺:t ∵ fun-⇒ e⇒s e⇒t' under (Γ ⊢_≺: t)}
    yes (chk-syn e⇒t' t'≺:t)
-- ↓ Variable case singled out (for use in application etc.), but otherwise the same
check Γ (var x) t = check-var Γ x t
check-var Γ x t = let e = var x in do
    yes (t' , e⇒t') ← synth Γ e
        where no ∄t,sy → no λ{(chk-syn sy _) → ∄t,sy $ _ , sy}
    yes t'≺:t ← subty Γ t' t
        where no t'⊀:t → no λ{(chk-syn e⇒s s≺:t) → t'⊀:t $ s≺:t ∵ fun-⇒ e⇒s e⇒t' under (Γ ⊢_≺: t)}
    yes (chk-syn e⇒t' t'≺:t)
 