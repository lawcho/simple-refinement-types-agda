-- (Incomplete) Decision procedure for VC Validity.
-- Decides just enough theory to run the examples (gets stuck on the rest)
module Common.Example-Solver where

open import Util.All

open import Common.SMT-API

open import Common.VC-Syntax.Type
open import Common.VC-Syntax.Predicate renaming (∧ to ∧')
open import Common.VC-Syntax.Constraint

open import Common.VC-Semantics.Type
open import Common.VC-Semantics.Predicate
open import Common.VC-Semantics.Constraint

-- Architecture:
--
--  (input : VC)
--      ↓               [pre-processor]
--  (Equi-True input)
--      ↓               [look-up table]
--  (output : Maybe (Dec (Valid input)))


-- Infrastruture
----------------

open Bi-Impl

-- Glorified Σ types
record Equi-Trueᶜ {Δ} (c : Constraint Δ) : Set₁ where
    constructor ETᶜ
    field c' : Constraint Δ
    field pf : ∀ ρ → go ρ c ↔ go ρ c'

record Equi-Trueᵖ {Δ} {τ} (p : Predicate Δ τ) : Set₁ where
    constructor ETᵖ
    field p' : Predicate Δ τ
    field pf : ∀ ρ v → (ρ ⊢ p ⇓ v) ↔ (ρ ⊢ p' ⇓ v)

-- Helper theorem: the predicate semantics are (at least partial-) functional
pfun-⇓ : ∀ {Δ ρ τ} (p : Predicate Δ τ) → Σ ⟦ τ ⟧ₜ (ρ ⊢ p ⇓_)
pfun-⇓ (var _) = _ , ⇓var refl
pfun-⇓ true = _ , ⇓true
pfun-⇓ false = _ , ⇓false
pfun-⇓ (num _) = _ , ⇓num
pfun-⇓ (¬ p)
  with _ , r ← pfun-⇓ p
  = _ , ⇓¬ r refl
pfun-⇓ (p₁ ▹ x ◃ p₂)
  with _ , r₁ ← pfun-⇓ p₁
  with _ , r₂ ← pfun-⇓ p₂
  = _ , ⇓op r₁ r₂ refl
pfun-⇓ (if p₁ then p₂ else p₃)
  with _ , r₁ ← pfun-⇓ p₁
  with _ , r₂ ← pfun-⇓ p₂
  with _ , r₃ ← pfun-⇓ p₃
  = _ , ⇓if r₁ r₂ r₃ refl

-- Helper theroem: false never reduced to true, or vice versa
¬f⇓t : ∀ {Γ} {Δ : All ⟦_⟧ₜ Γ} → ¬' (Δ ⊢ false ⇓ 𝔹.true)
¬f⇓t ()

default-val : (t : Type) → ⟦ t ⟧ₜ
default-val int = 0
default-val bool = 𝔹.true

-- Preprocessor
---------------

-- "Shallow" simplification passes for predicates & constraints
module Shallow-Transforms where

    open import Function.Base using (const)

    -- Remove "true" constants in identity positions
    simp-c : ∀ {Δ} → (c : Constraint Δ) → Equi-Trueᶜ c
    simp-c (true ⇒ c)       = ETᶜ c λ _ → Bi (_$ ⇓true) const
    simp-c (pred true ∧ c)  = ETᶜ c λ _ → Bi Σ.proj₂ (⇓true ,_)
    simp-c (c ∧ pred true)  = ETᶜ c λ _ → Bi Σ.proj₁ (_, ⇓true)
    -- Propagate up "true"/"false" constants in annihilating positions
    simp-c (false ⇒ _)      = ETᶜ (pred true) λ _ → Bi (const ⇓true) λ _ ()
    simp-c (_ ⇒ pred true)  = ETᶜ (pred true) λ _ → Bi (const ⇓true) (const (const ⇓true))
    simp-c (pred false ∧ _) = ETᶜ (pred false) λ _ → Bi Σ.proj₁ λ ()
    simp-c (_ ∧ pred false) = ETᶜ (pred false) λ _ → Bi Σ.proj₂ λ ()
    simp-c (∀∀ t ∙ pred true)   = ETᶜ (pred true) λ _ → Bi (const ⇓true) (const λ _ → ⇓true)
    simp-c (∀∀ t ∙ pred false)  = ETᶜ (pred false) λ _ → Bi (λ k → explode (¬f⇓t (k (default-val t)))) λ ()
    -- Leave others unchanged
    simp-c c = ETᶜ c λ _ → id-↔

    simp-p : ∀ {Δ τ} → (c : Predicate Δ τ) → Equi-Trueᵖ c
    simp-p (p₁ ▹ > ◃  p₂) = ETᵖ (p₂ ▹ < ◃ p₁) λ _ _ → Bi
                              (λ {(⇓op x₁ x₂ eq) → ⇓op x₂ x₁ eq})
                              (λ {(⇓op x₁ x₂ eq) → ⇓op x₂ x₁ eq})
    simp-p (true ▹ ∧' ◃ p)  = ETᵖ p λ _ _ → Bi (λ{(⇓op ⇓true d refl) → d})  λ d  → ⇓op ⇓true d refl
    simp-p (false ▹ ∨ ◃  p) = ETᵖ p λ _ _ → Bi (λ{(⇓op ⇓false d refl) → d})  λ d  → ⇓op ⇓false d refl
    simp-p (p ▹ ∧' ◃ true)  = ETᵖ p λ _ _ → Bi (λ{(⇓op d ⇓true refl) → d ∵ (𝔹.∧-identityʳ _ flipped) under (_ ⊢ p ⇓_)}) λ d → ⇓op d ⇓true (𝔹.∧-identityʳ _ flipped)
    simp-p (p ▹ ∨ ◃  false) = ETᵖ p λ _ _ → Bi (λ{(⇓op d ⇓false refl) → d ∵ (𝔹.∨-identityʳ _ flipped) under (_ ⊢ p ⇓_)}) λ d → ⇓op d ⇓false (𝔹.∨-identityʳ _ flipped)
    simp-p (false ▹ ∧' ◃ p) = ETᵖ false λ _ _ → Bi (λ{(⇓op ⇓false d refl) → ⇓false}) λ{⇓false → ⇓op ⇓false (Σ.proj₂ $ pfun-⇓ p) refl}
    simp-p (true ▹ ∨ ◃  p)  = ETᵖ true  λ _ _ → Bi (λ{(⇓op ⇓true d refl) → ⇓true}) λ{⇓true → ⇓op ⇓true (Σ.proj₂ $ pfun-⇓ p) refl}
    simp-p (p ▹ ∧' ◃ false) = ETᵖ false λ ρ _ → Bi (λ{(⇓op d ⇓false refl) → ⇓false ∵ 𝔹.∧-zeroʳ _ flipped under (_ ⊢ _ ⇓_)}) λ{⇓false → ⇓op (Σ.proj₂ $ pfun-⇓ p) ⇓false (𝔹.∧-zeroʳ (Σ.proj₁ $ pfun-⇓ {ρ = ρ} p) flipped)}
    simp-p (p ▹ ∨ ◃  true)  = ETᵖ true λ ρ _ → Bi (λ{(⇓op d ⇓true refl) → ⇓true ∵ 𝔹.∨-zeroʳ _ flipped under (_ ⊢ _ ⇓_)}) λ{⇓true → ⇓op (Σ.proj₂ $ pfun-⇓ p) ⇓true (𝔹.∨-zeroʳ (Σ.proj₁ $ pfun-⇓ {ρ = ρ} p) flipped)}
    simp-p (¬ true)  = ETᵖ false λ _ _ → Bi (λ{(⇓¬ ⇓true refl) → ⇓false}) λ {⇓false → ⇓¬ ⇓true refl}
    simp-p (¬ false) = ETᵖ true  λ _ _ → Bi (λ{(⇓¬ ⇓false refl) → ⇓true}) λ {⇓true → ⇓¬ ⇓false refl}
    simp-p (if true  then p else q) = ETᵖ p λ _ _ → Bi (λ {(⇓if ⇓true d _ refl) → d}) λ d → ⇓if ⇓true d (Σ.proj₂ $ pfun-⇓ q) refl
    simp-p (if false then q else p) = ETᵖ p λ _ _ → Bi (λ {(⇓if ⇓false _ d refl) → d}) λ d → ⇓if ⇓false (Σ.proj₂ $ pfun-⇓ q) d refl
    simp-p p = ETᵖ p λ _ _ → id-↔

-- Boolean lemmas
flip-not : ∀ {p q} → p ≡ 𝔹.not q → q ≡ 𝔹.not p
flip-not {𝔹.false} {𝔹.true}  refl = refl
flip-not {𝔹.true}  {𝔹.false} refl = refl

dne : ∀ {p} → p ≡ 𝔹.not (𝔹.not p)
dne {𝔹.false} = refl
dne {𝔹.true} = refl

↔-¬ : ∀ {Δ ρ v} → {p : Predicate Δ bool} → (ρ ⊢ (¬ p) ⇓ v) ↔ (ρ ⊢ p ⇓ 𝔹.not v)
↔-¬ .fwd (⇓¬ d x) = d ∵ flip-not x under (_ ⊢ _ ⇓_)
↔-¬ .bck d = ⇓¬ d dne

↔-flip : {ℓa ℓb : _}{A : Set ℓa}{B : Set ℓb} → A ↔ B → B ↔ A
↔-flip bi .fwd = bck bi
↔-flip bi .bck = fwd bi

-- Bottom-up simplification passes
module Deep-Transforms where

    module S = Shallow-Transforms

    simp-p : ∀ {Δ τ} → (p : Predicate Δ τ) → Equi-Trueᵖ p
    simp-p (¬ p)
      with ETᵖ p'  pf₁ ← simp-p p
      with ETᵖ p'' pf₂ ← S.simp-p (¬ p')
         = ETᵖ p'' λ ρ v
         → ↔-¬ ∘∘ pf₁ ρ _ ∘∘  ↔-flip ↔-¬ ∘∘ pf₂ ρ v
    simp-p (p₁ ▹ x ◃ p₂)
      with ETᵖ p₁' pf₁ ← simp-p p₁
      with ETᵖ p₂' pf₂ ← simp-p p₂
      with ETᵖ p' pf ← S.simp-p (p₁' ▹ x ◃ p₂')
         = ETᵖ p' λ ρ v
         → Bi
           (λ{(⇓op r₁ r₂ q) → ⇓op (fwd (pf₁ ρ _) r₁) (fwd (pf₂ ρ _) r₂) q})
           (λ{(⇓op r₁ r₂ q) → ⇓op (bck (pf₁ ρ _) r₁) (bck (pf₂ ρ _) r₂) q})
         ∘∘ pf ρ v
    simp-p (if p₁ then p₂ else p₃)
      with ETᵖ p₁' pf₁ ← simp-p p₁
      with ETᵖ p₂' pf₂ ← simp-p p₂
      with ETᵖ p₃' pf₃ ← simp-p p₃
      with ETᵖ p' pf ← S.simp-p (if p₁' then p₂' else p₃')
         = ETᵖ p' λ ρ v
         → Bi
           (λ{(⇓if r₁ r₂ r₃ q) → ⇓if (fwd (pf₁ ρ _) r₁) (fwd (pf₂ ρ _) r₂) (fwd (pf₃ ρ _) r₃) q})
           (λ{(⇓if r₁ r₂ r₃ q) → ⇓if (bck (pf₁ ρ _) r₁) (bck (pf₂ ρ _) r₂) (bck (pf₃ ρ _) r₃) q})
         ∘∘ pf ρ v
    simp-p = S.simp-p

    simp-c : ∀ {Δ} → (c : Constraint Δ) → Equi-Trueᶜ c
    simp-c (pred p₁)
      with ETᵖ p₁' pf₁ ← simp-p p₁
      with ETᶜ c' pf ← S.simp-c (pred p₁')
         = ETᶜ c' λ ρ
         →  pf₁ ρ 𝔹.true
         ∘∘ pf ρ
    simp-c (c₁ ∧ c₂)
      with ETᶜ c₁' pf₁ ← simp-c c₁
      with ETᶜ c₂' pf₂ ← simp-c c₂
      with ETᶜ c' pf ← S.simp-c (c₁' ∧ c₂')
         = ETᶜ c' λ ρ
         →  Bi
            (λ{(d₁ , d₂) → fwd (pf₁ ρ) d₁ , fwd (pf₂ ρ) d₂})
            (λ{(d₁ , d₂) → bck (pf₁ ρ) d₁ , bck (pf₂ ρ) d₂})
         ∘∘ pf ρ
    simp-c (∀∀ t ∙ c₁)
      with ETᶜ c₁' pf₁ ← simp-c c₁
      with ETᶜ c' pf ← S.simp-c (∀∀ t ∙ c₁')
         = ETᶜ c' λ ρ
         → Bi
           (λ f v → fwd (pf₁ _) (f v))
           (λ f v → bck (pf₁ _) (f v))
         ∘∘ pf ρ
    simp-c (p₁ ⇒ c₂)
      with ETᵖ p₁' pf₁ ← simp-p p₁
      with ETᶜ c₂' pf₂ ← simp-c c₂
      with ETᶜ c' pf ← S.simp-c (p₁' ⇒ c₂')
         = ETᶜ c' λ ρ
         → Bi
           (λ f → fwd (pf₂ ρ) ∘ f ∘ bck (pf₁ ρ 𝔹.true))
           (λ f → bck (pf₂ ρ) ∘ f ∘ fwd (pf₁ ρ 𝔹.true))
         ∘∘ pf ρ
module D = Deep-Transforms


-- Wrap a Solver in a pre-processor that simplifies its input
_with-preprocessor_ : Solver → ((vc : VC) → Equi-Trueᶜ vc) → Solver
(solve with-preprocessor pp) c =
  let ETᶜ c' pf = pp c
  in map′ (bck $ pf []) (fwd $ pf []) (solve c')

-- Look-up table
----------------

-- Helpers for manipulating values of "true ≡ ..." and "false ≡ ..." type

from-ted : ∀{ℓp}{P : Set ℓp}(P? : Dec P) → 𝔹.true ≡ does P? → P
from-ted (yes p) refl = p

from-fed : ∀{ℓp}{P : Set ℓp}(P? : Dec P) → 𝔹.false ≡ does P? → ¬' P
from-fed (no dp) refl = dp

to-ted : ∀{ℓp}{P : Set ℓp}(P? : Dec P) → P → 𝔹.true ≡ does P?
to-ted (yes _) _ = refl
to-ted (no ¬p) p = explode $ ¬p p

split-te∨ : ∀ b₁ b₂ → 𝔹.true ≡ b₁ 𝔹.∨ b₂ → (𝔹.true ≡ b₁) ⊎ (𝔹.true ≡ b₂)
split-te∨ 𝔹.true _ _ = inl refl
split-te∨ _ 𝔹.true _ = inr refl

split-fe∨ : ∀ b₁ b₂ → 𝔹.false ≡ b₁ 𝔹.∨ b₂ → (𝔹.false ≡ b₁) × (𝔹.false ≡ b₂)
split-fe∨ 𝔹.false 𝔹.false _ = refl , refl

-- Integer arithmetic lemmas
0≤x⇒-1<x : ∀ {x} → 0 ℤ.≤ x → -1 ℤ.< x
0≤x⇒-1<x (ℤ.+≤+ _) = ℤ.-<+

-1<x⇒0≤x : ∀ {x} → -1 ℤ.< x → 0 ℤ.≤ x
-1<x⇒0≤x ℤ.-<+ = ℤ.+≤+ ℕ.z≤n

0≮x⇒-1<-x : ∀{x} → 0 ℤ.≮ x → -1 ℤ.< 0 ℤ.- x
0≮x⇒-1<-x {ℤ.pos (ℕ.suc n)} dp = explode (dp (ℤ.+<+ (ℕ.s≤s ℕ.z≤n)))
0≮x⇒-1<-x {ℤ.pos ℕ.zero} _ = ℤ.-<+
0≮x⇒-1<-x {ℤ.negsuc n} _ = ℤ.-<+

z-z=0 : ∀{z} → z ℤ.- z ≡ 0
z-z=0 {z} = ℤ.i≡j⇒i-j≡0 {z} {z} refl

x<y⇒0<y-x : ∀{x} {y} → x ℤ.< y → 0 ℤ.< y ℤ.- x
x<y⇒0<y-x {x} {y} x<y = ℤ.+-mono-<-≤ x<y (ℤ.≤-reflexive {ℤ.- x} refl)
  ∵ (z-z=0 {x}) and refl under ℤ._<_

x<y⇒-1<y-x : ∀{x} {y} → x ℤ.< y → -1 ℤ.< y ℤ.- x
x<y⇒-1<y-x x<y = ℤ.<-trans ℤ.-<+ (x<y⇒0<y-x x<y)

open import Relation.Binary.Definitions using (module Tri)

x≮y∧x≠y⇒y<x : ∀{x}{y} → x ℤ.≮ y → x ≢ y → y ℤ.< x
x≮y∧x≠y⇒y<x {x} {y} x≮y x≠y
  with ℤ.<-cmp x y
... | Tri.tri< x<y _ _ with () ← x≮y x<y
... | Tri.tri≈ _ x=y _ with () ← x≠y x=y
... | Tri.tri> _ _ y<x = y<x

open Do-id

solver' : Solver

-- Trivial theory
solver' (pred true) = yes ⇓true

-- More tricky theory involving arithmetic
solver'    -- natural number constants are > -1
  (∀∀ int ∙ var ↑0 ▹ == ◃ num (ℤ.pos n) ⇒
      pred (num (ℤ.negsuc 0) ▹ < ◃ var ↑0))
    = yes $ λ {
        z₁ (⇓op (⇓var refl) ⇓num o)
    → do
      refl ← from-ted (z₁ ℤ.≟ _) o
      ⇓op ⇓num (⇓var refl) refl
    }
solver'    -- addition of int variables > -1 to natural number constants gives ints > -1
    (∀∀ int ∙ num (ℤ.negsuc 0) ▹ < ◃ var ↑0 ⇒
        (∀∀ int ∙ var ↑0 ▹ == ◃ num (ℤ.pos _) ⇒
            (∀∀ int ∙ var ↑0 ▹ == ◃ (var ↑2 ▹ + ◃ var ↑1)
                ⇒ pred (num (ℤ.negsuc 0) ▹ < ◃ var ↑0))))
    = yes $ λ {
        z₁ (⇓op ⇓num (⇓var refl) o₁)
          z₂ (⇓op (⇓var refl) (⇓num {z}) o₂)
            z₃ (⇓op (⇓var refl) (⇓op (⇓var refl) (⇓var refl) refl) o₄)
    → do
      0≤z₁ ← -1<x⇒0≤x $ from-ted (-1 ℤ.<? z₁) o₁
      refl ← from-ted (z₂ ℤ.≟ z) o₂
      refl ← from-ted (z₃ ℤ.≟ (z₁ ℤ.+ z₂)) o₄
      ⇓op ⇓num (⇓var refl) (to-ted
        (-1 ℤ.<? z₁ ℤ.+ z)
        let open ℤ.≤-Reasoning in
          0≤x⇒-1<x $ begin
            0
              ≤⟨ 0≤z₁ ⟩
            z₁
              ≤⟨ ℤ.i≤i+j z₁ z₂ ⟩
            z₁ ℤ.+ z
              ∎
        )
    }
solver'    -- addition of int variables < 0 to positive constants *does not* always give ints < 0
    (∀∀ int ∙ var ↑0 ▹ < ◃ num (ℤ.pos 0) ⇒
        (∀∀ int ∙ var ↑0 ▹ == ◃ num (ℤ.pos (ℕ.suc n)) ⇒
            (∀∀ int ∙ var ↑0 ▹ == ◃ (var ↑2 ▹ + ◃ var ↑1)
                ⇒ pred (var ↑0 ▹ < ◃ num (ℤ.pos 0)))))
    = no $ λ der →
      let psn = ℤ.pos (ℕ.suc n) in do
      ⇓op (⇓var refl) ⇓num ted[n<0] ← der
        -1 (⇓op (⇓var refl) ⇓num refl)
           psn (⇓op (⇓var refl) ⇓num (to-ted (psn ℤ.≟ psn) refl))
             (psn ℤ.+ -1) (⇓op (⇓var refl) (⇓op (⇓var refl) (⇓var refl) refl) (to-ted (n ℕ.≟ n) refl))
      () ← from-ted (n ℕ.<? 0) ted[n<0]
solver'
  (∀∀ int ∙ (var ↑0 ▹ == ◃ num (ℤ.pos 0)) ⇒
    ∀∀ int ∙ ∀∀ bool ∙
        (var ↑0 ▹ == ◃
        ((var ↑2 ▹ < ◃ var ↑1) ▹ ∨ ◃ (var ↑2 ▹ == ◃ var ↑1)))
      ⇒
      (var ↑0 ▹ == ◃ true) ⇒
          ∀∀ int ∙ (var ↑2 ▹ == ◃ var ↑0) ⇒
            pred (num (ℤ.negsuc 0) ▹ < ◃ var ↑0))
  = yes $ λ{
      (ℤ.pos 0) (⇓op (⇓var refl) ⇓num refl)
        z₁ b₁
          (⇓op {v₂ = b₂} (⇓var refl)
          (⇓op (⇓op (⇓var refl) (⇓var refl) refl) (⇓op (⇓var refl) (⇓var refl) refl) o₁) ted[b₁=b₂])
        (⇓op (⇓var refl) ⇓true ted[b₁=true])
         z₂ (⇓op (⇓var refl) (⇓var refl) ted[z₁=z₂])
    → ⇓op ⇓num (⇓var refl) $ do
      refl ← from-ted (b₁ 𝔹.≟ b₂) ted[b₁=b₂]
      refl ← from-ted (b₁ 𝔹.≟ 𝔹.true) ted[b₁=true]
      refl ← from-ted (z₁ ℤ.≟ z₂) ted[z₁=z₂]
      inl ted[0<z₁] ← split-te∨ (does (0 ℤ.<? z₁)) (does (0 ℤ.≟ z₁)) o₁ where
        inr ted[0=z₁] → do
          refl ← from-ted (0 ℤ.≟ z₁) ted[0=z₁]
          refl
      0<z₁ ← from-ted (0 ℤ.<? z₁) ted[0<z₁]
      to-ted (-1 ℤ.<? z₁) (ℤ.<-trans ℤ.-<+ 0<z₁)
  }
solver'
  (∀∀ int ∙ (var ↑0 ▹ == ◃ num (ℤ.pos 0)) ⇒
    ∀∀ int ∙ ∀∀ bool ∙
        (var ↑0 ▹ == ◃
        ((var ↑2 ▹ < ◃ var ↑1) ▹ ∨ ◃ (var ↑2 ▹ == ◃ var ↑1)))
      ⇒
        (var ↑0 ▹ == ◃ false) ⇒
          ∀∀ int ∙ (var ↑0 ▹ == ◃ (var ↑3 ▹ - ◃ var ↑2)) ⇒
            pred (num (ℤ.negsuc 0) ▹ < ◃ var ↑0))
  = yes $ λ{
      (ℤ.pos 0) (⇓op (⇓var refl) ⇓num refl)
        z₁ b₁
          (⇓op {v₂ = b₂} (⇓var refl)
          (⇓op (⇓op (⇓var refl) (⇓var refl) refl) (⇓op (⇓var refl) (⇓var refl) refl) o₁) ted[b₁=b₂])
        (⇓op (⇓var refl) ⇓false ted[b₁=false])
          z₂ (⇓op (⇓var refl) (⇓op (⇓var refl) (⇓var refl) refl) ted[z₂=0-z₁])
    → ⇓op ⇓num (⇓var refl) $ do
      refl ← from-ted (b₁ 𝔹.≟ b₂) ted[b₁=b₂]
      refl ← from-ted (b₁ 𝔹.≟ 𝔹.false) ted[b₁=false]
      refl ← from-ted (z₂ ℤ.≟ (0 ℤ.- z₁)) ted[z₂=0-z₁]
      fed[0<z₁] , _ ← split-fe∨ (does (ℤ.pos ℕ.zero ℤ.<? z₁)) (does (ℤ.pos ℕ.zero ℤ.≟ z₁)) o₁
      0≮z₁ ← from-fed (0 ℤ.<? z₁) fed[0<z₁]
      to-ted (-1 ℤ.<? 0 ℤ.- z₁) (0≮x⇒-1<-x 0≮z₁)
  }
solver'
  (∀∀ int ∙ ∀∀ int ∙ ∀∀ bool ∙
    (var ↑0 ▹ == ◃ ((var ↑2 ▹ < ◃ var ↑1) ▹ ∨ ◃ (var ↑2 ▹ == ◃ var ↑1))) ⇒
      (var ↑0 ▹ == ◃ true) ⇒
        ∀∀ int ∙
          (var ↑0 ▹ == ◃ (var ↑2 ▹ - ◃ var ↑3)) ⇒
            pred (num (ℤ.negsuc 0) ▹ < ◃ var ↑0))
  = yes $ λ{
      z₁ z₂ b₁
        (⇓op (⇓var refl) (⇓op {v₁ = b₂} (⇓op (⇓var refl) (⇓var refl) p) (⇓op (⇓var refl) (⇓var refl) refl) refl) ted[b₁=b₂∨∙∙∙])
          (⇓op (⇓var refl) ⇓true ted[b₁=true])
            z₃ (⇓op (⇓var refl) (⇓op (⇓var refl) (⇓var refl) refl) ted[z₃=z₂-z₁])
      → ⇓op ⇓num (⇓var refl) $ do
        refl ← from-ted (b₁ 𝔹.≟ 𝔹.true) ted[b₁=true]
        refl ← from-ted (z₃ ℤ.≟ z₂ ℤ.- z₁) ted[z₃=z₂-z₁]
        to-ted (ℤ.negsuc ℕ.zero ℤ.<? z₂ ℤ.- z₁) $ do
          te[b₂∨∙∙∙] ← from-ted (b₁ 𝔹.≟ b₂ 𝔹.∨ does (z₁ ℤ.≟ z₂)) ted[b₁=b₂∨∙∙∙]
          inl refl ← split-te∨ b₂ (does (z₁ ℤ.≟ z₂)) te[b₂∨∙∙∙]
            where inr ted[z₁=z₂] → do
              refl ← from-ted (z₁ ℤ.≟ z₂) ted[z₁=z₂]
              q ← z-z=0 {z₁}
              ℤ.-<+ ∵ (q flipped) under (_ ℤ.<_)
          z₁<z₂ ← from-ted (z₁ ℤ.<? z₂) p
          x<y⇒-1<y-x z₁<z₂
  }
solver'
  (∀∀ int ∙ ∀∀ int ∙ ∀∀ bool ∙
    (var ↑0 ▹ == ◃ ((var ↑2 ▹ < ◃ var ↑1) ▹ ∨ ◃ (var ↑2 ▹ == ◃ var ↑1))) ⇒
      (var ↑0 ▹ == ◃ false) ⇒
          ∀∀ int ∙
            (var ↑0 ▹ == ◃ (var ↑3 ▹ - ◃ var ↑2)) ⇒
              pred (num (ℤ.negsuc 0) ▹ < ◃ var ↑0))
  = yes $ λ{
      z₁ z₂ b₁
        (⇓op (⇓var refl) (⇓op {v₁ = b₂} (⇓op (⇓var refl) (⇓var refl) p) (⇓op (⇓var refl) (⇓var refl) refl) refl) ted[b₁=b₂∨∙∙∙])
          (⇓op (⇓var refl) ⇓false ted[b₁=false])
            z₃ (⇓op (⇓var refl) (⇓op (⇓var refl) (⇓var refl) refl) ted[z₃=z₁-z₂])
      → ⇓op ⇓num (⇓var refl) $ do
        refl ← from-ted (b₁ 𝔹.≟ 𝔹.false) ted[b₁=false]
        refl ← from-ted (z₃ ℤ.≟ z₁ ℤ.- z₂) ted[z₃=z₁-z₂]
        to-ted (ℤ.negsuc ℕ.zero ℤ.<? z₁ ℤ.- z₂) $ do
          fe[b₂∨∙∙∙] ← from-ted (b₁ 𝔹.≟ b₂ 𝔹.∨ does (z₁ ℤ.≟ z₂)) ted[b₁=b₂∨∙∙∙]
          refl , fe[z₁=z₂] ← split-fe∨ b₂ (does (z₁ ℤ.≟ z₂)) fe[b₂∨∙∙∙]
          z₁≮z₂ ← from-fed (z₁ ℤ.<? z₂) p
          z₁≠z₂ ← from-fed (z₁ ℤ.≟ z₂) fe[z₁=z₂]
          x<y⇒-1<y-x (x≮y∧x≠y⇒y<x z₁≮z₂ z₁≠z₂)
  }
-- ↑ Cases above (& pre-processor) are crafted to avoid
-- case below ever being hit
solver' = stuck
  where postulate stuck : Solver

-- Connecting the parts together
--------------------------------
solver = solver' with-preprocessor D.simp-c
