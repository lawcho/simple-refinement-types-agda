-- ↓ Re-exports from standard library

module Util.Stdlib where

-- Basic Data types

module 𝕊 where
  open import Data.String public
𝕊 = 𝕊.String

module ℕ where
  open import Data.Nat public
  open ℕ public
ℕ = ℕ.ℕ

module ℤ where
  open import Data.Integer hiding (pos) public
  open import Data.Integer.Properties public
  open ℤ public
ℤ = ℤ.ℤ

module 𝔹 where
  open import Data.Bool.Properties public
  open import Data.Bool public
  open Bool public
𝔹 = 𝔹.Bool

open import
    Data.Unit
    using (⊤)
    public
open import
    Data.Empty
    using (⊥)
    public

-- Container Data Types

open import
    Data.Sum
    using (_⊎_)
    renaming (inj₁ to inl; inj₂ to inr)
    public
open import
    Data.Product
    using (_×_ ; Σ ; _,_)
    renaming (proj₁ to fst; proj₂ to snd)
    public
open import
    Data.Maybe
    using (Maybe; just; nothing)
    public
-- Lists & variants
open import
    Data.List
    using (List;[];_∷_;map)
    public
open import
    Data.List.Relation.Unary.All
    using (All;[];_∷_)
    public
open import Data.List.Relation.Unary.Any
    using (Any; here; there)
    public

-- Proof-related

open import
    Relation.Binary.PropositionalEquality
    using (_≡_;refl)
    public
open import
    Relation.Nullary
    using (Dec;does;proof;yes;no;ofʸ;ofⁿ;_because_)
    renaming (¬_ to ¬'_)
    public
open import
    Relation.Nullary.Reflects
    using (invert)
    public
open import
    Relation.Nullary.Decidable
    using (map′)
    public
open import
    Relation.Unary
    using (Decidable)
    public
open import
    Relation.Binary
    using (DecidableEquality)
    public
open import
    Function.Base
    using (id;_$_)
    public
