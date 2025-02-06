module Utils.Axioms where
-- standard library imports
open import Level
open import Relation.Nullary using (¬_)
open import Data.Product using (Σ; Σ-syntax ; _,_ ; proj₁ ; proj₂)

-- Absurd pattern for proofs by contradiction
postulate
  absurd : ∀ {ℓ} (P : Set ℓ) → ¬ (¬ P) → P

-- postulating axioms of negation and quantifiers
¬∀→∃¬ : ∀ {a b} {A : Set a} {B : A → Set b}
      → ¬ (∀ (x : A) → B x)
      → Σ[ x ∈ A ] ¬ (B x)
¬∀→∃¬ {a} {b} {A} {B} ¬∀ =
  absurd
    (Σ[ x ∈ A ] ¬ (B x))
    λ ¬∃x → ¬∀ λ x → absurd (B x) λ ¬Bx → ¬∃x (x , ¬Bx) 
