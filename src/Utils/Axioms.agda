module Utils.Axioms where
-- standard library imports
open import Relation.Nullary using (¬_)
open import Data.Product using (Σ; Σ-syntax)

-- Absurd pattern for proofs by contradiction
postulate
  absurd : ∀ {ℓ} (P : Set ℓ) → ¬ (¬ P) → P

-- postulating axioms of negation and quantifiers
postulate
  ¬∀→∃¬ : ∀ {a b} {A : Set a} {B : A → Set b} → ¬ (∀ (x : A) → (B x)) → Σ[ x ∈ A ] ¬ (B x)
  ∃¬→¬∀ : ∀ {a b} {A : Set a} {B : A → Set b} → Σ[ x ∈ A ] ¬ (B x) → ¬ (∀ (x : A) → (B x))
  ¬∃→∀¬ : ∀ {a b} {A : Set a} {B : A → Set b} → ¬ (Σ[ x ∈ A ]  (B x)) → ∀ (x : A) → ¬ (B x)

