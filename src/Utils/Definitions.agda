module Utils.Definitions where

open import Level
open import Relation.Binary renaming (Rel to BinRel)

-- arbitray intersection
⋂ᵣ : ∀ {i ρ s a} {A : Set a} (I : Set i) → (I → BinRel A ρ) → BinRel A (ρ ⊔ i ⊔ s)
⋂ᵣ {j} {ρ} {s} I R = λ x y → (i : I) → Lift (ρ ⊔ j ⊔ s) (R i x y)
