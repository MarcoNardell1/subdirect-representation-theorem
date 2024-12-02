module Utils.Definitions where

open import Level
open import Data.Product
open import Function using (id)
open import Relation.Binary using (_⇔_ ; IsEquivalence) renaming (Rel to BinRel )

-- arbitray intersection
⋂ᵣ : ∀ {i ρ s a} {A : Set a} (I : Set i) → (I → BinRel A ρ) → BinRel A (ρ ⊔ i ⊔ s)
⋂ᵣ {j} {ρ} {s} I R = λ x y → (i : I) → Lift (ρ ⊔ j ⊔ s) (R i x y)

⇔isEq : ∀ {a ℓ} {A : Set a}→ IsEquivalence {A = BinRel A ℓ} _⇔_
⇔isEq = record { refl = id , id
                ; sym = λ x=y → proj₂ x=y , proj₁ x=y
                ; trans = λ x=y y=z → ( λ x → proj₁ y=z (proj₁ x=y x))
                                       , λ x → proj₂ x=y (proj₂ y=z x)
                }

⇔hetTrans : ∀ {a ℓ ℓ₁ ℓ₂} {A : Set a} {P : BinRel A ℓ} {Q : BinRel A ℓ₁} {R : BinRel A ℓ₂}
           → P ⇔ Q
           → Q ⇔ R
           → P ⇔ R
⇔hetTrans p=q q=r = (λ x → proj₁ q=r (proj₁ p=q x))
                   , λ x → proj₂ p=q (proj₂ q=r x)

⇔hetSym : ∀ {a ℓ ℓ₁} {A : Set a} {P : BinRel A ℓ} {Q : BinRel A ℓ₁}
        → P ⇔ Q
        → Q ⇔ P
⇔hetSym p=q = (proj₂ p=q) , (proj₁ p=q)
