module Poset where

-- Standard library imports
open import Relation.Binary         using (Rel ; IsPartialOrder; Poset; Maximum)
open import Level                   using (Level ; _⊔_ ; suc)
open import Relation.Unary          using (Pred ; _⊆_)
open import Relation.Nullary        using (¬_)
open import Data.Product            using (_×_ ; ∃; ∃-syntax)
open import Data.Sum                using (_⊎_) 
open import Function                using (flip)


-- Complete Lattices
{-
  A complete lattice is a partial ordered set in which all subsets have both supremum and infimum.
  𝐏 = ⟨ P , ≤ ⟩, ∀ X ⊆ P exists ⋁ X and ⋀ X.  
-}

IsUpperBound : ∀ {a ℓ ℓ₁} {A : Set a} → Rel A ℓ → Pred A ℓ₁ → Pred A _
IsUpperBound _≤_ P x = ∀ y → P y → y ≤ x

IsSupremum : ∀ {a ℓ ℓ₁} {A : Set a} → Rel A ℓ → Pred A ℓ₁ → Pred A _
IsSupremum _≤_ P x = IsUpperBound _≤_ P x × (∀ y → IsUpperBound _≤_ P y → x ≤ y)

IsInfimum : ∀ {a ℓ ℓ₁} {A : Set a} → Rel A ℓ → Pred A ℓ₁ → Pred A _
IsInfimum _≤_ = IsSupremum (flip _≤_) 

Op : ∀ {ℓ₁} → Set ℓ₁ → ∀ {ℓ} → Set (suc ℓ ⊔ ℓ₁)
Op A {ℓ} = Pred A ℓ → A 

record IsCompleteLattice {a ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Set a}
                 (_≈_ : Rel A ℓ₁) -- The underlying equality.
                 (_≤_ : Rel A ℓ₂) -- The partial order.
                 (⋁_ : Op A {ℓ₃})     -- The join operation.
                 (⋀_ : Op A {ℓ₄})     -- The meet operation.
                 : Set (a ⊔ ℓ₁ ⊔ ℓ₂ ⊔ suc ℓ₃ ⊔ suc ℓ₄) where
    field
      isPartialOrder : IsPartialOrder _≈_ _≤_
      isSupremum : ∀ (P : Pred A ℓ₃) → IsSupremum _≤_ P (⋁ P)     
      isInfimum :  ∀ (P : Pred A ℓ₄) → IsInfimum _≤_ P (⋀ P)
open IsCompleteLattice public

record CompleteLattice c ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂ ⊔ suc ℓ₃ ⊔ suc ℓ₄)) where
  field
    Carrier : Set c
    _≈_ : Rel Carrier ℓ₁
    _≤_ : Rel Carrier ℓ₂
    ⋁_ : Op Carrier {ℓ₃}
    ⋀_ : Op Carrier {ℓ₄}
    isCompleteLattice : IsCompleteLattice _≈_ _≤_ ⋁_ ⋀_

-- Requisites for Zorn's Lemma
--- Notion of Chain 
{-
  A Poset 𝐏 is called linear or chain, if it satisfies:
    (∀ x, y ∈ P) → x ≤ y ⊎ y ≤ x
-}
record IsChain {a ℓ₁ ℓ₂} {A : Set a} (_≈_ : Rel A ℓ₁)
               (_≤_ : Rel A ℓ₂) : Set (suc (a ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    isPartialOrder : IsPartialOrder _≈_ _≤_
    isChain : ∀ {x y : A} → x ≤ y ⊎ y ≤ x
open IsChain
  
record Chain c ℓ₁ ℓ₂ : Set (suc(c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _≤_
  field
    Carrier : Set c
    _≈_ : Rel Carrier ℓ₁
    _≤_ : Rel Carrier ℓ₂
    isPartialOrder : IsPartialOrder _≈_ _≤_
    isChain : IsChain _≈_ _≤_
open Chain

ChainIsPoset : ∀ {c ℓ₁ ℓ₂} → Chain c ℓ₁ ℓ₂ → Poset c ℓ₁ ℓ₂
ChainIsPoset C = record { isPartialOrder = isPartialOrder C }

-- maximal elements
{-
  Let 𝐏 be a Poset, An element x is maximal in 𝐏, if ¬ ∃ y ∈ A → x ≤ y. 
-}

IsMaximal : ∀ {a ℓ₁ ℓ₂} {A : Set a} → Rel A ℓ₁ → Rel A ℓ₂ → A → Set (a ⊔ ℓ₁ ⊔ ℓ₂)
IsMaximal _≈_ _≤_ x = ¬ (∃[ y ] (x ≤ y ×  ¬(x ≈ y)))

