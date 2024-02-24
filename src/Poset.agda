module Poset where

-- Standard library imports
open import Relation.Binary         using (Rel ; IsPartialOrder; Poset)
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

IsLowerBound : ∀ {a ℓ ℓ₁} {A : Set a} → Rel A ℓ → Pred A ℓ₁ → Pred A _
IsLowerBound _≤_ P x = ∀ y → P y → x ≤ y

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
record IsChain {a ℓ₁ ℓ₂ ℓ₃} {A : Set a} (P : Pred A ℓ₃) (_≈_ : Rel A ℓ₁)
               (_≤_ : Rel A ℓ₂) : Set (suc (a ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) where
  field
    isPartialOrder : IsPartialOrder _≈_ _≤_
    isChain : ∀ {x y : A} → P x → P y → x ≤ y ⊎ y ≤ x
open IsChain
  
record Chain c ℓ₁ ℓ₂ ℓ₃ (C : Set c) : Set (suc(c ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) where
  infix 4 _≈_ _≤_
  field
    isSubPoset : Pred C ℓ₃ 
    _≈_ : Rel C ℓ₁
    _≤_ : Rel C ℓ₂
    isPartialOrder : IsPartialOrder _≈_ _≤_
    isChain : IsChain isSubPoset _≈_ _≤_
open Chain

ChainIsPoset : ∀ {c ℓ₁ ℓ₂ ℓ₃} {Cr : Set c} → Chain c ℓ₁ ℓ₂ ℓ₃ Cr → Poset c ℓ₁ ℓ₂
ChainIsPoset C = record { isPartialOrder = isPartialOrder C }

-- maximal elements
{-
  Let 𝐏 be a Poset, An element x is maximal in 𝐏, if ¬ ∃ y ∈ A → x ≤ y. 
-}

IsMaximal : ∀ {a ℓ₁ ℓ₂} {A : Set a} → Rel A ℓ₁ → Rel A ℓ₂ → A → Set (a ⊔ ℓ₁ ⊔ ℓ₂)
IsMaximal _≈_ _≤_ x = ¬ (∃[ y ] (x ≤ y ×  ¬(x ≈ y)))

-- Zorn's Lemma
{-
  Let 𝐏 be a nonempty Poset, Suppose that every chain in P has an upper bound.
  Then 𝐏 has a maximal element
-}

-- Assuming Zorn's Lemma as an axiom
ZornsLemma : ∀ {c ℓ₁ ℓ₂ ℓ₃} (P : Poset c ℓ₁ ℓ₂) → Set _
ZornsLemma {c} {ℓ₁} {ℓ₂} {ℓ₃} P = (∀ (C : Chain c ℓ₁ ℓ₂ ℓ₃ A)
                 → ∃[ x ] (IsUpperBound (_≤_ C) (isSubPoset C) x))
             → ∃[ y ] (IsMaximal  _≈p_
                                  _≤p_ y)
  where
  open Poset P renaming ( _≤_ to _≤p_
                        ; _≈_ to _≈p_
                        ; Carrier to A
                        ) 
