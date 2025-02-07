module Poset where

-- Standard library imports
open import Relation.Binary         using ( Rel
                                          ; IsPartialOrder
                                          ; Poset
                                          ; IsPreorder
                                          ; IsEquivalence
                                          )
open import Level                   using (Level ; _⊔_ ; suc)
open import Relation.Unary          using (Pred)
open import Relation.Nullary        using (¬_)
open import Data.Product            using (_×_ ; ∃; ∃-syntax; proj₁ ; proj₂ ; Σ ; Σ-syntax ; _,_)
open import Data.Unit.Polymorphic   using (⊤)
open import Data.Sum                using (_⊎_) 
open import Function                using (flip)

{- Upper bounds and lower bounds of subset given a binary relation -}
IsUpperBound : ∀ {a ℓ ℓ₁} {A : Set a} → Rel A ℓ → Pred A ℓ₁ → Pred A _
IsUpperBound _≤_ P x = ∀ y → P y → y ≤ x

IsLowerBound : ∀ {a ℓ ℓ₁} {A : Set a} → Rel A ℓ → Pred A ℓ₁ → Pred A _
IsLowerBound _≤_ P x = ∀ y → P y → x ≤ y

{- Supremum and infimum of an arbitrary subset of a set A -}
IsSupremum : ∀ {a ℓ ℓ₁} {A : Set a} → Rel A ℓ → Pred A ℓ₁ → Pred A _
IsSupremum _≤_ P x = IsUpperBound _≤_ P x × (∀ y → IsUpperBound _≤_ P y → x ≤ y)

IsInfimum : ∀ {a ℓ ℓ₁} {A : Set a} → Rel A ℓ → Pred A ℓ₁ → Pred A _
IsInfimum _≤_ = IsSupremum (flip _≤_) 

{- Arbitrary n-ary operation -}
Op : ∀ {ℓ₁} → Set ℓ₁ → ∀ {ℓ} → Set (suc ℓ ⊔ ℓ₁)
Op A {ℓ} = Pred A ℓ → A 

-- Complete Lattices
{-
  A complete lattice is a partial ordered set in which all subsets have both supremum and infimum.
  𝐏 = ⟨ P , ≤ ⟩, ∀ X ⊆ P exists ⋁ X and ⋀ X.  
-}
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
    module PO = IsPartialOrder isPartialOrder
    open PO public
open IsCompleteLattice public

{- Structure that encapsulates relations, operations and the proof of been a complete lattice -}
record CompleteLattice c ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂ ⊔ suc ℓ₃ ⊔ suc ℓ₄)) where
  field
    Carrier : Set c
    _≈_ : Rel Carrier ℓ₁
    _≤_ : Rel Carrier ℓ₂
    ⋁_ : Op Carrier {ℓ₃}
    ⋀_ : Op Carrier {ℓ₄}
    isCompleteLattice : IsCompleteLattice _≈_ _≤_ ⋁_ ⋀_
  module CL = IsCompleteLattice isCompleteLattice
  meetL : ∀ X x → X x → (⋀ X) ≤ x
  meetL X x p =  proj₁ (CL.isInfimum X) x p  

  ¬≈-trans : ∀ {x y z} → ¬ (x ≈ y) → y ≈ z → ¬ (x ≈ z)
  ¬≈-trans ¬x≈y y≈z x≈z = ¬x≈y (CL.Eq.trans x≈z (CL.Eq.sym y≈z))

  ¬≈-transˡ : ∀ {x y z} → ¬ (x ≈ y) → x ≈ z → ¬ (z ≈ y)
  ¬≈-transˡ ¬x≈y x≈z z≈y = ¬x≈y (CL.Eq.trans x≈z z≈y)
  
  LB≤⋀ : ∀ X x → IsLowerBound _≤_ X x → x ≤ (⋀ X)
  LB≤⋀ X x LB = proj₂ (CL.isInfimum X) x LB

  ≤-eq : ∀ {x y z} → x ≤ y → y ≈ z → x ≤ z
  ≤-eq {x} {y} {z} x≤y y≈z = CL.trans x≤y (y≤z y≈z) 
    where
      y≤z : y ≈ z → y ≤ z
      y≤z y≈z = proj₁ CL.≤-resp-≈ y≈z CL.refl
 
  ≤-eqˡ : ∀ {x y z} → x ≤ y → x ≈ z → z ≤ y
  ≤-eqˡ {x} {y} {z} x≤y x≈z = CL.trans (z≤x x≈z) x≤y
    where
      z≤x : x ≈ z → z ≤ x 
      z≤x x≈z = proj₂ CL.≤-resp-≈ x≈z CL.refl

-- Proving thatt a complete lattice is a poset
CompleteLatticeIsPoset : ∀ {c ℓ₁ ℓ₂} (CL : CompleteLattice c ℓ₁ ℓ₂ ℓ₁ ℓ₁) → Poset c ℓ₁ ℓ₂
CompleteLatticeIsPoset CL = record {isPartialOrder = isPartialOrder isCompleteLattice}
  where
  open CompleteLattice CL

{- Minimum and maximum element of a finitary complete lattice -}
1L : ∀ {c ℓ₁ ℓ₂ ℓ₃ ℓ₄} (CL : CompleteLattice c ℓ₁ ℓ₂ ℓ₃ ℓ₄) → CompleteLattice.Carrier CL   
1L CL = ⋁ λ x → ⊤
  where
  open CompleteLattice CL

0L : ∀ {c ℓ₁ ℓ₂ ℓ₃ ℓ₄} (CL : CompleteLattice c ℓ₁ ℓ₂ ℓ₃ ℓ₄) → CompleteLattice.Carrier CL
0L CL = ⋀ λ x → ⊤ 
  where
  open CompleteLattice CL

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

{-
  Let 𝐏 a poset, a, b ∈ P. We define the interval 𝐈[ a , b ] as the subset of P such that {x ∈ P : a ≤ x ≤ b}
-}

module _ {c ℓ₁ ℓ₂}  (𝐏 : Poset c ℓ₁ ℓ₂) where
  open Poset 𝐏 renaming (Carrier to P ; _≤_ to _≤p_)
  𝐈[_][_,_] : ∀ (a b : P) → Pred P ℓ₂ 
  𝐈[_][_,_] a b x = (a ≤p x) × (x ≤p b)

{-
  Proposition: 
  Let 𝐏 a Poset in which inf X exists for each X ⊆ P. Then 𝐏 is a complete lattice.
-}
module _ {c ℓ₁ ℓ₂} (𝐏 : Poset c ℓ₁ ℓ₂) where
  open Poset 𝐏 renaming (Carrier to P
                        ; _≤_ to _≤p_
                        ; _≈_ to _≈p_
                        ; isPartialOrder to PO
                        )
  open IsPartialOrder PO renaming (isPreorder to preO ; ≤-resp-≈ to resp) 
  open IsPreorder preO renaming (isEquivalence to equiv ; trans to ≤trans)
  open IsEquivalence equiv renaming (refl to reflp ; sym to symp ; trans to transp)

  compLatticeDef : (∀ {ℓ} (X : Pred P ℓ) →  Σ[ ⋀_ ∈ (Op P) ] (IsInfimum _≤p_ X (⋀ X)))
                 → CompleteLattice c ℓ₁ ℓ₂ (c ⊔ ℓ₂) (c ⊔ ℓ₂)
  compLatticeDef prop = record
                       { Carrier = P
                       ; _≈_ = _≈p_
                       ; _≤_ = _≤p_
                       ; ⋁_ = ⋁p_
                       ; ⋀_ = ⋀p_
                       ; isCompleteLattice = isCompLattice
                       }
    where
      -- Infimum is carried by hipotesis
      ⋀p_ : Op P
      ⋀p_ X = proj₁ (prop X) X

      -- Defining set of all upper bounds of an arbitrary subset X
      Y : (X : Pred P (c ⊔ ℓ₂)) → Pred P _
      Y X y = IsUpperBound _≤p_ X y

      -- Supremum is the infimum of Y 
      ⋁p_ : Op P
      ⋁p_ X = proj₁ (prop (Y X)) (Y X)

      -- Let a = ⋀Y 
      a : (X : Pred P (c ⊔ ℓ₂)) → P
      a X = ⋀p (Y X)

      {- Let x ∈ X, x is a lower bound of Y -}
      x≤y : (x : P) {X : Pred P (c ⊔ ℓ₂)}
          → X x
          → (∀ {y : P} → (Y X) y → x ≤p y)
      x≤y x x∈X y∈Y = y∈Y x x∈X

      xisLBofY : (x : P) {X : Pred P (c ⊔ ℓ₂)}
               → X x
               → IsLowerBound _≤p_ (Y X) x
      xisLBofY x x∈X y y∈Y = x≤y x x∈X y∈Y

      {- Because x is a lower bound of Y and a is the greatest lower bound of Y.
      Then x ≤ a -}
      x≤a : (x : P) {X : Pred P (c ⊔ ℓ₂)}
          → X x
          → x ≤p (a X)
      x≤a x {X} x∈X = proj₂ (proj₂ (prop (Y X))) x (xisLBofY x x∈X)

      {- because x is arbitrary, then x ≤ a implies a ∈ Y -}
      a∈Y : {X : Pred P (c ⊔ ℓ₂)} → (Y X) (a X)
      a∈Y {X} x x∈X = x≤a x x∈X

      {- Because a ∈ Y, a is the greatest lower bound of Y -}
      y∈Y→a≤y : {y : P} {X : Pred P (c ⊔ ℓ₂)} → (Y X) y → (a X) ≤p y
      y∈Y→a≤y {y} {X} y∈Y = proj₁ (proj₂ (prop (Y X))) y y∈Y  

      {- Been the gretest lower bound of Y means to be the least upper bound of X-} 
      ⋁pIsSup : (X : Pred P (c ⊔ ℓ₂)) → IsSupremum _≤p_ X (⋁p X)
      ⋁pIsSup X = (λ x x∈X → x≤a→x≤⋁pX (x≤a x x∈X))
                , ⋁pisLeastUB
        where
          a≈⋁pX : (a X) ≈p (⋁p X)
          a≈⋁pX = reflp

          x≤a→x≤⋁pX : {x : P} → x ≤p (a X) → x ≤p (⋁p X)
          x≤a→x≤⋁pX x≤a = proj₁ resp a≈⋁pX x≤a

          ⋁pisLeastUB : (y : P) → IsUpperBound _≤p_ X y → (⋁p X) ≤p y
          ⋁pisLeastUB y yisUB = proj₂ resp a≈⋁pX (y∈Y→a≤y y∈Y)
            where
              y∈Y : (Y X) y
              y∈Y = yisUB

      isCompLattice : IsCompleteLattice _≈p_ _≤p_ ⋁p_ ⋀p_
      isCompLattice = record { isPartialOrder = PO
                             ; isSupremum = λ X → ⋁pIsSup X
                             ; isInfimum = λ X → proj₂ (prop X)
                             }

