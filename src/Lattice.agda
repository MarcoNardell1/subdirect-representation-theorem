module Lattice where

-- Standard library imports
open import Relation.Binary.Lattice using (Lattice ; Infimum ; Supremum ; IsLattice)
open import Relation.Binary         using (Rel ; IsPartialOrder)
open import Level                   using (Level ; _⊔_ ; suc)
open import Relation.Unary          using (Pred)
open import Relation.Nullary        using (¬_)
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Unit.Polymorphic using (⊤)
open import Agda.Builtin.Unit       using (tt) 
open import Algebra.Core            using (Op₂)

-- Local imports
open import Poset                         

{-
  Lemma: 
  Let 𝐋 be a Complete Lattice , then 𝐋 is a lattice.
  Proof: 
  Let 𝐋 be an arbitrary complete lattice, by assumption for every X ⊆ L exists ⋁ X and ⋀ X.
  Then let X = {x , y} be a subset of L. Since X ⊆ L, ⋁ X = sup X = sup {x, y} = x ∨ y.
  Identically, ⋀ X = inf X = inf {x , y} = x ∧ y.
  ∎ 
-}
 
CompleteLatticeIsLattice : ∀ {c ℓ₁ ℓ₂}
                         → CompleteLattice c ℓ₁ ℓ₂ ℓ₁ ℓ₁
                         → Lattice c ℓ₁ ℓ₂
CompleteLatticeIsLattice CL = record { Carrier = Carrier
                                       ; _≈_ = _≈_
                                       ; _≤_ = _≤_
                                       ; _∨_ = _∨_
                                       ; _∧_ = _∧_
                                       ; isLattice = isLattice
                                       }

  where
    open CompleteLattice CL
    -- utils
    subsetTwoElems : {x y : Carrier} → Pred (Carrier) _   
    subsetTwoElems {x} {y} z = (x ≈ z) ⊎ (y ≈ z)

    eqReflPoset = IsPartialOrder.Eq.refl
                  (isPartialOrder isCompleteLattice)
   
    -- binary operations
    _∨_ : Op₂ (Carrier)
    _∨_ = λ x y → ⋁ (subsetTwoElems {x} {y})

    _∧_ : Op₂ (Carrier)
    _∧_ = λ x y → ⋀ (subsetTwoElems {x} {y})

    -- proof of _∨_ is supremum
    supTwoElems : {x y : Carrier}
                → IsSupremum _≤_ subsetTwoElems (⋁ subsetTwoElems)
    supTwoElems {x} {y} = isSupremum isCompleteLattice
                                     (subsetTwoElems {x} {y})
 
    x≤x∨y :{x y : Carrier} →  x ≤ (x ∨ y)
    x≤x∨y {x} {y} =  (proj₁ (supTwoElems {x} {y})) x (inj₁ eqReflPoset)

    y≤x∨y : {x y : Carrier} → y ≤ (x ∨ y)
    y≤x∨y {x} {y} = (proj₁ (supTwoElems {x} {y})) y (inj₂ eqReflPoset)

    lUpperbound : {x y : Carrier} (z : Carrier)
                → x ≤ z
                → y ≤ z
                → IsUpperBound _≤_ (subsetTwoElems {x} {y}) z
    lUpperbound {x} {y} z x≤z y≤z _ (inj₁ x₁) = IsPartialOrder.≤-respˡ-≈
                                                (isPartialOrder isCompleteLattice)
                                                x₁
                                                x≤z
    lUpperbound {x} {y} z x≤z y≤z _ (inj₂ y₁) = IsPartialOrder.≤-respˡ-≈
                                                (isPartialOrder isCompleteLattice)
                                                y₁
                                                y≤z
                    
    supIsLeastUpperBound : {x y : Carrier} (z : Carrier)
                         → x ≤ z
                         → y ≤ z
                         → (x ∨ y) ≤ z
    supIsLeastUpperBound {x} {y} z x≤z y≤z = proj₂ (supTwoElems {x} {y})
                                                   z
                                                   (lUpperbound {x} {y} z x≤z y≤z) 

    sup : Supremum (_≤_) _∨_
    sup x y = x≤x∨y {x} {y}
            , y≤x∨y {x} {y}
            , λ z → supIsLeastUpperBound {x} {y} z

    -- proof of _∧_ is infimum
    infTwoElems : {x y : Carrier}
                → IsInfimum _≤_ subsetTwoElems (⋀ subsetTwoElems)
    infTwoElems {x} {y} = isInfimum isCompleteLattice
                                    (subsetTwoElems {x} {y})

    x∧y≤x : {x y : Carrier} → (x ∧ y) ≤ x
    x∧y≤x {x} {y} = proj₁ (infTwoElems {x} {y}) x (inj₁ eqReflPoset)

    x∧y≤y : {x y : Carrier} → (x ∧ y) ≤ y
    x∧y≤y {x} {y} = proj₁ (infTwoElems {x} {y}) y (inj₂ eqReflPoset)

    gUpperbound : {x y : Carrier} (z : Carrier)
                → z ≤ x
                → z ≤ y
                → IsLowerBound _≤_ (subsetTwoElems {x} {y}) z
    gUpperbound {x} {y} z z≤x z≤y _ (inj₁ x₁) = IsPartialOrder.≤-respʳ-≈
                                                 (isPartialOrder isCompleteLattice)
                                                 x₁
                                                 z≤x
    gUpperbound {x} {y} z z≤x z≤y _ (inj₂ y₁) = IsPartialOrder.≤-respʳ-≈
                                                (isPartialOrder isCompleteLattice)
                                                y₁
                                                z≤y
    
    infIsGreatestLowerbound : {x y : Carrier} (z : Carrier)
                            → z ≤ x
                            → z ≤ y
                            → z ≤ (x ∧ y)
    infIsGreatestLowerbound {x} {y} z z≤x z≤y = proj₂ (infTwoElems {x} {y})
                                                      z
                                                      (gUpperbound {x}
                                                                   {y}
                                                                   z
                                                                   z≤x
                                                                   z≤y
                                                       )
    
    inf : Infimum (_≤_) _∧_
    inf x y = x∧y≤x
            , x∧y≤y
            , λ z → infIsGreatestLowerbound {x} {y} z  

    isLattice : IsLattice (_≈_) (_≤_) (_∨_) (_∧_)
    isLattice = record { isPartialOrder = isPartialOrder (isCompleteLattice)
                       ; supremum = sup
                       ; infimum = inf
                       } 

-- Meet-irreducible elements
{-
  Let 𝐋 be a complete lattice.
  An element a is called meet-irreducible if a = b ∧ c implies a = b or a = c.
  The element a is completely meet-irreducible if a ≠ 1_𝐋 and whenever a = ⋀_{i ∈ I} bᵢ,
  there is a j ∈ I such that a = bⱼ.  
-}
postulate
  absurd : ∀ {ℓ} (P : Set ℓ) → ¬ (¬ P) → P

module MeetIrreducible {c ℓ₁} {CL : CompleteLattice c ℓ₁ ℓ₁ ℓ₁ ℓ₁} where
  open CompleteLattice CL

  L : Lattice c ℓ₁ ℓ₁
  L = CompleteLatticeIsLattice CL
  open Lattice L renaming ( Carrier to A
                          ; _≈_ to _≈l_
                          ; _≤_ to _≤l_
                          )

  -- Check if an element is meet-irreducible
  IsMI : Pred Carrier _
  IsMI x = ∀ b c → x ≈l (b ∧ c) → (x ≈l b) ⊎ (x ≈l c)

  -- check if an element is completely meet-irreducible
  ≈-closed : ∀ {ℓ} (P : Pred Carrier ℓ) → Set (c ⊔ ℓ₁ ⊔ ℓ)
  ≈-closed P = ∀ x y → P x → x ≈ y → P y
  
  IsCMI : Pred Carrier _
  IsCMI x = ¬ (x ≈ (1L CL)) × (∀ P → ≈-closed P → (⋀ P) ≈ x → P x)

-- Some strict order properties 
  _<CL_ : Rel Carrier _
  a <CL b = a ≤ b × ¬ (a ≈ b)

  <CL-trans :  ∀ (x y z : Carrier) → (x <CL y) × (y ≤ z) → x <CL z
  <CL-trans x y z ((x≤y , ¬x≈y) , y≤z) = CL.trans x≤y y≤z , ¬x≈z x≤y y≤z ¬x≈y
    where
      ¬x≈z : x ≤ y → y ≤ z → ¬ (x ≈ y) → ¬ (x ≈ z)
      ¬x≈z x≤y y≤z ¬x≈y = λ x₁ → ¬x≈y (CL.antisym x≤y (≤-eq  y≤z (CL.Eq.sym x₁)))   

  <CL-eq : ∀ (x y z : Carrier) → x <CL y → y ≈ z → x <CL z
  <CL-eq x y z (x≤y , ¬x≈y) y≈z = ≤-eq x≤y y≈z , ¬≈-trans ¬x≈y y≈z
  
  <CL-irr : ∀ (x : Carrier) → x <CL x → ⊥
  <CL-irr x (_ , x≠x) = x≠x CL.Eq.refl
  
  1L≤-refl : ∀ (x : Carrier) → 1L CL ≤ x → 1L CL ≈ x
  1L≤-refl x 1≤x = CL.Eq.trans 1≈⋁ (⋁≈x xIsSup) 
    where
      all : Pred Carrier ℓ₁
      all = λ x → ⊤

      y∈all : ∀ (y : Carrier) → all y
      y∈all y = Level.lift Agda.Builtin.Unit.tt
      
      1≈⋁ : (1L CL) ≈ (⋁ all)
      1≈⋁ = CL.Eq.refl
      
      y≤1 : ∀ (y : Carrier) → y ≤ 1L CL
      y≤1 y =
        proj₁
          (isSupremum isCompleteLattice all)
          y
          (y∈all y)
      
      xIsSup : IsSupremum _≤_ all x 
      xIsSup = (λ y y∈L → CL.trans (y≤1 y) 1≤x)
             , λ z zIsUpper → zIsUpper x (Level.lift tt)

      sup-refl : ∀ (X : Pred Carrier ℓ₁) {x y : Carrier}
               → IsSupremum _≤_ X x
               → IsSupremum _≤_ X y → x ≈ y
      sup-refl X {x} {y} (xUB , xisLUB) (yUB , yisLUB) =
        CL.antisym
          (xisLUB y yUB)
          (yisLUB x xUB)
      
      ⋁≈x : IsSupremum _≤_ all x → (⋁ all) ≈ x
      ⋁≈x xIsSup =
        sup-refl
          all
          (isSupremum isCompleteLattice all)
          xIsSup
      
  <CL-not1 : ∀ (x y : Carrier) → x <CL y → ¬ (x ≈ 1L CL)
  <CL-not1 x y x<y = λ x≈1 → 1L<y (<CL-eqˡ x<y x≈1)
    where
      <CL-eqˡ : x <CL y → x ≈ 1L CL → 1L CL <CL y
      <CL-eqˡ (x≤y , ¬x≈y) x≈1 = ≤-eqˡ x≤y x≈1
                               , ¬≈-transˡ ¬x≈y x≈1
      
      1L<y : (1L CL) <CL y → ⊥
      1L<y (1≤y , ¬1≈y) = ¬1≈y (1L≤-refl y 1≤y)
  
  -- Lemma
  {-
  Suppose that a is an element of a Complete Lattice 𝐋. The following are equivalent
  (a) a is completely meet irreducible

  (b) There is an element c ∈ L such that a < c and for every x ∈ L, a < x implies that c ≤ x. 
  -}
  CMI→Cover : (a : Carrier)
            → IsCMI a
            → ∃[ c ] ((a <CL c) × (∀ (x : A) → a <CL x → c ≤ x))
  CMI→Cover a p = c' , (LB≤⋀ X a aIsLowerBound , abs) , meetL X
    where
    
      X : Pred Carrier ℓ₁
      X = λ x → a <CL x

      XisClosed : ≈-closed X
      XisClosed = λ x y Xx x≈y → <CL-eq a x y Xx x≈y
      
      c' : A
      c' = ⋀ X

      aIsLowerBound : IsLowerBound _≤_ X a
      aIsLowerBound y a≤y = proj₁ a≤y

      abs : a ≈ c' → ⊥
      abs a=c' = <CL-irr a a<a
        where
          a<a : a <CL a
          a<a = proj₂ p X XisClosed (CL.Eq.sym a=c')
    
  cover→CMI : (a : Carrier)
            → ∃[ c ] ((a <CL c) × (∀ (x : A) → a <CL x → c ≤ x))  → IsCMI a
  cover→CMI a (c' , (a<c , p)) = <CL-not1 a c' a<c
                               , λ P PisClosed inf≈a
                                   → absurd (P a) (λ a∉P
                                                     → <CL-irr a
                                                              (a<a P
                                                                   PisClosed
                                                                   (CL.Eq.sym inf≈a
                                                                    , a∉P
                                                                    )
                                                                )
                                                    )
    where

      a<x : ∀ (X : Pred Carrier ℓ₁) (x : Carrier)
          → ≈-closed X
          → a ≈ (⋀ X) × ¬ (X a)
          → X x → a ≤ x
          → a <CL x
      a<x X x XClosed (a≈inf , a∉X) x∈X a≤x = a≤x , λ a≈x → a∉X (a∈X x∈X a≈x)
        where
          a∈X : X x → a ≈ x → X a
          a∈X x∈X a≈x = XClosed x a x∈X (CL.Eq.sym a≈x)

      c≤inf : ∀ (X : Pred Carrier ℓ₁)
            → ≈-closed X
            → a ≈ (⋀ X) × ¬ (X a)
            → c' ≤ (⋀ X)
      c≤inf X XClosed (a≈inf , a∉X) = LB≤⋀ X c' cIsLowerBound
        where
          cIsLowerBound : IsLowerBound _≤_ X c'
          cIsLowerBound y y∈X = p y (a<x X
                                         y
                                         XClosed
                                         (a≈inf , a∉X)
                                         y∈X
                                         (≤-eqˡ (meetL X y y∈X) (CL.Eq.sym a≈inf))
                                     )

      a<a : ∀ (X : Pred Carrier ℓ₁)
          →  ≈-closed X
          → a ≈ (⋀ X) × ¬ (X a)
          → a <CL a
      a<a X XClosed p = <CL-trans a
                                  c'
                                  a
                                  (a<c , ≤-eq (c≤inf X XClosed p)
                                  (CL.Eq.sym (proj₁ p)))
      
open MeetIrreducible
