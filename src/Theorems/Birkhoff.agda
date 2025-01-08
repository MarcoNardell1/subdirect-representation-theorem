open import Overture using (Signature ; 𝓞 ; 𝓥)

module Theorems.Birkhoff {𝑆 : Signature 𝓞 𝓥} where
open import Level
open import Data.Product
open import Relation.Nullary
open import Relation.Unary using (Pred)
open import Relation.Binary using (Setoid ; IsEquivalence ; _⇔_ ; Rel ; _⇒_)
open import Function using (Func ; id)
open import Function.Construct.Composition using (function)

open import Relation.Binary.PropositionalEquality as ≡ using ()
import Relation.Binary.Reasoning.Setoid           as SReasoning  using ( begin_ ; step-≈˘; step-≈; _∎)


open import Setoid.Algebras  {𝑆 = 𝑆}
open import Setoid.Homomorphisms using (hom ; IsHom ; IsMon)
open import Setoid.Homomorphisms.Isomorphisms {𝑆 = 𝑆}
open import Setoid.Relations using (0rel ; fker)
open import Setoid.Functions using (IsInjective ; IsSurjective)

open import Prod.SubdirIrreducible {𝑆 = 𝑆} using ( SubdirectlyIrreducible ; IsSubIrreducible )
open import Prod.NatMapProps {𝑆 = 𝑆} using ( familyOfRels
                                           ; NatMapIsSubEmb
                                           ; NatMap
                                           ; subemb→quot≅Bᵢ
                                           ; famOfCong
                                           ; ∩=0
                                           )
open import Prod.Subdirect {𝑆 = 𝑆} using ( ⨅-fun ; IsSubdirectProduct)
open import Prod.Subembedding {𝑆 = 𝑆}
open import Structures.Algebras {𝑆 = 𝑆}
open import Structures.CompLattices {𝑆 = 𝑆}
open import Theorems.SubdirectRepresentations {𝑆 = 𝑆} hiding (𝐀)
open import Isomorphisms.Isomorphisms {𝑆 = 𝑆}
open import Lattice
open import Poset
open import Utils.Axioms
open import Utils.Definitions

private variable α ρᵅ i : Level

{-
Theorem:
Every nontrivial algebra is isomorphic to a subdirect product of subdirectly irreducible algebras
-}

{- Given a nontrivial algebra, we need to define a subdirect product by giving an arbitrary set of indexes -}
module _ (n𝐀 : NonTrivialAlgebra {β = α} {ρ = ρᵅ}) where
  𝐀 : Algebra α ρᵅ
  𝐀 = proj₁ n𝐀

  open Algebra 𝐀 renaming (Domain to A)
  open Setoid A renaming (Carrier to Car ; _≈_ to _≈a_)

  -- Seria existe x, existe y tales que x ≠ y
  I : Set (α ⊔ ρᵅ)
  I =  Σ[ x ∈ 𝕌[ 𝐀 ] ] Σ[ y ∈ 𝕌[ 𝐀 ] ] ¬ (x ≈a y)

  -- Usar el Lema de Zorn para dar la congruencia maximal en la cadena que excluye (a , b)
  -- existe θ una congruencia, maximal con respecto a la exclusion de (a , b) 
  -- 1. Sabiendo que (a , b) ∉ θab ⇒ θab ≠ 1_A
  -- 2. Sabiendo que es maximal tambien ⇒ θabIsCongCMI
  postulate
    θabCMI : (ab : I) → Σ[ θ ∈ (Con 𝐀 {ρᵅ}) ] ((¬ (proj₁ θ) (proj₁ ab) (proj₁ (proj₂ ab)))) × IsCongCMI n𝐀 θ

  famOfCongs : (ab : I) → Con 𝐀 {ρᵅ}
  famOfCongs ab = proj₁ (θabCMI ab)

  famOfRels : (ab : I) → Rel Car ρᵅ
  famOfRels ab = proj₁ (famOfCongs ab)

  θab≠1 : (ab : I) → ¬ (∀ (x y : 𝕌[ 𝐀 ]) → (proj₁ (proj₁ (θabCMI ab))) x y)
  θab≠1 ab xθy = proj₁ (proj₂ (θabCMI ab)) (xθy (proj₁ ab) (proj₁ (proj₂ ab)))

  𝐀/θabNonTrivial : (ab : I) → NonTrivialAlgebra {β = α} {ρ = ρᵅ} 
  𝐀/θabNonTrivial ab = quotNonTrivial n𝐀 (proj₁ (θabCMI ab) , θab≠1 ab)

  fam : (ab : I) → Algebra α ρᵅ
  fam ab = proj₁ (𝐀/θabNonTrivial ab) 

  natSubIrrMap : Func A 𝔻[ (⨅ fam)]
  natSubIrrMap = NatMap 𝐀 famOfCongs
  
  𝐀/θabIsSubIrr : (ab : I) → IsSubIrreducible (𝐀/θabNonTrivial ab) {i = i}
  𝐀/θabIsSubIrr ab =  θCMI→𝐀/θisSubIrr n𝐀 (proj₁ (θabCMI ab) , θab≠1 ab) (proj₂ (proj₂ (θabCMI ab)))

  ∩abθab⇔0A : ⋂ᵣ {s = α ⊔ ρᵅ} I famOfRels ⇔ proj₁ (0relCong n𝐀)
  ∩abθab⇔0A = ∩θ⊆0 , 0=∩θ
    where
      0=∩θ : proj₁ (0relCong n𝐀) ⇒ ⋂ᵣ {s = α ⊔ ρᵅ} I famOfRels
      0=∩θ x=y ab = lift (θreflexive (lower x=y))
        where
          open IsCongruence (proj₂ (proj₁ (θabCMI ab))) renaming (reflexive to θreflexive)

      ∩θ⊆0 : ⋂ᵣ {s = α ⊔ ρᵅ} I famOfRels ⇒ proj₁ (0relCong n𝐀)
      ∩θ⊆0 {x} {y} ∩θxy = lift (absurd (x ≈a y) abs)
        where
          abs : ¬ (¬ (x ≈a y))
          abs ¬x≈y = proj₁ (proj₂ (θabCMI xy)) (lower (∩θxy xy))
            where
              xy : I
              xy = x , (y , ¬x≈y)

  subEmb : IsSubEmb 𝐀 fam natSubIrrMap
  subEmb = NatMapIsSubEmb 𝐀 famOfCongs ∩abθab⇔0A
 
  {- TODO :
   4. Prove that HomImageOf[ g ] ≅ 𝐀, where g is the natural map given by 3.17
  -}
