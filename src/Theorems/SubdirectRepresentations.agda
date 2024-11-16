open import Overture using ( 𝓞 ; 𝓥 ; Signature)

module Theorems.SubdirectRepresentations {𝑆 : Signature 𝓞 𝓥} where
open import Level
open import Data.Product
open import Relation.Unary using (Pred)
open import Relation.Binary using (Setoid ; IsEquivalence)
open import Function using (Func)

open import Setoid.Algebras  {𝑆 = 𝑆}
open import Setoid.Relations using (0rel ; fker)

open import Prod.SubdirIrreducible {𝑆 = 𝑆}
open import Structures.Algebras {𝑆 = 𝑆}
open import Structures.CompLattices {𝑆 = 𝑆}
open import Lattice
open import Poset

private variable α ρᵅ i : Level
open MeetIrreducible 
{-
 Theorem :
 An algebra 𝐀 is subdirectly irreducible iff 0_A is completely meet irreducible in Con 𝐀.
 More generally, if θ is a congruence on an algebra 𝐀, then 𝐀／θ is subdirectly irreducible
 iff θ is completely meet irreducible in Con 𝐀. 

-}

{- Tomemos un conjunto de indices, un algebra no trivial 𝐀 y una familia de algebras del mismo tipo de 𝐀,
esta familia sera la que formara la representacion de 𝐀
-}

{- 𝓐 deberia ser la familia de todas las algebras cocientes -} 
module _ {I : Set i} (𝐀 : NonTrivialAlgebra {β = α} {ρ = ρᵅ}) (𝓐 : I → Algebra α ρᵅ) where

  Alg : Algebra α ρᵅ
  Alg = proj₁ 𝐀
  
  open Algebra Alg renaming ( Domain to A
                            ; Interp to AInterp
                            )
  open Setoid A renaming ( _≈_ to _≈ₐ_
                         ; refl to arefl
                         ; sym to asym
                         ; trans to atrans
                         )
  open Algebra (⨅ 𝓐) renaming (Domain to ⨅A)
  open Setoid ⨅A renaming (_≈_ to _≈b_)

  -- Lattice of congruences of 𝐀 
  CongsOf𝐀 : CompleteLattice (α ⊔ (ov ρᵅ)) (α ⊔ (ov ρᵅ)) (α ⊔ (ov ρᵅ)) (α ⊔ (ov ρᵅ)) (α ⊔ (ov ρᵅ))
  CongsOf𝐀 = congCompLattice I Alg

  open CompleteLattice CongsOf𝐀 renaming (Carrier to Cg)

  0relCong : Con Alg {ρᵅ}
  0relCong = 0rel {𝐴 = A} {𝐵 = ⨅A} {ℓ = ρᵅ} , isCong
    where
      0isEquiv : IsEquivalence (0rel {𝐴 = A} {𝐵 = ⨅A} {ℓ = ρᵅ})
      0isEquiv = record { refl = lift arefl
                        ; sym = λ x0y → lift (asym (lower x0y))
                        ; trans = λ x0y y0z → lift (atrans (lower x0y) (lower y0z))
                        }

      isCong : IsCongruence Alg (0rel {𝐴 = A} {𝐵 = ⨅A} {ℓ = ρᵅ})
      isCong = record { reflexive = λ x=y → lift x=y
                      ; is-equivalence = 0isEquiv
                      ; is-compatible = λ 𝑓 x → {!!}
                      }

-- Aca debemos ver que efectivamente la congruencia dada por 0_A pertenece al universo del reticulado de congruencias
{-
  No se si nos podemos asegurar porque no sabemos la forma del reticulado de congruencias todavia.
-}
  0rel∈Cg : Cg
  0rel∈Cg = {!0relCong!}
{-
  We are going to split the theorem above in two propositions for each of the statements,
  the particular for 𝐀 and the general for each 𝐀／θ.
-} 


-- first we are going to particular case for 𝐀 to be subdirectly irreducible
{- for this we need to divide this into two cases
 1. A is subdir irreducible implies 0_A is CMI in Con 𝐀
 2. 0_A is CMI in Con 𝐀 implies A is subdir irreducible
-}

  postulate
    AisSubdir→0IsCMI : IsSubIrreducible 𝐀 𝓐 → IsCMI {CL = CongsOf𝐀} {!0relCong!}
    0IsCMI : IsCMI {CL = CongsOf𝐀} {!0relCong!} → IsSubIrreducible 𝐀 𝓐
