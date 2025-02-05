# subdirect-representation-theorem

This library written in Agda proof assistant language is an extension of DeMeo's [Universal Algebra Library](https://github.com/ualib/agda-algebras). This library also expands the definitions over lattices and posets from the [Standard Library](https://github.com/agda/agda-stdlib).

---

## Purpose of the project
This repository provides a formalization of Birkhoff subdirect representation theorem as well as some intermediate lemmas and theorems required for the proof of Birkhoff's theorem. An implementation of a library that provides the definitions over complete lattices can also be found here. Some documentation of the theorems to be proved here are in docs/ folder.

---
## Distribution of the content

### Poset
In Poset module we can find the propositions that we need to define `CompletteLattice` data type. Furthermore, here we postulate Zorn's Lemma and also a definition of interval of a poset is here.

### Lattice
In Lattice module a proof that a `CompleteLattice` defined in the module aboved described is also a Lattice from Agda Standard Library. Moreover, here there is a proposition that proves that an interval from a `Lattice` is also a `Lattice`. Finally, the definition of completely meet irreducible elements of a complete lattice is here and a proof of a Lemma of an element that covers a completely meet irreducible element is formalized here.

### Utils
+ Utils/Axioms provides postulates of classical logic for more complex proofs.
+ Utils/Definitions defines arbitrary intersection of an indexed family of binray relations `Rel`. Here, some properties over binary relations equality can also be found.

### Isomorphisms
In Isomorphisms/Isomorphisms module we define an alternative definition of algebras isomorphism and finally we prove that we can build an isomorphism of **agda-algebras**. A postulate of the converse is in this module, too.

### Structures
+ Structures/Algebra module provides the definition for trivial algebras and non trivial algebras.
+ Structures/CompleteLattices explores the limitations of bundles and strcutures at the moment of defining the `CompleteLattice` of congruences of an Algebra.

### Prod
+ Prod/Subdirect gives the definition of projections of a direct product and the `SubdirectProduct` type.
+ Prod/Subembedding has the record type for subdirect embedding encapsulating an inyective homomorphism.
+ Prod/ImageProperties is used for studying the concept of homomorphic images and how they can be used. Homomorphic images are used on the definition of subdirect embeddings.
+ Prop/NatMapProps formalizes a lemma for a family of algebra that *separate points*. A more important result for properties of a natural map is also formalized here.
* Prod/SubdirIrreducible defines the record type for subdirectly irreducible algebra `SubdirectlyIrreducible`.

### Theorems
+ Theorems/SubdirectRepresentations formalizes the theorem about the relation between subdirectly irreducible algebras and completely meet irreducible congruences. We can find the proof of a non trivial algebra is subdirectly irreducible iff the identity congruence is completeley meet irreducible in the complete lattices of congruences. A postulate for the general case for any congruence that is not the 1 congruence is here.
+ Theorems/Birkhoff have the proof of the Birkhoff's subdirect representation theorem, the steps that requires to use Zorn's lemma to obtain a maximal congruence that it will also be completely meet irreducible is postulated.
