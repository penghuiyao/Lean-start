import TQI.Capacities

/-!
# Blueprint

This file is the roadmap for formalizing John Watrous's *The Theory of Quantum
Information*.  Like the BooleanFunctions blueprint, it may contain definitions
and theorem statements before the polished proofs are moved into the main
chapter files.

## Milestone 0: infrastructure

1. Keep the existing Lake workspace and add `TQI` as a second Lean library.
2. Record Watrous's global conventions: finite alphabets, `C^Sigma`, matrices
   as operators, and the standard inner product.
3. Keep advanced predicates named but lightweight until the right mathlib APIs
   are chosen.

## Milestone 1: Chapter 1 linear algebra

1. Formalize direct sums and tensor products through sum/product alphabets.
2. Add adjoint, trace, standard basis, elementary matrices, and rank.
3. Use mathlib's matrix API for Hermitian, positive semidefinite, projection,
   unitary, trace, and rank facts.
4. Develop the finite-dimensional trace identities needed for quantum states.

## Milestone 2: Chapter 2 quantum objects

1. Reuse Physlib `MState` and `Ket` for mixed and pure states.
2. Reuse Physlib `CPTPMap`, `MatrixMap`, and CP/TP predicates for channels.
3. Reuse Physlib's Choi, Kraus, composition, and tensor-product channel API.
4. Reuse Physlib `POVM`, `MEnsemble`, and `PEnsemble` for measurements and
   ensembles.

## Milestone 3: Chapter 3 distances

1. Formalize trace norm and trace distance.
2. Formalize fidelity and its basic characterizations.
3. Prove the two-state discrimination theorem.
4. Define the completely bounded trace norm and channel distance.

## Milestone 4: Chapters 4 and 5

1. Formalize unital-channel subclasses and majorization.
2. Define classical and quantum entropy functions.
3. Prove elementary entropy identities and inequalities.
4. Build toward source-coding theorems.

## Milestone 5: Chapters 6 to 8

1. Formalize separability, LOCC-flavored maps, and partial transposition.
2. Formalize permutation invariance and the symmetry tools used later.
3. State and gradually prove the main channel-capacity theorems.
-/

namespace TQI

section Roadmap

universe u v

variable (Sigma : Type u) (Gamma : Type v)
variable [Fintype Sigma] [Fintype Gamma]

/-- Chapter 1's core space convention: `C^Sigma`. -/
abbrev Chapter1Space :=
  EuclideanSpace Sigma

/-- Chapter 1's core operator convention: matrices as operators. -/
abbrev Chapter1Operator :=
  Operator Sigma Gamma

end Roadmap

end TQI
