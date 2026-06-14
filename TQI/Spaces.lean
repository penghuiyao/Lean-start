import TQI.Basic

/-!
# Complex Euclidean spaces

This file tracks Chapter 1.1.1 of Watrous: alphabets, complex Euclidean
spaces, standard basis vectors, direct sums, tensor products, unit vectors, and
the book's matrix-indexed view of finite-dimensional spaces.

For normalized pure states, use Physlib's `Ket` from
`QuantumInfo.States.Pure.Braket` in the files that actually need pure-state
formalization.
-/

namespace TQI

universe u v

/-- A register with classical state set `Sigma` has state space `C^Sigma`. -/
abbrev RegisterSpace (Sigma : Type u) :=
  EuclideanSpace Sigma

/-- The alphabet for a direct sum of two complex Euclidean spaces. -/
abbrev DirectSumAlphabet (Sigma : Type u) (Gamma : Type v) :=
  Sum Sigma Gamma

/-- The alphabet for the tensor product of two complex Euclidean spaces. -/
abbrev TensorProductAlphabet (Sigma : Type u) (Gamma : Type v) :=
  Sigma × Gamma

/-- The direct sum `C^Sigma direct_sum C^Gamma`, represented by a sum alphabet. -/
abbrev DirectSumSpace (Sigma : Type u) (Gamma : Type v) :=
  EuclideanSpace (DirectSumAlphabet Sigma Gamma)

/-- The tensor product `C^Sigma tensor C^Gamma`, represented by a product alphabet. -/
abbrev TensorProductSpace (Sigma : Type u) (Gamma : Type v) :=
  EuclideanSpace (TensorProductAlphabet Sigma Gamma)

end TQI
