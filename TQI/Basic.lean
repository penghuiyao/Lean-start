import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Basic project setup

This file contains the lightweight common vocabulary for formalizing John
Watrous's *The Theory of Quantum Information*.

The project deliberately reuses mathlib and Physlib/QuantumInfo rather than
redefining quantum-information primitives.  This basic file only records the
mathlib-level finite-dimensional conventions:

* finite alphabets are ordinary finite types;
* `C^Sigma` is the mathlib function space `Sigma -> Complex`;
* operators are mathlib matrices.

Physlib aliases such as `Ket`, `MState`, `CPTPMap`, and `POVM` live in the
chapter files where they are first needed.
-/

namespace TQI

universe u v

/--
An alphabet in Watrous's sense is a finite nonempty type.

Most definitions below keep `[Fintype Sigma]` and `[Nonempty Sigma]` as ordinary
typeclass assumptions, but this structure records the intended convention.
-/
structure Alphabet (Sigma : Type u) where
  fintype : Fintype Sigma
  nonempty : Nonempty Sigma

/-- The complex Euclidean space `C^Sigma`. -/
abbrev EuclideanSpace (Sigma : Type u) :=
  Sigma -> Complex

/-- Operators `L(C^Sigma, C^Gamma)`, represented by matrix entries. -/
abbrev Operator (Sigma : Type u) (Gamma : Type v) :=
  Matrix Gamma Sigma Complex

/-- Square operators `L(C^Sigma)`. -/
abbrev End (Sigma : Type u) :=
  Operator Sigma Sigma

/-- The standard basis vector `e_a`. -/
def basisVector {Sigma : Type u} [DecidableEq Sigma] (a : Sigma) :
    EuclideanSpace Sigma :=
  fun b => if b = a then 1 else 0

/--
The standard inner product on `C^Sigma`, conjugate-linear in the first argument
and linear in the second, matching Watrous's convention.
-/
noncomputable def inner {Sigma : Type u} [Fintype Sigma]
    (u v : EuclideanSpace Sigma) : Complex :=
  Finset.univ.sum (fun a : Sigma => star (u a) * v a)

/-- Matrix adjoint, i.e. conjugate transpose. -/
def adjoint {Sigma : Type u} {Gamma : Type v} (A : Operator Sigma Gamma) :
    Operator Gamma Sigma :=
  Matrix.conjTranspose A

/-- The trace of a square operator. -/
noncomputable def trace {Sigma : Type u} [Fintype Sigma] (A : End Sigma) :
    Complex :=
  Matrix.trace A

/-- A square operator is Hermitian when it equals its mathlib adjoint. -/
abbrev IsHermitian {Sigma : Type u} (A : End Sigma) : Prop :=
  Matrix.IsHermitian A

end TQI
