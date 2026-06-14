import TQI.Spaces
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Linear operators

This file is the staging area for Chapter 1.1.2 and the operator vocabulary.

Operator-level objects that already exist should be imported from mathlib or
Physlib when needed:

* Hermitian and positive semidefinite operators: Physlib `HermitianMat`
  and its order API from `QuantumInfo.ForMathlib.HermitianMat`.
* Mixed states/density operators: Physlib `MState` from
  `QuantumInfo.States.Mixed.MState`.
-/

namespace TQI

universe u v

/-- A linear operator between the spaces indexed by `Sigma` and `Gamma`. -/
abbrev LinearOperator (Sigma : Type u) (Gamma : Type v) :=
  Operator Sigma Gamma

/-- A square operator on the space indexed by `Sigma`. -/
abbrev SquareOperator (Sigma : Type u) :=
  End Sigma

/-- A super-operator maps square operators to square operators. -/
abbrev SuperOperator (Sigma : Type u) (Gamma : Type v) :=
  End Sigma -> End Gamma

/-- A trace-one square operator. -/
def HasTraceOne {Sigma : Type u} [Fintype Sigma] (A : End Sigma) : Prop :=
  trace A = 1

/-- Unitary operators are mathlib unitary-group elements. -/
abbrev UnitaryOperator (Sigma : Type u) [Fintype Sigma] [DecidableEq Sigma] :=
  Matrix.unitaryGroup Sigma Complex

end TQI
