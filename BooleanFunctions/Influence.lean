import BooleanFunctions.BasicFunctions
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring

/-!
# Influence

Definitions and basic formal statements from O'Donnell, Sections 2.2 and 2.3.

This file is deliberately API-oriented: it names the objects that later proofs
need, including coordinate flips, discrete derivatives, influences, total
influence, gradients, and the cube Laplacian.
-/

namespace BooleanFunctions

/-! ## Section 2.2. Influences and derivatives -/

/-- Replace the `i`th coordinate of `x` by `b`. -/
def setCoordSign {n : Nat} (x : SignCube n) (i : Fin n) (b : SignBit) :
    SignCube n :=
  fun j => if j = i then b else x j

@[simp]
lemma setCoordSign_same {n : Nat} (x : SignCube n) (i : Fin n)
    (b : SignBit) :
    setCoordSign x i b i = b := by
  simp [setCoordSign]

@[simp]
lemma setCoordSign_ne {n : Nat} (x : SignCube n) {i j : Fin n}
    (b : SignBit) (h : j ≠ i) :
    setCoordSign x i b j = x j := by
  simp [setCoordSign, h]

/-- The neighbor `x ⊕ i`, obtained by flipping the `i`th coordinate. -/
def flipCoordSign {n : Nat} (x : SignCube n) (i : Fin n) : SignCube n :=
  setCoordSign x i (negSignBit (x i))

/-- Definition 2.12: coordinate `i` is pivotal for `f` at `x`. -/
def IsPivotal {n : Nat} (f : BooleanFunctionSign n)
    (i : Fin n) (x : SignCube n) : Prop :=
  f x ≠ f (flipCoordSign x i)

/-- Definition 2.13: Boolean influence as pivotal probability. -/
noncomputable def booleanInfluence {n : Nat}
    (f : BooleanFunctionSign n) (i : Fin n) : Real :=
  by
    classical
    exact cubeProbability (fun x : SignCube n => IsPivotal f i x)

/--
The dimension-`i` boundary-edge fraction.  With the cube's uniform vertex
measure, this is exactly the pivotal probability.
-/
noncomputable def dimensionBoundaryEdgeFraction {n : Nat}
    (f : BooleanFunctionSign n) (i : Fin n) : Real :=
  booleanInfluence f i

/-- Definition 2.16: the discrete derivative `D_i f`. -/
noncomputable def discreteDerivative {n : Nat}
    (f : RealValuedBooleanFunction n) (i : Fin n) :
    RealValuedBooleanFunction n :=
  fun x =>
    (f (setCoordSign x i SignBit.posOne) -
        f (setCoordSign x i SignBit.negOne)) / 2

/-- Definition 2.17: influence defined from the derivative. -/
noncomputable def derivativeInfluence {n : Nat}
    (f : RealValuedBooleanFunction n) (i : Fin n) : Real :=
  cubeExpectation (fun x : SignCube n => discreteDerivative f i x ^ 2)

/-- The Fourier-side expression for the influence of coordinate `i`. -/
noncomputable def fourierInfluence {n : Nat}
    (f : RealValuedBooleanFunction n) (i : Fin n) : Real :=
  Finset.univ.sum (fun S : CoordinateSet n =>
    if i ∈ S then functionFourierCoeff f S ^ 2 else 0)

/--
The canonical influence used by the later files.

The book first defines influence via `D_i f` and then proves Theorem 2.20,
which identifies it with this Fourier expression.  We keep both names:
`derivativeInfluence` for the derivative definition and `influence` for the
Fourier-normalized form used in Section 2.3.
-/
noncomputable def influence {n : Nat}
    (f : RealValuedBooleanFunction n) (i : Fin n) : Real :=
  fourierInfluence f i

/-- Definition 2.18: a coordinate is relevant when its influence is positive. -/
def IsRelevantCoordinate {n : Nat}
    (f : RealValuedBooleanFunction n) (i : Fin n) : Prop :=
  0 < influence f i

/-- The right-hand side of Proposition 2.19. -/
noncomputable def derivativeFourierExpansion {n : Nat}
    (f : RealValuedBooleanFunction n) (i : Fin n) :
    RealValuedBooleanFunction n :=
  fun x =>
    Finset.univ.sum (fun S : CoordinateSet n =>
      if i ∈ S then functionFourierCoeff f S * chiSign (S.erase i) x else 0)

/-- Definition 2.23: the expectation operator `E_i`. -/
noncomputable def coordinateExpectation {n : Nat}
    (f : RealValuedBooleanFunction n) (i : Fin n) :
    RealValuedBooleanFunction n :=
  fun x =>
    (f (setCoordSign x i SignBit.posOne) +
        f (setCoordSign x i SignBit.negOne)) / 2

/-- Proposition 2.24, Fourier part: keep only coefficients not containing `i`. -/
noncomputable def coordinateExpectationFourierExpansion {n : Nat}
    (f : RealValuedBooleanFunction n) (i : Fin n) :
    RealValuedBooleanFunction n :=
  fun x =>
    Finset.univ.sum (fun S : CoordinateSet n =>
      if i ∈ S then 0 else functionFourierCoeff f S * chiSign S x)

/-- Definition 2.25: the coordinate Laplacian `L_i f = f - E_i f`. -/
noncomputable def coordinateLaplacian {n : Nat}
    (f : RealValuedBooleanFunction n) (i : Fin n) :
    RealValuedBooleanFunction n :=
  fun x => f x - coordinateExpectation f i x

/-! ## Section 2.3. Total influence -/

/-- Definition 2.27: total influence. -/
noncomputable def totalInfluence {n : Nat}
    (f : RealValuedBooleanFunction n) : Real :=
  Finset.univ.sum (fun i : Fin n => influence f i)

/-- The sensitivity of a sign-valued Boolean function at `x`. -/
noncomputable def sensitivity {n : Nat}
    (f : BooleanFunctionSign n) (x : SignCube n) : Nat :=
  by
    classical
    exact (Finset.univ.filter (fun i : Fin n => IsPivotal f i x)).card

/-- Fraction of all cube edges lying in the boundary of a Boolean function. -/
noncomputable def boundaryEdgeFraction {n : Nat}
    (f : BooleanFunctionSign n) : Real :=
  totalInfluence (signFunctionToReal f) / n

/-- The degree-one Fourier sum appearing in social choice applications. -/
noncomputable def degreeOneFourierSum {n : Nat}
    (f : BooleanFunctionSign n) : Real :=
  Finset.univ.sum (fun i : Fin n =>
    functionFourierCoeff (signFunctionToReal f) ({i} : CoordinateSet n))

/-- Number of voters whose vote agrees with the sign-valued outcome. -/
def agreeingVoteCount {n : Nat}
    (f : BooleanFunctionSign n) (x : SignCube n) : Nat :=
  (Finset.univ.filter (fun i : Fin n => x i = f x)).card

/-- Expected number of voters whose vote agrees with the outcome. -/
noncomputable def expectedAgreeingVotes {n : Nat}
    (f : BooleanFunctionSign n) : Real :=
  cubeExpectation (fun x : SignCube n => (agreeingVoteCount f x : Real))

/-- Definition 2.34: the gradient `∇f`. -/
noncomputable def gradient {n : Nat}
    (f : RealValuedBooleanFunction n) (x : SignCube n) : Fin n → Real :=
  fun i => discreteDerivative f i x

/-- Squared Euclidean norm of the gradient. -/
noncomputable def gradientNormSq {n : Nat}
    (f : RealValuedBooleanFunction n) (x : SignCube n) : Real :=
  Finset.univ.sum (fun i : Fin n => gradient f x i ^ 2)

/-- Definition 2.36: the cube Laplacian `L = sum_i L_i`. -/
noncomputable def laplacian {n : Nat}
    (f : RealValuedBooleanFunction n) : RealValuedBooleanFunction n :=
  fun x => Finset.univ.sum (fun i : Fin n => coordinateLaplacian f i x)

/-- The Fourier-side expression for the cube Laplacian. -/
noncomputable def laplacianFourierExpansion {n : Nat}
    (f : RealValuedBooleanFunction n) : RealValuedBooleanFunction n :=
  fun x =>
    Finset.univ.sum (fun S : CoordinateSet n =>
      (S.card : Real) * functionFourierCoeff f S * chiSign S x)

/-- The Fourier formula on the right-hand side of Theorem 2.38. -/
noncomputable def fourierTotalInfluence {n : Nat}
    (f : RealValuedBooleanFunction n) : Real :=
  Finset.univ.sum (fun S : CoordinateSet n =>
    (S.card : Real) * functionFourierCoeff f S ^ 2)

/-- Fourier weight at level `k`, as used in the second form of Theorem 2.38. -/
noncomputable def totalFourierWeightAtDegree {n : Nat}
    (f : RealValuedBooleanFunction n) (k : Nat) : Real :=
  Finset.univ.sum (fun S : CoordinateSet n =>
    if S.card = k then functionFourierCoeff f S ^ 2 else 0)

/-- The standard lower bound shape used in the edge-isoperimetric theorem. -/
noncomputable def edgeIsoperimetricLowerBound (α : Real) : Real :=
  2 * α * (Real.log (1 / α) / Real.log 2)

end BooleanFunctions
