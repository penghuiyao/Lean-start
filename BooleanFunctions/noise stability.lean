import BooleanFunctions.Influence

/-!
# Noise stability

Definitions from O'Donnell, Section 2.4.

The book defines the noise process probabilistically.  In this finite-cube
development we record that process as an explicit transition weight.  The
operator used for Fourier theorems is the equivalent diagonal Fourier operator:
it multiplies the coefficient on level `S` by `rho ^ S.card`.
-/

namespace BooleanFunctions

/-! ## Definitions 2.40 and 2.41: rho-correlated strings -/

/--
One-coordinate transition weight for the `rho`-noise process.

For `rho in [-1,1]`, this is `(1 + rho) / 2` when the bit is preserved and
`(1 - rho) / 2` when it is flipped.  For `rho in [0,1]`, this agrees with the
"keep with probability rho, otherwise resample uniformly" description.
-/
noncomputable def noiseBitTransitionWeight
    (rho : Real) (x y : SignBit) : Real :=
  if y = x then (1 + rho) / 2 else (1 - rho) / 2

/--
Finite transition weight for `y ~ N_rho(x)`.

The coordinates are independent, so the transition weight is the product of the
one-coordinate weights.
-/
noncomputable def noiseTransitionWeight {n : Nat}
    (rho : Real) (x y : SignCube n) : Real :=
  Finset.univ.prod (fun i : Fin n => noiseBitTransitionWeight rho (x i) (y i))

/--
Joint weight for a `rho`-correlated pair `(x,y)`: first choose `x` uniformly,
then choose `y ~ N_rho(x)`.
-/
noncomputable def rhoCorrelatedPairWeight {n : Nat}
    (rho : Real) (x y : SignCube n) : Real :=
  ((2 : Real) ^ n)⁻¹ * noiseTransitionWeight rho x y

/--
Kernel form of the noise operator from Definition 2.46.

This is the literal finite expectation `E_{y ~ N_rho(x)}[f y]`.
-/
noncomputable def noiseOperatorKernel {n : Nat}
    (rho : Real) (f : RealValuedBooleanFunction n) :
    RealValuedBooleanFunction n :=
  fun x => Finset.univ.sum (fun y : SignCube n =>
    noiseTransitionWeight rho x y * f y)

/-! ## Definitions 2.42, 2.43, and 2.46 -/

/--
Definition 2.46, Fourier-diagonal form of the noise operator `T_rho`.

The theorem file proves the displayed Fourier formula for this operator.  The
kernel form above records the probabilistic definition.
-/
noncomputable def noiseOperator {n : Nat}
    (rho : Real) (f : RealValuedBooleanFunction n) :
    RealValuedBooleanFunction n :=
  Finset.univ.sum (fun S : CoordinateSet n =>
    (rho ^ S.card * functionFourierCoeff f S) • fourierCharacterBasis n S)

/-- Definition 2.42: noise stability `Stab_rho[f]`. -/
noncomputable def noiseStability {n : Nat}
    (rho : Real) (f : RealValuedBooleanFunction n) : Real :=
  cubeInner f (noiseOperator rho f)

/-- Noise stability for sign-valued Boolean functions. -/
noncomputable def booleanNoiseStability {n : Nat}
    (rho : Real) (f : BooleanFunctionSign n) : Real :=
  noiseStability rho (signFunctionToReal f)

/--
Pair-expectation form of noise stability.

This is the expression in Definition 2.42, written with the finite joint weight
for `rho`-correlated pairs.
-/
noncomputable def noiseStabilityByPairs {n : Nat}
    (rho : Real) (f : RealValuedBooleanFunction n) : Real :=
  Finset.univ.sum (fun x : SignCube n =>
    Finset.univ.sum (fun y : SignCube n =>
      rhoCorrelatedPairWeight rho x y * (f x * f y)))

/-- Definition 2.43: noise sensitivity `NS_delta[f]`. -/
noncomputable def noiseSensitivity {n : Nat}
    (delta : Real) (f : BooleanFunctionSign n) : Real :=
  1 / 2 - (1 / 2) * booleanNoiseStability (1 - 2 * delta) f

/-! ## Definition 2.52: stable influences -/

/--
Definition 2.52: the `rho`-stable influence of coordinate `i`.

The exponent `S.card - 1` uses natural-number subtraction; when `S = {i}` and
`rho = 0`, Lean's convention `0 ^ 0 = 1` matches the book's convention.
-/
noncomputable def stableInfluence {n : Nat}
    (rho : Real) (f : RealValuedBooleanFunction n) (i : Fin n) : Real :=
  Finset.univ.sum (fun S : CoordinateSet n =>
    if i ∈ S then rho ^ (S.card - 1) * functionFourierCoeff f S ^ 2 else 0)

/-- Definition 2.52: total `rho`-stable influence. -/
noncomputable def stableTotalInfluence {n : Nat}
    (rho : Real) (f : RealValuedBooleanFunction n) : Real :=
  Finset.univ.sum (fun i : Fin n => stableInfluence rho f i)

/--
The set of coordinates whose `(1 - delta)`-stable influence is at least
`epsilon`, used in Proposition 2.54.
-/
noncomputable def stableInfluentialCoordinates {n : Nat}
    (delta epsilon : Real) (f : RealValuedBooleanFunction n) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n =>
    epsilon ≤ stableInfluence (1 - delta) f i)

end BooleanFunctions
