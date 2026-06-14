import BooleanFunctions.Parseval
import Mathlib.Tactic.Linarith

/-!
# O'Donnell, Section 1.4

This file formalizes the basic Fourier formulas from Section 1.4 of
*Analysis of Boolean Functions*.

Definitions such as `functionFourierCoeff`, `cubeMean`, `cubeVariance`,
`cubeCovariance`, Boolean distance, and Fourier weights live in `Fourierexpansion.lean`.
-/

namespace BooleanFunctions

/-! ## Elementary expectation algebra -/

/-- The expectation of a constant function is the constant. -/
lemma cubeExpectation_const {n : Nat} (a : Real) :
    cubeExpectation (fun _ : SignCube n => a) = a := by
  classical
  unfold cubeExpectation
  simp [SignCube, StringOver]

/-- Linearity of expectation: subtraction. -/
lemma cubeExpectation_add {n : Nat}
    (f g : RealValuedBooleanFunction n) :
    cubeExpectation (fun x : SignCube n => f x + g x) =
      cubeExpectation f + cubeExpectation g := by
  unfold cubeExpectation
  simp [Finset.sum_add_distrib, mul_add]

/-- Linearity of expectation: subtraction. -/
lemma cubeExpectation_sub {n : Nat}
    (f g : RealValuedBooleanFunction n) :
    cubeExpectation (fun x : SignCube n => f x - g x) =
      cubeExpectation f - cubeExpectation g := by
  unfold cubeExpectation
  simp [Finset.sum_sub_distrib, mul_sub]

/-- Pull a scalar out of an expectation. -/
lemma cubeExpectation_mul_const {n : Nat}
    (a : Real) (f : RealValuedBooleanFunction n) :
    cubeExpectation (fun x : SignCube n => a * f x) =
      a * cubeExpectation f := by
  unfold cubeExpectation
  rw [← Finset.mul_sum]
  ring

/-- Uniform probabilities are nonnegative. -/
lemma cubeProbability_nonneg {n : Nat}
    (event : SignCube n -> Prop) [DecidablePred event] :
    0 ≤ cubeProbability event := by
  unfold cubeProbability cubeExpectation
  apply mul_nonneg
  · exact inv_nonneg.mpr (pow_nonneg (zero_le_two : (0 : Real) ≤ 2) n)
  · apply Finset.sum_nonneg
    intro x _hx
    by_cases h : event x <;> simp [h]

/-! ## Proposition 1.8 -/

/-- The Fourier coefficients of a character are Kronecker deltas. -/
lemma functionFourierCoeff_fourierCharacters {n : Nat}
    (S T : CoordinateSet n) :
    functionFourierCoeff (fourierCharacters n S) T =
      if S = T then 1 else 0 := by
  rw [← fourierCharacterBasis_eq_fourierCharacters S]
  exact Module.Basis.repr_self_apply (fourierCharacterBasis n) S T

/-- Summing against the delta coefficients of `chi_S` selects the `S` coefficient. -/
lemma sum_mul_fourierCoeff_character {n : Nat}
    (f : RealValuedBooleanFunction n) (S : CoordinateSet n) :
    Finset.univ.sum (fun T : CoordinateSet n =>
        functionFourierCoeff f T * functionFourierCoeff (fourierCharacters n S) T) =
      functionFourierCoeff f S := by
  classical
  simp [functionFourierCoeff_fourierCharacters]

/--
Proposition 1.8.

The Fourier coefficient of `f` on `S` is `<f, chi_S>`.
-/
theorem proposition_1_8 {n : Nat}
    (f : RealValuedBooleanFunction n) (S : CoordinateSet n) :
    functionFourierCoeff f S = cubeInner f (fourierCharacters n S) := by
  symm
  calc
    cubeInner f (fourierCharacters n S) =
        Finset.univ.sum (fun T : CoordinateSet n =>
          functionFourierCoeff f T *
            functionFourierCoeff (fourierCharacters n S) T) := by
      exact plancherel_theorem f (fourierCharacters n S)
    _ = functionFourierCoeff f S :=
      sum_mul_fourierCoeff_character f S

/-! ## Proposition 1.9 and Definition 1.10 -/

/-- Pointwise product of two sign-valued functions as an agreement indicator. -/
lemma sign_toReal_mul_eq_one_sub_two_disagree
    (a b : SignBit) :
    a.toReal * b.toReal = 1 - 2 * (if a ≠ b then (1 : Real) else 0) := by
  cases a <;> cases b <;> simp [SignBit.toReal] <;> ring

/--
Proposition 1.9, distance form.

For sign-valued Boolean functions, the inner product is `1 - 2 dist(f,g)`.
-/
theorem proposition_1_9_distance {n : Nat}
    (f g : BooleanFunctionSign n) :
    cubeInner (signFunctionToReal f) (signFunctionToReal g) =
      1 - 2 * signFunctionDistance f g := by
  classical
  let disagree : RealValuedBooleanFunction n :=
    fun x => if f x ≠ g x then 1 else 0
  have hpoint :
      ∀ x : SignCube n,
        signFunctionToReal f x * signFunctionToReal g x =
          1 - 2 * disagree x := by
    intro x
    simpa [disagree] using sign_toReal_mul_eq_one_sub_two_disagree (f x) (g x)
  rw [cubeInner]
  calc
    cubeExpectation (fun x : SignCube n =>
        signFunctionToReal f x * signFunctionToReal g x)
        = cubeExpectation (fun x : SignCube n => 1 - 2 * disagree x) := by
      congr
      funext x
      exact hpoint x
    _ = 1 - 2 * cubeExpectation disagree := by
      rw [cubeExpectation_sub, cubeExpectation_const, cubeExpectation_mul_const]
    _ = 1 - 2 * signFunctionDistance f g := by
      rfl

/-- Agreement probability is one minus disagreement probability. -/
lemma signFunctionAgreeProbability_eq_one_sub_disagree {n : Nat}
    (f g : BooleanFunctionSign n) :
    signFunctionAgreeProbability f g =
      1 - signFunctionDisagreeProbability f g := by
  classical
  let disagree : RealValuedBooleanFunction n :=
    fun x => if f x ≠ g x then 1 else 0
  let agree : RealValuedBooleanFunction n :=
    fun x => if f x = g x then 1 else 0
  have hpoint : agree = fun x : SignCube n => 1 - disagree x := by
    funext x
    by_cases hfg : f x = g x <;> simp [agree, disagree, hfg]
  rw [signFunctionAgreeProbability, signFunctionDisagreeProbability,
    cubeProbability, cubeProbability]
  change cubeExpectation agree = 1 - cubeExpectation disagree
  rw [hpoint, cubeExpectation_sub, cubeExpectation_const]

/--
Proposition 1.9, agreement-minus-disagreement form.
-/
theorem proposition_1_9 {n : Nat}
    (f g : BooleanFunctionSign n) :
    cubeInner (signFunctionToReal f) (signFunctionToReal g) =
      signFunctionAgreeProbability f g - signFunctionDisagreeProbability f g := by
  rw [proposition_1_9_distance]
  rw [signFunctionAgreeProbability_eq_one_sub_disagree, signFunctionDistance]
  ring

/-! ## Mean and variance -/

/-- Fact 1.12: the mean is the empty-set Fourier coefficient. -/
theorem fact_1_12 {n : Nat} (f : RealValuedBooleanFunction n) :
    cubeMean f = functionFourierCoeff f ∅ := by
  rw [cubeMean, proposition_1_8 f ∅]
  congr
  funext x
  simp [fourierCharacters, chiSign]

/-- Second-moment formula for variance. -/
lemma cubeVariance_eq_secondMoment_sub_mean_sq {n : Nat}
    (f : RealValuedBooleanFunction n) :
    cubeVariance f =
      cubeExpectation (fun x : SignCube n => f x ^ 2) - cubeMean f ^ 2 := by
  classical
  let mu := cubeMean f
  have hmu : cubeExpectation f = mu := rfl
  unfold cubeVariance centeredFunction cubeInner
  change cubeExpectation (fun x : SignCube n => (f x - mu) * (f x - mu)) =
      cubeExpectation (fun x : SignCube n => f x ^ 2) - mu ^ 2
  have hpoint :
      (fun x : SignCube n => (f x - mu) * (f x - mu)) =
        (fun x : SignCube n => f x ^ 2 - (2 * mu) * f x + mu ^ 2) := by
    funext x
    ring
  rw [hpoint]
  rw [cubeExpectation_add, cubeExpectation_sub, cubeExpectation_mul_const,
    cubeExpectation_const, hmu]
  ring

/-- The empty character is the constant-one function. -/
lemma fourierCharacterBasis_empty {n : Nat} :
    fourierCharacterBasis n (∅ : CoordinateSet n) =
      (fun _ : SignCube n => (1 : Real)) := by
  funext x
  simp [fourierCharacterBasis_apply, chiSign]

/-- Centering subtracts the mean times the empty character. -/
lemma centeredFunction_eq_sub_mean_smul {n : Nat}
    (f : RealValuedBooleanFunction n) :
    centeredFunction f =
      f - cubeMean f • fourierCharacterBasis n (∅ : CoordinateSet n) := by
  funext x
  simp [centeredFunction, fourierCharacterBasis_empty]

/-- Fourier coefficients of the centered function. -/
lemma functionFourierCoeff_centered {n : Nat}
    (f : RealValuedBooleanFunction n) (S : CoordinateSet n) :
    functionFourierCoeff (centeredFunction f) S =
      if S = ∅ then 0 else functionFourierCoeff f S := by
  classical
  rw [centeredFunction_eq_sub_mean_smul f]
  by_cases hS : S = ∅
  · subst S
    simp [functionFourierCoeff]
    change functionFourierCoeff f (∅ : CoordinateSet n) - cubeMean f = 0
    rw [← fact_1_12 f]
    ring
  · simp [functionFourierCoeff, hS]

/--
The Fourier formula for variance.
-/
lemma cubeVariance_eq_sum_nonempty_fourierWeight {n : Nat}
    (f : RealValuedBooleanFunction n) :
    cubeVariance f =
      Finset.univ.sum (fun S : CoordinateSet n =>
        if S = ∅ then 0 else fourierWeight f S) := by
  classical
  rw [cubeVariance]
  rw [parseval_theorem (centeredFunction f)]
  apply Finset.sum_congr rfl
  intro S _hS
  rw [functionFourierCoeff_centered f S]
  by_cases hS : S = ∅ <;> simp [hS, fourierWeight]

/--
Proposition 1.13.

The variance has both the second-moment formula and the Fourier-weight formula.
-/
theorem proposition_1_13 {n : Nat} (f : RealValuedBooleanFunction n) :
    cubeVariance f =
        cubeExpectation (fun x : SignCube n => f x ^ 2) - cubeMean f ^ 2 ∧
      cubeVariance f =
        Finset.univ.sum (fun S : CoordinateSet n =>
          if S = ∅ then 0 else fourierWeight f S) := by
  exact ⟨cubeVariance_eq_secondMoment_sub_mean_sq f,
    cubeVariance_eq_sum_nonempty_fourierWeight f⟩

/--
Fact 1.14, first formula: Boolean variance is `1 - E[f]^2`.
-/
theorem fact_1_14_variance {n : Nat} (f : BooleanFunctionSign n) :
    cubeVariance (signFunctionToReal f) =
      1 - cubeMean (signFunctionToReal f) ^ 2 := by
  have h := cubeVariance_eq_secondMoment_sub_mean_sq (signFunctionToReal f)
  rw [h]
  congr 1
  rw [cubeExpectation]
  have hpow : ((2 : Real) ^ n) ≠ 0 :=
    pow_ne_zero n (by exact (two_ne_zero : (2 : Real) ≠ 0))
  have hsum :
      (Finset.univ.sum (fun x : SignCube n => signFunctionToReal f x ^ 2)) =
        (2 : Real) ^ n := by
    simp [signFunctionToReal, pow_two, SignBit.toReal_mul_self]
  rw [hsum]
  exact inv_mul_cancel₀ hpow

/-- A sign-valued function is always either `+1` or `-1`. -/
lemma signValueProbability_pos_add_neg {n : Nat}
    (f : BooleanFunctionSign n) :
    signValueProbability f SignBit.posOne +
      signValueProbability f SignBit.negOne = 1 := by
  classical
  let posInd : RealValuedBooleanFunction n :=
    fun x => if f x = SignBit.posOne then 1 else 0
  let negInd : RealValuedBooleanFunction n :=
    fun x => if f x = SignBit.negOne then 1 else 0
  have hpoint : (fun x : SignCube n => posInd x + negInd x) =
      (fun _ : SignCube n => (1 : Real)) := by
    funext x
    rcases hfx : f x with _ | _ <;> simp [posInd, negInd, hfx]
  rw [signValueProbability, signValueProbability, cubeProbability, cubeProbability]
  rw [← cubeExpectation_add]
  rw [hpoint, cubeExpectation_const]

/-- For sign-valued functions, the mean is `Pr[f=1] - Pr[f=-1]`. -/
lemma cubeMean_signFunctionToReal {n : Nat}
    (f : BooleanFunctionSign n) :
    cubeMean (signFunctionToReal f) =
      signValueProbability f SignBit.posOne -
        signValueProbability f SignBit.negOne := by
  classical
  let posInd : RealValuedBooleanFunction n :=
    fun x => if f x = SignBit.posOne then 1 else 0
  let negInd : RealValuedBooleanFunction n :=
    fun x => if f x = SignBit.negOne then 1 else 0
  have hpoint : signFunctionToReal f = fun x : SignCube n => posInd x - negInd x := by
    funext x
    rcases hfx : f x with _ | _ <;>
      simp [signFunctionToReal, posInd, negInd, SignBit.toReal, hfx]
  rw [cubeMean, hpoint, cubeExpectation_sub]
  rfl

/-- Distance to the constant `+1` function is the probability of value `-1`. -/
lemma signFunctionDistanceToConstant_posOne {n : Nat}
    (f : BooleanFunctionSign n) :
    signFunctionDistanceToConstant f SignBit.posOne =
      signValueProbability f SignBit.negOne := by
  classical
  rw [signFunctionDistanceToConstant, signFunctionDistance,
    signFunctionDisagreeProbability, signValueProbability, cubeProbability, cubeProbability]
  congr
  funext x
  cases f x <;> simp [constantSignFunction]

/-- Distance to the constant `-1` function is the probability of value `+1`. -/
lemma signFunctionDistanceToConstant_negOne {n : Nat}
    (f : BooleanFunctionSign n) :
    signFunctionDistanceToConstant f SignBit.negOne =
      signValueProbability f SignBit.posOne := by
  classical
  rw [signFunctionDistanceToConstant, signFunctionDistance,
    signFunctionDisagreeProbability, signValueProbability, cubeProbability, cubeProbability]
  congr
  funext x
  cases f x <;> simp [constantSignFunction]

/--
Fact 1.14.

For Boolean-valued functions, variance can be written using the mean or using
the two one-point probabilities.
-/
theorem fact_1_14 {n : Nat} (f : BooleanFunctionSign n) :
    cubeVariance (signFunctionToReal f) =
        1 - cubeMean (signFunctionToReal f) ^ 2 ∧
      cubeVariance (signFunctionToReal f) =
        4 * signValueProbability f SignBit.posOne *
          signValueProbability f SignBit.negOne := by
  constructor
  · exact fact_1_14_variance f
  · rw [fact_1_14_variance, cubeMean_signFunctionToReal]
    let p := signValueProbability f SignBit.posOne
    let q := signValueProbability f SignBit.negOne
    have hsum : p + q = 1 := by
      simpa [p, q] using signValueProbability_pos_add_neg f
    change 1 - (p - q) ^ 2 = 4 * p * q
    calc
      1 - (p - q) ^ 2 = (p + q) ^ 2 - (p - q) ^ 2 := by
        rw [hsum]
        ring
      _ = 4 * p * q := by
        ring

/--
Proposition 1.15.

If `epsilon` is the smaller distance from a Boolean-valued function to a
constant sign function, then `2 epsilon <= Var[f] <= 4 epsilon`.
-/
theorem proposition_1_15 {n : Nat} (f : BooleanFunctionSign n) :
    let ε := signFunctionDistanceFromConstant f
    2 * ε ≤ cubeVariance (signFunctionToReal f) ∧
      cubeVariance (signFunctionToReal f) ≤ 4 * ε := by
  classical
  let a := signFunctionDistanceToConstant f SignBit.posOne
  let b := signFunctionDistanceToConstant f SignBit.negOne
  have ha : 0 ≤ a := by
    simpa [a, signFunctionDistanceToConstant, signFunctionDistance,
      signFunctionDisagreeProbability] using
      (cubeProbability_nonneg
        (fun x : SignCube n => f x ≠ constantSignFunction SignBit.posOne x))
  have hb : 0 ≤ b := by
    simpa [b, signFunctionDistanceToConstant, signFunctionDistance,
      signFunctionDisagreeProbability] using
      (cubeProbability_nonneg
        (fun x : SignCube n => f x ≠ constantSignFunction SignBit.negOne x))
  have hsum : a + b = 1 := by
    dsimp [a, b]
    rw [signFunctionDistanceToConstant_posOne, signFunctionDistanceToConstant_negOne]
    rw [add_comm]
    exact signValueProbability_pos_add_neg f
  have hvar : cubeVariance (signFunctionToReal f) = 4 * a * b := by
    dsimp [a, b]
    rw [signFunctionDistanceToConstant_posOne, signFunctionDistanceToConstant_negOne]
    rw [(fact_1_14 f).2]
    ring
  dsimp [signFunctionDistanceFromConstant]
  change 2 * min a b ≤ cubeVariance (signFunctionToReal f) ∧
    cubeVariance (signFunctionToReal f) ≤ 4 * min a b
  rw [hvar]
  constructor
  · by_cases h : a ≤ b
    · rw [min_eq_left h]
      have hbhalf : (1 : Real) / 2 ≤ b := by linarith
      nlinarith [ha, hb, hbhalf]
    · have hb_le_a : b ≤ a := le_of_not_ge h
      rw [min_eq_right hb_le_a]
      have hahalf : (1 : Real) / 2 ≤ a := by linarith
      nlinarith [ha, hb, hahalf]
  · by_cases h : a ≤ b
    · rw [min_eq_left h]
      have hb_le_one : b ≤ 1 := by linarith
      nlinarith [ha, hb, hb_le_one]
    · have hb_le_a : b ≤ a := le_of_not_ge h
      rw [min_eq_right hb_le_a]
      have ha_le_one : a ≤ 1 := by linarith
      nlinarith [ha, hb, ha_le_one]

/-! ## Covariance -/

/-- Covariance equals `E[fg] - E[f] E[g]`. -/
lemma cubeCovariance_eq_expectation_mul_sub_mean_mul_mean {n : Nat}
    (f g : RealValuedBooleanFunction n) :
    cubeCovariance f g =
      cubeExpectation (fun x : SignCube n => f x * g x) - cubeMean f * cubeMean g := by
  classical
  let μ := cubeMean f
  let ν := cubeMean g
  have hμ : cubeExpectation f = μ := rfl
  have hν : cubeExpectation g = ν := rfl
  unfold cubeCovariance centeredFunction cubeInner
  change cubeExpectation (fun x : SignCube n => (f x - μ) * (g x - ν)) =
    cubeExpectation (fun x : SignCube n => f x * g x) - μ * ν
  have hpoint :
      (fun x : SignCube n => (f x - μ) * (g x - ν)) =
        (fun x : SignCube n => (f x * g x - μ * g x) - ν * f x + μ * ν) := by
    funext x
    ring
  rw [hpoint]
  rw [cubeExpectation_add, cubeExpectation_sub, cubeExpectation_sub,
    cubeExpectation_mul_const, cubeExpectation_mul_const, cubeExpectation_const, hμ, hν]
  ring

/--
Proposition 1.16, Fourier formula for covariance.
-/
theorem proposition_1_16_fourier {n : Nat}
    (f g : RealValuedBooleanFunction n) :
    cubeCovariance f g =
      Finset.univ.sum (fun S : CoordinateSet n =>
        if S = ∅ then 0 else functionFourierCoeff f S * functionFourierCoeff g S) := by
  classical
  rw [cubeCovariance]
  rw [plancherel_theorem (centeredFunction f) (centeredFunction g)]
  apply Finset.sum_congr rfl
  intro S _hS
  rw [functionFourierCoeff_centered f S, functionFourierCoeff_centered g S]
  by_cases hS : S = ∅ <;> simp [hS]

/--
Proposition 1.16.

Covariance has the centered-inner-product formula, the `E[fg] - E[f]E[g]`
formula, and the Fourier formula over nonempty sets.  The first formula is the
definition of `cubeCovariance`; the theorem records the two nontrivial
rewrites used in the book.
-/
theorem proposition_1_16 {n : Nat}
    (f g : RealValuedBooleanFunction n) :
    cubeCovariance f g =
        cubeExpectation (fun x : SignCube n => f x * g x) - cubeMean f * cubeMean g ∧
      cubeCovariance f g =
        Finset.univ.sum (fun S : CoordinateSet n =>
          if S = ∅ then 0 else functionFourierCoeff f S * functionFourierCoeff g S) := by
  exact ⟨cubeCovariance_eq_expectation_mul_sub_mean_mul_mean f g,
    proposition_1_16_fourier f g⟩

end BooleanFunctions
