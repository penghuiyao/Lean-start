import BooleanFunctions.«Thm Inf Core»
import BooleanFunctions.majority
import Mathlib.Tactic.Linarith

/-!
# Theorem 2.33

This file contains the proof of O'Donnell's Theorem 2.33.

The first-level Fourier sum is maximized exactly by majority functions.  In the
project's notation, a majority function is a sign-valued Boolean function which
agrees with the sign of the vote margin away from the tie layer; on ties it may
break arbitrarily.
-/

namespace BooleanFunctions

/-! ## Theorem 2.33: majority maximizes the degree-one Fourier sum -/

/--
Statement 2.33, first-level extremality form.

The uniqueness/equality case is recorded separately as
`theorem_2_33_equality_iff_isMajorityFunction` and
`theorem_2_33_unique_maximizers`.
-/
def Statement2_33 (n : Nat) : Prop :=
  ∀ f : BooleanFunctionSign n,
    degreeOneFourierSum f ≤
      degreeOneFourierSum (majorityFunction : BooleanFunctionSign n)

/-- Convert a sign bit to `Real` either directly or through `Int`. -/
@[simp]
lemma SignBit.intCast_toInt (b : SignBit) :
    ((b.toInt : Int) : Real) = b.toReal := by
  cases b <;> simp [SignBit.toInt, SignBit.toReal]

/-- The real vote margin is the cast of the integer vote margin. -/
lemma real_voteMargin_eq_intCast {n : Nat} (x : SignCube n) :
    Finset.univ.sum (fun i : Fin n => (x i).toReal) =
      ((signCubeSumInt x : Int) : Real) := by
  unfold signCubeSumInt
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  exact (SignBit.intCast_toInt (x i)).symm

/--
The degree-one Fourier sum is `E[f(x) * (x_1 + ... + x_n)]`.
-/
lemma degreeOneFourierSum_eq_cubeExpectation_voteMargin {n : Nat}
    (f : BooleanFunctionSign n) :
    degreeOneFourierSum f =
      cubeExpectation
        (fun x : SignCube n =>
          signFunctionToReal f x *
            Finset.univ.sum (fun i : Fin n => (x i).toReal)) := by
  unfold degreeOneFourierSum
  calc
    Finset.univ.sum
        (fun i : Fin n =>
          functionFourierCoeff (signFunctionToReal f) ({i} : CoordinateSet n))
        =
        Finset.univ.sum
          (fun i : Fin n =>
            cubeExpectation
              (fun x : SignCube n => (x i).toReal * signFunctionToReal f x)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [cubeExpectation_coord_mul_eq_fourierCoeff_singleton]
    _ =
        Finset.univ.sum
          (fun i : Fin n =>
            cubeExpectation
              (fun x : SignCube n => signFunctionToReal f x * (x i).toReal)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      congr
      funext x
      ring
    _ =
        cubeExpectation
          (fun x : SignCube n =>
            Finset.univ.sum
              (fun i : Fin n => signFunctionToReal f x * (x i).toReal)) := by
      rw [cubeExpectation_finset_sum]
    _ =
        cubeExpectation
          (fun x : SignCube n =>
            signFunctionToReal f x *
              Finset.univ.sum (fun i : Fin n => (x i).toReal)) := by
      congr
      funext x
      rw [Finset.mul_sum]

/-- A sign-valued multiplier is bounded by absolute value. -/
lemma sign_mul_le_abs (a : SignBit) (t : Real) :
    a.toReal * t ≤ |t| := by
  cases a
  · simpa [SignBit.toReal] using neg_le_abs t
  · simpa [SignBit.toReal] using le_abs_self t

/-- Equality in the positive-margin case forces the sign to be `+1`. -/
lemma sign_eq_posOne_of_mul_eq_abs_of_pos {a : SignBit} {t : Real}
    (h : a.toReal * t = |t|) (ht : 0 < t) :
    a = SignBit.posOne := by
  cases a
  · have habs : |t| = t := abs_of_pos ht
    simp [SignBit.toReal, habs] at h
    linarith
  · rfl

/-- Equality in the negative-margin case forces the sign to be `-1`. -/
lemma sign_eq_negOne_of_mul_eq_abs_of_neg {a : SignBit} {t : Real}
    (h : a.toReal * t = |t|) (ht : t < 0) :
    a = SignBit.negOne := by
  cases a
  · rfl
  · have habs : |t| = -t := abs_of_neg ht
    simp [SignBit.toReal, habs] at h
    linarith

/-- Majority attains the pointwise upper bound in Theorem 2.33. -/
lemma majority_voteMargin_eq_abs {n : Nat} (x : SignCube n) :
    signFunctionToReal (majorityFunction : BooleanFunctionSign n) x *
        Finset.univ.sum (fun i : Fin n => (x i).toReal) =
      |Finset.univ.sum (fun i : Fin n => (x i).toReal)| := by
  unfold signFunctionToReal majorityFunction signOfIntWithPositiveTie
  rw [real_voteMargin_eq_intCast x]
  by_cases hzero : signCubeSumInt x = 0
  · simp [hzero]
  · by_cases hpos : 0 < signCubeSumInt x
    · have hnonneg : 0 ≤ signCubeSumInt x := le_of_lt hpos
      have hreal_nonneg : 0 ≤ ((signCubeSumInt x : Int) : Real) := by
        exact_mod_cast hnonneg
      simp [hnonneg, abs_of_nonneg hreal_nonneg, SignBit.toReal]
    · have hneg : signCubeSumInt x < 0 := by
        omega
      have hnot_nonneg : ¬ 0 ≤ signCubeSumInt x := not_le.mpr hneg
      have hreal_nonpos : ((signCubeSumInt x : Int) : Real) ≤ 0 := by
        exact_mod_cast le_of_lt hneg
      simp [hnot_nonneg, abs_of_nonpos hreal_nonpos, SignBit.toReal]

/--
If two cube functions satisfy `f <= g` pointwise and have the same expectation,
then they are equal pointwise.  This is the finite-cube equality case used in
the uniqueness proof.
-/
lemma cubeExpectation_eq_of_pointwise_le_eq {n : Nat}
    {f g : RealValuedBooleanFunction n}
    (hle : ∀ x : SignCube n, f x ≤ g x)
    (hE : cubeExpectation f = cubeExpectation g) :
    ∀ x : SignCube n, f x = g x := by
  classical
  have hscale_ne : ((2 : Real) ^ n)⁻¹ ≠ 0 :=
    inv_ne_zero (pow_ne_zero n (by norm_num : (2 : Real) ≠ 0))
  have hsum_eq :
      Finset.univ.sum (fun x : SignCube n => f x) =
        Finset.univ.sum (fun x : SignCube n => g x) := by
    unfold cubeExpectation at hE
    exact mul_left_cancel₀ hscale_ne hE
  have hdiff_sum :
      Finset.univ.sum (fun x : SignCube n => g x - f x) = 0 := by
    rw [Finset.sum_sub_distrib, hsum_eq]
    ring
  have hdiff_zero :
      ∀ x ∈ (Finset.univ : Finset (SignCube n)), g x - f x = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun x _hx => sub_nonneg.mpr (hle x))).mp hdiff_sum
  intro x
  have hx := hdiff_zero x (Finset.mem_univ x)
  linarith

/--
Theorem 2.33, extremal inequality: among all Boolean functions,
majority maximizes the sum of the degree-one Fourier coefficients.
-/
theorem theorem_2_33_degreeOneFourierSum_le_majority {n : Nat}
    (f : BooleanFunctionSign n) :
    degreeOneFourierSum f ≤
      degreeOneFourierSum (majorityFunction : BooleanFunctionSign n) := by
  rw [degreeOneFourierSum_eq_cubeExpectation_voteMargin f]
  rw [degreeOneFourierSum_eq_cubeExpectation_voteMargin
    (majorityFunction : BooleanFunctionSign n)]
  unfold cubeExpectation
  have hpoint :
      ∀ x : SignCube n,
        signFunctionToReal f x *
            Finset.univ.sum (fun i : Fin n => (x i).toReal) ≤
          signFunctionToReal (majorityFunction : BooleanFunctionSign n) x *
            Finset.univ.sum (fun i : Fin n => (x i).toReal) := by
    intro x
    calc
      signFunctionToReal f x *
          Finset.univ.sum (fun i : Fin n => (x i).toReal)
          ≤ |Finset.univ.sum (fun i : Fin n => (x i).toReal)| := by
        exact sign_mul_le_abs (f x) _
      _ =
          signFunctionToReal (majorityFunction : BooleanFunctionSign n) x *
            Finset.univ.sum (fun i : Fin n => (x i).toReal) := by
        rw [majority_voteMargin_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun x _hx => hpoint x))
    (inv_nonneg.mpr (pow_nonneg (by norm_num : (0 : Real) ≤ 2) n))

/-- The project statement `Statement2_33` upgraded to a proved theorem. -/
theorem theorem_2_33 (n : Nat) : Statement2_33 n := by
  intro f
  exact theorem_2_33_degreeOneFourierSum_le_majority f

/--
Equality in the global degree-one bound implies equality in the pointwise
absolute-value bound at every cube point.
-/
lemma pointwise_extremal_of_degreeOneFourierSum_eq_majority {n : Nat}
    {f : BooleanFunctionSign n}
    (h :
      degreeOneFourierSum f =
        degreeOneFourierSum (majorityFunction : BooleanFunctionSign n))
    (x : SignCube n) :
    signFunctionToReal f x *
        Finset.univ.sum (fun i : Fin n => (x i).toReal) =
      |Finset.univ.sum (fun i : Fin n => (x i).toReal)| := by
  have hE := h
  rw [degreeOneFourierSum_eq_cubeExpectation_voteMargin f,
    degreeOneFourierSum_eq_cubeExpectation_voteMargin
      (majorityFunction : BooleanFunctionSign n)] at hE
  have hmajority :
      (fun x : SignCube n =>
        signFunctionToReal (majorityFunction : BooleanFunctionSign n) x *
          Finset.univ.sum (fun i : Fin n => (x i).toReal)) =
        (fun x : SignCube n =>
          |Finset.univ.sum (fun i : Fin n => (x i).toReal)|) := by
    funext x
    exact majority_voteMargin_eq_abs x
  rw [hmajority] at hE
  exact cubeExpectation_eq_of_pointwise_le_eq
    (fun x => sign_mul_le_abs (f x)
      (Finset.univ.sum (fun i : Fin n => (x i).toReal))) hE x

/--
At a non-tie point, equality in the pointwise bound forces `f` to agree with
the majority rule.
-/
lemma eq_majority_value_of_pointwise_extremal_at_non_tie {n : Nat}
    {f : BooleanFunctionSign n} {x : SignCube n}
    (h :
      signFunctionToReal f x *
          Finset.univ.sum (fun i : Fin n => (x i).toReal) =
        |Finset.univ.sum (fun i : Fin n => (x i).toReal)|)
    (hnotTie : signCubeSumInt x ≠ 0) :
    f x =
      if 0 < signCubeSumInt x then SignBit.posOne else SignBit.negOne := by
  have hsign :
      (f x).toReal * Finset.univ.sum (fun i : Fin n => (x i).toReal) =
        |Finset.univ.sum (fun i : Fin n => (x i).toReal)| := by
    simpa [signFunctionToReal] using h
  by_cases hpos : 0 < signCubeSumInt x
  · have ht :
        0 < Finset.univ.sum (fun i : Fin n => (x i).toReal) := by
      rw [real_voteMargin_eq_intCast x]
      exact_mod_cast hpos
    have hfpos := sign_eq_posOne_of_mul_eq_abs_of_pos hsign ht
    simp [hpos, hfpos]
  · have hneg : signCubeSumInt x < 0 := by
      omega
    have ht :
        Finset.univ.sum (fun i : Fin n => (x i).toReal) < 0 := by
      rw [real_voteMargin_eq_intCast x]
      exact_mod_cast hneg
    have hfneg := sign_eq_negOne_of_mul_eq_abs_of_neg hsign ht
    simp [hpos, hfneg]

/--
The equality case in Theorem 2.33: if `f` reaches the majority value of the
degree-one Fourier sum, then `f` is a majority function.
-/
theorem isMajorityFunction_of_degreeOneFourierSum_eq_majority {n : Nat}
    {f : BooleanFunctionSign n}
    (h :
      degreeOneFourierSum f =
        degreeOneFourierSum (majorityFunction : BooleanFunctionSign n)) :
    IsMajorityFunction f := by
  intro x hnotTie
  exact eq_majority_value_of_pointwise_extremal_at_non_tie
    (pointwise_extremal_of_degreeOneFourierSum_eq_majority h x) hnotTie

/-- Away from ties, any majority function agrees with the standard majority rule. -/
lemma eq_majorityFunction_of_IsMajorityFunction {n : Nat}
    {f : BooleanFunctionSign n} (hf : IsMajorityFunction f)
    {x : SignCube n} (hnotTie : signCubeSumInt x ≠ 0) :
    f x = majorityFunction x := by
  unfold majorityFunction signOfIntWithPositiveTie
  rw [hf x hnotTie]
  by_cases hpos : 0 < signCubeSumInt x
  · have hnonneg : 0 ≤ signCubeSumInt x := le_of_lt hpos
    simp [hpos, hnonneg]
  · have hneg : signCubeSumInt x < 0 := by
      omega
    have hnot_nonneg : ¬ 0 ≤ signCubeSumInt x := not_le.mpr hneg
    simp [hpos, hnot_nonneg]

/--
Conversely, any majority function attains the same degree-one Fourier sum as
the standard majority rule.  The tie layer contributes zero vote margin.
-/
theorem degreeOneFourierSum_eq_majority_of_IsMajorityFunction {n : Nat}
    {f : BooleanFunctionSign n} (hf : IsMajorityFunction f) :
    degreeOneFourierSum f =
      degreeOneFourierSum (majorityFunction : BooleanFunctionSign n) := by
  rw [degreeOneFourierSum_eq_cubeExpectation_voteMargin f]
  rw [degreeOneFourierSum_eq_cubeExpectation_voteMargin
    (majorityFunction : BooleanFunctionSign n)]
  congr
  funext x
  by_cases hzero : signCubeSumInt x = 0
  · have hmargin :
        Finset.univ.sum (fun i : Fin n => (x i).toReal) = 0 := by
      rw [real_voteMargin_eq_intCast x, hzero]
      norm_num
    simp [hmargin]
  · have hfx : f x = majorityFunction x :=
      eq_majorityFunction_of_IsMajorityFunction hf hzero
    have hreal :
        signFunctionToReal f x =
          signFunctionToReal (majorityFunction : BooleanFunctionSign n) x := by
      unfold signFunctionToReal
      rw [hfx]
    rw [hreal]

/--
The equality case in Theorem 2.33: equality holds exactly for majority
functions.
-/
theorem theorem_2_33_equality_iff_isMajorityFunction {n : Nat}
    (f : BooleanFunctionSign n) :
    degreeOneFourierSum f =
        degreeOneFourierSum (majorityFunction : BooleanFunctionSign n) ↔
      IsMajorityFunction f := by
  constructor
  · exact isMajorityFunction_of_degreeOneFourierSum_eq_majority
  · intro hf
    exact degreeOneFourierSum_eq_majority_of_IsMajorityFunction hf

/--
The unique maximizers of the degree-one Fourier sum are exactly the majority
functions.
-/
theorem theorem_2_33_unique_maximizers {n : Nat}
    (f : BooleanFunctionSign n) :
    (∀ g : BooleanFunctionSign n, degreeOneFourierSum g ≤ degreeOneFourierSum f) ↔
      IsMajorityFunction f := by
  constructor
  · intro hmax
    have hle :
        degreeOneFourierSum f ≤
          degreeOneFourierSum (majorityFunction : BooleanFunctionSign n) :=
      theorem_2_33_degreeOneFourierSum_le_majority f
    have hge :
        degreeOneFourierSum (majorityFunction : BooleanFunctionSign n) ≤
          degreeOneFourierSum f :=
      hmax (majorityFunction : BooleanFunctionSign n)
    exact isMajorityFunction_of_degreeOneFourierSum_eq_majority
      (le_antisymm hle hge)
  · intro hf g
    calc
      degreeOneFourierSum g
          ≤ degreeOneFourierSum (majorityFunction : BooleanFunctionSign n) :=
        theorem_2_33_degreeOneFourierSum_le_majority g
      _ = degreeOneFourierSum f :=
        (degreeOneFourierSum_eq_majority_of_IsMajorityFunction hf).symm

/-- Majority is monotone on the sign cube. -/
lemma majorityFunction_monotone {n : Nat} :
    IsMonotoneSignFunction (majorityFunction : BooleanFunctionSign n) := by
  intro x y hxy
  unfold majorityFunction signOfIntWithPositiveTie
  have hsum :
      signCubeSumInt x ≤ signCubeSumInt y := by
    unfold signCubeSumInt
    exact Finset.sum_le_sum (fun i _hi => hxy i)
  by_cases hy : 0 ≤ signCubeSumInt y
  · by_cases hx : 0 ≤ signCubeSumInt x
    · simp [hx, hy, SignBit.toInt]
    · simp [hx, hy, SignBit.toInt]
  · have hx : ¬ 0 ≤ signCubeSumInt x := by
      exact fun hx => hy (le_trans hx hsum)
    simp [hx, hy, SignBit.toInt]

/--
Theorem 2.33, total-influence corollary for monotone functions:
`I[f] <= I[Maj_n]`.
-/
theorem theorem_2_33_totalInfluence_le_majority_of_monotone {n : Nat}
    (f : BooleanFunctionSign n) (hf : IsMonotoneSignFunction f) :
    totalInfluence (signFunctionToReal f) ≤
      totalInfluence
        (signFunctionToReal (majorityFunction : BooleanFunctionSign n)) := by
  rw [proposition_2_31 f hf]
  rw [proposition_2_31
    (majorityFunction : BooleanFunctionSign n) majorityFunction_monotone]
  exact theorem_2_33_degreeOneFourierSum_le_majority f

/--
Theorem 2.33, odd-dimensional quantitative form.  This is the point where the
proof calls Exercise 2.22 from `majority.lean`.
-/
theorem theorem_2_33_totalInfluence_le_majorityOddFormula
    (m : Nat) (f : BooleanFunctionSign (2 * m + 1))
    (hf : IsMonotoneSignFunction f) :
    totalInfluence (signFunctionToReal f) ≤
      majorityTotalInfluenceOddFormula m := by
  calc
    totalInfluence (signFunctionToReal f)
        ≤ totalInfluence
            (signFunctionToReal
              (majorityFunction : BooleanFunctionSign (2 * m + 1))) :=
      theorem_2_33_totalInfluence_le_majority_of_monotone f hf
    _ = majorityTotalInfluenceOddFormula m :=
      exercise_2_22e_totalInfluence_formula_odd m

/--
The asymptotic estimate for the majority term in Theorem 2.33, imported from
Exercise 2.22(e) in `majority.lean`.
-/
theorem theorem_2_33_majority_totalInfluence_asymptotic_odd :
    Asymptotics.IsBigO Filter.atTop
      (fun m : Nat =>
        totalInfluence
            (signFunctionToReal
              (majorityFunction : BooleanFunctionSign (2 * m + 1))) -
          Real.sqrt (2 / Real.pi) *
            Real.sqrt (((2 * m + 1 : Nat) : Real)))
      (fun m : Nat =>
        1 / Real.sqrt (((2 * m + 1 : Nat) : Real))) :=
  exercise_2_22e_totalInfluence_asymptotic_odd

end BooleanFunctions
