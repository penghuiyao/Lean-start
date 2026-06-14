import BooleanFunctions.Poincare
import BooleanFunctions.«Thm sec 1_4»
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.NormNum

/-!
# Theorem 2.39

This file develops O'Donnell's Theorem 2.39, the edge-isoperimetric
inequality on the Boolean cube.

The first lemmas record the part of the argument that comes directly from the
Poincare inequality already proved in `Poincare.lean`: for a sign-valued
Boolean function, total influence controls the Boolean variance
`4 * Pr[f = 1] * Pr[f = -1]`.
-/

namespace BooleanFunctions

/-! ## Last-coordinate slicing -/

lemma fintype_sum_signBit {M : Type} [AddCommMonoid M] (f : SignBit → M) :
    (∑ b : SignBit, f b) = f SignBit.negOne + f SignBit.posOne := by
  classical
  rw [show (Finset.univ : Finset SignBit) =
      {SignBit.negOne, SignBit.posOne} by
    ext b
    cases b <;> simp]
  simp

/-- The slice of a Boolean function obtained by fixing the last coordinate. -/
def lastSlice {n : Nat} (f : BooleanFunctionSign (n + 1))
    (b : SignBit) : BooleanFunctionSign n :=
  fun x => f (Fin.snoc x b)

@[simp]
lemma setCoordSign_snoc_castSucc {n : Nat} (x : SignCube n)
    (b c : SignBit) (i : Fin n) :
    setCoordSign (Fin.snoc x b) i.castSucc c =
      Fin.snoc (setCoordSign x i c) b := by
  ext j
  induction j using Fin.lastCases with
  | last =>
      have h : Fin.last n ≠ i.castSucc := (Fin.castSucc_ne_last i).symm
      simp [setCoordSign, h]
  | cast j =>
      by_cases hji : j = i <;> simp [setCoordSign, hji]

@[simp]
lemma setCoordSign_snoc_last {n : Nat} (x : SignCube n)
    (b c : SignBit) :
    setCoordSign (Fin.snoc x b) (Fin.last n) c = Fin.snoc x c := by
  ext j
  induction j using Fin.lastCases with
  | last =>
      simp [setCoordSign]
  | cast j =>
      simp [setCoordSign]

lemma isPivotal_snoc_castSucc {n : Nat}
    (f : BooleanFunctionSign (n + 1)) (x : SignCube n)
    (b : SignBit) (i : Fin n) :
    IsPivotal f i.castSucc (Fin.snoc x b) ↔
      IsPivotal (lastSlice f b) i x := by
  unfold IsPivotal flipCoordSign lastSlice
  simp

lemma isPivotal_snoc_last {n : Nat}
    (f : BooleanFunctionSign (n + 1)) (x : SignCube n)
    (b : SignBit) :
    IsPivotal f (Fin.last n) (Fin.snoc x b) ↔
      lastSlice f SignBit.negOne x ≠ lastSlice f SignBit.posOne x := by
  unfold IsPivotal flipCoordSign lastSlice
  cases b <;> simp [negSignBit, ne_comm]

/-- Uniform expectation on the `(n+1)`-cube splits as the average of the two last-coordinate slices. -/
lemma cubeExpectation_snoc {n : Nat}
    (g : RealValuedBooleanFunction (n + 1)) :
    cubeExpectation g =
      (cubeExpectation (fun x : SignCube n => g (Fin.snoc x SignBit.negOne)) +
          cubeExpectation (fun x : SignCube n => g (Fin.snoc x SignBit.posOne))) / 2 := by
  classical
  unfold cubeExpectation
  have hsum :
      (∑ y : SignCube (n + 1), g y) =
        ∑ p : SignBit × SignCube n, g (Fin.snoc p.2 p.1) := by
    symm
    exact Fintype.sum_equiv
      (Fin.snocEquiv (fun _ : Fin (n + 1) => SignBit))
      (fun p : SignBit × SignCube n => g (Fin.snoc p.2 p.1))
      (fun y : SignCube (n + 1) => g y)
      (by intro p; rfl)
  rw [hsum, Fintype.sum_prod_type]
  rw [fintype_sum_signBit]
  rw [pow_succ]
  ring

lemma cubeExpectation_mono {n : Nat}
    {g h : RealValuedBooleanFunction n}
    (hpoint : ∀ x : SignCube n, g x ≤ h x) :
    cubeExpectation g ≤ cubeExpectation h := by
  unfold cubeExpectation
  apply mul_le_mul_of_nonneg_left
  · exact Finset.sum_le_sum (fun x _hx => hpoint x)
  · exact inv_nonneg.mpr (pow_nonneg (by norm_num) n)

lemma signValueProbability_lastSlice {n : Nat}
    (f : BooleanFunctionSign (n + 1)) (a : SignBit) :
    signValueProbability f a =
      (signValueProbability (lastSlice f SignBit.negOne) a +
          signValueProbability (lastSlice f SignBit.posOne) a) / 2 := by
  classical
  unfold signValueProbability cubeProbability
  rw [cubeExpectation_snoc]
  rfl

/-- Probability that the two last-coordinate slices disagree. -/
noncomputable def lastSliceDisagreementProbability {n : Nat}
    (f : BooleanFunctionSign (n + 1)) : Real :=
  cubeProbability (fun x : SignCube n =>
    lastSlice f SignBit.negOne x ≠ lastSlice f SignBit.posOne x)

lemma signValueProbability_slice_sub_le_disagreement {n : Nat}
    (f : BooleanFunctionSign (n + 1)) :
    signValueProbability (lastSlice f SignBit.negOne) SignBit.negOne -
        signValueProbability (lastSlice f SignBit.posOne) SignBit.negOne ≤
      lastSliceDisagreementProbability f := by
  classical
  unfold signValueProbability cubeProbability lastSliceDisagreementProbability
  rw [← cubeExpectation_sub]
  apply cubeExpectation_mono
  intro x
  cases hneg : lastSlice f SignBit.negOne x <;>
    cases hpos : lastSlice f SignBit.posOne x <;>
    simp [hneg, hpos]

lemma signValueProbability_slice_sub_le_disagreement' {n : Nat}
    (f : BooleanFunctionSign (n + 1)) :
    signValueProbability (lastSlice f SignBit.posOne) SignBit.negOne -
        signValueProbability (lastSlice f SignBit.negOne) SignBit.negOne ≤
      lastSliceDisagreementProbability f := by
  classical
  unfold signValueProbability cubeProbability lastSliceDisagreementProbability
  rw [← cubeExpectation_sub]
  apply cubeExpectation_mono
  intro x
  cases hneg : lastSlice f SignBit.negOne x <;>
    cases hpos : lastSlice f SignBit.posOne x <;>
    simp [hneg, hpos]

lemma signValueProbability_slice_abs_sub_le_disagreement {n : Nat}
    (f : BooleanFunctionSign (n + 1)) :
    |signValueProbability (lastSlice f SignBit.negOne) SignBit.negOne -
        signValueProbability (lastSlice f SignBit.posOne) SignBit.negOne| ≤
      lastSliceDisagreementProbability f := by
  rw [abs_sub_le_iff]
  exact ⟨signValueProbability_slice_sub_le_disagreement f,
    signValueProbability_slice_sub_le_disagreement' f⟩

lemma signFunction_discreteDerivative_last_snoc_sq {n : Nat}
    (f : BooleanFunctionSign (n + 1)) (x : SignCube n) (b : SignBit) :
    discreteDerivative (signFunctionToReal f) (Fin.last n) (Fin.snoc x b) ^ 2 =
      if lastSlice f SignBit.negOne x ≠ lastSlice f SignBit.posOne x then
        (1 : Real)
      else
        0 := by
  classical
  simpa [isPivotal_snoc_last] using
    signFunction_discreteDerivative_sq_eq_pivotalIndicator f (Fin.last n) (Fin.snoc x b)

lemma influence_last_eq_disagreement {n : Nat}
    (f : BooleanFunctionSign (n + 1)) :
    influence (signFunctionToReal f) (Fin.last n) =
      lastSliceDisagreementProbability f := by
  rw [influence_eq_derivativeInfluence]
  unfold derivativeInfluence lastSliceDisagreementProbability cubeProbability
  rw [cubeExpectation_snoc]
  have hneg :
      cubeExpectation
          (fun x : SignCube n =>
            discreteDerivative (signFunctionToReal f) (Fin.last n)
              (Fin.snoc x SignBit.negOne) ^ 2) =
        cubeExpectation
          (fun x : SignCube n =>
            if lastSlice f SignBit.negOne x ≠ lastSlice f SignBit.posOne x then
              (1 : Real)
            else
              0) := by
    congr
    funext x
    rw [signFunction_discreteDerivative_last_snoc_sq]
  have hpos :
      cubeExpectation
          (fun x : SignCube n =>
            discreteDerivative (signFunctionToReal f) (Fin.last n)
              (Fin.snoc x SignBit.posOne) ^ 2) =
        cubeExpectation
          (fun x : SignCube n =>
            if lastSlice f SignBit.negOne x ≠ lastSlice f SignBit.posOne x then
              (1 : Real)
            else
              0) := by
    congr
    funext x
    rw [signFunction_discreteDerivative_last_snoc_sq]
  rw [hneg, hpos]
  ring

lemma discreteDerivative_castSucc_snoc {n : Nat}
    (f : BooleanFunctionSign (n + 1)) (x : SignCube n)
    (b : SignBit) (i : Fin n) :
    discreteDerivative (signFunctionToReal f) i.castSucc (Fin.snoc x b) =
      discreteDerivative (signFunctionToReal (lastSlice f b)) i x := by
  unfold discreteDerivative signFunctionToReal lastSlice
  simp

lemma influence_castSucc_eq_average_slices {n : Nat}
    (f : BooleanFunctionSign (n + 1)) (i : Fin n) :
    influence (signFunctionToReal f) i.castSucc =
      (influence (signFunctionToReal (lastSlice f SignBit.negOne)) i +
          influence (signFunctionToReal (lastSlice f SignBit.posOne)) i) / 2 := by
  rw [influence_eq_derivativeInfluence]
  rw [influence_eq_derivativeInfluence]
  rw [influence_eq_derivativeInfluence]
  unfold derivativeInfluence
  rw [cubeExpectation_snoc]
  have hneg :
      cubeExpectation
          (fun x : SignCube n =>
            discreteDerivative (signFunctionToReal f) i.castSucc
              (Fin.snoc x SignBit.negOne) ^ 2) =
        cubeExpectation
          (fun x : SignCube n =>
            discreteDerivative
              (signFunctionToReal (lastSlice f SignBit.negOne)) i x ^ 2) := by
    congr
    funext x
    rw [discreteDerivative_castSucc_snoc]
  have hpos :
      cubeExpectation
          (fun x : SignCube n =>
            discreteDerivative (signFunctionToReal f) i.castSucc
              (Fin.snoc x SignBit.posOne) ^ 2) =
        cubeExpectation
          (fun x : SignCube n =>
            discreteDerivative
              (signFunctionToReal (lastSlice f SignBit.posOne)) i x ^ 2) := by
    congr
    funext x
    rw [discreteDerivative_castSucc_snoc]
  rw [hneg, hpos]

lemma totalInfluence_succ_eq_average_slices_add_disagreement {n : Nat}
    (f : BooleanFunctionSign (n + 1)) :
    totalInfluence (signFunctionToReal f) =
      (totalInfluence (signFunctionToReal (lastSlice f SignBit.negOne)) +
          totalInfluence (signFunctionToReal (lastSlice f SignBit.posOne))) / 2 +
        lastSliceDisagreementProbability f := by
  unfold totalInfluence
  rw [Fin.sum_univ_castSucc]
  rw [influence_last_eq_disagreement]
  have hsum :
      (∑ i : Fin n, influence (signFunctionToReal f) i.castSucc) =
        ((∑ i : Fin n,
            influence (signFunctionToReal (lastSlice f SignBit.negOne)) i) +
          (∑ i : Fin n,
            influence (signFunctionToReal (lastSlice f SignBit.posOne)) i)) / 2 := by
    calc
      (∑ i : Fin n, influence (signFunctionToReal f) i.castSucc)
          =
          ∑ i : Fin n,
            (influence (signFunctionToReal (lastSlice f SignBit.negOne)) i +
              influence (signFunctionToReal (lastSlice f SignBit.posOne)) i) / 2 := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [influence_castSucc_eq_average_slices]
      _ =
          ((∑ i : Fin n,
              influence (signFunctionToReal (lastSlice f SignBit.negOne)) i) +
            (∑ i : Fin n,
              influence (signFunctionToReal (lastSlice f SignBit.posOne)) i)) / 2 := by
        simp_rw [div_eq_mul_inv]
        rw [← Finset.sum_mul]
        rw [Finset.sum_add_distrib]
  rw [hsum]

/-! ## Poincare consequences for Boolean-valued functions -/

/--
The Poincare inequality specialized to sign-valued Boolean functions.

This is the reusable bridge from `Poincare.lean`: the analytic variance of the
real-valued version of a Boolean function is bounded by its total influence.
-/
theorem poincare_inequality_sign {n : Nat} (f : BooleanFunctionSign n) :
    cubeVariance (signFunctionToReal f) ≤
      totalInfluence (signFunctionToReal f) := by
  exact poincare_inequality_from_cubeVariance_formula
    (signFunctionToReal f)
    (cubeVariance_eq_sum_nonempty_fourierWeight (signFunctionToReal f))

/--
For a sign-valued Boolean function, Poincare gives the usual variance lower
bound on total influence, written in the probability notation of Fact 1.14.
-/
theorem totalInfluence_ge_boolean_variance {n : Nat}
    (f : BooleanFunctionSign n) :
    4 * signValueProbability f SignBit.posOne *
        signValueProbability f SignBit.negOne ≤
      totalInfluence (signFunctionToReal f) := by
  have hpoincare := poincare_inequality_sign f
  have hvar := (fact_1_14 f).2
  rw [hvar] at hpoincare
  exact hpoincare

/-! ## Theorem 2.39 -/

/-! ### Negating a Boolean function and minority probability -/

/-- The pointwise negation of a sign-valued Boolean function. -/
def negateSignFunction {n : Nat} (f : BooleanFunctionSign n) : BooleanFunctionSign n :=
  fun x => negSignBit (f x)

/--
The minority probability of a sign-valued Boolean function:
the smaller of `Pr[f = -1]` and `Pr[f = 1]`.
-/
noncomputable def minorityProbability {n : Nat} (f : BooleanFunctionSign n) : Real :=
  min (signValueProbability f SignBit.negOne)
    (signValueProbability f SignBit.posOne)

lemma signValueProbability_negate_negOne {n : Nat}
    (f : BooleanFunctionSign n) :
    signValueProbability (negateSignFunction f) SignBit.negOne =
      signValueProbability f SignBit.posOne := by
  classical
  unfold signValueProbability cubeProbability cubeExpectation negateSignFunction
  congr 1
  apply Finset.sum_congr rfl
  intro x _hx
  cases h : f x <;> simp [h, negSignBit]

lemma signValueProbability_negate_posOne {n : Nat}
    (f : BooleanFunctionSign n) :
    signValueProbability (negateSignFunction f) SignBit.posOne =
      signValueProbability f SignBit.negOne := by
  classical
  unfold signValueProbability cubeProbability cubeExpectation negateSignFunction
  congr 1
  apply Finset.sum_congr rfl
  intro x _hx
  cases h : f x <;> simp [h, negSignBit]

lemma minorityProbability_nonneg {n : Nat}
    (f : BooleanFunctionSign n) :
    0 ≤ minorityProbability f := by
  unfold minorityProbability
  exact le_min (cubeProbability_nonneg _) (cubeProbability_nonneg _)

lemma minorityProbability_le_half {n : Nat}
    (f : BooleanFunctionSign n) :
    minorityProbability f ≤ (1 : Real) / 2 := by
  classical
  unfold minorityProbability
  have hsum := signValueProbability_pos_add_neg f
  by_cases hle :
      signValueProbability f SignBit.negOne ≤
        signValueProbability f SignBit.posOne
  · rw [min_eq_left hle]
    linarith
  · have hle' :
        signValueProbability f SignBit.posOne ≤
          signValueProbability f SignBit.negOne := le_of_not_ge hle
    rw [min_eq_right hle']
    linarith

lemma signValueProbability_le_one {n : Nat}
    (f : BooleanFunctionSign n) (a : SignBit) :
    signValueProbability f a ≤ 1 := by
  have hsum := signValueProbability_pos_add_neg f
  cases a
  · have hpos :
        0 ≤ signValueProbability f SignBit.posOne :=
      cubeProbability_nonneg _
    linarith
  · have hneg :
        0 ≤ signValueProbability f SignBit.negOne :=
      cubeProbability_nonneg _
    linarith

lemma minorityProbability_eq_negOne_of_le_half {n : Nat}
    {f : BooleanFunctionSign n}
    (h : signValueProbability f SignBit.negOne ≤ (1 : Real) / 2) :
    minorityProbability f =
      signValueProbability f SignBit.negOne := by
  unfold minorityProbability
  have hsum := signValueProbability_pos_add_neg f
  have hle :
      signValueProbability f SignBit.negOne ≤
        signValueProbability f SignBit.posOne := by
    linarith
  exact min_eq_left hle

lemma minorityProbability_eq_posOne_of_le_half {n : Nat}
    {f : BooleanFunctionSign n}
    (h : signValueProbability f SignBit.posOne ≤ (1 : Real) / 2) :
    minorityProbability f =
      signValueProbability f SignBit.posOne := by
  unfold minorityProbability
  have hsum := signValueProbability_pos_add_neg f
  have hle :
      signValueProbability f SignBit.posOne ≤
        signValueProbability f SignBit.negOne := by
    linarith
  exact min_eq_right hle

lemma minorityProbability_negate {n : Nat}
    (f : BooleanFunctionSign n) :
    minorityProbability (negateSignFunction f) =
      minorityProbability f := by
  unfold minorityProbability
  rw [signValueProbability_negate_negOne,
    signValueProbability_negate_posOne]
  exact min_comm _ _

lemma signFunctionToReal_negate {n : Nat}
    (f : BooleanFunctionSign n) :
    signFunctionToReal (negateSignFunction f) =
      fun x => - signFunctionToReal f x := by
  funext x
  cases h : f x <;> simp [signFunctionToReal, negateSignFunction, negSignBit, h,
    SignBit.toReal]

lemma discreteDerivative_neg {n : Nat}
    (f : RealValuedBooleanFunction n) (i : Fin n) (x : SignCube n) :
    discreteDerivative (fun y => - f y) i x =
      - discreteDerivative f i x := by
  unfold discreteDerivative
  ring

lemma derivativeInfluence_neg {n : Nat}
    (f : RealValuedBooleanFunction n) (i : Fin n) :
    derivativeInfluence (fun x => - f x) i =
      derivativeInfluence f i := by
  unfold derivativeInfluence
  congr 1
  funext x
  rw [discreteDerivative_neg]
  ring

lemma influence_neg {n : Nat}
    (f : RealValuedBooleanFunction n) (i : Fin n) :
    influence (fun x => - f x) i =
      influence f i := by
  rw [influence_eq_derivativeInfluence (fun x => - f x) i,
    influence_eq_derivativeInfluence f i]
  exact derivativeInfluence_neg f i

lemma totalInfluence_neg {n : Nat}
    (f : RealValuedBooleanFunction n) :
    totalInfluence (fun x => - f x) =
      totalInfluence f := by
  unfold totalInfluence
  apply Finset.sum_congr rfl
  intro i _hi
  exact influence_neg f i

lemma totalInfluence_negateSignFunction {n : Nat}
    (f : BooleanFunctionSign n) :
    totalInfluence (signFunctionToReal (negateSignFunction f)) =
      totalInfluence (signFunctionToReal f) := by
  rw [signFunctionToReal_negate]
  exact totalInfluence_neg (signFunctionToReal f)

/-! ### The real-variable induction inequality

The sharp edge-isoperimetric induction step reduces to the following
one-dimensional inequality for

`φ α = 2 * α * log₂ (1 / α)`.

The proof uses mathlib's binary entropy API: `Real.strictConcave_binEntropy`
and Jensen's inequality give the chord lower bound for `binEntropy`, and
`Real.negMulLog_mul` turns that statement into the midpoint inequality for
`φ`.
-/

/--
Binary entropy lies above the chord joining `(1/2, log 2)` and `(1, 0)`.

This is the only place where we use concavity: it is Jensen's inequality for
the concave function `Real.binEntropy` on the interval `[0,1]`.
-/
lemma binEntropy_chord_lower_bound {p : Real}
    (hp0 : (2 : Real)⁻¹ ≤ p) (hp1 : p ≤ 1) :
    2 * (1 - p) * Real.log 2 ≤ Real.binEntropy p := by
  let w : Bool → Real := fun b => if b then (2 * p - 1) else (2 * (1 - p))
  let q : Bool → Real := fun b => if b then (1 : Real) else (2 : Real)⁻¹
  have hw_nonneg : ∀ i ∈ (Finset.univ : Finset Bool), 0 ≤ w i := by
    intro i _hi
    cases i
    · dsimp [w]
      linarith
    · dsimp [w]
      linarith
  have hw_sum : (∑ i ∈ (Finset.univ : Finset Bool), w i) = 1 := by
    simp [w]
    ring
  have hq_mem : ∀ i ∈ (Finset.univ : Finset Bool), q i ∈ Set.Icc (0 : Real) 1 := by
    intro i _hi
    cases i
    · simp [q]
      norm_num
    · simp [q]
  have hJ := Real.strictConcave_binEntropy.concaveOn.le_map_sum
      (s := Set.Icc (0 : Real) 1) (f := Real.binEntropy)
      (t := (Finset.univ : Finset Bool)) (w := w) (p := q)
      hw_nonneg hw_sum hq_mem
  have hp_eq : (∑ i ∈ (Finset.univ : Finset Bool), w i • q i) = p := by
    simp [w, q]
    ring
  have hleft :
      (∑ i ∈ (Finset.univ : Finset Bool), w i • Real.binEntropy (q i)) =
        2 * (1 - p) * Real.log 2 := by
    simp [w, q]
  rw [hp_eq] at hJ
  rw [hleft] at hJ
  exact hJ

lemma negMulLog_two_inv :
    Real.negMulLog ((2 : Real)⁻¹) = Real.log 2 / 2 := by
  rw [Real.negMulLog, Real.log_inv]
  ring

/-- Expanding the two half-scaled `negMulLog` terms. -/
lemma negMulLog_scaled_pair (t : Real) :
    ((2 : Real)⁻¹ * Real.negMulLog (1 + t) +
            (1 + t) * Real.negMulLog ((2 : Real)⁻¹)) +
          ((2 : Real)⁻¹ * Real.negMulLog (1 - t) +
            (1 - t) * Real.negMulLog ((2 : Real)⁻¹)) =
        (Real.negMulLog (1 - t) + Real.negMulLog (1 + t)) / 2 +
        Real.log 2 := by
  have hhalf := negMulLog_two_inv
  nlinarith

/--
Rewrite `binEntropy ((1+t)/2)` in the symmetric `negMulLog (1±t)` form.
This is the algebraic bridge from entropy to the edge-isoperimetric function.
-/
lemma binEntropy_one_add_div_two (t : Real) :
    Real.binEntropy ((1 + t) / 2) =
      (Real.negMulLog (1 - t) + Real.negMulLog (1 + t)) / 2 +
        Real.log 2 := by
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  have hleft : (1 + t) / 2 = (1 + t) * (2 : Real)⁻¹ := by ring
  have hright : 1 - (1 + t) * (2 : Real)⁻¹ = (1 - t) * (2 : Real)⁻¹ := by ring
  rw [hleft, hright]
  rw [Real.negMulLog_mul, Real.negMulLog_mul]
  exact negMulLog_scaled_pair t

/--
The one-dimensional real inequality left after the entropy change of variables.
-/
lemma negMulLog_one_sub_add_one_add_nonneg {t : Real}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ Real.negMulLog (1 - t) + Real.negMulLog (1 + t) +
      2 * t * Real.log 2 := by
  have hp0 : (2 : Real)⁻¹ ≤ (1 + t) / 2 := by
    linarith
  have hp1 : (1 + t) / 2 ≤ 1 := by
    linarith
  have h := binEntropy_chord_lower_bound hp0 hp1
  rw [binEntropy_one_add_div_two] at h
  linarith

/--
The book's edge-isoperimetric lower-bound function, rewritten via
`Real.negMulLog`.
-/
lemma edgeIsoperimetricLowerBound_eq_negMulLog (a : Real) :
    edgeIsoperimetricLowerBound a =
      (2 / Real.log 2) * Real.negMulLog a := by
  rw [edgeIsoperimetricLowerBound, Real.negMulLog, one_div, Real.log_inv]
  ring

/--
Parameterized midpoint form of the real induction inequality.

The two slice probabilities are `x * (1 - t)` and `x * (1 + t)`, their average
is `x`, and the slice-disagreement term is `2 * x * t`.
-/
lemma edgeIsoperimetricLowerBound_midpoint_param {x t : Real}
    (hx : 0 ≤ x) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    edgeIsoperimetricLowerBound x ≤
      (edgeIsoperimetricLowerBound (x * (1 - t)) +
          edgeIsoperimetricLowerBound (x * (1 + t))) / 2 +
        2 * x * t := by
  have hlog_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcore := negMulLog_one_sub_add_one_add_nonneg ht0 ht1
  have hscaled :
      0 ≤ (x / Real.log 2) *
        (Real.negMulLog (1 - t) + Real.negMulLog (1 + t) +
          2 * t * Real.log 2) := by
    exact mul_nonneg (div_nonneg hx hlog_pos.le) hcore
  have hscaled' :
      0 ≤ (x / Real.log 2) *
          (Real.negMulLog (1 - t) + Real.negMulLog (1 + t)) +
        2 * x * t := by
    convert hscaled using 1
    field_simp [hlog_pos.ne']
  rw [edgeIsoperimetricLowerBound_eq_negMulLog,
    edgeIsoperimetricLowerBound_eq_negMulLog,
    edgeIsoperimetricLowerBound_eq_negMulLog]
  rw [Real.negMulLog_mul, Real.negMulLog_mul]
  ring_nf at hscaled' ⊢
  nlinarith

/--
Midpoint form ready for slicing: for nonnegative slice probabilities `a` and
`b`, the edge lower bound at their average is controlled by the average of the
two lower bounds plus the slice gap.
-/
lemma edgeIsoperimetricLowerBound_midpoint_le_average_add_abs {a b : Real}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    edgeIsoperimetricLowerBound ((a + b) / 2) ≤
      (edgeIsoperimetricLowerBound a + edgeIsoperimetricLowerBound b) / 2 +
        |a - b| := by
  have haux :
      ∀ {a b : Real}, 0 ≤ a → 0 ≤ b → a ≤ b →
        edgeIsoperimetricLowerBound ((a + b) / 2) ≤
          (edgeIsoperimetricLowerBound a + edgeIsoperimetricLowerBound b) / 2 +
            |a - b| := by
    intro a b ha hb hab
    by_cases hsum : a + b = 0
    · have ha0 : a = 0 := by nlinarith
      have hb0 : b = 0 := by nlinarith
      subst a
      subst b
      simp [edgeIsoperimetricLowerBound]
    · have hsum_pos : 0 < a + b :=
        lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hsum)
      have hx : 0 ≤ (a + b) / 2 := by positivity
      have ht0 : 0 ≤ (b - a) / (a + b) := by
        exact div_nonneg (sub_nonneg.mpr hab) hsum_pos.le
      have ht1 : (b - a) / (a + b) ≤ 1 := by
        rw [div_le_one hsum_pos]
        linarith
      have hleft :
          ((a + b) / 2) * (1 - (b - a) / (a + b)) = a := by
        field_simp [hsum]
        ring
      have hright :
          ((a + b) / 2) * (1 + (b - a) / (a + b)) = b := by
        field_simp [hsum]
        ring
      have hgap :
          2 * ((a + b) / 2) * ((b - a) / (a + b)) = b - a := by
        field_simp [hsum]
      have habs : |a - b| = b - a := by
        rw [abs_of_nonpos (sub_nonpos.mpr hab)]
        ring
      have h := edgeIsoperimetricLowerBound_midpoint_param
        (x := (a + b) / 2) (t := (b - a) / (a + b)) hx ht0 ht1
      simpa [hleft, hright, hgap, habs] using h
  by_cases hab : a ≤ b
  · exact haux ha hb hab
  · have hba : b ≤ a := le_of_not_ge hab
    have h := haux hb ha hba
    simpa [add_comm, add_left_comm, add_assoc, abs_sub_comm] using h

/-- A logarithmic inequality used to compare a set with its complement. -/
lemma log_ratio_bound {r : Real} (hr : 1 ≤ r) :
    (r - 1) * Real.log (r + 1) ≤ r * Real.log r := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hnonneg : 0 ≤ r - 1 := sub_nonneg.mpr hr
  have hone :
      Real.log (r + 1) ≤ Real.log r + 1 / r := by
    have hpos : 0 < 1 + 1 / r := by positivity
    have hlog : Real.log (1 + 1 / r) ≤ 1 / r := by
      have h := Real.log_le_sub_one_of_pos hpos
      linarith
    calc
      Real.log (r + 1) =
          Real.log (r * (1 + 1 / r)) := by
            congr 1
            field_simp [hrpos.ne']
      _ = Real.log r + Real.log (1 + 1 / r) := by
            rw [Real.log_mul hrpos.ne' hpos.ne']
      _ ≤ Real.log r + 1 / r := by
            linarith
  have hmul :
      (r - 1) * Real.log (r + 1) ≤
        (r - 1) * (Real.log r + 1 / r) :=
    mul_le_mul_of_nonneg_left hone hnonneg
  have hlower : 1 - r⁻¹ ≤ Real.log r :=
    Real.one_sub_inv_le_log_of_pos hrpos
  have hupper :
      (r - 1) * (Real.log r + 1 / r) ≤ r * Real.log r := by
    have hrewrite :
        (r - 1) * (Real.log r + 1 / r) =
          (r - 1) * Real.log r + (1 - r⁻¹) := by
      field_simp [hrpos.ne']
    nlinarith [hrewrite, hlower]
  exact hmul.trans hupper

lemma one_sub_mul_log_le_mul_log {p : Real}
    (hp_half : (1 : Real) / 2 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) * Real.log (1 - p) ≤ p * Real.log p := by
  by_cases hp_one : p = 1
  · subst p
    simp
  · have hqpos : 0 < 1 - p := sub_pos.mpr (lt_of_le_of_ne hp1 hp_one)
    have hppos : 0 < p := by linarith
    let r : Real := p / (1 - p)
    have hr : 1 ≤ r := by
      dsimp [r]
      rw [le_div_iff₀ hqpos]
      linarith
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
    have hp_eq : p = r * (1 - p) := by
      dsimp [r]
      rw [div_mul_cancel₀ _ hqpos.ne']
    have hq_eq : 1 - p = (r + 1)⁻¹ := by
      dsimp [r]
      field_simp [hqpos.ne']
      ring
    have hlogp : Real.log p = Real.log r + Real.log (1 - p) := by
      calc
        Real.log p = Real.log (r * (1 - p)) := congrArg Real.log hp_eq
        _ = Real.log r + Real.log (1 - p) :=
          Real.log_mul hrpos.ne' hqpos.ne'
    have hlogq : Real.log (1 - p) = - Real.log (r + 1) := by
      rw [hq_eq, Real.log_inv]
    have hbase := log_ratio_bound hr
    have hscaled :
        (1 - p) * ((r - 1) * Real.log (r + 1)) ≤
          (1 - p) * (r * Real.log r) :=
      mul_le_mul_of_nonneg_left hbase hqpos.le
    have hscaled' :
        (p - (1 - p)) * Real.log (r + 1) ≤ p * Real.log r := by
      have hp_eq_mul : (1 - p) * r = p := by
        rw [mul_comm, ← hp_eq]
      have hleft :
          (1 - p) * ((r - 1) * Real.log (r + 1)) =
            (p - (1 - p)) * Real.log (r + 1) := by
        calc
          (1 - p) * ((r - 1) * Real.log (r + 1)) =
              ((1 - p) * r - (1 - p)) * Real.log (r + 1) := by ring
          _ = (p - (1 - p)) * Real.log (r + 1) := by
              rw [hp_eq_mul]
      have hright :
          (1 - p) * (r * Real.log r) = p * Real.log r := by
        calc
          (1 - p) * (r * Real.log r) =
              ((1 - p) * r) * Real.log r := by ring
          _ = p * Real.log r := by
              rw [hp_eq_mul]
      simpa [hleft, hright] using hscaled
    have haux :
        (1 - p - p) * Real.log (1 - p) ≤ p * Real.log r := by
      rw [hlogq]
      convert hscaled' using 1
      ring
    rw [hlogp]
    nlinarith

lemma negMulLog_le_negMulLog_one_sub_of_half_le {p : Real}
    (hp_half : (1 : Real) / 2 ≤ p) (hp1 : p ≤ 1) :
    Real.negMulLog p ≤ Real.negMulLog (1 - p) := by
  have h := one_sub_mul_log_le_mul_log hp_half hp1
  unfold Real.negMulLog
  nlinarith

lemma edgeIsoperimetricLowerBound_le_complement_of_half_le {p : Real}
    (hp_half : (1 : Real) / 2 ≤ p) (hp1 : p ≤ 1) :
    edgeIsoperimetricLowerBound p ≤
      edgeIsoperimetricLowerBound (1 - p) := by
  rw [edgeIsoperimetricLowerBound_eq_negMulLog,
    edgeIsoperimetricLowerBound_eq_negMulLog]
  have hlog_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact mul_le_mul_of_nonneg_left
    (negMulLog_le_negMulLog_one_sub_of_half_le hp_half hp1)
    (div_nonneg (by norm_num) hlog_pos.le)

lemma edgeIsoperimetricLowerBound_le_min_of_probability {p : Real}
    (_hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    edgeIsoperimetricLowerBound p ≤
      edgeIsoperimetricLowerBound (min p (1 - p)) := by
  by_cases hp_half : p ≤ (1 : Real) / 2
  · have hmin : min p (1 - p) = p := by
      rw [min_eq_left]
      linarith
    rw [hmin]
  · have hp_half' : (1 : Real) / 2 ≤ p := le_of_not_ge hp_half
    have hmin : min p (1 - p) = 1 - p := by
      rw [min_eq_right]
      linarith
    rw [hmin]
    exact edgeIsoperimetricLowerBound_le_complement_of_half_le hp_half' hp1

lemma edgeIsoperimetricLowerBound_le_minorityProbability {n : Nat}
    (f : BooleanFunctionSign n) (a : SignBit) :
    edgeIsoperimetricLowerBound (signValueProbability f a) ≤
      edgeIsoperimetricLowerBound (minorityProbability f) := by
  have hp0 : 0 ≤ signValueProbability f a := cubeProbability_nonneg _
  have hp1 : signValueProbability f a ≤ 1 := signValueProbability_le_one f a
  have hsum := signValueProbability_pos_add_neg f
  cases a
  · have hcomp :
        1 - signValueProbability f SignBit.negOne =
          signValueProbability f SignBit.posOne := by
      linarith
    simpa [minorityProbability, hcomp] using
      edgeIsoperimetricLowerBound_le_min_of_probability hp0 hp1
  · have hcomp :
        1 - signValueProbability f SignBit.posOne =
          signValueProbability f SignBit.negOne := by
      linarith
    simpa [minorityProbability, min_comm, hcomp] using
      edgeIsoperimetricLowerBound_le_min_of_probability hp0 hp1

/--
The direct Poincare consequence in the notation of Theorem 2.39.

This is not yet the sharp edge-isoperimetric bound
`2 * α * log_2 (1 / α) ≤ I[f]`; it is the part obtained immediately from
Poincare and Fact 1.14:

`4 * α * (1 - α) ≤ I[f]`.
-/
theorem theorem_2_39_poincare_variance_bound {n : Nat}
    (f : BooleanFunctionSign n) :
    let α := signValueProbability f SignBit.negOne
    4 * α * (1 - α) ≤ totalInfluence (signFunctionToReal f) := by
  classical
  intro α
  have hsum := signValueProbability_pos_add_neg f
  have hpoincare := totalInfluence_ge_boolean_variance f
  have hpos :
      signValueProbability f SignBit.posOne = 1 - α := by
    dsimp [α]
    linarith
  simpa [α, hpos, mul_comm, mul_left_comm, mul_assoc] using hpoincare

/-- On the zero-dimensional cube, a point probability is just an indicator. -/
lemma signValueProbability_zero
    (f : BooleanFunctionSign 0) (a : SignBit) :
    signValueProbability f a =
      if f (fun i : Fin 0 => Fin.elim0 i) = a then 1 else 0 := by
  classical
  let x0 : SignCube 0 := fun i : Fin 0 => Fin.elim0 i
  have huniv : (Finset.univ : Finset (SignCube 0)) = {x0} := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact Subsingleton.elim x x0
  unfold signValueProbability cubeProbability cubeExpectation
  rw [huniv]
  by_cases h : f x0 = a
  · have hfilter :
        ({x ∈ ({x0} : Finset (SignCube 0)) | f x = a}) = {x0} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · intro hx
        exact hx.1
      · intro hx
        subst x
        exact ⟨rfl, h⟩
    simp [x0, h, hfilter]
  · have hfilter :
        ({x ∈ ({x0} : Finset (SignCube 0)) | f x = a}) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · intro hx
        exfalso
        have hx0 : x = x0 := hx.1
        subst x
        exact h hx.2
      · intro hx
        simp at hx
    simp [x0, h, hfilter]

/--
The induction hypothesis in Theorem 2.39 can be applied to the minority side
of an arbitrary sign-valued Boolean function. If `Pr[f = -1]` is already at
most `1/2`, use the hypothesis directly; otherwise apply it to `-f`.
-/
lemma statement2_39_minority_bound {n : Nat}
    (h : Statement2_39 n) (f : BooleanFunctionSign n) :
    edgeIsoperimetricLowerBound (minorityProbability f) ≤
      totalInfluence (signFunctionToReal f) := by
  classical
  by_cases hneg :
      signValueProbability f SignBit.negOne ≤ (1 : Real) / 2
  · have hdirect := h f
    dsimp [Statement2_39] at hdirect
    have hbound := hdirect hneg
    rwa [minorityProbability_eq_negOne_of_le_half hneg]
  · have hpos :
        signValueProbability f SignBit.posOne ≤ (1 : Real) / 2 := by
      have hsum := signValueProbability_pos_add_neg f
      have hneg_half : (1 : Real) / 2 ≤
          signValueProbability f SignBit.negOne := le_of_not_ge hneg
      linarith
    have hnegate_prob :
        signValueProbability (negateSignFunction f) SignBit.negOne ≤
          (1 : Real) / 2 := by
      simpa [signValueProbability_negate_negOne] using hpos
    have hdirect := h (negateSignFunction f)
    dsimp [Statement2_39] at hdirect
    have hbound := hdirect hnegate_prob
    rw [signValueProbability_negate_negOne,
      totalInfluence_negateSignFunction] at hbound
    rwa [minorityProbability_eq_posOne_of_le_half hpos]

/-- O'Donnell, Theorem 2.39: the edge-isoperimetric lower bound. -/
theorem theorem_2_39 : ∀ n : Nat, Statement2_39 n := by
  intro n
  induction n with
  | zero =>
      intro f
      dsimp [Statement2_39]
      intro hα
      let x0 : SignCube 0 := fun i : Fin 0 => Fin.elim0 i
      cases hfx : f x0
      · have hprob :
            signValueProbability f SignBit.negOne = 1 := by
          simpa [x0, hfx] using
            signValueProbability_zero f SignBit.negOne
        linarith
      · have hprob :
            signValueProbability f SignBit.negOne = 0 := by
          simpa [x0, hfx] using
            signValueProbability_zero f SignBit.negOne
        rw [hprob]
        simp [edgeIsoperimetricLowerBound, totalInfluence]
  | succ n ih =>
      intro f
      dsimp [Statement2_39]
      intro hα
      let f0 : BooleanFunctionSign n := lastSlice f SignBit.negOne
      let f1 : BooleanFunctionSign n := lastSlice f SignBit.posOne
      let p : Real := signValueProbability f0 SignBit.negOne
      let q : Real := signValueProbability f1 SignBit.negOne
      have hprob :
          signValueProbability f SignBit.negOne = (p + q) / 2 := by
        dsimp [p, q, f0, f1]
        exact signValueProbability_lastSlice f SignBit.negOne
      have hp0 : 0 ≤ p := by
        dsimp [p]
        exact cubeProbability_nonneg _
      have hq0 : 0 ≤ q := by
        dsimp [q]
        exact cubeProbability_nonneg _
      have hreal :
          edgeIsoperimetricLowerBound ((p + q) / 2) ≤
            (edgeIsoperimetricLowerBound p +
                edgeIsoperimetricLowerBound q) / 2 +
              |p - q| :=
        edgeIsoperimetricLowerBound_midpoint_le_average_add_abs hp0 hq0
      have hgap :
          |p - q| ≤ lastSliceDisagreementProbability f := by
        dsimp [p, q, f0, f1]
        exact signValueProbability_slice_abs_sub_le_disagreement f
      have hminor0 :
          edgeIsoperimetricLowerBound (minorityProbability f0) ≤
            totalInfluence (signFunctionToReal f0) :=
        statement2_39_minority_bound ih f0
      have hminor1 :
          edgeIsoperimetricLowerBound (minorityProbability f1) ≤
            totalInfluence (signFunctionToReal f1) :=
        statement2_39_minority_bound ih f1
      have hI0 :
          edgeIsoperimetricLowerBound p ≤
            totalInfluence (signFunctionToReal f0) := by
        dsimp [p]
        exact (edgeIsoperimetricLowerBound_le_minorityProbability
          f0 SignBit.negOne).trans hminor0
      have hI1 :
          edgeIsoperimetricLowerBound q ≤
            totalInfluence (signFunctionToReal f1) := by
        dsimp [q]
        exact (edgeIsoperimetricLowerBound_le_minorityProbability
          f1 SignBit.negOne).trans hminor1
      rw [hprob]
      rw [totalInfluence_succ_eq_average_slices_add_disagreement f]
      dsimp [f0, f1] at hI0 hI1
      nlinarith

end BooleanFunctions
