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

/-!
The sharp Theorem 2.39 still requires one additional block:

* the induction-by-restrictions real inequality for
  `φ α = 2 * α * (Real.log (1 / α) / Real.log 2)`;
* then the already-proved slicing identity
  `totalInfluence_succ_eq_average_slices_add_disagreement` supplies the
  recursive influence decomposition.
-/

end BooleanFunctions
