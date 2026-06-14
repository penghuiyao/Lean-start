import InformationTheory.Entropy

/-!
# Theorems for Section 2.1: Entropy

This file contains the Lean proofs corresponding to Cover and Thomas,
Section 2.1.
-/

namespace InformationTheory

universe u

variable {α : Type u}

@[simp]
theorem logBase_eq_logb (b x : ℝ) : logBase b x = Real.logb b x :=
  rfl

theorem entropyTermWithBase_eq_negMulLog_div (b p : ℝ) :
    entropyTermWithBase b p = Real.negMulLog p / Real.log b := by
  simp [entropyTermWithBase, logBase, Real.logb, Real.negMulLog]
  ring

theorem entropyTerm_eq_negMulLog_div_log_two (p : ℝ) :
    entropyTerm p = Real.negMulLog p / Real.log 2 := by
  rw [entropyTerm, entropyTermWithBase_eq_negMulLog_div]

@[simp]
theorem entropyTermWithBase_zero (b : ℝ) : entropyTermWithBase b 0 = 0 := by
  simp [entropyTermWithBase, logBase, Real.logb]

@[simp]
theorem entropyTermWithBase_one (b : ℝ) : entropyTermWithBase b 1 = 0 := by
  simp [entropyTermWithBase, logBase, Real.logb]

@[simp]
theorem entropyTerm_zero : entropyTerm 0 = 0 := by
  simp [entropyTerm]

@[simp]
theorem entropyTerm_one : entropyTerm 1 = 0 := by
  simp [entropyTerm]

theorem entropyTermWithBase_eq_mul_informationContentWithBase [Fintype α]
    (b : ℝ) (P : PMF α) (a : α) :
    entropyTermWithBase b (P.prob a) =
      P.prob a * informationContentWithBase b P a := by
  simp [entropyTermWithBase, informationContentWithBase, Real.logb_inv]

/-- Equation (2.3): entropy is the expected self-information. -/
theorem entropyWithBase_eq_expectation_informationContentWithBase [Fintype α]
    (b : ℝ) (P : PMF α) :
    entropyWithBase b P = expectation P (informationContentWithBase b P) := by
  unfold entropyWithBase expectation
  exact Finset.sum_congr rfl fun a _ =>
    entropyTermWithBase_eq_mul_informationContentWithBase b P a

theorem entropy_eq_expectation_informationContent [Fintype α] (P : PMF α) :
    entropy P = expectation P (informationContent P) := by
  simpa [entropy, informationContent] using
    entropyWithBase_eq_expectation_informationContentWithBase (b := 2) P

theorem entropyTermWithBase_nonneg {b p : ℝ} (hb : 1 < b)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ entropyTermWithBase b p := by
  rw [entropyTermWithBase_eq_negMulLog_div]
  exact div_nonneg (Real.negMulLog_nonneg hp0 hp1) (Real.log_pos hb).le

/-- Lemma 2.1.1 for an arbitrary valid base: entropy is nonnegative. -/
theorem entropyWithBase_nonneg [Fintype α] {b : ℝ} (hb : 1 < b) (P : PMF α) :
    0 ≤ entropyWithBase b P := by
  unfold entropyWithBase
  exact Finset.sum_nonneg fun a _ =>
    entropyTermWithBase_nonneg hb (P.nonneg a) (P.prob_le_one a)

/-- Lemma 2.1.1: entropy in bits is nonnegative. -/
theorem entropy_nonneg [Fintype α] (P : PMF α) : 0 ≤ entropy P := by
  exact entropyWithBase_nonneg (by norm_num : (1 : ℝ) < 2) P

/-- Lemma 2.1.1, using the textbook notation `H`. -/
theorem H_nonneg [Fintype α] (P : PMF α) : 0 ≤ H P :=
  entropy_nonneg P

theorem entropyTermWithBase_change_base {a b p : ℝ} (ha : 1 < a) :
    entropyTermWithBase b p =
      logBase b a * entropyTermWithBase a p := by
  have ha0 : a ≠ 0 := by positivity
  have ha1 : a ≠ 1 := by linarith
  have ham1 : a ≠ -1 := by linarith
  unfold entropyTermWithBase logBase
  calc
    -p * Real.logb b p =
        -p * (Real.logb b a * Real.logb a p) := by
          rw [Real.mul_logb ha0 ha1 ham1]
    _ = Real.logb b a * (-p * Real.logb a p) := by
          ring

/-- Lemma 2.1.2: change of logarithm base for entropy. -/
theorem entropyWithBase_change_base [Fintype α] {a b : ℝ} (ha : 1 < a)
    (P : PMF α) :
    entropyWithBase b P = logBase b a * entropyWithBase a P := by
  unfold entropyWithBase
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ =>
    entropyTermWithBase_change_base (b := b) (p := P.prob p) ha

theorem binaryEntropy_eq_real_binEntropy_div_log_two (p : ℝ) :
    binaryEntropy p = Real.binEntropy p / Real.log 2 := by
  rw [binaryEntropy, entropyTerm_eq_negMulLog_div_log_two,
    entropyTerm_eq_negMulLog_div_log_two,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  ring

@[simp]
theorem binaryEntropy_zero : binaryEntropy 0 = 0 := by
  simp [binaryEntropy]

@[simp]
theorem binaryEntropy_one : binaryEntropy 1 = 0 := by
  simp [binaryEntropy]

/-- Example 2.1.1: a fair bit has entropy one bit. -/
@[simp]
theorem binaryEntropy_half : binaryEntropy (1 / 2) = 1 := by
  rw [binaryEntropy_eq_real_binEntropy_div_log_two]
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.binEntropy_two_inv]
  exact div_self (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'

end InformationTheory
