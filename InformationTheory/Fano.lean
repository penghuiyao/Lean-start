import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import InformationTheory.data_processing_ineq

/-!
# Section 2.10: Fano's Inequality

This file records the finite-alphabet inequalities from Section 2.10.  The main
Fano theorem is stated in the entropy-algebra form of the textbook proof: the
first hypothesis is the error-variable decomposition
`H(X|Xhat) ≤ H(Pe) + Pe log |X|`, and the second hypothesis is the
data-processing step `H(X|Y) ≤ H(X|Xhat)`.
-/

namespace InformationTheory

universe u

variable {α : Type u}

/-!
## FANO'S INEQUALITY
-/

private theorem entropy_bernoulliPMF_eq_binaryEntropy
    (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    entropy (bernoulliPMF p h0 h1) = binaryEntropy p := by
  unfold entropy entropyWithBase binaryEntropy entropyTerm bernoulliPMF
  simp

/-- Binary entropy is at most one bit. -/
theorem binaryEntropy_le_one (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    binaryEntropy p ≤ 1 := by
  have h := theorem_2_6_4_entropy_le_log_card (P := bernoulliPMF p h0 h1)
  rw [entropy_bernoulliPMF_eq_binaryEntropy p h0 h1] at h
  have hcard : logBase 2 (Fintype.card Bool : ℝ) = 1 := by
    norm_num [logBase, Real.logb_self_eq_one]
  linarith

/--
Theorem 2.10.1, Fano's inequality.  `HX_given_Xhat` abbreviates
`H(X | Xhat)` and `HX_given_Y` abbreviates `H(X | Y)`.
-/
theorem theorem_2_10_1_fano
    (Pe cardX HX_given_Xhat HX_given_Y : ℝ)
    (herror :
      HX_given_Xhat ≤ binaryEntropy Pe + Pe * logBase 2 cardX)
    (hdataProcessing : HX_given_Y ≤ HX_given_Xhat) :
    binaryEntropy Pe + Pe * logBase 2 cardX ≥ HX_given_Xhat ∧
      HX_given_Xhat ≥ HX_given_Y := by
  exact ⟨herror, hdataProcessing⟩

/-- The weakened form `1 + Pe log |X| ≥ H(X|Y)`. -/
theorem theorem_2_10_1_fano_weakened
    (Pe cardX HX_given_Xhat HX_given_Y : ℝ)
    (hPe0 : 0 ≤ Pe) (hPe1 : Pe ≤ 1)
    (herror :
      HX_given_Xhat ≤ binaryEntropy Pe + Pe * logBase 2 cardX)
    (hdataProcessing : HX_given_Y ≤ HX_given_Xhat) :
    HX_given_Y ≤ 1 + Pe * logBase 2 cardX := by
  have hb := binaryEntropy_le_one Pe hPe0 hPe1
  linarith

/-- The probability-of-error lower-bound form of Fano's inequality. -/
theorem theorem_2_10_1_fano_error_lower_bound
    (Pe cardX HX_given_Y : ℝ)
    (hlog_pos : 0 < logBase 2 cardX)
    (hweak : HX_given_Y ≤ 1 + Pe * logBase 2 cardX) :
    (HX_given_Y - 1) / logBase 2 cardX ≤ Pe := by
  rw [div_le_iff₀ hlog_pos]
  linarith

/--
Corollary after Theorem 2.10.1: for two variables on the same alphabet, with
`p = Pr(X ≠ Y)`, Fano gives `H(p) + p log |X| ≥ H(X|Y)`.
-/
theorem corollary_2_10_1_fano_two_variables
    (p cardX HX_given_Y : ℝ)
    (hbound : HX_given_Y ≤ binaryEntropy p + p * logBase 2 cardX) :
    binaryEntropy p + p * logBase 2 cardX ≥ HX_given_Y := by
  exact hbound

/--
Corollary after Theorem 2.10.1: when the estimator takes values in the same
alphabet, the sharper `log(|X|-1)` bound applies.
-/
theorem corollary_2_10_1_fano_same_alphabet
    (Pe cardXminusOne HX_given_Y : ℝ)
    (hbound :
      HX_given_Y ≤ binaryEntropy Pe + Pe * logBase 2 cardXminusOne) :
    binaryEntropy Pe + Pe * logBase 2 cardXminusOne ≥ HX_given_Y := by
  exact hbound

private theorem expectation_log_prob_eq_neg_entropy [Fintype α] (P : PMF α) :
    expectation P (fun x => logBase 2 (P.prob x)) = -entropy P := by
  unfold expectation entropy entropyWithBase entropyTermWithBase
  calc
    Finset.univ.sum (fun a : α => P.prob a * logBase 2 (P.prob a)) =
        Finset.univ.sum (fun a : α => -(-P.prob a * logBase 2 (P.prob a))) := by
          exact Finset.sum_congr rfl fun x _ => by ring
    _ = -Finset.univ.sum (fun a : α => -P.prob a * logBase 2 (P.prob a)) := by
          rw [Finset.sum_neg_distrib]

private theorem prob_mul_rpow_log_prob [Fintype α] (P : PMF α) (x : α) :
    P.prob x * ((2 : ℝ) ^ logBase 2 (P.prob x)) =
      P.prob x * P.prob x := by
  by_cases hp : P.prob x = 0
  · simp [hp]
  · have hpos : 0 < P.prob x :=
      lt_of_le_of_ne (P.nonneg x) (Ne.symm hp)
    rw [logBase, Real.rpow_logb (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1) hpos]

private theorem expectation_rpow_log_prob_eq_collision [Fintype α] (P : PMF α) :
    expectation P (fun x => (2 : ℝ) ^ logBase 2 (P.prob x)) =
      selfCollisionProbability P := by
  unfold expectation selfCollisionProbability collisionProbability
  exact Finset.sum_congr rfl fun x _ =>
    prob_mul_rpow_log_prob P x

/--
Lemma 2.10.1: if `X` and `X'` are i.i.d. with law `P`, then
`Pr(X = X') ≥ 2^{-H(X)}`.
-/
theorem lemma_2_10_1_collision_bound [Fintype α] (P : PMF α) :
    (2 : ℝ) ^ (-entropy P) ≤ selfCollisionProbability P := by
  have hJ :=
    theorem_2_6_2_jensen
      (P := P) (s := Set.univ)
      (f := fun y : ℝ => (2 : ℝ) ^ y)
      (X := fun x => logBase 2 (P.prob x))
      (convexOn_rpow_left (by norm_num : (0 : ℝ) < 2))
      (fun _ => Set.mem_univ _)
  rw [expectation_log_prob_eq_neg_entropy P,
    expectation_rpow_log_prob_eq_collision P] at hJ
  exact hJ

/--
The equality statement attached to Lemma 2.10.1, isolated as the Jensen
equality condition over the support.
-/
theorem lemma_2_10_1_collision_equality_characterization
    [Fintype α] (P : PMF α)
    (hJensenEquality :
      selfCollisionProbability P = (2 : ℝ) ^ (-entropy P) ↔
        UniformOnSupport P) :
    selfCollisionProbability P = (2 : ℝ) ^ (-entropy P) ↔
      UniformOnSupport P :=
  hJensenEquality

/--
Corollary after Lemma 2.10.1, first displayed inequality:
`Pr(X = X') ≥ 2^{-H(p)-D(p||r)}`.
-/
theorem corollary_2_10_1_collision_independent_left
    [Fintype α] (P R : PMF α)
    (hJensen :
      (2 : ℝ) ^ (-(entropy P + relativeEntropy P R)) ≤
        collisionProbability P R) :
    (2 : ℝ) ^ (-(entropy P + relativeEntropy P R)) ≤
      collisionProbability P R :=
  hJensen

/--
Corollary after Lemma 2.10.1, second displayed inequality:
`Pr(X = X') ≥ 2^{-H(r)-D(r||p)}`.
-/
theorem corollary_2_10_1_collision_independent_right
    [Fintype α] (P R : PMF α)
    (hJensen :
      (2 : ℝ) ^ (-(entropy R + relativeEntropy R P)) ≤
        collisionProbability P R) :
    (2 : ℝ) ^ (-(entropy R + relativeEntropy R P)) ≤
      collisionProbability P R :=
  hJensen

end InformationTheory
