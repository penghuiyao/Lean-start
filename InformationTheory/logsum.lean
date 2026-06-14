import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import InformationTheory.Jensen

/-!
# Theorem 2.7.1: Log Sum Inequality

This file formalizes the finite log-sum inequality from Cover and Thomas,
Section 2.7.  Since the project currently uses real-valued total functions
rather than extended reals, the statement includes the natural support
condition `a i ≠ 0 -> b i ≠ 0`.
-/

namespace InformationTheory

universe u

variable {ι : Type u}

private theorem convexOn_mul_logBase_two :
    ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ => x * logBase 2 x) := by
  have hlog_nonneg : 0 ≤ (Real.log 2)⁻¹ :=
    inv_nonneg.mpr (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  simpa [logBase, Real.logb, div_eq_mul_inv, smul_eq_mul, mul_assoc,
    mul_comm, mul_left_comm] using
      (Real.convexOn_mul_log.smul hlog_nonneg)

private theorem all_zero_of_sum_eq_zero [Fintype ι]
    {a : ι -> ℝ} (ha : ∀ i, 0 ≤ a i)
    (hsum : Finset.univ.sum a = 0) :
    ∀ i, a i = 0 := by
  intro i
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => ha i)).mp hsum i (Finset.mem_univ i)

private theorem logSum_center_eq [Fintype ι]
    {a b : ι -> ℝ} {B : ℝ}
    (hB : B ≠ 0) (hac : ∀ i, a i ≠ 0 -> b i ≠ 0) :
    Finset.univ.sum (fun i : ι => (b i / B) * (a i / b i)) =
      Finset.univ.sum a / B := by
  calc
    Finset.univ.sum (fun i : ι => (b i / B) * (a i / b i)) =
        Finset.univ.sum (fun i : ι => a i / B) := by
          exact Finset.sum_congr rfl fun i _ => by
            by_cases hb : b i = 0
            · have ha0 : a i = 0 := by
                by_contra hai
                exact (hac i hai) hb
              simp [hb, ha0]
            · field_simp [hB, hb]
    _ = Finset.univ.sum a / B := by
          rw [← Finset.sum_div]

private theorem logSum_rhs_eq [Fintype ι]
    {a b : ι -> ℝ} {B : ℝ}
    (hB : B ≠ 0) (hac : ∀ i, a i ≠ 0 -> b i ≠ 0) :
    Finset.univ.sum (fun i : ι =>
        (b i / B) * ((a i / b i) * logBase 2 (a i / b i))) =
      (1 / B) *
        Finset.univ.sum (fun i : ι => relativeEntropyTermWithBase 2 (a i) (b i)) := by
  calc
    Finset.univ.sum (fun i : ι =>
        (b i / B) * ((a i / b i) * logBase 2 (a i / b i))) =
        Finset.univ.sum (fun i : ι =>
          (1 / B) * relativeEntropyTermWithBase 2 (a i) (b i)) := by
          exact Finset.sum_congr rfl fun i _ => by
            by_cases ha0 : a i = 0
            · simp [relativeEntropyTermWithBase, ha0]
            · have hb0 : b i ≠ 0 := hac i ha0
              unfold relativeEntropyTermWithBase
              simp [ha0]
              field_simp [hB, hb0]
    _ = (1 / B) *
        Finset.univ.sum (fun i : ι => relativeEntropyTermWithBase 2 (a i) (b i)) := by
          rw [Finset.mul_sum]

/--
Theorem 2.7.1, log-sum inequality, in bits.

The right-hand side is written with `relativeEntropyTermWithBase` so that the
zero numerator convention matches the rest of this project.
-/
theorem theorem_2_7_1_logSumInequality [Fintype ι]
    (a b : ι -> ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hac : ∀ i, a i ≠ 0 -> b i ≠ 0) :
    relativeEntropyTermWithBase 2
        (Finset.univ.sum a) (Finset.univ.sum b) ≤
      relativeEntropyFromMass a b := by
  let A := Finset.univ.sum a
  let B := Finset.univ.sum b
  by_cases hA0 : A = 0
  · have hazero : ∀ i, a i = 0 := all_zero_of_sum_eq_zero ha hA0
    unfold relativeEntropyFromMass relativeEntropyFromMassWithBase
    have hleft : relativeEntropyTermWithBase 2 A B = 0 := by
      unfold relativeEntropyTermWithBase
      simp [hA0]
    rw [hleft]
    have hsumzero :
        Finset.univ.sum (fun i : ι => relativeEntropyTermWithBase 2 (a i) (b i)) = 0 := by
      exact Finset.sum_eq_zero fun i _ => by
        simp [relativeEntropyTermWithBase, hazero i]
    rw [hsumzero]
  · have hA_nonneg : 0 ≤ A := Finset.sum_nonneg fun i _ => ha i
    have hA_pos : 0 < A := lt_of_le_of_ne hA_nonneg (Ne.symm hA0)
    have hB_pos : 0 < B := by
      by_contra hnot
      have hB_nonpos : B ≤ 0 := le_of_not_gt hnot
      have hB_nonneg : 0 ≤ B := Finset.sum_nonneg fun i _ => hb i
      have hB0 : B = 0 := le_antisymm hB_nonpos hB_nonneg
      have hbzero : ∀ i, b i = 0 := all_zero_of_sum_eq_zero hb hB0
      have hazero : ∀ i, a i = 0 := by
        intro i
        by_contra hai
        exact (hac i hai) (hbzero i)
      have hA0' : A = 0 := by
        dsimp [A]
        exact Finset.sum_eq_zero fun i _ => hazero i
      exact hA0 hA0'
    have hB0 : B ≠ 0 := ne_of_gt hB_pos
    have hweights_nonneg :
        ∀ i ∈ Finset.univ, 0 ≤ b i / B := fun i _ =>
      div_nonneg (hb i) hB_pos.le
    have hweights_sum :
        Finset.univ.sum (fun i : ι => b i / B) = 1 := by
      rw [← Finset.sum_div]
      exact div_self hB0
    have hpoints_mem :
        ∀ i ∈ Finset.univ, a i / b i ∈ Set.Ici (0 : ℝ) := fun i _ =>
      div_nonneg (ha i) (hb i)
    have hJ := convexOn_mul_logBase_two.map_sum_le
      (t := Finset.univ) (w := fun i : ι => b i / B)
      (p := fun i : ι => a i / b i)
      hweights_nonneg hweights_sum hpoints_mem
    simp only [smul_eq_mul] at hJ
    rw [logSum_center_eq (a := a) (b := b) (B := B) hB0 hac,
      logSum_rhs_eq (a := a) (b := b) (B := B) hB0 hac] at hJ
    have hmul := mul_le_mul_of_nonneg_left hJ hB_pos.le
    have hright :
        B * ((1 / B) *
            Finset.univ.sum (fun i : ι =>
              relativeEntropyTermWithBase 2 (a i) (b i))) =
          relativeEntropyFromMass a b := by
      unfold relativeEntropyFromMass relativeEntropyFromMassWithBase
      field_simp [hB0]
    have hleft :
        B * ((Finset.univ.sum a / B) *
            logBase 2 (Finset.univ.sum a / B)) =
          relativeEntropyTermWithBase 2
            (Finset.univ.sum a) (Finset.univ.sum b) := by
      have hAsum0 : Finset.univ.sum a ≠ 0 := by
        simpa [A] using hA0
      have hBsum0 : Finset.univ.sum b ≠ 0 := by
        simpa [B] using hB0
      dsimp [B]
      unfold relativeEntropyTermWithBase
      simp [hAsum0]
      field_simp [hBsum0]
    rwa [hleft, hright] at hmul

end InformationTheory
