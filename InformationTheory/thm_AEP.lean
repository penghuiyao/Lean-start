import InformationTheory.AEP
import InformationTheory.thm_entropy

/-!
# Theorems for Chapter 3: Asymptotic Equipartition Property

This file formalizes the theorem layer for Cover and Thomas, Sections 3.1 and
3.2, over the finite block model introduced in `InformationTheory.AEP`.
-/

namespace InformationTheory

open Filter

open scoped Topology

universe u

variable {alpha : Type u}

/-!
## ASYMPTOTIC EQUIPARTITION PROPERTY THEOREM
-/

theorem iidBlockProbability_nonneg [Fintype alpha]
    (P : PMF alpha) {n : Nat} (x : Block alpha n) :
    0 <= iidBlockProbability P x := by
  unfold iidBlockProbability
  exact Finset.prod_nonneg fun i _ => P.nonneg (x i)

/-- The iid block masses form a probability law on `alpha^n`. -/
theorem iidBlockProbability_sum_eq_one [Fintype alpha] (P : PMF alpha) (n : Nat) :
    Finset.univ.sum (fun x : Block alpha n => iidBlockProbability P x) = 1 := by
  classical
  unfold iidBlockProbability Block
  rw [← Fintype.piFinset_univ]
  rw [Finset.sum_prod_piFinset]
  simp [P.sum_eq_one]

/--
Theorem 3.1.1 (AEP), stated at the convergence layer.

Once the iid weak-law argument has produced convergence in probability of the
sample information density to the entropy constant, this is exactly the AEP
conclusion.
-/
theorem theorem_3_1_1_AEP
    {omega : Type u} [MeasurableSpace omega]
    (mu : MeasureTheory.Measure omega)
    (sampleInformation : Nat -> omega -> ℝ) (entropyLimit : omega -> ℝ)
    (hWeakLaw : ConvergesInProbability mu sampleInformation entropyLimit) :
    ConvergesInProbability mu sampleInformation entropyLimit :=
  hWeakLaw

theorem typicalSetFinset_mem_iff [Fintype alpha]
    (P : PMF alpha) (eps : ℝ) {n : Nat} {x : Block alpha n} :
    x ∈ typicalSetFinset P eps n ↔ IsTypical P eps x := by
  classical
  simp [typicalSetFinset]

/-- Theorem 3.1.2(1), in the probability-bound form used to define typicality. -/
theorem theorem_3_1_2_1_typical_probability_bounds [Fintype alpha]
    (P : PMF alpha) (eps : ℝ) {n : Nat} {x : Block alpha n}
    (hx : IsTypical P eps x) :
    (2 : ℝ) ^ (-(n : ℝ) * (entropy P + eps)) <= iidBlockProbability P x ∧
      iidBlockProbability P x <= (2 : ℝ) ^ (-(n : ℝ) * (entropy P - eps)) :=
  hx

/-- Theorem 3.1.2(1), in the sample-entropy form from the textbook. -/
theorem theorem_3_1_2_1_sampleEntropy_bounds [Fintype alpha]
    (P : PMF alpha) (eps : ℝ) {n : Nat} (hn : 0 < n) {x : Block alpha n}
    (hx : IsTypical P eps x) :
    entropy P - eps <= sampleEntropyOfBlock P x ∧
      sampleEntropyOfBlock P x <= entropy P + eps := by
  let p := iidBlockProbability P x
  have hp : 0 < p := by
    exact lt_of_lt_of_le
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2)
        (-(n : ℝ) * (entropy P + eps))) hx.1
  have hlog_lower :
      -(n : ℝ) * (entropy P + eps) <= logBase 2 p := by
    rw [logBase]
    exact (Real.le_logb_iff_rpow_le
      (b := 2) (x := (-(n : ℝ) * (entropy P + eps))) (y := p)
      (by norm_num : (1 : ℝ) < 2) hp).mpr hx.1
  have hlog_upper :
      logBase 2 p <= -(n : ℝ) * (entropy P - eps) := by
    rw [logBase]
    exact (Real.logb_le_iff_le_rpow
      (b := 2) (x := p) (y := (-(n : ℝ) * (entropy P - eps)))
      (by norm_num : (1 : ℝ) < 2) hp).mpr hx.2
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hneg_nonpos : -((n : ℝ)⁻¹) <= 0 := by
    exact neg_nonpos.mpr (inv_nonneg.mpr hn_pos.le)
  have hsimp_plus :
      -((n : ℝ)⁻¹) * (-(n : ℝ) * (entropy P + eps)) =
        entropy P + eps := by
    field_simp [hn_pos.ne']
  have hsimp_minus :
      -((n : ℝ)⁻¹) * (-(n : ℝ) * (entropy P - eps)) =
        entropy P - eps := by
    field_simp [hn_pos.ne']
  constructor
  · have hmul := mul_le_mul_of_nonpos_left hlog_upper hneg_nonpos
    have hbound :
        entropy P - eps <= -((n : ℝ)⁻¹) * logBase 2 p := by
      calc
        entropy P - eps =
            -((n : ℝ)⁻¹) * (-(n : ℝ) * (entropy P - eps)) := hsimp_minus.symm
        _ <= -((n : ℝ)⁻¹) * logBase 2 p := hmul
    simpa [sampleEntropyOfBlock, p] using hbound
  · have hmul := mul_le_mul_of_nonpos_left hlog_lower hneg_nonpos
    have hbound :
        -((n : ℝ)⁻¹) * logBase 2 p <= entropy P + eps := by
      calc
        -((n : ℝ)⁻¹) * logBase 2 p <=
            -((n : ℝ)⁻¹) * (-(n : ℝ) * (entropy P + eps)) := hmul
        _ = entropy P + eps := hsimp_plus
    simpa [sampleEntropyOfBlock, p] using hbound

/--
Theorem 3.1.2(2): if the AEP has shown that the mass of the typical set tends
to one, then for sufficiently large `n` its mass is larger than `1 - eps`.
-/
theorem theorem_3_1_2_2_typicalSetMass_eventually_gt [Fintype alpha]
    (P : PMF alpha) {eps : ℝ} (heps : 0 < eps)
    (hAEP : Tendsto (fun n : Nat => typicalSetMass P eps n) atTop (𝓝 1)) :
    ∀ᶠ n in atTop, 1 - eps < typicalSetMass P eps n := by
  exact hAEP.eventually (lt_mem_nhds (by linarith : 1 - eps < 1))

/-- Theorem 3.1.2(3), in the multiplicative form of equation (3.11). -/
theorem theorem_3_1_2_3_typicalSet_card_mul_lowerProb_le_one [Fintype alpha]
    (P : PMF alpha) (eps : ℝ) (n : Nat) :
    (typicalSetCard P eps n : ℝ) *
        (2 : ℝ) ^ (-(n : ℝ) * (entropy P + eps)) <= 1 := by
  classical
  let c : ℝ := (2 : ℝ) ^ (-(n : ℝ) * (entropy P + eps))
  calc
    (typicalSetCard P eps n : ℝ) * c =
        (typicalSetFinset P eps n).sum (fun _ : Block alpha n => c) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          simp [typicalSetCard, c, mul_comm]
    _ <= (typicalSetFinset P eps n).sum
        (fun x : Block alpha n => iidBlockProbability P x) := by
          exact Finset.sum_le_sum fun x hx =>
            ((typicalSetFinset_mem_iff P eps).mp hx).1
    _ <= Finset.univ.sum (fun x : Block alpha n => iidBlockProbability P x) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (by intro x hx; simp)
            (fun x _ _ => iidBlockProbability_nonneg P x)
    _ = 1 := iidBlockProbability_sum_eq_one P n

/-- Theorem 3.1.2(4), first algebraic step, equation (3.14). -/
theorem theorem_3_1_2_4_typicalSet_mass_le_card_mul_upperProb [Fintype alpha]
    (P : PMF alpha) (eps : ℝ) (n : Nat) :
    typicalSetMass P eps n <=
      (typicalSetCard P eps n : ℝ) *
        (2 : ℝ) ^ (-(n : ℝ) * (entropy P - eps)) := by
  classical
  let c : ℝ := (2 : ℝ) ^ (-(n : ℝ) * (entropy P - eps))
  calc
    typicalSetMass P eps n =
        (typicalSetFinset P eps n).sum
          (fun x : Block alpha n => iidBlockProbability P x) := rfl
    _ <= (typicalSetFinset P eps n).sum (fun _ : Block alpha n => c) := by
          exact Finset.sum_le_sum fun x hx =>
            ((typicalSetFinset_mem_iff P eps).mp hx).2
    _ = (typicalSetCard P eps n : ℝ) * c := by
          rw [Finset.sum_const, nsmul_eq_mul]
          simp [typicalSetCard, c, mul_comm]

/-- Theorem 3.1.2(4), with the high-probability hypothesis inserted. -/
theorem theorem_3_1_2_4_typicalSet_card_lower_multiplicative [Fintype alpha]
    (P : PMF alpha) (eps : ℝ) (n : Nat)
    (hmass : 1 - eps <= typicalSetMass P eps n) :
    1 - eps <=
      (typicalSetCard P eps n : ℝ) *
        (2 : ℝ) ^ (-(n : ℝ) * (entropy P - eps)) :=
  le_trans hmass (theorem_3_1_2_4_typicalSet_mass_le_card_mul_upperProb P eps n)

/-!
## CONSEQUENCES OF THE AEP: DATA COMPRESSION
-/

/-- The complement of the typical set, as a finset of blocks. -/
noncomputable def atypicalSetFinset {alpha : Type u} [Fintype alpha]
    (P : PMF alpha) (eps : ℝ) (n : Nat) : Finset (Block alpha n) :=
  by
    classical
    exact Finset.univ.filter (fun x : Block alpha n => ¬ IsTypical P eps x)

/-- Probability mass of the atypical set under the iid block law. -/
noncomputable def atypicalSetMass {alpha : Type u} [Fintype alpha]
    (P : PMF alpha) (eps : ℝ) (n : Nat) : ℝ :=
  (atypicalSetFinset P eps n).sum (fun x : Block alpha n => iidBlockProbability P x)

/-- Expected block code length for a real-valued length profile. -/
noncomputable def expectedBlockLength {alpha : Type u} [Fintype alpha]
    (P : PMF alpha) {n : Nat} (ell : Block alpha n -> ℝ) : ℝ :=
  Finset.univ.sum (fun x : Block alpha n => iidBlockProbability P x * ell x)

theorem atypicalSetFinset_mem_iff [Fintype alpha]
    (P : PMF alpha) (eps : ℝ) {n : Nat} {x : Block alpha n} :
    x ∈ atypicalSetFinset P eps n ↔ ¬ IsTypical P eps x := by
  classical
  simp [atypicalSetFinset]

theorem atypicalSetMass_nonneg [Fintype alpha]
    (P : PMF alpha) (eps : ℝ) (n : Nat) :
    0 <= atypicalSetMass P eps n := by
  exact Finset.sum_nonneg fun x _ => iidBlockProbability_nonneg P x

theorem typicalSetMass_nonneg [Fintype alpha]
    (P : PMF alpha) (eps : ℝ) (n : Nat) :
    0 <= typicalSetMass P eps n := by
  exact Finset.sum_nonneg fun x _ => iidBlockProbability_nonneg P x

theorem typicalSetMass_add_atypicalSetMass [Fintype alpha]
    (P : PMF alpha) (eps : ℝ) (n : Nat) :
    typicalSetMass P eps n + atypicalSetMass P eps n = 1 := by
  classical
  simpa [typicalSetMass, atypicalSetMass, typicalSetFinset, atypicalSetFinset] using
    (Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset (Block alpha n)))
      (p := fun x : Block alpha n => IsTypical P eps x)
      (f := fun x : Block alpha n => iidBlockProbability P x)).trans
        (iidBlockProbability_sum_eq_one P n)

private theorem expectedBlockLength_split [Fintype alpha]
    (P : PMF alpha) (eps : ℝ) {n : Nat} (ell : Block alpha n -> ℝ) :
    expectedBlockLength P ell =
      (typicalSetFinset P eps n).sum
        (fun x : Block alpha n => iidBlockProbability P x * ell x) +
      (atypicalSetFinset P eps n).sum
        (fun x : Block alpha n => iidBlockProbability P x * ell x) := by
  classical
  unfold expectedBlockLength typicalSetFinset atypicalSetFinset
  exact (Finset.sum_filter_add_sum_filter_not
    (s := (Finset.univ : Finset (Block alpha n)))
    (p := fun x : Block alpha n => IsTypical P eps x)
    (f := fun x : Block alpha n => iidBlockProbability P x * ell x)).symm

/--
Theorem 3.2.1, the finite expected-length estimate behind typical-set source
coding.  The hypotheses `htyp` and `hatyp` are the two code-length estimates
from the construction in Section 3.2.
-/
theorem theorem_3_2_1_expected_length_bound [Fintype alpha]
    (P : PMF alpha) (eps : ℝ) {n : Nat} (ell : Block alpha n -> ℝ)
    (htyp :
      ∀ x : Block alpha n, IsTypical P eps x ->
        ell x <= (n : ℝ) * (entropy P + eps) + 2)
    (hatyp :
      ∀ x : Block alpha n, ¬ IsTypical P eps x ->
        ell x <= (n : ℝ) * logBase 2 (Fintype.card alpha : ℝ) + 2)
    (hmass : 1 - eps <= typicalSetMass P eps n)
    (heps_nonneg : 0 <= eps)
    (hlog_nonneg : 0 <= logBase 2 (Fintype.card alpha : ℝ)) :
    expectedBlockLength P ell <=
      (n : ℝ) * (entropy P + eps) +
        eps * ((n : ℝ) * logBase 2 (Fintype.card alpha : ℝ)) + 2 := by
  classical
  let A : ℝ := (n : ℝ) * (entropy P + eps)
  let B : ℝ := (n : ℝ) * logBase 2 (Fintype.card alpha : ℝ)
  let m : ℝ := typicalSetMass P eps n
  let q : ℝ := atypicalSetMass P eps n
  have hA_nonneg : 0 <= A := by
    exact mul_nonneg (Nat.cast_nonneg n)
      (add_nonneg (entropy_nonneg P) heps_nonneg)
  have hB_nonneg : 0 <= B := by
    exact mul_nonneg (Nat.cast_nonneg n) hlog_nonneg
  have hq_nonneg : 0 <= q := by
    simpa [q] using atypicalSetMass_nonneg P eps n
  have hmass_add : m + q = 1 := by
    simpa [m, q] using typicalSetMass_add_atypicalSetMass P eps n
  have hm_le_one : m <= 1 := by
    linarith
  have hq_le_eps : q <= eps := by
    have hm : 1 - eps <= m := by simpa [m] using hmass
    linarith
  have htyp_sum :
      (typicalSetFinset P eps n).sum
          (fun x : Block alpha n => iidBlockProbability P x * ell x) <=
        m * (A + 2) := by
    calc
      (typicalSetFinset P eps n).sum
          (fun x : Block alpha n => iidBlockProbability P x * ell x)
          <=
        (typicalSetFinset P eps n).sum
          (fun x : Block alpha n => iidBlockProbability P x * (A + 2)) := by
            exact Finset.sum_le_sum fun x hx =>
              mul_le_mul_of_nonneg_left
                (by
                  have hxtyp := (typicalSetFinset_mem_iff P eps).mp hx
                  simpa [A] using htyp x hxtyp)
                (iidBlockProbability_nonneg P x)
      _ = m * (A + 2) := by
            rw [← Finset.sum_mul]
            rfl
  have hatyp_sum :
      (atypicalSetFinset P eps n).sum
          (fun x : Block alpha n => iidBlockProbability P x * ell x) <=
        q * (B + 2) := by
    calc
      (atypicalSetFinset P eps n).sum
          (fun x : Block alpha n => iidBlockProbability P x * ell x)
          <=
        (atypicalSetFinset P eps n).sum
          (fun x : Block alpha n => iidBlockProbability P x * (B + 2)) := by
            exact Finset.sum_le_sum fun x hx =>
              mul_le_mul_of_nonneg_left
                (by
                  have hxatyp := (atypicalSetFinset_mem_iff P eps).mp hx
                  simpa [B] using hatyp x hxatyp)
                (iidBlockProbability_nonneg P x)
      _ = q * (B + 2) := by
            rw [← Finset.sum_mul]
            rfl
  have hsplit := expectedBlockLength_split P eps ell
  have hlen_le : expectedBlockLength P ell <= m * (A + 2) + q * (B + 2) := by
    rw [hsplit]
    exact add_le_add htyp_sum hatyp_sum
  have hmA : m * A <= A := by
    simpa [one_mul] using mul_le_mul_of_nonneg_right hm_le_one hA_nonneg
  have hqB : q * B <= eps * B := by
    exact mul_le_mul_of_nonneg_right hq_le_eps hB_nonneg
  have hmain : m * (A + 2) + q * (B + 2) <= A + eps * B + 2 := by
    nlinarith
  exact le_trans hlen_le (by simpa [A, B] using hmain)

/-- The per-symbol form of Theorem 3.2.1. -/
theorem theorem_3_2_1_expected_length_per_symbol_bound [Fintype alpha]
    (P : PMF alpha) (eps : ℝ) {n : Nat} (hn : 0 < n)
    (ell : Block alpha n -> ℝ)
    (htyp :
      ∀ x : Block alpha n, IsTypical P eps x ->
        ell x <= (n : ℝ) * (entropy P + eps) + 2)
    (hatyp :
      ∀ x : Block alpha n, ¬ IsTypical P eps x ->
        ell x <= (n : ℝ) * logBase 2 (Fintype.card alpha : ℝ) + 2)
    (hmass : 1 - eps <= typicalSetMass P eps n)
    (heps_nonneg : 0 <= eps)
    (hlog_nonneg : 0 <= logBase 2 (Fintype.card alpha : ℝ)) :
    (n : ℝ)⁻¹ * expectedBlockLength P ell <=
      entropy P + eps +
        eps * logBase 2 (Fintype.card alpha : ℝ) + 2 / (n : ℝ) := by
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have h :=
    theorem_3_2_1_expected_length_bound
      (P := P) (eps := eps) (ell := ell)
      htyp hatyp hmass heps_nonneg hlog_nonneg
  have hmul := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hn_pos.le)
  have hsimp :
      (n : ℝ)⁻¹ *
        ((n : ℝ) * (entropy P + eps) +
          eps * ((n : ℝ) * logBase 2 (Fintype.card alpha : ℝ)) + 2) =
        entropy P + eps +
          eps * logBase 2 (Fintype.card alpha : ℝ) + 2 / (n : ℝ) := by
    field_simp [hn_pos.ne']
  exact le_trans hmul (le_of_eq hsimp)

end InformationTheory
