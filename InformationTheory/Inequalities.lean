import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import InformationTheory.Channels
import InformationTheory.Jensen
import InformationTheory.logsum
import InformationTheory.Thm_chainrule

/-!
# Inequality targets

This file records named proposition shapes for the core inequalities.  The
statements will be sharpened as the surrounding definitions mature.
-/

namespace InformationTheory

universe u v w

variable {α : Type u} {β : Type v}

/-- Target shape for nonnegativity of Shannon entropy. -/
def EntropyNonnegativeTarget [Fintype α] (P : PMF α) : Prop :=
  0 ≤ H P

/-- Target shape for Gibbs' inequality. -/
def GibbsInequalityTarget [Fintype α] (P Q : PMF α) : Prop :=
  0 ≤ KL P Q

/-- Target shape for nonnegativity of mutual information. -/
def MutualInformationNonnegativeTarget [Fintype α] [Fintype β]
    (P : JointPMF α β) : Prop :=
  0 ≤ mutualInformation P

/-!
## JENSEN’S INEQUALITY AND ITS CONSEQUENCES
-/

private theorem relativeEntropyTerm_gap_nonneg
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hac : p ≠ 0 -> q ≠ 0) :
    0 ≤ relativeEntropyTermWithBase 2 p q - (p - q) / Real.log 2 := by
  have hlog_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  by_cases hp0 : p = 0
  · subst hp0
    unfold relativeEntropyTermWithBase
    simp
    have hqdiv : 0 ≤ q / Real.log 2 := div_nonneg hq hlog_pos.le
    simpa only [neg_div] using (neg_nonpos.mpr hqdiv)
  · have hp_pos : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
    have hq0 : q ≠ 0 := hac hp0
    have hq_pos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
    have hratio_nonneg : 0 ≤ p / q := div_nonneg hp hq
    have hmul :
        p - q ≤ p * Real.log (p / q) := by
      have hbase := Real.self_sub_one_le_mul_log hratio_nonneg
      have hmul' :
          q * (p / q - 1) ≤ q * ((p / q) * Real.log (p / q)) :=
        mul_le_mul_of_nonneg_left hbase hq
      calc
        p - q = q * (p / q - 1) := by field_simp [hq0]
        _ ≤ q * ((p / q) * Real.log (p / q)) := hmul'
        _ = p * Real.log (p / q) := by field_simp [hq0]
    have hdiv :
        (p - q) / Real.log 2 ≤
          (p * Real.log (p / q)) / Real.log 2 :=
      div_le_div_of_nonneg_right hmul hlog_pos.le
    have hterm :
        relativeEntropyTermWithBase 2 p q =
          (p * Real.log (p / q)) / Real.log 2 := by
      unfold relativeEntropyTermWithBase logBase
      simp [hp0]
      rw [← Real.log_div_log]
      ring
    linarith

private theorem relativeEntropyTerm_gap_pos_of_ne
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hac : p ≠ 0 -> q ≠ 0)
    (hpq : p ≠ q) :
    0 < relativeEntropyTermWithBase 2 p q - (p - q) / Real.log 2 := by
  have hlog_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  by_cases hp0 : p = 0
  · subst hp0
    have hq_ne : q ≠ 0 := by
      intro hq0
      exact hpq hq0.symm
    have hq_pos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq_ne)
    unfold relativeEntropyTermWithBase
    simp
    have hqdiv : 0 < q / Real.log 2 := div_pos hq_pos hlog_pos
    simpa only [neg_div] using (neg_lt_zero.mpr hqdiv)
  · have hp_pos : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
    have hq0 : q ≠ 0 := hac hp0
    have hq_pos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
    have hratio_nonneg : 0 ≤ p / q := div_nonneg hp hq
    have hratio_ne_one : p / q ≠ 1 := by
      intro h
      apply hpq
      calc
        p = (p / q) * q := by field_simp [hq0]
        _ = q := by rw [h, one_mul]
    have hmul :
        p - q < p * Real.log (p / q) := by
      have hbase := Real.self_sub_one_lt_mul_log hratio_nonneg hratio_ne_one
      have hmul' :
          q * (p / q - 1) < q * ((p / q) * Real.log (p / q)) :=
        mul_lt_mul_of_pos_left hbase hq_pos
      calc
        p - q = q * (p / q - 1) := by field_simp [hq0]
        _ < q * ((p / q) * Real.log (p / q)) := hmul'
        _ = p * Real.log (p / q) := by field_simp [hq0]
    have hdiv :
        (p - q) / Real.log 2 <
          (p * Real.log (p / q)) / Real.log 2 :=
      div_lt_div_of_pos_right hmul hlog_pos
    have hterm :
        relativeEntropyTermWithBase 2 p q =
          (p * Real.log (p / q)) / Real.log 2 := by
      unfold relativeEntropyTermWithBase logBase
      simp [hp0]
      rw [← Real.log_div_log]
      ring
    linarith

private theorem relativeEntropyFromMass_eq_sum_gap [Fintype α]
    {p q : α -> ℝ} (hp_sum : Finset.univ.sum p = 1)
    (hq_sum : Finset.univ.sum q = 1) :
    relativeEntropyFromMass p q =
      Finset.univ.sum (fun a : α =>
        relativeEntropyTermWithBase 2 (p a) (q a) - (p a - q a) / Real.log 2) := by
  unfold relativeEntropyFromMass relativeEntropyFromMassWithBase
  calc
    Finset.univ.sum (fun a : α => relativeEntropyTermWithBase 2 (p a) (q a)) =
        Finset.univ.sum (fun a : α =>
          (relativeEntropyTermWithBase 2 (p a) (q a) -
              (p a - q a) / Real.log 2) +
            (p a - q a) / Real.log 2) := by
          exact Finset.sum_congr rfl fun a _ => by ring
    _ =
        Finset.univ.sum (fun a : α =>
          relativeEntropyTermWithBase 2 (p a) (q a) -
            (p a - q a) / Real.log 2) +
          Finset.univ.sum (fun a : α => (p a - q a) / Real.log 2) := by
          rw [Finset.sum_add_distrib]
    _ =
        Finset.univ.sum (fun a : α =>
          relativeEntropyTermWithBase 2 (p a) (q a) -
            (p a - q a) / Real.log 2) := by
          have hcorr :
              Finset.univ.sum (fun a : α => (p a - q a) / Real.log 2) = 0 := by
            change
              Finset.univ.sum (fun a : α => (p a - q a) * (Real.log 2)⁻¹) = 0
            rw [← Finset.sum_mul, Finset.sum_sub_distrib, hp_sum, hq_sum]
            ring
          rw [hcorr, add_zero]

/-- Theorem 2.6.3, information inequality, for finite real mass functions. -/
theorem relativeEntropyFromMass_nonneg [Fintype α]
    {p q : α -> ℝ}
    (hp_nonneg : ∀ a, 0 ≤ p a) (hq_nonneg : ∀ a, 0 ≤ q a)
    (hp_sum : Finset.univ.sum p = 1) (hq_sum : Finset.univ.sum q = 1)
    (hac : ∀ a, p a ≠ 0 -> q a ≠ 0) :
    0 ≤ relativeEntropyFromMass p q := by
  rw [relativeEntropyFromMass_eq_sum_gap hp_sum hq_sum]
  exact Finset.sum_nonneg fun a _ =>
    relativeEntropyTerm_gap_nonneg (hp_nonneg a) (hq_nonneg a) (hac a)

/--
Theorem 2.6.3, equality case for the information inequality, for finite real
mass functions.
-/
theorem relativeEntropyFromMass_eq_zero_iff [Fintype α]
    {p q : α -> ℝ}
    (hp_nonneg : ∀ a, 0 ≤ p a) (hq_nonneg : ∀ a, 0 ≤ q a)
    (hp_sum : Finset.univ.sum p = 1) (hq_sum : Finset.univ.sum q = 1)
    (hac : ∀ a, p a ≠ 0 -> q a ≠ 0) :
    relativeEntropyFromMass p q = 0 ↔ ∀ a, p a = q a := by
  constructor
  · intro hzero a
    rw [relativeEntropyFromMass_eq_sum_gap hp_sum hq_sum] at hzero
    have hgap_zero :
        ∀ a, relativeEntropyTermWithBase 2 (p a) (q a) -
            (p a - q a) / Real.log 2 = 0 := by
      intro a
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun a _ => relativeEntropyTerm_gap_nonneg
          (hp_nonneg a) (hq_nonneg a) (hac a))).mp hzero a (Finset.mem_univ a)
    by_contra hneq
    have hpos := relativeEntropyTerm_gap_pos_of_ne
      (hp_nonneg a) (hq_nonneg a) (hac a) hneq
    rw [hgap_zero a] at hpos
    exact (lt_irrefl (0 : ℝ)) hpos
  · intro h
    unfold relativeEntropyFromMass relativeEntropyFromMassWithBase
    exact Finset.sum_eq_zero fun a _ => by
      unfold relativeEntropyTermWithBase logBase
      by_cases hp0 : p a = 0
      · simp [hp0]
      · have hq0 : q a ≠ 0 := by simpa [h a] using hp0
        have hratio : p a / q a = 1 := by
          rw [h a, div_self hq0]
        simp [hp0, hratio]

/-- Theorem 2.6.3, information inequality, for bundled PMFs. -/
theorem theorem_2_6_3_information_inequality [Fintype α]
    (P Q : PMF α) (hac : ∀ a, P.prob a ≠ 0 -> Q.prob a ≠ 0) :
    0 ≤ relativeEntropy P Q := by
  simpa [relativeEntropy, relativeEntropyWithBase] using
    relativeEntropyFromMass_nonneg
      (p := P.prob) (q := Q.prob)
      P.nonneg Q.nonneg P.sum_eq_one Q.sum_eq_one hac

/-- Theorem 2.6.3, equality case, for bundled PMFs. -/
theorem theorem_2_6_3_information_inequality_eq_zero_iff [Fintype α]
    (P Q : PMF α) (hac : ∀ a, P.prob a ≠ 0 -> Q.prob a ≠ 0) :
    relativeEntropy P Q = 0 ↔ ∀ a, P.prob a = Q.prob a := by
  simpa [relativeEntropy, relativeEntropyWithBase] using
    relativeEntropyFromMass_eq_zero_iff
      (p := P.prob) (q := Q.prob)
      P.nonneg Q.nonneg P.sum_eq_one Q.sum_eq_one hac

/-- Independence of the two coordinates of a bundled joint PMF. -/
def JointIndependent [Fintype α] [Fintype β] (P : JointPMF α β) : Prop :=
  ∀ ab : α × β,
    P.prob ab = marginalLeftMass P ab.1 * marginalRightMass P ab.2

private theorem marginalLeftMass_nonneg [Fintype α] [Fintype β]
    (P : JointPMF α β) (a : α) :
    0 ≤ marginalLeftMass P a := by
  unfold marginalLeftMass
  exact Finset.sum_nonneg fun b _ => P.nonneg (a, b)

private theorem marginalRightMass_nonneg [Fintype α] [Fintype β]
    (P : JointPMF α β) (b : β) :
    0 ≤ marginalRightMass P b := by
  unfold marginalRightMass
  exact Finset.sum_nonneg fun a _ => P.nonneg (a, b)

private theorem marginalLeftMass_sum_eq_one [Fintype α] [Fintype β]
    (P : JointPMF α β) :
    Finset.univ.sum (marginalLeftMass P) = 1 := by
  unfold marginalLeftMass
  rw [← Fintype.sum_prod_type]
  exact P.sum_eq_one

private theorem marginalRightMass_sum_eq_one [Fintype α] [Fintype β]
    (P : JointPMF α β) :
    Finset.univ.sum (marginalRightMass P) = 1 := by
  unfold marginalRightMass
  rw [Finset.sum_comm]
  simpa [Fintype.sum_prod_type] using P.sum_eq_one

private theorem productMarginalMass_sum_eq_one [Fintype α] [Fintype β]
    (P : JointPMF α β) :
    Finset.univ.sum (fun ab : α × β =>
      marginalLeftMass P ab.1 * marginalRightMass P ab.2) = 1 := by
  rw [Fintype.sum_prod_type]
  calc
    Finset.univ.sum (fun a : α =>
        Finset.univ.sum (fun b : β =>
          marginalLeftMass P a * marginalRightMass P b)) =
        Finset.univ.sum (fun a : α =>
          marginalLeftMass P a * Finset.univ.sum (marginalRightMass P)) := by
          exact Finset.sum_congr rfl fun a _ => by
            rw [Finset.mul_sum]
    _ = Finset.univ.sum (marginalLeftMass P) *
        Finset.univ.sum (marginalRightMass P) := by
          rw [Finset.sum_mul]
    _ = 1 := by
          rw [marginalLeftMass_sum_eq_one P, marginalRightMass_sum_eq_one P]
          ring

private theorem marginalLeftMass_pos_of_joint_ne_zero [Fintype α] [Fintype β]
    (P : JointPMF α β) {ab : α × β} (h : P.prob ab ≠ 0) :
    0 < marginalLeftMass P ab.1 := by
  have hp_pos : 0 < P.prob ab := lt_of_le_of_ne (P.nonneg ab) (Ne.symm h)
  have hle : P.prob ab ≤ marginalLeftMass P ab.1 := by
    unfold marginalLeftMass
    simpa using
      Finset.single_le_sum
        (fun b _ => P.nonneg (ab.1, b)) (Finset.mem_univ ab.2)
  exact lt_of_lt_of_le hp_pos hle

private theorem marginalRightMass_pos_of_joint_ne_zero [Fintype α] [Fintype β]
    (P : JointPMF α β) {ab : α × β} (h : P.prob ab ≠ 0) :
    0 < marginalRightMass P ab.2 := by
  have hp_pos : 0 < P.prob ab := lt_of_le_of_ne (P.nonneg ab) (Ne.symm h)
  have hle : P.prob ab ≤ marginalRightMass P ab.2 := by
    unfold marginalRightMass
    simpa using
      Finset.single_le_sum
        (fun a _ => P.nonneg (a, ab.2)) (Finset.mem_univ ab.1)
  exact lt_of_lt_of_le hp_pos hle

private theorem productMarginalMass_ac [Fintype α] [Fintype β]
    (P : JointPMF α β) :
    ∀ ab : α × β, P.prob ab ≠ 0 ->
      marginalLeftMass P ab.1 * marginalRightMass P ab.2 ≠ 0 := by
  intro ab h
  exact mul_ne_zero
    (ne_of_gt (marginalLeftMass_pos_of_joint_ne_zero P h))
    (ne_of_gt (marginalRightMass_pos_of_joint_ne_zero P h))

/-- Corollary after Theorem 2.6.3: mutual information is nonnegative. -/
theorem theorem_2_6_3_mutualInformation_nonneg
    [Fintype α] [Fintype β] (P : JointPMF α β) :
    0 ≤ mutualInformation P := by
  simpa [mutualInformation, mutualInformationWithBase,
    mutualInformationFromMass, mutualInformationFromMassWithBase,
    relativeEntropyFromMass, relativeEntropyFromMassWithBase] using
      relativeEntropyFromMass_nonneg
        (p := P.prob)
        (q := fun ab : α × β =>
          marginalLeftMass P ab.1 * marginalRightMass P ab.2)
        P.nonneg
        (fun ab => mul_nonneg
          (marginalLeftMass_nonneg P ab.1)
          (marginalRightMass_nonneg P ab.2))
        P.sum_eq_one
        (productMarginalMass_sum_eq_one P)
        (productMarginalMass_ac P)

/--
Corollary after Theorem 2.6.3: equality in mutual-information nonnegativity
is independence.
-/
theorem theorem_2_6_3_mutualInformation_eq_zero_iff_independent
    [Fintype α] [Fintype β] (P : JointPMF α β) :
    mutualInformation P = 0 ↔ JointIndependent P := by
  simpa [mutualInformation, mutualInformationWithBase,
    mutualInformationFromMass, mutualInformationFromMassWithBase,
    relativeEntropyFromMass, relativeEntropyFromMassWithBase,
    JointIndependent] using
      relativeEntropyFromMass_eq_zero_iff
        (p := P.prob)
        (q := fun ab : α × β =>
          marginalLeftMass P ab.1 * marginalRightMass P ab.2)
        P.nonneg
        (fun ab => mul_nonneg
          (marginalLeftMass_nonneg P ab.1)
          (marginalRightMass_nonneg P ab.2))
        P.sum_eq_one
        (productMarginalMass_sum_eq_one P)
        (productMarginalMass_ac P)

/-- Conditional independence for a kernel `z ↦ law(X,Y | Z=z)`. -/
def ConditionallyIndependentKernel [Fintype γ] [Fintype α] [Fintype β]
    (K : γ -> JointPMF α β) : Prop :=
  ∀ z, JointIndependent (K z)

/-- Corollary after Theorem 2.6.3: conditional mutual information is nonnegative. -/
theorem theorem_2_6_3_conditionalMutualInformation_nonneg
    [Fintype γ] [Fintype α] [Fintype β]
    (R : PMF γ) (K : γ -> JointPMF α β) :
    0 ≤ conditionalMutualInformationKernel R K := by
  unfold conditionalMutualInformationKernel conditionalMutualInformationKernelWithBase
  exact Finset.sum_nonneg fun z _ =>
    mul_nonneg (R.nonneg z)
      (by simpa [mutualInformation] using
        theorem_2_6_3_mutualInformation_nonneg (K z))

/--
Corollary after Theorem 2.6.3: equality in conditional mutual information is
conditional independence on every positive-probability conditioning atom.
-/
theorem theorem_2_6_3_conditionalMutualInformation_eq_zero_iff
    [Fintype γ] [Fintype α] [Fintype β]
    (R : PMF γ) (K : γ -> JointPMF α β)
    (hR : ∀ z, R.prob z ≠ 0) :
    conditionalMutualInformationKernel R K = 0 ↔
      ConditionallyIndependentKernel K := by
  unfold conditionalMutualInformationKernel conditionalMutualInformationKernelWithBase
  constructor
  · intro hzero z
    have hterm :
        ∀ z, R.prob z * mutualInformationWithBase 2 (K z) = 0 := by
      intro z
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun z _ => mul_nonneg (R.nonneg z)
          (by simpa [mutualInformation] using
            theorem_2_6_3_mutualInformation_nonneg (K z)))).mp hzero
        z (Finset.mem_univ z)
    have hmi : mutualInformation (K z) = 0 := by
      have hz := hterm z
      cases mul_eq_zero.mp hz with
      | inl hzR => exact False.elim (hR z hzR)
      | inr hzI => simpa [mutualInformation] using hzI
    exact (theorem_2_6_3_mutualInformation_eq_zero_iff_independent (K z)).mp hmi
  · intro hcond
    exact Finset.sum_eq_zero fun z _ => by
      have hmi : mutualInformationWithBase 2 (K z) = 0 := by
        simpa [mutualInformation] using
          (theorem_2_6_3_mutualInformation_eq_zero_iff_independent (K z)).mpr
            (hcond z)
      rw [hmi, mul_zero]

private theorem conditionalMassRightGivenLeft_nonneg
    [Fintype α] [Fintype β] (P : JointPMF α β) (a : α) (b : β)
    (hleft : marginalLeftMass P a ≠ 0) :
    0 ≤ conditionalMassRightGivenLeft P a b := by
  have hleft_pos : 0 < marginalLeftMass P a :=
    lt_of_le_of_ne (marginalLeftMass_nonneg P a) (Ne.symm hleft)
  exact div_nonneg (P.nonneg (a, b)) hleft_pos.le

private theorem conditionalMassRightGivenLeft_sum_eq_one
    [Fintype α] [Fintype β] (P : JointPMF α β) (a : α)
    (hleft : marginalLeftMass P a ≠ 0) :
    Finset.univ.sum (fun b : β => conditionalMassRightGivenLeft P a b) = 1 := by
  unfold conditionalMassRightGivenLeft
  rw [← Finset.sum_div]
  change marginalLeftMass P a / marginalLeftMass P a = 1
  exact div_self hleft

private theorem conditionalMassRightGivenLeft_ac
    [Fintype α] [Fintype β] (P Q : JointPMF α β)
    (hQleft : ∀ a : α, marginalLeftMass Q a ≠ 0)
    (hac : ∀ ab : α × β, P.prob ab ≠ 0 -> Q.prob ab ≠ 0) :
    ∀ a b,
      conditionalMassRightGivenLeft P a b ≠ 0 ->
        conditionalMassRightGivenLeft Q a b ≠ 0 := by
  intro a b hcond
  have hPab : P.prob (a, b) ≠ 0 := by
    intro hp
    simp [conditionalMassRightGivenLeft, hp] at hcond
  exact div_ne_zero (hac (a, b) hPab) (hQleft a)

private theorem conditionalRelativeEntropy_eq_sum_rows
    [Fintype α] [Fintype β] (P Q : JointPMF α β)
    (hPleft : ∀ a : α, marginalLeftMass P a ≠ 0) :
    conditionalRelativeEntropy P Q =
      Finset.univ.sum (fun a : α =>
        marginalLeftMass P a *
          relativeEntropyFromMass
            (fun b : β => conditionalMassRightGivenLeft P a b)
            (fun b : β => conditionalMassRightGivenLeft Q a b)) := by
  unfold conditionalRelativeEntropy conditionalRelativeEntropyWithBase
    relativeEntropyFromMass relativeEntropyFromMassWithBase
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun a _ => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by
      by_cases hp : P.prob (a, b) = 0
      · have hcond : conditionalMassRightGivenLeft P a b = 0 := by
          simp [conditionalMassRightGivenLeft, hp]
        simp [weightedLogRatioTermWithBase, relativeEntropyTermWithBase, hp, hcond]
      · have hcond : conditionalMassRightGivenLeft P a b ≠ 0 :=
          div_ne_zero hp (hPleft a)
        unfold weightedLogRatioTermWithBase relativeEntropyTermWithBase
          conditionalMassRightGivenLeft
        simp [hp]
        field_simp [hPleft a]
        simp [hPleft a]

/--
Corollary after Theorem 2.6.3: conditional relative entropy is nonnegative.
-/
theorem theorem_2_6_3_conditionalRelativeEntropy_nonneg
    [Fintype α] [Fintype β] (P Q : JointPMF α β)
    (hPleft : ∀ a : α, marginalLeftMass P a ≠ 0)
    (hQleft : ∀ a : α, marginalLeftMass Q a ≠ 0)
    (hac : ∀ ab : α × β, P.prob ab ≠ 0 -> Q.prob ab ≠ 0) :
    0 ≤ conditionalRelativeEntropy P Q := by
  rw [conditionalRelativeEntropy_eq_sum_rows P Q hPleft]
  exact Finset.sum_nonneg fun a _ =>
    mul_nonneg (marginalLeftMass_nonneg P a)
      (relativeEntropyFromMass_nonneg
        (p := fun b : β => conditionalMassRightGivenLeft P a b)
        (q := fun b : β => conditionalMassRightGivenLeft Q a b)
        (fun b => conditionalMassRightGivenLeft_nonneg P a b (hPleft a))
        (fun b => conditionalMassRightGivenLeft_nonneg Q a b (hQleft a))
        (conditionalMassRightGivenLeft_sum_eq_one P a (hPleft a))
        (conditionalMassRightGivenLeft_sum_eq_one Q a (hQleft a))
        (conditionalMassRightGivenLeft_ac P Q hQleft hac a))

/--
Corollary after Theorem 2.6.3, equality case for conditional relative entropy.
-/
theorem theorem_2_6_3_conditionalRelativeEntropy_eq_zero_iff
    [Fintype α] [Fintype β] (P Q : JointPMF α β)
    (hPleft : ∀ a : α, marginalLeftMass P a ≠ 0)
    (hQleft : ∀ a : α, marginalLeftMass Q a ≠ 0)
    (hac : ∀ ab : α × β, P.prob ab ≠ 0 -> Q.prob ab ≠ 0) :
    conditionalRelativeEntropy P Q = 0 ↔
      ∀ a b,
        conditionalMassRightGivenLeft P a b =
          conditionalMassRightGivenLeft Q a b := by
  rw [conditionalRelativeEntropy_eq_sum_rows P Q hPleft]
  constructor
  · intro hzero a b
    have hrowTermZero :
        ∀ a : α,
          marginalLeftMass P a *
              relativeEntropyFromMass
                (fun b : β => conditionalMassRightGivenLeft P a b)
                (fun b : β => conditionalMassRightGivenLeft Q a b) = 0 := by
      intro a
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun a _ => mul_nonneg (marginalLeftMass_nonneg P a)
          (relativeEntropyFromMass_nonneg
            (p := fun b : β => conditionalMassRightGivenLeft P a b)
            (q := fun b : β => conditionalMassRightGivenLeft Q a b)
            (fun b => conditionalMassRightGivenLeft_nonneg P a b (hPleft a))
            (fun b => conditionalMassRightGivenLeft_nonneg Q a b (hQleft a))
            (conditionalMassRightGivenLeft_sum_eq_one P a (hPleft a))
            (conditionalMassRightGivenLeft_sum_eq_one Q a (hQleft a))
            (conditionalMassRightGivenLeft_ac P Q hQleft hac a)))).mp
        hzero a (Finset.mem_univ a)
    have hrowZero :
        relativeEntropyFromMass
          (fun b : β => conditionalMassRightGivenLeft P a b)
          (fun b : β => conditionalMassRightGivenLeft Q a b) = 0 := by
      have hprod := hrowTermZero a
      cases mul_eq_zero.mp hprod with
      | inl hleft0 => exact False.elim (hPleft a hleft0)
      | inr hD => exact hD
    exact (relativeEntropyFromMass_eq_zero_iff
      (p := fun b : β => conditionalMassRightGivenLeft P a b)
      (q := fun b : β => conditionalMassRightGivenLeft Q a b)
      (fun b => conditionalMassRightGivenLeft_nonneg P a b (hPleft a))
      (fun b => conditionalMassRightGivenLeft_nonneg Q a b (hQleft a))
      (conditionalMassRightGivenLeft_sum_eq_one P a (hPleft a))
      (conditionalMassRightGivenLeft_sum_eq_one Q a (hQleft a))
      (conditionalMassRightGivenLeft_ac P Q hQleft hac a)).mp hrowZero b
  · intro heq
    exact Finset.sum_eq_zero fun a _ => by
      have hrowZero :
          relativeEntropyFromMass
            (fun b : β => conditionalMassRightGivenLeft P a b)
            (fun b : β => conditionalMassRightGivenLeft Q a b) = 0 := by
        apply (relativeEntropyFromMass_eq_zero_iff
          (p := fun b : β => conditionalMassRightGivenLeft P a b)
          (q := fun b : β => conditionalMassRightGivenLeft Q a b)
          (fun b => conditionalMassRightGivenLeft_nonneg P a b (hPleft a))
          (fun b => conditionalMassRightGivenLeft_nonneg Q a b (hQleft a))
          (conditionalMassRightGivenLeft_sum_eq_one P a (hPleft a))
          (conditionalMassRightGivenLeft_sum_eq_one Q a (hQleft a))
          (conditionalMassRightGivenLeft_ac P Q hQleft hac a)).mpr
        intro b
        exact heq a b
      rw [hrowZero, mul_zero]

/-- Uniform PMF on a nonempty finite type. -/
noncomputable def uniformPMF (α : Type u) [Fintype α] [Nonempty α] : PMF α where
  prob _ := (Fintype.card α : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  sum_eq_one := by
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

private theorem uniformPMF_prob_ne_zero
    [Fintype α] [Nonempty α] (a : α) :
    (uniformPMF α).prob a ≠ 0 := by
  unfold uniformPMF
  exact inv_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

private theorem relativeEntropyTerm_uniform_atom
    (n p : ℝ) (hn : n ≠ 0) :
    relativeEntropyTermWithBase 2 p n⁻¹ =
      -entropyTermWithBase 2 p + p * logBase 2 n := by
  by_cases hp : p = 0
  · simp [relativeEntropyTermWithBase, entropyTermWithBase, hp]
  · unfold relativeEntropyTermWithBase entropyTermWithBase
    simp [hp]
    rw [Real.logb_mul hp hn]
    ring

private theorem relativeEntropy_uniform_eq_log_card_sub_entropy
    [Fintype α] [Nonempty α] (P : PMF α) :
    relativeEntropy P (uniformPMF α) =
      logBase 2 (Fintype.card α : ℝ) - entropy P := by
  unfold relativeEntropy relativeEntropyWithBase relativeEntropyFromMassWithBase
    entropy entropyWithBase uniformPMF
  calc
    Finset.univ.sum (fun a : α =>
        relativeEntropyTermWithBase 2 (P.prob a) (Fintype.card α : ℝ)⁻¹) =
        Finset.univ.sum (fun a : α =>
          -entropyTermWithBase 2 (P.prob a) +
            P.prob a * logBase 2 (Fintype.card α : ℝ)) := by
          exact Finset.sum_congr rfl fun a _ =>
            relativeEntropyTerm_uniform_atom
              (Fintype.card α : ℝ) (P.prob a)
              (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    _ = -Finset.univ.sum (fun a : α => entropyTermWithBase 2 (P.prob a)) +
        Finset.univ.sum (fun a : α =>
          P.prob a * logBase 2 (Fintype.card α : ℝ)) := by
          rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ = -Finset.univ.sum (fun a : α => entropyTermWithBase 2 (P.prob a)) +
        logBase 2 (Fintype.card α : ℝ) := by
          rw [← Finset.sum_mul, P.sum_eq_one, one_mul]
    _ = logBase 2 (Fintype.card α : ℝ) -
        Finset.univ.sum (fun a : α => entropyTermWithBase 2 (P.prob a)) := by
          ring

/-- Theorem 2.6.4: entropy is at most the logarithm of the alphabet size. -/
theorem theorem_2_6_4_entropy_le_log_card
    [Fintype α] [Nonempty α] (P : PMF α) :
    entropy P ≤ logBase 2 (Fintype.card α : ℝ) := by
  have hD : 0 ≤ relativeEntropy P (uniformPMF α) :=
    theorem_2_6_3_information_inequality P (uniformPMF α)
      (fun a _ => uniformPMF_prob_ne_zero a)
  rw [relativeEntropy_uniform_eq_log_card_sub_entropy] at hD
  linarith

/-- Theorem 2.6.4, equality case: equality holds exactly for the uniform PMF. -/
theorem theorem_2_6_4_entropy_eq_log_card_iff_uniform
    [Fintype α] [Nonempty α] (P : PMF α) :
    entropy P = logBase 2 (Fintype.card α : ℝ) ↔
      ∀ a, P.prob a = (Fintype.card α : ℝ)⁻¹ := by
  have hiff :=
    theorem_2_6_3_information_inequality_eq_zero_iff P (uniformPMF α)
      (fun a _ => uniformPMF_prob_ne_zero a)
  constructor
  · intro h
    apply hiff.mp
    rw [relativeEntropy_uniform_eq_log_card_sub_entropy]
    linarith
  · intro h
    have hD : relativeEntropy P (uniformPMF α) = 0 := by
      apply hiff.mpr
      intro a
      simpa [uniformPMF] using h a
    rw [relativeEntropy_uniform_eq_log_card_sub_entropy] at hD
    linarith

/-- Theorem 2.6.5: conditioning reduces entropy, `H(X | Y) ≤ H(X)`. -/
theorem theorem_2_6_5_conditioning_reduces_entropy
    [Fintype α] [Fintype β] (P : JointPMF α β)
    (hleft : ∀ a : α, marginalLeftMass P a ≠ 0)
    (hright : ∀ b : β, marginalRightMass P b ≠ 0) :
    conditionalEntropyLeftGivenRight P ≤ marginalLeftEntropy P := by
  have hmi :=
    mutualInformationWithBase_eq_marginalLeftEntropy_sub_conditional
      (base := 2) P hleft hright
  have hnonneg : 0 ≤ mutualInformationWithBase 2 P := by
    simpa [mutualInformation] using theorem_2_6_3_mutualInformation_nonneg P
  rw [hmi] at hnonneg
  unfold conditionalEntropyLeftGivenRight marginalLeftEntropy
  linarith

/-- Theorem 2.6.5, equality case: equality holds exactly under independence. -/
theorem theorem_2_6_5_conditioning_reduces_entropy_eq_iff_independent
    [Fintype α] [Fintype β] (P : JointPMF α β)
    (hleft : ∀ a : α, marginalLeftMass P a ≠ 0)
    (hright : ∀ b : β, marginalRightMass P b ≠ 0) :
    conditionalEntropyLeftGivenRight P = marginalLeftEntropy P ↔
      JointIndependent P := by
  have hmi :=
    mutualInformationWithBase_eq_marginalLeftEntropy_sub_conditional
      (base := 2) P hleft hright
  constructor
  · intro h
    apply (theorem_2_6_3_mutualInformation_eq_zero_iff_independent P).mp
    have hzero : mutualInformationWithBase 2 P = 0 := by
      rw [hmi]
      unfold conditionalEntropyLeftGivenRight marginalLeftEntropy at h
      linarith
    simpa [mutualInformation] using hzero
  · intro hind
    have hzero : mutualInformationWithBase 2 P = 0 := by
      simpa [mutualInformation] using
        (theorem_2_6_3_mutualInformation_eq_zero_iff_independent P).mpr hind
    rw [hmi] at hzero
    unfold conditionalEntropyLeftGivenRight marginalLeftEntropy
    linarith

/-!
## LOG SUM INEQUALITY AND ITS APPLICATIONS
-/

/-- Pointwise mixture of two finite mass functions. -/
noncomputable def mixMass (theta : ℝ) (p q : α -> ℝ) : α -> ℝ :=
  fun a => theta * p a + (1 - theta) * q a

/-- Mixture of two PMFs. -/
noncomputable def mixPMF [Fintype α] (theta : ℝ)
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1) (P Q : PMF α) : PMF α where
  prob := mixMass theta P.prob Q.prob
  nonneg a := by
    unfold mixMass
    exact add_nonneg
      (mul_nonneg htheta0 (P.nonneg a))
      (mul_nonneg (sub_nonneg.mpr htheta1) (Q.nonneg a))
  sum_eq_one := by
    unfold mixMass
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      P.sum_eq_one, Q.sum_eq_one]
    ring

/-- Product PMF on a product alphabet. -/
noncomputable def productPMF [Fintype α] [Fintype β]
    (P : PMF α) (Q : PMF β) : JointPMF α β where
  prob := productMass P Q
  nonneg ab := mul_nonneg (P.nonneg ab.1) (Q.nonneg ab.2)
  sum_eq_one := by
    unfold productMass
    rw [Fintype.sum_prod_type]
    calc
      Finset.univ.sum (fun a : α =>
          Finset.univ.sum (fun b : β => P.prob a * Q.prob b)) =
          Finset.univ.sum (fun a : α => P.prob a * Finset.univ.sum Q.prob) := by
            exact Finset.sum_congr rfl fun a _ => by
              rw [Finset.mul_sum]
      _ = Finset.univ.sum (fun a : α => P.prob a) := by
            rw [Q.sum_eq_one]
            simp
      _ = 1 := P.sum_eq_one

/-- Output law induced by an input PMF and a channel. -/
noncomputable def outputPMF [Fintype α] [Fintype β]
    (P : PMF α) (W : Channel α β) : PMF β where
  prob := outputMass P W
  nonneg b := by
    unfold outputMass
    exact Finset.sum_nonneg fun a _ => mul_nonneg (P.nonneg a) ((W a).nonneg b)
  sum_eq_one := by
    unfold outputMass
    calc
      Finset.univ.sum (fun b : β =>
          Finset.univ.sum (fun a : α => P.prob a * (W a).prob b)) =
          Finset.univ.sum (fun a : α =>
            Finset.univ.sum (fun b : β => P.prob a * (W a).prob b)) := by
            rw [Finset.sum_comm]
      _ = Finset.univ.sum (fun a : α => P.prob a) := by
            exact Finset.sum_congr rfl fun a _ => by
              rw [← Finset.mul_sum, (W a).sum_eq_one, mul_one]
      _ = 1 := P.sum_eq_one

/-- Joint law induced by an input PMF and a channel. -/
noncomputable def channelJointPMF [Fintype α] [Fintype β]
    (P : PMF α) (W : Channel α β) : JointPMF α β where
  prob := jointMassOfChannel P W
  nonneg ab := mul_nonneg (P.nonneg ab.1) ((W ab.1).nonneg ab.2)
  sum_eq_one := by
    unfold jointMassOfChannel
    rw [Fintype.sum_prod_type]
    calc
      Finset.univ.sum (fun a : α =>
          Finset.univ.sum (fun b : β => P.prob a * (W a).prob b)) =
          Finset.univ.sum (fun a : α => P.prob a) := by
            exact Finset.sum_congr rfl fun a _ => by
              rw [← Finset.mul_sum, (W a).sum_eq_one, mul_one]
      _ = 1 := P.sum_eq_one

/-- Product of the input law and the induced output law. -/
noncomputable def channelProductPMF [Fintype α] [Fintype β]
    (P : PMF α) (W : Channel α β) : JointPMF α β :=
  productPMF P (outputPMF P W)

/-- Mixture of two channels, row by row. -/
noncomputable def mixChannel [Fintype β] (theta : ℝ)
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (W₁ W₂ : Channel α β) : Channel α β :=
  fun a => mixPMF theta htheta0 htheta1 (W₁ a) (W₂ a)

/-- Conditional entropy of a channel under an input PMF, with arbitrary base. -/
noncomputable def channelConditionalEntropyWithBase [Fintype α] [Fintype β]
    (base : ℝ) (P : PMF α) (W : Channel α β) : ℝ :=
  Finset.univ.sum (fun a : α => P.prob a * entropyWithBase base (W a))

/-- Conditional entropy of a channel under an input PMF, in bits. -/
noncomputable def channelConditionalEntropy [Fintype α] [Fintype β]
    (P : PMF α) (W : Channel α β) : ℝ :=
  channelConditionalEntropyWithBase 2 P W

private theorem relativeEntropyTermWithBase_scale
    (c p q : ℝ) :
    relativeEntropyTermWithBase 2 (c * p) (c * q) =
      c * relativeEntropyTermWithBase 2 p q := by
  by_cases hc : c = 0
  · simp [relativeEntropyTermWithBase, hc]
  · by_cases hp : p = 0
    · simp [relativeEntropyTermWithBase, hp]
    · have hcp : c * p ≠ 0 := mul_ne_zero hc hp
      unfold relativeEntropyTermWithBase
      simp [hp, hcp]
      have hratio : (c * p) / (c * q) = p / q := by
        field_simp [hc]
      rw [hratio]
      ring

private theorem relativeEntropyTermWithBase_mix_convex
    (theta p₁ p₂ q₁ q₂ : ℝ)
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂)
    (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (hac₁ : p₁ ≠ 0 -> q₁ ≠ 0)
    (hac₂ : p₂ ≠ 0 -> q₂ ≠ 0) :
    relativeEntropyTermWithBase 2
        (theta * p₁ + (1 - theta) * p₂)
        (theta * q₁ + (1 - theta) * q₂) ≤
      theta * relativeEntropyTermWithBase 2 p₁ q₁ +
        (1 - theta) * relativeEntropyTermWithBase 2 p₂ q₂ := by
  have htheta1_nonneg : 0 ≤ 1 - theta := sub_nonneg.mpr htheta1
  have hlog :=
    theorem_2_7_1_logSumInequality
      (ι := Bool)
      (fun t => if t then (1 - theta) * p₂ else theta * p₁)
      (fun t => if t then (1 - theta) * q₂ else theta * q₁)
      (by
        intro t
        cases t <;> simp [mul_nonneg, htheta0, htheta1_nonneg, hp₁, hp₂])
      (by
        intro t
        cases t <;> simp [mul_nonneg, htheta0, htheta1_nonneg, hq₁, hq₂])
      (by
        intro t ht
        cases t
        · simp at ht ⊢
          exact ⟨ht.1, hac₁ ht.2⟩
        · simp at ht ⊢
          exact ⟨ht.1, hac₂ ht.2⟩)
  simpa [relativeEntropyFromMass, relativeEntropyFromMassWithBase,
    relativeEntropyTermWithBase_scale, add_comm, add_left_comm, add_assoc] using hlog

/-- Theorem 2.7.2: relative entropy is convex in the pair `(p, q)`. -/
theorem theorem_2_7_2_relativeEntropy_convex
    [Fintype α] (theta : ℝ) (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (P₁ Q₁ P₂ Q₂ : PMF α)
    (hac₁ : ∀ a, P₁.prob a ≠ 0 -> Q₁.prob a ≠ 0)
    (hac₂ : ∀ a, P₂.prob a ≠ 0 -> Q₂.prob a ≠ 0) :
    relativeEntropy
        (mixPMF theta htheta0 htheta1 P₁ P₂)
        (mixPMF theta htheta0 htheta1 Q₁ Q₂) ≤
      theta * relativeEntropy P₁ Q₁ + (1 - theta) * relativeEntropy P₂ Q₂ := by
  unfold relativeEntropy relativeEntropyWithBase relativeEntropyFromMassWithBase
    mixPMF mixMass
  calc
    Finset.univ.sum (fun a : α =>
        relativeEntropyTermWithBase 2
          (theta * P₁.prob a + (1 - theta) * P₂.prob a)
          (theta * Q₁.prob a + (1 - theta) * Q₂.prob a)) ≤
        Finset.univ.sum (fun a : α =>
          theta * relativeEntropyTermWithBase 2 (P₁.prob a) (Q₁.prob a) +
            (1 - theta) * relativeEntropyTermWithBase 2 (P₂.prob a) (Q₂.prob a)) := by
          exact Finset.sum_le_sum fun a _ =>
            relativeEntropyTermWithBase_mix_convex theta
              (P₁.prob a) (P₂.prob a) (Q₁.prob a) (Q₂.prob a)
              htheta0 htheta1 (P₁.nonneg a) (P₂.nonneg a) (Q₁.nonneg a) (Q₂.nonneg a)
              (hac₁ a) (hac₂ a)
    _ = theta * Finset.univ.sum (fun a : α =>
          relativeEntropyTermWithBase 2 (P₁.prob a) (Q₁.prob a)) +
        (1 - theta) * Finset.univ.sum (fun a : α =>
          relativeEntropyTermWithBase 2 (P₂.prob a) (Q₂.prob a)) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

private theorem relativeEntropy_mix_uniform_eq
    [Fintype α] [Nonempty α] (theta : ℝ) (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (P : PMF α) :
    relativeEntropy P (mixPMF theta htheta0 htheta1 (uniformPMF α) (uniformPMF α)) =
      relativeEntropy P (uniformPMF α) := by
  unfold relativeEntropy relativeEntropyWithBase relativeEntropyFromMassWithBase
    mixPMF mixMass uniformPMF
  exact Finset.sum_congr rfl fun a _ => by
    congr 2
    ring_nf

/-- Theorem 2.7.3: entropy is concave as a function of the distribution. -/
theorem theorem_2_7_3_entropy_concave
    [Fintype α] [Nonempty α] (theta : ℝ) (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (P₁ P₂ : PMF α) :
    theta * entropy P₁ + (1 - theta) * entropy P₂ ≤
      entropy (mixPMF theta htheta0 htheta1 P₁ P₂) := by
  let U := uniformPMF α
  have hconv :=
    theorem_2_7_2_relativeEntropy_convex
      (theta := theta) htheta0 htheta1 P₁ U P₂ U
      (fun a _ => uniformPMF_prob_ne_zero a)
      (fun a _ => uniformPMF_prob_ne_zero a)
  rw [relativeEntropy_mix_uniform_eq theta htheta0 htheta1
    (mixPMF theta htheta0 htheta1 P₁ P₂)] at hconv
  repeat rw [relativeEntropy_uniform_eq_log_card_sub_entropy] at hconv
  have hsum : theta + (1 - theta) = 1 := by ring
  linarith

private theorem entropy_eq_of_prob [Fintype α] {P Q : PMF α}
    (h : ∀ a, P.prob a = Q.prob a) :
    entropy P = entropy Q := by
  unfold entropy entropyWithBase
  exact Finset.sum_congr rfl fun a _ => by rw [h a]

private theorem relativeEntropy_eq_of_prob [Fintype α]
    {P Q R S : PMF α}
    (hP : ∀ a, P.prob a = R.prob a)
    (hQ : ∀ a, Q.prob a = S.prob a) :
    relativeEntropy P Q = relativeEntropy R S := by
  unfold relativeEntropy relativeEntropyWithBase relativeEntropyFromMassWithBase
  exact Finset.sum_congr rfl fun a _ => by rw [hP a, hQ a]

private theorem marginalLeftMass_channelJointPMF [Fintype α] [Fintype β]
    (P : PMF α) (W : Channel α β) (a : α) :
    marginalLeftMass (channelJointPMF P W) a = P.prob a := by
  unfold marginalLeftMass channelJointPMF jointMassOfChannel
  change Finset.univ.sum (fun b : β => P.prob a * (W a).prob b) = P.prob a
  rw [← Finset.mul_sum, (W a).sum_eq_one, mul_one]

private theorem marginalRightMass_channelJointPMF [Fintype α] [Fintype β]
    (P : PMF α) (W : Channel α β) (b : β) :
    marginalRightMass (channelJointPMF P W) b = outputMass P W b := by
  rfl

private theorem marginalRightEntropyWithBase_channelJointPMF
    [Fintype α] [Fintype β] (base : ℝ) (P : PMF α) (W : Channel α β) :
    marginalRightEntropyWithBase base (channelJointPMF P W) =
      entropyWithBase base (outputPMF P W) := by
  unfold marginalRightEntropyWithBase entropyWithBase outputPMF
  exact Finset.sum_congr rfl fun b _ => by
    rw [marginalRightMass_channelJointPMF]

private theorem conditionalEntropyWithBase_channelJointPMF_eq_channelConditionalEntropyWithBase
    [Fintype α] [Fintype β] (base : ℝ) (P : PMF α) (W : Channel α β)
    (hP : ∀ a : α, P.prob a ≠ 0) :
    conditionalEntropyWithBase base (channelJointPMF P W) =
      channelConditionalEntropyWithBase base P W := by
  unfold conditionalEntropyWithBase channelConditionalEntropyWithBase
    entropyWithBase
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun a _ => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by
      unfold conditionalEntropyTermWithBase entropyTermWithBase
        conditionalMassRightGivenLeft
      rw [marginalLeftMass_channelJointPMF]
      unfold channelJointPMF jointMassOfChannel
      have hcond :
          (P.prob a * (W a).prob b) / P.prob a = (W a).prob b := by
        field_simp [hP a]
      rw [hcond]
      ring

private theorem channelMutualInformation_eq_entropy_sub
    [Fintype α] [Fintype β] (P : PMF α) (W : Channel α β)
    (hP : ∀ a : α, P.prob a ≠ 0)
    (hOut : ∀ b : β, outputMass P W b ≠ 0) :
    channelMutualInformation P W =
      entropy (outputPMF P W) - channelConditionalEntropy P W := by
  have hmi :=
    mutualInformationWithBase_eq_marginalRightEntropy_sub_conditional
      (base := 2) (P := channelJointPMF P W)
      (fun a => by
        rw [marginalLeftMass_channelJointPMF]
        exact hP a)
      (fun b => by
        rw [marginalRightMass_channelJointPMF]
        exact hOut b)
  calc
    channelMutualInformation P W =
        mutualInformationWithBase 2 (channelJointPMF P W) := rfl
    _ = marginalRightEntropyWithBase 2 (channelJointPMF P W) -
        conditionalEntropyWithBase 2 (channelJointPMF P W) := hmi
    _ = entropy (outputPMF P W) - channelConditionalEntropy P W := by
        rw [marginalRightEntropyWithBase_channelJointPMF,
          conditionalEntropyWithBase_channelJointPMF_eq_channelConditionalEntropyWithBase
            (base := 2) (P := P) (W := W) hP]
        rfl

private theorem channelMutualInformation_eq_relativeEntropyProduct
    [Fintype α] [Fintype β] (P : PMF α) (W : Channel α β) :
    channelMutualInformation P W =
      relativeEntropy (channelJointPMF P W) (channelProductPMF P W) := by
  unfold channelMutualInformation mutualInformationFromMass mutualInformationFromMassWithBase
    relativeEntropy relativeEntropyWithBase relativeEntropyFromMassWithBase
  exact Finset.sum_congr rfl fun ab _ => by
    unfold channelJointPMF channelProductPMF productPMF productMass outputPMF
      jointMassOfChannel
    by_cases hxy : P.prob ab.1 * (W ab.1).prob ab.2 = 0
    · simp [mutualInformationTermWithBase, relativeEntropyTermWithBase, hxy]
    · unfold mutualInformationTermWithBase relativeEntropyTermWithBase
      simp [hxy]
      have hleft :
          Finset.univ.sum (fun b : β => P.prob ab.1 * (W ab.1).prob b) =
            P.prob ab.1 := by
        rw [← Finset.mul_sum, (W ab.1).sum_eq_one, mul_one]
      rw [hleft]
      unfold outputMass
      rfl

private theorem outputPMF_mix_input_prob [Fintype α] [Fintype β]
    (theta : ℝ) (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (P₁ P₂ : PMF α) (W : Channel α β) (b : β) :
    (outputPMF (mixPMF theta htheta0 htheta1 P₁ P₂) W).prob b =
      (mixPMF theta htheta0 htheta1 (outputPMF P₁ W) (outputPMF P₂ W)).prob b := by
  unfold outputPMF outputMass mixPMF mixMass
  calc
    Finset.univ.sum (fun a : α =>
        (theta * P₁.prob a + (1 - theta) * P₂.prob a) * (W a).prob b) =
        Finset.univ.sum (fun a : α =>
          theta * (P₁.prob a * (W a).prob b) +
            (1 - theta) * (P₂.prob a * (W a).prob b)) := by
          exact Finset.sum_congr rfl fun a _ => by ring
    _ = theta * Finset.univ.sum (fun a : α => P₁.prob a * (W a).prob b) +
        (1 - theta) * Finset.univ.sum (fun a : α => P₂.prob a * (W a).prob b) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

private theorem channelConditionalEntropy_mix_input [Fintype α] [Fintype β]
    (theta : ℝ) (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (P₁ P₂ : PMF α) (W : Channel α β) :
    channelConditionalEntropy (mixPMF theta htheta0 htheta1 P₁ P₂) W =
      theta * channelConditionalEntropy P₁ W +
        (1 - theta) * channelConditionalEntropy P₂ W := by
  unfold channelConditionalEntropy channelConditionalEntropyWithBase mixPMF mixMass
  calc
    Finset.univ.sum (fun a : α =>
        (theta * P₁.prob a + (1 - theta) * P₂.prob a) *
          entropyWithBase 2 (W a)) =
        Finset.univ.sum (fun a : α =>
          theta * (P₁.prob a * entropyWithBase 2 (W a)) +
            (1 - theta) * (P₂.prob a * entropyWithBase 2 (W a))) := by
          exact Finset.sum_congr rfl fun a _ => by ring
    _ = theta * Finset.univ.sum (fun a : α =>
          P₁.prob a * entropyWithBase 2 (W a)) +
        (1 - theta) * Finset.univ.sum (fun a : α =>
          P₂.prob a * entropyWithBase 2 (W a)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/--
Theorem 2.7.4, first part: for a fixed channel, mutual information is
concave as a function of the input distribution.

The support hypotheses are the finite-real side conditions needed by the
entropy identity from Theorem 2.4.1.
-/
theorem theorem_2_7_4_mutualInformation_concave_input
    [Fintype α] [Fintype β] [Nonempty β]
    (theta : ℝ) (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (P₁ P₂ : PMF α) (W : Channel α β)
    (hP₁ : ∀ a : α, P₁.prob a ≠ 0)
    (hP₂ : ∀ a : α, P₂.prob a ≠ 0)
    (hPmix : ∀ a : α, (mixPMF theta htheta0 htheta1 P₁ P₂).prob a ≠ 0)
    (hOut₁ : ∀ b : β, outputMass P₁ W b ≠ 0)
    (hOut₂ : ∀ b : β, outputMass P₂ W b ≠ 0)
    (hOutMix : ∀ b : β, outputMass (mixPMF theta htheta0 htheta1 P₁ P₂) W b ≠ 0) :
    theta * channelMutualInformation P₁ W +
        (1 - theta) * channelMutualInformation P₂ W ≤
      channelMutualInformation (mixPMF theta htheta0 htheta1 P₁ P₂) W := by
  let Pmix := mixPMF theta htheta0 htheta1 P₁ P₂
  have hEntropy :=
    theorem_2_7_3_entropy_concave
      (α := β) theta htheta0 htheta1 (outputPMF P₁ W) (outputPMF P₂ W)
  have hOutputEntropy :
      entropy (mixPMF theta htheta0 htheta1 (outputPMF P₁ W) (outputPMF P₂ W)) =
        entropy (outputPMF Pmix W) := by
    apply entropy_eq_of_prob
    intro b
    exact (outputPMF_mix_input_prob theta htheta0 htheta1 P₁ P₂ W b).symm
  rw [hOutputEntropy] at hEntropy
  have hCond :
      channelConditionalEntropy Pmix W =
        theta * channelConditionalEntropy P₁ W +
          (1 - theta) * channelConditionalEntropy P₂ W := by
    simpa [Pmix] using
      channelConditionalEntropy_mix_input theta htheta0 htheta1 P₁ P₂ W
  rw [channelMutualInformation_eq_entropy_sub P₁ W hP₁ hOut₁,
    channelMutualInformation_eq_entropy_sub P₂ W hP₂ hOut₂,
    channelMutualInformation_eq_entropy_sub Pmix W (by simpa [Pmix] using hPmix)
      (by simpa [Pmix] using hOutMix),
    hCond]
  linarith

private theorem channelJointPMF_mix_channel_prob [Fintype α] [Fintype β]
    (theta : ℝ) (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (P : PMF α) (W₁ W₂ : Channel α β) (ab : α × β) :
    (channelJointPMF P (mixChannel theta htheta0 htheta1 W₁ W₂)).prob ab =
      (mixPMF theta htheta0 htheta1
        (channelJointPMF P W₁) (channelJointPMF P W₂)).prob ab := by
  unfold channelJointPMF jointMassOfChannel mixChannel mixPMF mixMass
  ring

private theorem outputPMF_mix_channel_prob [Fintype α] [Fintype β]
    (theta : ℝ) (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (P : PMF α) (W₁ W₂ : Channel α β) (b : β) :
    (outputPMF P (mixChannel theta htheta0 htheta1 W₁ W₂)).prob b =
      (mixPMF theta htheta0 htheta1 (outputPMF P W₁) (outputPMF P W₂)).prob b := by
  unfold outputPMF outputMass mixChannel mixPMF mixMass
  calc
    Finset.univ.sum (fun a : α =>
        P.prob a *
          (theta * (W₁ a).prob b + (1 - theta) * (W₂ a).prob b)) =
        Finset.univ.sum (fun a : α =>
          theta * (P.prob a * (W₁ a).prob b) +
            (1 - theta) * (P.prob a * (W₂ a).prob b)) := by
          exact Finset.sum_congr rfl fun a _ => by ring
    _ = theta * Finset.univ.sum (fun a : α => P.prob a * (W₁ a).prob b) +
        (1 - theta) * Finset.univ.sum (fun a : α => P.prob a * (W₂ a).prob b) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

private theorem channelProductPMF_mix_channel_prob [Fintype α] [Fintype β]
    (theta : ℝ) (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (P : PMF α) (W₁ W₂ : Channel α β) (ab : α × β) :
    (channelProductPMF P (mixChannel theta htheta0 htheta1 W₁ W₂)).prob ab =
      (mixPMF theta htheta0 htheta1
        (channelProductPMF P W₁) (channelProductPMF P W₂)).prob ab := by
  unfold channelProductPMF productPMF productMass
  change
    P.prob ab.1 * (outputPMF P (mixChannel theta htheta0 htheta1 W₁ W₂)).prob ab.2 =
      theta * (P.prob ab.1 * (outputPMF P W₁).prob ab.2) +
        (1 - theta) * (P.prob ab.1 * (outputPMF P W₂).prob ab.2)
  rw [outputPMF_mix_channel_prob theta htheta0 htheta1 P W₁ W₂ ab.2]
  unfold mixPMF mixMass
  ring

private theorem channelProductPMF_ac [Fintype α] [Fintype β]
    (P : PMF α) (W : Channel α β) :
    ∀ ab : α × β,
      (channelJointPMF P W).prob ab ≠ 0 ->
        (channelProductPMF P W).prob ab ≠ 0 := by
  intro ab h
  have hjoint :
      P.prob ab.1 * (W ab.1).prob ab.2 ≠ 0 := by
    simpa [channelJointPMF, jointMassOfChannel] using h
  have hp : P.prob ab.1 ≠ 0 := by
    intro hp0
    exact hjoint (by simp [hp0])
  have hout_pos : 0 < outputMass P W ab.2 := by
    have hm :=
      marginalRightMass_pos_of_joint_ne_zero
        (P := channelJointPMF P W) h
    simpa [marginalRightMass_channelJointPMF] using hm
  unfold channelProductPMF productPMF productMass outputPMF
  change P.prob ab.1 * outputMass P W ab.2 ≠ 0
  exact mul_ne_zero hp (ne_of_gt hout_pos)

/--
Theorem 2.7.4, second part: for a fixed input distribution, mutual information
is convex as a function of the channel.
-/
theorem theorem_2_7_4_mutualInformation_convex_channel
    [Fintype α] [Fintype β]
    (theta : ℝ) (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (P : PMF α) (W₁ W₂ : Channel α β) :
    channelMutualInformation P (mixChannel theta htheta0 htheta1 W₁ W₂) ≤
      theta * channelMutualInformation P W₁ +
        (1 - theta) * channelMutualInformation P W₂ := by
  let Wmix := mixChannel theta htheta0 htheta1 W₁ W₂
  have hconv :=
    theorem_2_7_2_relativeEntropy_convex
      (theta := theta) htheta0 htheta1
      (channelJointPMF P W₁) (channelProductPMF P W₁)
      (channelJointPMF P W₂) (channelProductPMF P W₂)
      (channelProductPMF_ac P W₁)
      (channelProductPMF_ac P W₂)
  have hleft :
      relativeEntropy
          (mixPMF theta htheta0 htheta1
            (channelJointPMF P W₁) (channelJointPMF P W₂))
          (mixPMF theta htheta0 htheta1
            (channelProductPMF P W₁) (channelProductPMF P W₂)) =
        relativeEntropy (channelJointPMF P Wmix) (channelProductPMF P Wmix) := by
    apply relativeEntropy_eq_of_prob
    · intro ab
      exact (channelJointPMF_mix_channel_prob theta htheta0 htheta1 P W₁ W₂ ab).symm
    · intro ab
      exact (channelProductPMF_mix_channel_prob theta htheta0 htheta1 P W₁ W₂ ab).symm
  rw [hleft] at hconv
  rw [← channelMutualInformation_eq_relativeEntropyProduct P Wmix,
    ← channelMutualInformation_eq_relativeEntropyProduct P W₁,
    ← channelMutualInformation_eq_relativeEntropyProduct P W₂] at hconv
  simpa [Wmix] using hconv

end InformationTheory
