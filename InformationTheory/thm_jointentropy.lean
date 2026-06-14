import InformationTheory.thm_entropy

/-!
# Theorems for Section 2.2: Joint Entropy and Conditional Entropy

This file contains the Lean proofs corresponding to Cover and Thomas,
Section 2.2.
-/

namespace InformationTheory

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

private theorem entropyTermWithBase_chain_atom [Fintype α] [Fintype β]
    (base : ℝ) (P : JointPMF α β) (ab : α × β)
    (hleft : marginalLeftMass P ab.1 ≠ 0) :
    entropyTermWithBase base (P.prob ab) =
      -P.prob ab * logBase base (marginalLeftMass P ab.1) +
        conditionalEntropyTermWithBase base
          (P.prob ab)
          (conditionalMassRightGivenLeft P ab.1 ab.2) := by
  by_cases hp : P.prob ab = 0
  · simp [entropyTermWithBase, conditionalEntropyTermWithBase,
      conditionalMassRightGivenLeft, hp]
  · have hcond : P.prob ab / marginalLeftMass P ab.1 ≠ 0 :=
      div_ne_zero hp hleft
    have hprod :
        marginalLeftMass P ab.1 * (P.prob ab / marginalLeftMass P ab.1) =
          P.prob ab := by
      rw [mul_comm, div_mul_cancel₀ _ hleft]
    calc
      entropyTermWithBase base (P.prob ab) =
          -P.prob ab *
            logBase base
              (marginalLeftMass P ab.1 *
                (P.prob ab / marginalLeftMass P ab.1)) := by
            rw [hprod]
            rfl
      _ = -P.prob ab *
          (logBase base (marginalLeftMass P ab.1) +
            logBase base (P.prob ab / marginalLeftMass P ab.1)) := by
            unfold logBase
            rw [Real.logb_mul hleft hcond]
      _ = -P.prob ab * logBase base (marginalLeftMass P ab.1) +
          conditionalEntropyTermWithBase base
            (P.prob ab)
            (conditionalMassRightGivenLeft P ab.1 ab.2) := by
            unfold conditionalEntropyTermWithBase conditionalMassRightGivenLeft
            ring

private theorem sum_joint_marginalLog_eq_marginalLeftEntropyWithBase
    [Fintype α] [Fintype β] (base : ℝ) (P : JointPMF α β) :
    Finset.univ.sum (fun ab : α × β =>
      -P.prob ab * logBase base (marginalLeftMass P ab.1)) =
        marginalLeftEntropyWithBase base P := by
  unfold marginalLeftEntropyWithBase marginalLeftMass entropyTermWithBase
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun a _ => by
    change
      Finset.univ.sum (fun y : β =>
        -P.prob (a, y) *
          logBase base (Finset.univ.sum (fun b : β => P.prob (a, b)))) =
        (-Finset.univ.sum (fun b : β => P.prob (a, b))) *
          logBase base (Finset.univ.sum (fun b : β => P.prob (a, b)))
    rw [← Finset.sum_mul, Finset.sum_neg_distrib]

/-- Theorem 2.2.1, with an arbitrary logarithm base. -/
theorem jointEntropyWithBase_chain_rule [Fintype α] [Fintype β]
    (base : ℝ) (P : JointPMF α β)
    (hleft : ∀ a : α, marginalLeftMass P a ≠ 0) :
    jointEntropyWithBase base P =
      marginalLeftEntropyWithBase base P + conditionalEntropyWithBase base P := by
  calc
    jointEntropyWithBase base P =
        Finset.univ.sum (fun ab : α × β =>
          entropyTermWithBase base (P.prob ab)) := rfl
    _ = Finset.univ.sum (fun ab : α × β =>
          -P.prob ab * logBase base (marginalLeftMass P ab.1) +
            conditionalEntropyTermWithBase base
              (P.prob ab)
              (conditionalMassRightGivenLeft P ab.1 ab.2)) := by
          exact Finset.sum_congr rfl fun ab _ =>
            entropyTermWithBase_chain_atom base P ab (hleft ab.1)
    _ = Finset.univ.sum (fun ab : α × β =>
          -P.prob ab * logBase base (marginalLeftMass P ab.1)) +
        Finset.univ.sum (fun ab : α × β =>
          conditionalEntropyTermWithBase base
            (P.prob ab)
            (conditionalMassRightGivenLeft P ab.1 ab.2)) := by
          rw [Finset.sum_add_distrib]
    _ = marginalLeftEntropyWithBase base P + conditionalEntropyWithBase base P := by
          rw [sum_joint_marginalLog_eq_marginalLeftEntropyWithBase]
          rfl

/-- Theorem 2.2.1, in bits. -/
theorem jointEntropy_chain_rule [Fintype α] [Fintype β]
    (P : JointPMF α β) (hleft : ∀ a : α, marginalLeftMass P a ≠ 0) :
    jointEntropy P = marginalLeftEntropy P + conditionalEntropy P := by
  simpa [jointEntropy, marginalLeftEntropy, conditionalEntropy] using
    jointEntropyWithBase_chain_rule (base := 2) P hleft

/--
Corollary after Theorem 2.2.1, kernel form:
`H(X,Y | Z) = H(X | Z) + H(Y | X,Z)`.
-/
theorem conditionalJointEntropyKernelWithBase_chain_rule
    [Fintype γ] [Fintype α] [Fintype β]
    (base : ℝ) (R : PMF γ) (K : γ -> JointPMF α β)
    (hleft : ∀ z : γ, ∀ a : α, marginalLeftMass (K z) a ≠ 0) :
    conditionalJointEntropyKernelWithBase (α := α) (β := β) base R K =
      conditionalLeftEntropyKernelWithBase (α := α) (β := β) base R K +
        conditionalRightEntropyKernelWithBase (α := α) (β := β) base R K := by
  unfold conditionalJointEntropyKernelWithBase
    conditionalLeftEntropyKernelWithBase conditionalRightEntropyKernelWithBase
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun z _ => by
    calc
      R.prob z * jointEntropyWithBase base (K z) =
          R.prob z *
            (marginalLeftEntropyWithBase base (K z) +
              conditionalEntropyWithBase base (K z)) := by
            rw [jointEntropyWithBase_chain_rule (base := base) (P := K z) (hleft z)]
      _ = R.prob z * marginalLeftEntropyWithBase base (K z) +
          R.prob z * conditionalEntropyWithBase base (K z) := by
            ring

/--
Corollary after Theorem 2.2.1, in bits:
`H(X,Y | Z) = H(X | Z) + H(Y | X,Z)`.
-/
theorem conditionalJointEntropyKernel_chain_rule
    [Fintype γ] [Fintype α] [Fintype β]
    (R : PMF γ) (K : γ -> JointPMF α β)
    (hleft : ∀ z : γ, ∀ a : α, marginalLeftMass (K z) a ≠ 0) :
    conditionalJointEntropyKernel (α := α) (β := β) R K =
      conditionalLeftEntropyKernel (α := α) (β := β) R K +
        conditionalRightEntropyKernel (α := α) (β := β) R K := by
  simpa [conditionalJointEntropyKernel, conditionalLeftEntropyKernel,
    conditionalRightEntropyKernel] using
      conditionalJointEntropyKernelWithBase_chain_rule
        (α := α) (β := β) (base := 2) R K hleft

/-!
## Relationship Between Entropy and Mutual Information
-/

/-- Swap the two coordinates of a joint PMF. -/
noncomputable def swapJointPMF [Fintype α] [Fintype β]
    (P : JointPMF α β) : JointPMF β α where
  prob ba := P.prob (ba.2, ba.1)
  nonneg ba := P.nonneg (ba.2, ba.1)
  sum_eq_one := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simpa [Fintype.sum_prod_type] using P.sum_eq_one

/-- The joint PMF of `(X, X)`. -/
noncomputable def diagonalJointPMF [Fintype α] [DecidableEq α]
    (P : PMF α) : JointPMF α α where
  prob ab := if ab.1 = ab.2 then P.prob ab.1 else 0
  nonneg ab := by
    by_cases h : ab.1 = ab.2
    · simp [h, P.nonneg]
    · simp [h]
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simpa using P.sum_eq_one

private theorem sum_joint_marginalRightLog_eq_marginalRightEntropyWithBase
    [Fintype α] [Fintype β] (base : ℝ) (P : JointPMF α β) :
    Finset.univ.sum (fun ab : α × β =>
      -P.prob ab * logBase base (marginalRightMass P ab.2)) =
        marginalRightEntropyWithBase base P := by
  unfold marginalRightEntropyWithBase marginalRightMass entropyTermWithBase
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => by
    change
      Finset.univ.sum (fun a : α =>
        -P.prob (a, b) *
          logBase base (Finset.univ.sum (fun a : α => P.prob (a, b)))) =
        (-Finset.univ.sum (fun a : α => P.prob (a, b))) *
          logBase base (Finset.univ.sum (fun a : α => P.prob (a, b)))
    rw [← Finset.sum_mul, Finset.sum_neg_distrib]

private theorem mutualInformationTermWithBase_eq_left_sub_cond
    [Fintype α] [Fintype β] (base : ℝ) (P : JointPMF α β) (ab : α × β)
    (hleft : marginalLeftMass P ab.1 ≠ 0)
    (hright : marginalRightMass P ab.2 ≠ 0) :
    mutualInformationTermWithBase base
        (P.prob ab) (marginalLeftMass P ab.1) (marginalRightMass P ab.2) =
      -P.prob ab * logBase base (marginalLeftMass P ab.1) -
        conditionalEntropyTermWithBase base
          (P.prob ab)
          (conditionalMassLeftGivenRight P ab.1 ab.2) := by
  by_cases hp : P.prob ab = 0
  · simp [mutualInformationTermWithBase, conditionalEntropyTermWithBase,
      conditionalMassLeftGivenRight, hp]
  · have hcond : P.prob ab / marginalRightMass P ab.2 ≠ 0 :=
      div_ne_zero hp hright
    unfold mutualInformationTermWithBase conditionalEntropyTermWithBase
      conditionalMassLeftGivenRight
    simp [hp]
    rw [show P.prob ab / (marginalLeftMass P ab.1 * marginalRightMass P ab.2) =
        (P.prob ab / marginalRightMass P ab.2) / marginalLeftMass P ab.1 by
          field_simp [hleft, hright]]
    rw [Real.logb_div hcond hleft]
    ring

private theorem mutualInformationTermWithBase_eq_right_sub_cond
    [Fintype α] [Fintype β] (base : ℝ) (P : JointPMF α β) (ab : α × β)
    (hleft : marginalLeftMass P ab.1 ≠ 0)
    (hright : marginalRightMass P ab.2 ≠ 0) :
    mutualInformationTermWithBase base
        (P.prob ab) (marginalLeftMass P ab.1) (marginalRightMass P ab.2) =
      -P.prob ab * logBase base (marginalRightMass P ab.2) -
        conditionalEntropyTermWithBase base
          (P.prob ab)
          (conditionalMassRightGivenLeft P ab.1 ab.2) := by
  by_cases hp : P.prob ab = 0
  · simp [mutualInformationTermWithBase, conditionalEntropyTermWithBase,
      conditionalMassRightGivenLeft, hp]
  · have hcond : P.prob ab / marginalLeftMass P ab.1 ≠ 0 :=
      div_ne_zero hp hleft
    unfold mutualInformationTermWithBase conditionalEntropyTermWithBase
      conditionalMassRightGivenLeft
    simp [hp]
    rw [show P.prob ab / (marginalLeftMass P ab.1 * marginalRightMass P ab.2) =
        (P.prob ab / marginalLeftMass P ab.1) / marginalRightMass P ab.2 by
          field_simp [hleft, hright]]
    rw [Real.logb_div hcond hright]
    ring

/-- Theorem 2.4.1, equation (2.43), with an arbitrary logarithm base. -/
theorem mutualInformationWithBase_eq_marginalLeftEntropy_sub_conditional
    [Fintype α] [Fintype β] (base : ℝ) (P : JointPMF α β)
    (hleft : ∀ a : α, marginalLeftMass P a ≠ 0)
    (hright : ∀ b : β, marginalRightMass P b ≠ 0) :
    mutualInformationWithBase base P =
      marginalLeftEntropyWithBase base P -
        conditionalEntropyLeftGivenRightWithBase base P := by
  calc
    mutualInformationWithBase base P =
        Finset.univ.sum (fun ab : α × β =>
          mutualInformationTermWithBase base
            (P.prob ab) (marginalLeftMass P ab.1) (marginalRightMass P ab.2)) := rfl
    _ = Finset.univ.sum (fun ab : α × β =>
          -P.prob ab * logBase base (marginalLeftMass P ab.1) -
            conditionalEntropyTermWithBase base
              (P.prob ab)
              (conditionalMassLeftGivenRight P ab.1 ab.2)) := by
          exact Finset.sum_congr rfl fun ab _ =>
            mutualInformationTermWithBase_eq_left_sub_cond base P ab
              (hleft ab.1) (hright ab.2)
    _ = Finset.univ.sum (fun ab : α × β =>
          -P.prob ab * logBase base (marginalLeftMass P ab.1)) -
        Finset.univ.sum (fun ab : α × β =>
          conditionalEntropyTermWithBase base
            (P.prob ab)
            (conditionalMassLeftGivenRight P ab.1 ab.2)) := by
          rw [Finset.sum_sub_distrib]
    _ = marginalLeftEntropyWithBase base P -
        conditionalEntropyLeftGivenRightWithBase base P := by
          rw [sum_joint_marginalLog_eq_marginalLeftEntropyWithBase]
          rfl

/-- Theorem 2.4.1, equation (2.44), with an arbitrary logarithm base. -/
theorem mutualInformationWithBase_eq_marginalRightEntropy_sub_conditional
    [Fintype α] [Fintype β] (base : ℝ) (P : JointPMF α β)
    (hleft : ∀ a : α, marginalLeftMass P a ≠ 0)
    (hright : ∀ b : β, marginalRightMass P b ≠ 0) :
    mutualInformationWithBase base P =
      marginalRightEntropyWithBase base P - conditionalEntropyWithBase base P := by
  calc
    mutualInformationWithBase base P =
        Finset.univ.sum (fun ab : α × β =>
          mutualInformationTermWithBase base
            (P.prob ab) (marginalLeftMass P ab.1) (marginalRightMass P ab.2)) := rfl
    _ = Finset.univ.sum (fun ab : α × β =>
          -P.prob ab * logBase base (marginalRightMass P ab.2) -
            conditionalEntropyTermWithBase base
              (P.prob ab)
              (conditionalMassRightGivenLeft P ab.1 ab.2)) := by
          exact Finset.sum_congr rfl fun ab _ =>
            mutualInformationTermWithBase_eq_right_sub_cond base P ab
              (hleft ab.1) (hright ab.2)
    _ = Finset.univ.sum (fun ab : α × β =>
          -P.prob ab * logBase base (marginalRightMass P ab.2)) -
        Finset.univ.sum (fun ab : α × β =>
          conditionalEntropyTermWithBase base
            (P.prob ab)
            (conditionalMassRightGivenLeft P ab.1 ab.2)) := by
          rw [Finset.sum_sub_distrib]
    _ = marginalRightEntropyWithBase base P - conditionalEntropyWithBase base P := by
          rw [sum_joint_marginalRightLog_eq_marginalRightEntropyWithBase]
          rfl

/-- Theorem 2.4.1, equation (2.45), with an arbitrary logarithm base. -/
theorem mutualInformationWithBase_eq_marginal_entropies_sub_joint
    [Fintype α] [Fintype β] (base : ℝ) (P : JointPMF α β)
    (hleft : ∀ a : α, marginalLeftMass P a ≠ 0)
    (hright : ∀ b : β, marginalRightMass P b ≠ 0) :
    mutualInformationWithBase base P =
      marginalLeftEntropyWithBase base P + marginalRightEntropyWithBase base P -
        jointEntropyWithBase base P := by
  calc
    mutualInformationWithBase base P =
        marginalRightEntropyWithBase base P - conditionalEntropyWithBase base P := by
          exact mutualInformationWithBase_eq_marginalRightEntropy_sub_conditional
            base P hleft hright
    _ = marginalLeftEntropyWithBase base P + marginalRightEntropyWithBase base P -
        jointEntropyWithBase base P := by
          have hchain := jointEntropyWithBase_chain_rule base P hleft
          rw [hchain]
          ring

/-- Theorem 2.4.1, equation (2.46), with an arbitrary logarithm base. -/
private theorem mutualInformationTermWithBase_swap_marginals
    (base p px py : ℝ) :
    mutualInformationTermWithBase base p px py =
      mutualInformationTermWithBase base p py px := by
  by_cases hp : p = 0
  · simp [mutualInformationTermWithBase, hp]
  · simp [mutualInformationTermWithBase, hp, mul_comm]

theorem mutualInformationWithBase_comm
    [Fintype α] [Fintype β] (base : ℝ) (P : JointPMF α β) :
    mutualInformationWithBase base P =
      mutualInformationWithBase base (swapJointPMF P) := by
  unfold mutualInformationWithBase mutualInformationFromMassWithBase
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun a _ => by
      simp [swapJointPMF]
      exact mutualInformationTermWithBase_swap_marginals base (P.prob (a, b))
        (Finset.univ.sum fun y : β => P.prob (a, y))
        (Finset.univ.sum fun x : α => P.prob (x, b))

private theorem mutualInformationTermWithBase_self_atom
    (base p : ℝ) (hp : p ≠ 0) :
    mutualInformationTermWithBase base p p p = entropyTermWithBase base p := by
  unfold mutualInformationTermWithBase entropyTermWithBase
  simp [hp]

private theorem diagonalJointPMF_marginalLeftMass
    [Fintype α] [DecidableEq α] (P : PMF α) (a : α) :
    marginalLeftMass (diagonalJointPMF P) a = P.prob a := by
  unfold marginalLeftMass diagonalJointPMF
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    have hne : a ≠ b := Ne.symm hb
    simp [hne]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ a))

private theorem diagonalJointPMF_marginalRightMass
    [Fintype α] [DecidableEq α] (P : PMF α) (a : α) :
    marginalRightMass (diagonalJointPMF P) a = P.prob a := by
  unfold marginalRightMass diagonalJointPMF
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ a))

/-- Theorem 2.4.1, equation (2.47), with an arbitrary logarithm base. -/
theorem mutualInformationWithBase_self
    [Fintype α] [DecidableEq α] (base : ℝ) (P : PMF α)
    (hP : ∀ a : α, P.prob a ≠ 0) :
    mutualInformationWithBase base (diagonalJointPMF P) = entropyWithBase base P := by
  unfold mutualInformationWithBase mutualInformationFromMassWithBase entropyWithBase
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun a _ => by
    rw [Finset.sum_eq_single a]
    · change
        mutualInformationTermWithBase base
            ((diagonalJointPMF P).prob (a, a))
            (marginalLeftMass (diagonalJointPMF P) a)
            (marginalRightMass (diagonalJointPMF P) a) =
          entropyTermWithBase base (P.prob a)
      rw [diagonalJointPMF_marginalLeftMass, diagonalJointPMF_marginalRightMass]
      simpa [diagonalJointPMF] using
        mutualInformationTermWithBase_self_atom base (P.prob a) (hP a)
    · intro b _ hb
      have hne : a ≠ b := Ne.symm hb
      simp [diagonalJointPMF, hne, mutualInformationTermWithBase]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ a))

/-- Theorem 2.4.1, equations (2.43)--(2.46), in bits. -/
theorem theorem_2_4_1_mutualInformation_entropy
    [Fintype α] [Fintype β] (P : JointPMF α β)
    (hleft : ∀ a : α, marginalLeftMass P a ≠ 0)
    (hright : ∀ b : β, marginalRightMass P b ≠ 0) :
    mutualInformation P =
        marginalLeftEntropy P - conditionalEntropyLeftGivenRight P ∧
      mutualInformation P =
        marginalRightEntropy P - conditionalEntropy P ∧
      mutualInformation P =
        marginalLeftEntropy P + marginalRightEntropy P - jointEntropy P ∧
      mutualInformation P = mutualInformation (swapJointPMF P) := by
  constructor
  · simpa [mutualInformation, marginalLeftEntropy, conditionalEntropyLeftGivenRight] using
      mutualInformationWithBase_eq_marginalLeftEntropy_sub_conditional
        (base := 2) P hleft hright
  constructor
  · simpa [mutualInformation, marginalRightEntropy, conditionalEntropy] using
      mutualInformationWithBase_eq_marginalRightEntropy_sub_conditional
        (base := 2) P hleft hright
  constructor
  · simpa [mutualInformation, marginalLeftEntropy, marginalRightEntropy, jointEntropy] using
      mutualInformationWithBase_eq_marginal_entropies_sub_joint
        (base := 2) P hleft hright
  · simpa [mutualInformation] using
      mutualInformationWithBase_comm (base := 2) P

/-- Theorem 2.4.1, equation (2.47), in bits. -/
theorem theorem_2_4_1_mutualInformation_self
    [Fintype α] [DecidableEq α] (P : PMF α)
    (hP : ∀ a : α, P.prob a ≠ 0) :
    mutualInformation (diagonalJointPMF P) = entropy P := by
  simpa [mutualInformation, entropy] using
    mutualInformationWithBase_self (base := 2) P hP

end InformationTheory
