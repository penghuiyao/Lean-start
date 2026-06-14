import InformationTheory.thm_jointentropy

/-!
# Theorems for Section 2.5: Chain Rules

This file contains the Lean proofs corresponding to Cover and Thomas,
Section 2.5.  The finite-`n` textbook formulas are represented through the
one-step kernel identities that are iterated in the paper proof, together with
the finite-sum algebra used to pass from entropy chain rules to information
chain rules.
-/

namespace InformationTheory

universe u v w z

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Type z}

/-!
## CHAIN RULES FOR ENTROPY, RELATIVE ENTROPY,AND MUTUAL INFORMATION
-/

/-- Theorem 2.5.1, one-step kernel form, with an arbitrary logarithm base. -/
theorem theorem_2_5_1_entropy_chain_rule_withBase
    [Fintype γ] [Fintype α] [Fintype β]
    (base : ℝ) (R : PMF γ) (K : γ -> JointPMF α β)
    (hleft : ∀ z : γ, ∀ a : α, marginalLeftMass (K z) a ≠ 0) :
    conditionalJointEntropyKernelWithBase (α := α) (β := β) base R K =
      conditionalLeftEntropyKernelWithBase (α := α) (β := β) base R K +
        conditionalRightEntropyKernelWithBase (α := α) (β := β) base R K :=
  conditionalJointEntropyKernelWithBase_chain_rule (α := α) (β := β)
    (base := base) R K hleft

/-- Theorem 2.5.1, one-step kernel form, in bits. -/
theorem theorem_2_5_1_entropy_chain_rule
    [Fintype γ] [Fintype α] [Fintype β]
    (R : PMF γ) (K : γ -> JointPMF α β)
    (hleft : ∀ z : γ, ∀ a : α, marginalLeftMass (K z) a ≠ 0) :
    conditionalJointEntropyKernel (α := α) (β := β) R K =
      conditionalLeftEntropyKernel (α := α) (β := β) R K +
        conditionalRightEntropyKernel (α := α) (β := β) R K :=
  conditionalJointEntropyKernel_chain_rule (α := α) (β := β) R K hleft

/--
Conditional mutual information as the difference of the two entropy-chain-rule
summands, with an arbitrary logarithm base.
-/
theorem conditionalMutualInformationKernelWithBase_eq_entropy_sub
    [Fintype γ] [Fintype α] [Fintype β]
    (base : ℝ) (R : PMF γ) (K : γ -> JointPMF α β)
    (hleft : ∀ z : γ, ∀ a : α, marginalLeftMass (K z) a ≠ 0)
    (hright : ∀ z : γ, ∀ b : β, marginalRightMass (K z) b ≠ 0) :
    conditionalMutualInformationKernelWithBase (α := α) (β := β) base R K =
      conditionalLeftEntropyKernelWithBase (α := α) (β := β) base R K -
        conditionalLeftGivenRightEntropyKernelWithBase (α := α) (β := β) base R K := by
  unfold conditionalMutualInformationKernelWithBase
    conditionalLeftEntropyKernelWithBase conditionalLeftGivenRightEntropyKernelWithBase
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun z _ => by
    have hz :=
      mutualInformationWithBase_eq_marginalLeftEntropy_sub_conditional
        (base := base) (P := K z) (hleft z) (hright z)
    calc
      R.prob z * mutualInformationWithBase base (K z) =
          R.prob z *
            (marginalLeftEntropyWithBase base (K z) -
              conditionalEntropyLeftGivenRightWithBase base (K z)) := by
            rw [hz]
      _ = R.prob z * marginalLeftEntropyWithBase base (K z) -
          R.prob z * conditionalEntropyLeftGivenRightWithBase base (K z) := by
            ring

/--
Theorem 2.5.2, finite-sum algebra in the proof of the chain rule for
information: subtracting two entropy chain rules is the sum of the pointwise
differences.
-/
theorem theorem_2_5_2_information_chain_rule_sum
    [Fintype ι] (A B : ι -> ℝ) :
    Finset.univ.sum A - Finset.univ.sum B =
      Finset.univ.sum (fun i : ι => A i - B i) := by
  rw [Finset.sum_sub_distrib]

/-- Theorem 2.5.2, one-step conditional-information summand form, in bits. -/
theorem theorem_2_5_2_information_chain_rule
    [Fintype γ] [Fintype α] [Fintype β]
    (R : PMF γ) (K : γ -> JointPMF α β)
    (hleft : ∀ z : γ, ∀ a : α, marginalLeftMass (K z) a ≠ 0)
    (hright : ∀ z : γ, ∀ b : β, marginalRightMass (K z) b ≠ 0) :
    conditionalMutualInformationKernel (α := α) (β := β) R K =
      conditionalLeftEntropyKernel (α := α) (β := β) R K -
        conditionalLeftGivenRightEntropyKernel (α := α) (β := β) R K := by
  simpa [conditionalMutualInformationKernel, conditionalLeftEntropyKernel,
    conditionalLeftGivenRightEntropyKernel] using
      conditionalMutualInformationKernelWithBase_eq_entropy_sub
        (α := α) (β := β) (base := 2) R K hleft hright

private theorem relativeEntropyTermWithBase_chain_atom
    [Fintype α] [Fintype β] (base : ℝ) (P Q : JointPMF α β) (ab : α × β)
    (hPleft : marginalLeftMass P ab.1 ≠ 0)
    (hQleft : marginalLeftMass Q ab.1 ≠ 0)
    (hQ : Q.prob ab ≠ 0) :
    relativeEntropyTermWithBase base (P.prob ab) (Q.prob ab) =
      P.prob ab *
          logBase base (marginalLeftMass P ab.1 / marginalLeftMass Q ab.1) +
        weightedLogRatioTermWithBase base
          (P.prob ab)
          (conditionalMassRightGivenLeft P ab.1 ab.2)
          (conditionalMassRightGivenLeft Q ab.1 ab.2) := by
  by_cases hP : P.prob ab = 0
  · simp [relativeEntropyTermWithBase, weightedLogRatioTermWithBase,
      hP]
  · have hleftRatio :
        marginalLeftMass P ab.1 / marginalLeftMass Q ab.1 ≠ 0 :=
      div_ne_zero hPleft hQleft
    have hcondRatio :
        (P.prob ab / marginalLeftMass P ab.1) /
            (Q.prob ab / marginalLeftMass Q ab.1) ≠ 0 :=
      div_ne_zero (div_ne_zero hP hPleft) (div_ne_zero hQ hQleft)
    unfold relativeEntropyTermWithBase weightedLogRatioTermWithBase
      conditionalMassRightGivenLeft
    simp [hP]
    rw [show P.prob ab / Q.prob ab =
        (marginalLeftMass P ab.1 / marginalLeftMass Q ab.1) *
          ((P.prob ab / marginalLeftMass P ab.1) /
            (Q.prob ab / marginalLeftMass Q ab.1)) by
          field_simp [hP, hQ, hPleft, hQleft]]
    rw [Real.logb_mul hleftRatio hcondRatio]
    ring

private theorem sum_joint_leftLogRatio_eq_marginalRelativeEntropy
    [Fintype α] [Fintype β] (base : ℝ) (P Q : JointPMF α β)
    (hPleft : ∀ a : α, marginalLeftMass P a ≠ 0) :
    Finset.univ.sum (fun ab : α × β =>
      P.prob ab * logBase base (marginalLeftMass P ab.1 / marginalLeftMass Q ab.1)) =
        relativeEntropyFromMassWithBase base
          (marginalLeftMass P) (marginalLeftMass Q) := by
  unfold relativeEntropyFromMassWithBase relativeEntropyTermWithBase
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun a _ => by
    change
      (Finset.univ.sum fun y : β =>
        P.prob (a, y) *
          logBase base (marginalLeftMass P a / marginalLeftMass Q a)) =
        if marginalLeftMass P a = 0 then 0
        else
          marginalLeftMass P a *
            logBase base (marginalLeftMass P a / marginalLeftMass Q a)
    rw [← Finset.sum_mul]
    change
      marginalLeftMass P a *
          logBase base (marginalLeftMass P a / marginalLeftMass Q a) =
        if marginalLeftMass P a = 0 then 0
        else
          marginalLeftMass P a *
            logBase base (marginalLeftMass P a / marginalLeftMass Q a)
    simp [hPleft a]

/-- Theorem 2.5.3, chain rule for relative entropy, with an arbitrary base. -/
theorem relativeEntropyFromMassWithBase_chain_rule
    [Fintype α] [Fintype β] (base : ℝ) (P Q : JointPMF α β)
    (hPleft : ∀ a : α, marginalLeftMass P a ≠ 0)
    (hQleft : ∀ a : α, marginalLeftMass Q a ≠ 0)
    (hQ : ∀ ab : α × β, Q.prob ab ≠ 0) :
    relativeEntropyFromMassWithBase base P.prob Q.prob =
      relativeEntropyFromMassWithBase base
          (marginalLeftMass P) (marginalLeftMass Q) +
        conditionalRelativeEntropyWithBase base P Q := by
  calc
    relativeEntropyFromMassWithBase base P.prob Q.prob =
        Finset.univ.sum (fun ab : α × β =>
          P.prob ab *
              logBase base (marginalLeftMass P ab.1 / marginalLeftMass Q ab.1) +
            weightedLogRatioTermWithBase base
              (P.prob ab)
              (conditionalMassRightGivenLeft P ab.1 ab.2)
              (conditionalMassRightGivenLeft Q ab.1 ab.2)) := by
          unfold relativeEntropyFromMassWithBase
          exact Finset.sum_congr rfl fun ab _ =>
            relativeEntropyTermWithBase_chain_atom base P Q ab
              (hPleft ab.1) (hQleft ab.1) (hQ ab)
    _ = Finset.univ.sum (fun ab : α × β =>
          P.prob ab *
            logBase base (marginalLeftMass P ab.1 / marginalLeftMass Q ab.1)) +
        Finset.univ.sum (fun ab : α × β =>
          weightedLogRatioTermWithBase base
            (P.prob ab)
            (conditionalMassRightGivenLeft P ab.1 ab.2)
            (conditionalMassRightGivenLeft Q ab.1 ab.2)) := by
          rw [Finset.sum_add_distrib]
    _ = relativeEntropyFromMassWithBase base
          (marginalLeftMass P) (marginalLeftMass Q) +
        conditionalRelativeEntropyWithBase base P Q := by
          rw [sum_joint_leftLogRatio_eq_marginalRelativeEntropy base P Q hPleft]
          rfl

/-- Theorem 2.5.3, chain rule for relative entropy, in bits. -/
theorem theorem_2_5_3_relativeEntropy_chain_rule
    [Fintype α] [Fintype β] (P Q : JointPMF α β)
    (hPleft : ∀ a : α, marginalLeftMass P a ≠ 0)
    (hQleft : ∀ a : α, marginalLeftMass Q a ≠ 0)
    (hQ : ∀ ab : α × β, Q.prob ab ≠ 0) :
    relativeEntropyFromMass P.prob Q.prob =
      relativeEntropyFromMass (marginalLeftMass P) (marginalLeftMass Q) +
        conditionalRelativeEntropy P Q := by
  simpa [relativeEntropyFromMass, conditionalRelativeEntropy] using
    relativeEntropyFromMassWithBase_chain_rule (base := 2) P Q hPleft hQleft hQ

end InformationTheory
