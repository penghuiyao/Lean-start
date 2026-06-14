import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import InformationTheory.Probability

/-!
# Entropy

This file contains the definitions from Cover and Thomas, Sections 2.1 and 2.2.
Proofs are kept in `InformationTheory.thm_entropy` and
`InformationTheory.thm_jointentropy`.

Mathlib already has the analytic functions `Real.logb`, `Real.negMulLog`, and
`Real.binEntropy`, as well as a measure-theoretic Kullback-Leibler divergence.
The definitions below are the textbook finite-PMF layer for this project, and
are deliberately connected to those mathlib functions rather than duplicating
their analytic content.
-/

namespace InformationTheory

universe u v w z

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type z}

/-!
## ENTROPY

Definitions from Section 2.1.
-/

/-- Logarithm to an arbitrary base, using mathlib's `Real.logb`. -/
noncomputable abbrev logBase (b x : ℝ) : ℝ :=
  Real.logb b x

/-- Base-two logarithm, used throughout the textbook. -/
noncomputable abbrev log2 (x : ℝ) : ℝ :=
  Real.logb 2 x

/-- The entropy summand `-p log_b p`, with the conventional value at `p = 0`. -/
noncomputable def entropyTermWithBase (b p : ℝ) : ℝ :=
  -p * logBase b p

/-- The base-two entropy summand `-p log₂ p`. -/
noncomputable def entropyTerm (p : ℝ) : ℝ :=
  entropyTermWithBase 2 p

/-- Finite expectation `E_p[g(X)] = ∑ x, p(x) g(x)`. -/
noncomputable def expectation [Fintype α] (P : PMF α) (g : α -> ℝ) : ℝ :=
  Finset.univ.sum (fun a => P.prob a * g a)

/-- The self-information `log_b (1 / p(x))` of an atom. -/
noncomputable def informationContentWithBase [Fintype α] (b : ℝ) (P : PMF α) (a : α) :
    ℝ :=
  logBase b (P.prob a)⁻¹

/-- The base-two self-information `log₂ (1 / p(x))` of an atom. -/
noncomputable def informationContent [Fintype α] (P : PMF α) (a : α) : ℝ :=
  informationContentWithBase 2 P a

/-- Shannon entropy of a finite PMF, using an arbitrary logarithm base. -/
noncomputable def entropyWithBase [Fintype α] (b : ℝ) (P : PMF α) : ℝ :=
  Finset.univ.sum (fun a => entropyTermWithBase b (P.prob a))

/-- Shannon entropy of a finite PMF in bits. -/
noncomputable def entropy [Fintype α] (P : PMF α) : ℝ :=
  entropyWithBase 2 P

/-- Shannon entropy of a finite PMF. -/
noncomputable abbrev H [Fintype α] (P : PMF α) : ℝ :=
  entropy P

/-- The binary entropy function from Example 2.1.1, measured in bits. -/
noncomputable def binaryEntropy (p : ℝ) : ℝ :=
  entropyTerm p + entropyTerm (1 - p)

/-!
## JOINT ENTROPY AND CONDITIONAL ENTROPY

Definitions from Section 2.2.
-/

/-- Joint entropy of a finite joint PMF, with an arbitrary logarithm base. -/
noncomputable def jointEntropyWithBase [Fintype α] [Fintype β]
    (b : ℝ) (P : JointPMF α β) : ℝ :=
  entropyWithBase b P

/-- Joint entropy of a finite joint PMF, in bits. -/
noncomputable def jointEntropy [Fintype α] [Fintype β]
    (P : JointPMF α β) : ℝ :=
  jointEntropyWithBase 2 P

/-- Entropy of the left marginal of a joint PMF, with an arbitrary logarithm base. -/
noncomputable def marginalLeftEntropyWithBase [Fintype α] [Fintype β]
    (b : ℝ) (P : JointPMF α β) : ℝ :=
  Finset.univ.sum (fun a : α => entropyTermWithBase b (marginalLeftMass P a))

/-- Entropy of the left marginal of a joint PMF, in bits. -/
noncomputable def marginalLeftEntropy [Fintype α] [Fintype β]
    (P : JointPMF α β) : ℝ :=
  marginalLeftEntropyWithBase 2 P

/-- Entropy of the right marginal of a joint PMF, with an arbitrary logarithm base. -/
noncomputable def marginalRightEntropyWithBase [Fintype α] [Fintype β]
    (b : ℝ) (P : JointPMF α β) : ℝ :=
  Finset.univ.sum (fun a : β => entropyTermWithBase b (marginalRightMass P a))

/-- Entropy of the right marginal of a joint PMF, in bits. -/
noncomputable def marginalRightEntropy [Fintype α] [Fintype β]
    (P : JointPMF α β) : ℝ :=
  marginalRightEntropyWithBase 2 P

/-- The conditional mass `p(y | x)` associated to a joint PMF. -/
noncomputable def conditionalMassRightGivenLeft [Fintype α] [Fintype β]
    (P : JointPMF α β) (a : α) (b : β) : ℝ :=
  P.prob (a, b) / marginalLeftMass P a

/-- The conditional mass `p(x | y)` associated to a joint PMF. -/
noncomputable def conditionalMassLeftGivenRight [Fintype α] [Fintype β]
    (P : JointPMF α β) (a : α) (b : β) : ℝ :=
  P.prob (a, b) / marginalRightMass P b

/-- The conditional-entropy summand `-p(x,y) log_b p(y|x)`. -/
noncomputable def conditionalEntropyTermWithBase (b pxy pyGivenx : ℝ) : ℝ :=
  -pxy * logBase b pyGivenx

/-- Conditional entropy `H(Y | X)` from a joint PMF, with an arbitrary logarithm base. -/
noncomputable def conditionalEntropyWithBase [Fintype α] [Fintype β]
    (b : ℝ) (P : JointPMF α β) : ℝ :=
  Finset.univ.sum (fun ab : α × β =>
    conditionalEntropyTermWithBase b
      (P.prob ab)
      (conditionalMassRightGivenLeft P ab.1 ab.2))

/-- Conditional entropy `H(Y | X)` from a joint PMF, in bits. -/
noncomputable def conditionalEntropy [Fintype α] [Fintype β]
    (P : JointPMF α β) : ℝ :=
  conditionalEntropyWithBase 2 P

/-- Conditional entropy `H(X | Y)` from a joint PMF, with an arbitrary logarithm base. -/
noncomputable def conditionalEntropyLeftGivenRightWithBase [Fintype α] [Fintype β]
    (b : ℝ) (P : JointPMF α β) : ℝ :=
  Finset.univ.sum (fun ab : α × β =>
    conditionalEntropyTermWithBase b
      (P.prob ab)
      (conditionalMassLeftGivenRight P ab.1 ab.2))

/-- Conditional entropy `H(X | Y)` from a joint PMF, in bits. -/
noncomputable def conditionalEntropyLeftGivenRight [Fintype α] [Fintype β]
    (P : JointPMF α β) : ℝ :=
  conditionalEntropyLeftGivenRightWithBase 2 P

/--
Kernel form of `H(X,Y | Z)`: average joint entropy of the conditional joint
laws of `(X,Y)` given `Z`.
-/
noncomputable def conditionalJointEntropyKernelWithBase
    {γ : Type w} [Fintype γ] [Fintype α] [Fintype β]
    (b : ℝ) (R : PMF γ) (K : γ -> JointPMF α β) : ℝ :=
  Finset.univ.sum (fun z : γ => R.prob z * jointEntropyWithBase b (K z))

/-- Kernel form of `H(X | Z)`. -/
noncomputable def conditionalLeftEntropyKernelWithBase
    {γ : Type w} [Fintype γ] [Fintype α] [Fintype β]
    (b : ℝ) (R : PMF γ) (K : γ -> JointPMF α β) : ℝ :=
  Finset.univ.sum (fun z : γ => R.prob z * marginalLeftEntropyWithBase b (K z))

/-- Kernel form of `H(Y | X,Z)`. -/
noncomputable def conditionalRightEntropyKernelWithBase
    {γ : Type w} [Fintype γ] [Fintype α] [Fintype β]
    (b : ℝ) (R : PMF γ) (K : γ -> JointPMF α β) : ℝ :=
  Finset.univ.sum (fun z : γ => R.prob z * conditionalEntropyWithBase b (K z))

/-- Kernel form of `H(X | Y,Z)`. -/
noncomputable def conditionalLeftGivenRightEntropyKernelWithBase
    {γ : Type w} [Fintype γ] [Fintype α] [Fintype β]
    (b : ℝ) (R : PMF γ) (K : γ -> JointPMF α β) : ℝ :=
  Finset.univ.sum (fun z : γ =>
    R.prob z * conditionalEntropyLeftGivenRightWithBase b (K z))

/-- Kernel form of `H(X,Y | Z)`, in bits. -/
noncomputable def conditionalJointEntropyKernel
    {γ : Type w} [Fintype γ] [Fintype α] [Fintype β]
    (R : PMF γ) (K : γ -> JointPMF α β) : ℝ :=
  conditionalJointEntropyKernelWithBase 2 R K

/-- Kernel form of `H(X | Z)`, in bits. -/
noncomputable def conditionalLeftEntropyKernel
    {γ : Type w} [Fintype γ] [Fintype α] [Fintype β]
    (R : PMF γ) (K : γ -> JointPMF α β) : ℝ :=
  conditionalLeftEntropyKernelWithBase 2 R K

/-- Kernel form of `H(Y | X,Z)`, in bits. -/
noncomputable def conditionalRightEntropyKernel
    {γ : Type w} [Fintype γ] [Fintype α] [Fintype β]
    (R : PMF γ) (K : γ -> JointPMF α β) : ℝ :=
  conditionalRightEntropyKernelWithBase 2 R K

/-- Kernel form of `H(X | Y,Z)`, in bits. -/
noncomputable def conditionalLeftGivenRightEntropyKernel
    {γ : Type w} [Fintype γ] [Fintype α] [Fintype β]
    (R : PMF γ) (K : γ -> JointPMF α β) : ℝ :=
  conditionalLeftGivenRightEntropyKernelWithBase 2 R K

/-!
## RELATIVE ENTROPY AND MUTUAL INFORMATION

Early roadmap definitions from Section 2.3 that later files already depend on.
-/

/-- Mutual-information summand `p(x,y) log_b (p(x,y)/(p(x)p(y)))`. -/
noncomputable def mutualInformationTermWithBase (b pxy px py : ℝ) : ℝ :=
  if pxy = 0 then 0 else pxy * logBase b (pxy / (px * py))

/-- Mutual-information summand `p(x,y) log₂ (p(x,y)/(p(x)p(y)))`. -/
noncomputable def mutualInformationTerm (pxy px py : ℝ) : ℝ :=
  mutualInformationTermWithBase 2 pxy px py

/-- Mutual information from an unbundled joint mass function, with an arbitrary base. -/
noncomputable def mutualInformationFromMassWithBase [Fintype α] [Fintype β]
    (b : ℝ) (p : α × β -> ℝ) : ℝ :=
  Finset.univ.sum (fun ab : α × β =>
    mutualInformationTermWithBase b
      (p ab)
      (Finset.univ.sum (fun b : β => p (ab.1, b)))
      (Finset.univ.sum (fun a : α => p (a, ab.2))))

/-- Mutual information from an unbundled joint mass function. -/
noncomputable def mutualInformationFromMass [Fintype α] [Fintype β]
    (p : α × β -> ℝ) : ℝ :=
  mutualInformationFromMassWithBase 2 p

/-- Mutual information of a bundled joint PMF, with an arbitrary base. -/
noncomputable def mutualInformationWithBase [Fintype α] [Fintype β]
    (b : ℝ) (P : JointPMF α β) : ℝ :=
  mutualInformationFromMassWithBase b P.prob

/-- Mutual information of a bundled joint PMF. -/
noncomputable def mutualInformation [Fintype α] [Fintype β]
    (P : JointPMF α β) : ℝ :=
  mutualInformationWithBase 2 P

/-- Relative-entropy summand `p log_b (p/q)`, with the zero-mass convention. -/
noncomputable def relativeEntropyTermWithBase (b p q : ℝ) : ℝ :=
  if p = 0 then 0 else p * logBase b (p / q)

/-- Relative entropy from unbundled mass functions, with an arbitrary base. -/
noncomputable def relativeEntropyFromMassWithBase [Fintype α]
    (b : ℝ) (p q : α -> ℝ) : ℝ :=
  Finset.univ.sum (fun a : α => relativeEntropyTermWithBase b (p a) (q a))

/-- Relative entropy from unbundled mass functions, in bits. -/
noncomputable def relativeEntropyFromMass [Fintype α] (p q : α -> ℝ) : ℝ :=
  relativeEntropyFromMassWithBase 2 p q

/-- Relative entropy of bundled PMFs, with an arbitrary base. -/
noncomputable def relativeEntropyWithBase [Fintype α] (b : ℝ) (P Q : PMF α) : ℝ :=
  relativeEntropyFromMassWithBase b P.prob Q.prob

/-- Relative entropy of bundled PMFs, in bits. -/
noncomputable def relativeEntropy [Fintype α] (P Q : PMF α) : ℝ :=
  relativeEntropyWithBase 2 P Q

/-!
## CHAIN RULES FOR ENTROPY, RELATIVE ENTROPY,AND MUTUAL INFORMATION
-/

/-- Conditional mutual information `I(X;Y | Z)`, in kernel form and arbitrary base. -/
noncomputable def conditionalMutualInformationKernelWithBase
    [Fintype γ] [Fintype α] [Fintype β]
    (b : ℝ) (R : PMF γ) (K : γ -> JointPMF α β) : ℝ :=
  Finset.univ.sum (fun z : γ => R.prob z * mutualInformationWithBase b (K z))

/-- Conditional mutual information `I(X;Y | Z)`, in bits. -/
noncomputable def conditionalMutualInformationKernel
    [Fintype γ] [Fintype α] [Fintype β]
    (R : PMF γ) (K : γ -> JointPMF α β) : ℝ :=
  conditionalMutualInformationKernelWithBase 2 R K

/-- Weighted log-ratio summand `w log_b (p/q)`, with the zero-weight convention. -/
noncomputable def weightedLogRatioTermWithBase (b w p q : ℝ) : ℝ :=
  if w = 0 then 0 else w * logBase b (p / q)

/--
Conditional relative entropy `D(p(y|x) || q(y|x))`, with the conditioning
distribution supplied by the first joint law.
-/
noncomputable def conditionalRelativeEntropyWithBase [Fintype α] [Fintype β]
    (b : ℝ) (P Q : JointPMF α β) : ℝ :=
  Finset.univ.sum (fun ab : α × β =>
    weightedLogRatioTermWithBase b
      (P.prob ab)
      (conditionalMassRightGivenLeft P ab.1 ab.2)
      (conditionalMassRightGivenLeft Q ab.1 ab.2))

/-- Conditional relative entropy `D(p(y|x) || q(y|x))`, in bits. -/
noncomputable def conditionalRelativeEntropy [Fintype α] [Fintype β]
    (P Q : JointPMF α β) : ℝ :=
  conditionalRelativeEntropyWithBase 2 P Q

/-!
## DATA-PROCESSING INEQUALITY
-/

/-- Joint distributions of three finite random variables. -/
abbrev TriplePMF (α : Type u) (β : Type v) (γ : Type w)
    [Fintype α] [Fintype β] [Fintype γ] :=
  PMF (α × β × γ)

/--
Section 2.8 definition: `X → Y → Z` is a Markov chain when its joint law
factors as `p(x) p(y | x) p(z | y)`.
-/
def MarkovChain [Fintype α] [Fintype β] [Fintype γ]
    (P : TriplePMF α β γ) : Prop :=
  ∃ (PX : PMF α) (PYgivenX : Channel α β) (PZgivenY : Channel β γ),
    ∀ x y z,
      P.prob (x, y, z) =
        PX.prob x * (PYgivenX x).prob y * (PZgivenY y).prob z

/-!
## SUFFICIENT STATISTICS
-/

/--
The mass assigned to a statistic value under a model distribution.
Here `model θ` is the law of the sample when the parameter is `θ`.
-/
noncomputable def statisticMass [Fintype α] [Fintype γ] [DecidableEq γ]
    (model : β -> PMF α) (T : α -> γ) (theta : β) (t : γ) : ℝ :=
  Finset.univ.sum (fun x : α => if T x = t then (model theta).prob x else 0)

/--
Section 2.9 definition: a statistic `T(X)` is sufficient for the parameter
family `model` when, for every prior on the parameter, the joint law of
`θ, T(X), X` factors through `θ → T(X) → X`.
-/
def SufficientStatistic [Fintype β] [Fintype α] [Fintype γ] [DecidableEq γ]
    (model : β -> PMF α) (T : α -> γ) : Prop :=
  ∀ prior : PMF β, ∃ K : Channel γ α,
    ∀ theta t x,
      prior.prob theta * (model theta).prob x *
          (if T x = t then 1 else 0) =
        prior.prob theta * statisticMass model T theta t * (K t).prob x

/-- `T` is a function of `U`, pointwise on the sample space. -/
def StatisticIsFunctionOf (T : α -> γ) (U : α -> δ) : Prop :=
  ∃ phi : δ -> γ, ∀ x, T x = phi (U x)

/--
Section 2.9 definition: a minimal sufficient statistic is sufficient and is a
function of every other sufficient statistic.
-/
def MinimalSufficientStatistic [Fintype β] [Fintype α]
    [Fintype γ] [DecidableEq γ]
    (model : β -> PMF α) (T : α -> γ) : Prop :=
  SufficientStatistic model T ∧
    ∀ {δ : Type z} [Fintype δ] [DecidableEq δ] (U : α -> δ),
      SufficientStatistic model U -> StatisticIsFunctionOf T U

/-!
## FANO'S INEQUALITY
-/

/-- Bernoulli law with success probability `p`, represented on `Bool`. -/
noncomputable def bernoulliPMF (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : PMF Bool where
  prob b := if b then p else 1 - p
  nonneg b := by
    by_cases hb : b
    · simp [hb, h0]
    · simp [hb, sub_nonneg.mpr h1]
  sum_eq_one := by
    simp

/-- Collision probability `Pr(X = X')` for independent laws `P` and `Q`. -/
noncomputable def collisionProbability [Fintype α] (P Q : PMF α) : ℝ :=
  Finset.univ.sum (fun x : α => P.prob x * Q.prob x)

/-- Self-collision probability for an i.i.d. pair. -/
noncomputable def selfCollisionProbability [Fintype α] (P : PMF α) : ℝ :=
  collisionProbability P P

/-- Uniformity on the support, the equality condition for Lemma 2.10.1. -/
def UniformOnSupport [Fintype α] (P : PMF α) : Prop :=
  ∀ x y, P.prob x ≠ 0 -> P.prob y ≠ 0 -> P.prob x = P.prob y



end InformationTheory
