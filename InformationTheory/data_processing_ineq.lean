import InformationTheory.Inequalities

/-!
# Section 2.8: Data-Processing Inequality

The chapter proof of the data-processing inequality uses only the two chain-rule
expansions of `I(X;Y,Z)`, the Markov-chain identity `I(X;Z | Y) = 0`, and
nonnegativity of conditional mutual information.  This file records that finite
information-algebra argument directly.
-/

namespace InformationTheory

/-!
## DATA-PROCESSING INEQUALITY
-/

/--
Theorem 2.8.1, data-processing inequality, in the algebraic form used in the
textbook proof.

Here `IXYZ` denotes `I(X;Y,Z)`, `IXY` denotes `I(X;Y)`, `IXZ` denotes
`I(X;Z)`, and the two conditional terms are `I(X;Y|Z)` and `I(X;Z|Y)`.
-/
theorem theorem_2_8_1_dataProcessing
    (IXYZ IXY IXZ IXY_given_Z IXZ_given_Y : ℝ)
    (hchainZ : IXYZ = IXZ + IXY_given_Z)
    (hchainY : IXYZ = IXY + IXZ_given_Y)
    (hmarkov : IXZ_given_Y = 0)
    (hnonneg : 0 ≤ IXY_given_Z) :
    IXZ ≤ IXY := by
  linarith

/--
Equality case in Theorem 2.8.1: under the same chain-rule and Markov
hypotheses, equality holds exactly when the reverse conditional information
`I(X;Y|Z)` is zero.
-/
theorem theorem_2_8_1_dataProcessing_eq_iff
    (IXYZ IXY IXZ IXY_given_Z IXZ_given_Y : ℝ)
    (hchainZ : IXYZ = IXZ + IXY_given_Z)
    (hchainY : IXYZ = IXY + IXZ_given_Y)
    (hmarkov : IXZ_given_Y = 0) :
    IXY = IXZ ↔ IXY_given_Z = 0 := by
  constructor
  · intro h
    linarith
  · intro h
    linarith

/--
Corollary after Theorem 2.8.1: deterministic processing `Z = g(Y)` cannot
increase information.  The hypothesis `hdeterministicMarkov` is the Markov
identity supplied by the deterministic channel `Y ↦ g(Y)`.
-/
theorem corollary_2_8_dataProcessing_function
    (IXY IXgY IXYg IXY_given_gY IXgY_given_Y : ℝ)
    (hchainProcessed : IXYg = IXgY + IXY_given_gY)
    (hchainOriginal : IXYg = IXY + IXgY_given_Y)
    (hdeterministicMarkov : IXgY_given_Y = 0)
    (hnonneg : 0 ≤ IXY_given_gY) :
    IXgY ≤ IXY :=
  theorem_2_8_1_dataProcessing
    IXYg IXY IXgY IXY_given_gY IXgY_given_Y
    hchainProcessed hchainOriginal hdeterministicMarkov hnonneg

/--
Corollary after Theorem 2.8.1: if `X → Y → Z`, then observing the downstream
variable cannot increase the remaining dependence of `X` and `Y` beyond
`I(X;Y)`.
-/
theorem corollary_2_8_conditionalInformation_le
    (IXYZ IXY IXZ IXY_given_Z IXZ_given_Y : ℝ)
    (hchainZ : IXYZ = IXZ + IXY_given_Z)
    (hchainY : IXYZ = IXY + IXZ_given_Y)
    (hmarkov : IXZ_given_Y = 0)
    (hIXZ_nonneg : 0 ≤ IXZ) :
    IXY_given_Z ≤ IXY := by
  linarith

end InformationTheory
