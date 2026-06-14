import BooleanFunctions.Fourierexpansion
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The BLR Linearity Test

This file formalizes the Blum--Luby--Rubinfeld linearity test from
O'Donnell's Section 1.6.

Definitions such as `F2BooleanFunction`, `IsLinearF2Function`, distance, and
`epsilon`-closeness live in `Fourierexpansion.lean`.  The BLR-specific
definitions and their basic correctness proofs live here.
-/

namespace BooleanFunctions

/-! ## The randomized BLR test -/

/-- The BLR test accepts this particular query pair. -/
def blrAcceptsAt {n : Nat} (f : F2BooleanFunction n)
    (x y : CubeF2 n) : Prop :=
  f (addCubeF2 x y) = f x + f y

/-- The `0`/`1` indicator of BLR acceptance for one query pair. -/
noncomputable def blrAcceptIndicator {n : Nat} (f : F2BooleanFunction n)
    (x y : CubeF2 n) : Real :=
  by
    classical
    exact if blrAcceptsAt f x y then 1 else 0

/-- Expectation over an independent uniform pair `(x,y)` in `F_2^n x F_2^n`. -/
noncomputable def f2PairExpectation {n : Nat}
    (h : CubeF2 n -> CubeF2 n -> Real) : Real :=
  f2Expectation (fun x : CubeF2 n => f2Expectation (fun y : CubeF2 n => h x y))

/-- The acceptance probability of the BLR test. -/
noncomputable def blrAcceptanceProbability {n : Nat}
    (f : F2BooleanFunction n) : Real :=
  f2PairExpectation (fun x y => blrAcceptIndicator f x y)

/-- The rejection probability of the BLR test. -/
noncomputable def blrRejectionProbability {n : Nat}
    (f : F2BooleanFunction n) : Real :=
  1 - blrAcceptanceProbability f

/-- The hypothesis that BLR accepts with probability at least `1 - epsilon`. -/
def BLRAcceptsWithHighProbability {n : Nat} (epsilon : Real)
    (f : F2BooleanFunction n) : Prop :=
  1 - epsilon ≤ blrAcceptanceProbability f

/-! ## Sign encoding and local correction -/

/-- Encode an `F_2`-valued function as a `{-1, 1}`-valued real function. -/
def f2OutputToSignReal {n : Nat} (f : F2BooleanFunction n) :
    RealValuedF2Function n :=
  fun x => chiF2Bit (f x)

/--
The triple product `f(x) f(y) f(x+y)` after encoding outputs by `{-1,1}`.
This is the quantity used in the Fourier proof of Theorem 1.30.
-/
def blrTripleProduct {n : Nat} (f : F2BooleanFunction n)
    (x y : CubeF2 n) : Real :=
  f2OutputToSignReal f x *
    f2OutputToSignReal f y *
      f2OutputToSignReal f (addCubeF2 x y)

/--
The local-correction algorithm from Proposition 1.31, in `F_2` notation:
given target point `x` and random shift `y`, output `f y + f (x+y)`.
-/
def blrLocalCorrectionOutput {n : Nat} (f : F2BooleanFunction n)
    (x y : CubeF2 n) : F2 :=
  f y + f (addCubeF2 x y)

/-- The local-correction output succeeds against a target linear function. -/
def blrLocalCorrectionSucceedsAt {n : Nat}
    (f target : F2BooleanFunction n) (x y : CubeF2 n) : Prop :=
  blrLocalCorrectionOutput f x y = target x

/-! ## Elementary `F_2` facts -/

/-- Every element of `F_2` is either `0` or `1`. -/
lemma blr_f2_eq_zero_or_one (a : F2) : a = 0 ∨ a = 1 := by
  have hlt : a.val < 2 := ZMod.val_lt a
  have hle : a.val ≤ 1 := Nat.lt_succ_iff.mp hlt
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
  · left
    exact (ZMod.val_eq_zero a).mp h0
  · right
    have hval : (a.val : F2) = a := ZMod.natCast_zmod_val a
    rw [hval.symm]
    rw [h1]
    rfl

/-- In `F_2`, every element is its own additive inverse. -/
lemma blr_f2_add_self (a : F2) : a + a = 0 := by
  have htwo : (2 : F2) = 0 := ZMod.natCast_self 2
  calc
    a + a = a * (2 : F2) := by ring
    _ = 0 := by rw [htwo, mul_zero]

/-- In the `{-1,1}` encoding, addition in `F_2` becomes multiplication. -/
lemma blr_chiF2Bit_add (a b : F2) :
    chiF2Bit (a + b) = chiF2Bit a * chiF2Bit b := by
  rcases blr_f2_eq_zero_or_one a with ha | ha
  · rw [ha]
    rcases blr_f2_eq_zero_or_one b with hb | hb
    · rw [hb]
      simp [chiF2Bit]
    · rw [hb]
      have h : (1 : F2) ≠ 0 := one_ne_zero
      simp [chiF2Bit, h]
  · rw [ha]
    rcases blr_f2_eq_zero_or_one b with hb | hb
    · rw [hb]
      have h : (1 : F2) ≠ 0 := one_ne_zero
      simp [chiF2Bit, h]
    · rw [hb]
      have h11 : (1 : F2) + (1 : F2) = 0 := by
        simpa using (ZMod.natCast_self 2)
      have h1 : (1 : F2) ≠ 0 := one_ne_zero
      simp [chiF2Bit, h11, h1]

/-! ## Completeness of the BLR test -/

/-- The functions `x |-> sum_{i in S} x_i` are linear. -/
theorem linearF2BySet_isLinear {n : Nat} (S : CoordinateSet n) :
    IsLinearF2Function (linearF2BySet S) := by
  intro x y
  unfold linearF2BySet addCubeF2
  rw [Finset.sum_add_distrib]

/-- The functions `x |-> a . x` are linear. -/
theorem linearF2ByVector_isLinear {n : Nat} (a : CubeF2 n) :
    IsLinearF2Function (linearF2ByVector a) := by
  intro x y
  unfold linearF2ByVector dotF2 addCubeF2
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]

/-- Uniform expectation of a constant over `F_2^n`. -/
lemma f2Expectation_const {n : Nat} (a : Real) :
    f2Expectation (fun _ : CubeF2 n => a) = a := by
  classical
  unfold f2Expectation
  simp [CubeF2, StringOver, F2]

/-- Pair expectation of a constant over `F_2^n x F_2^n`. -/
lemma f2PairExpectation_const {n : Nat} (a : Real) :
    f2PairExpectation (fun _ _ : CubeF2 n => a) = a := by
  simp [f2PairExpectation, f2Expectation_const]

/-- The BLR test accepts every query pair exactly when the function is linear. -/
theorem blr_accepts_all_iff_linear {n : Nat} (f : F2BooleanFunction n) :
    (∀ x y : CubeF2 n, blrAcceptsAt f x y) ↔ IsLinearF2Function f := by
  rfl

/-- Perfect completeness: every linear function is accepted with probability `1`. -/
theorem blrAcceptanceProbability_of_linear {n : Nat}
    (f : F2BooleanFunction n) (hf : IsLinearF2Function f) :
    blrAcceptanceProbability f = 1 := by
  classical
  have hpoint : ∀ x y : CubeF2 n, blrAcceptIndicator f x y = 1 := by
    intro x y
    unfold blrAcceptIndicator blrAcceptsAt
    simp [hf x y]
  unfold blrAcceptanceProbability f2PairExpectation
  simp [hpoint, f2Expectation_const]

/-- The explicit linear functions `x |-> sum_{i in S} x_i` pass with probability `1`. -/
theorem blrAcceptanceProbability_linearF2BySet {n : Nat}
    (S : CoordinateSet n) :
    blrAcceptanceProbability (linearF2BySet S) = 1 :=
  blrAcceptanceProbability_of_linear _ (linearF2BySet_isLinear S)

/-! ## The sign-encoded acceptance formula -/

/-- The BLR accept indicator as a three-bit identity. -/
lemma blrAcceptIndicatorBit_eq_half_add_triple (a b c : F2) :
    (if c = a + b then (1 : Real) else 0) =
      (1 / 2 : Real) + (1 / 2 : Real) *
        (chiF2Bit a * chiF2Bit b * chiF2Bit c) := by
  rcases blr_f2_eq_zero_or_one a with ha | ha
  · rcases blr_f2_eq_zero_or_one b with hb | hb
    · rcases blr_f2_eq_zero_or_one c with hc | hc
      · rw [ha, hb, hc]
        norm_num [chiF2Bit]
      · rw [ha, hb, hc]
        have h1 : (1 : F2) ≠ 0 := one_ne_zero
        norm_num [chiF2Bit, h1]
    · rcases blr_f2_eq_zero_or_one c with hc | hc
      · rw [ha, hb, hc]
        have h1 : (1 : F2) ≠ 0 := one_ne_zero
        norm_num [chiF2Bit, h1]
      · rw [ha, hb, hc]
        have h1 : (1 : F2) ≠ 0 := one_ne_zero
        norm_num [chiF2Bit, h1]
  · rcases blr_f2_eq_zero_or_one b with hb | hb
    · rcases blr_f2_eq_zero_or_one c with hc | hc
      · rw [ha, hb, hc]
        have h1 : (1 : F2) ≠ 0 := one_ne_zero
        norm_num [chiF2Bit, h1]
      · rw [ha, hb, hc]
        have h1 : (1 : F2) ≠ 0 := one_ne_zero
        norm_num [chiF2Bit, h1]
    · rcases blr_f2_eq_zero_or_one c with hc | hc
      · rw [ha, hb, hc]
        have hcond : (0 : F2) = (1 : F2) + (1 : F2) := by
          simpa using (ZMod.natCast_self 2).symm
        have h1 : (1 : F2) ≠ 0 := one_ne_zero
        have hchi0 : chiF2Bit (0 : F2) = 1 := by simp [chiF2Bit]
        have hchi1 : chiF2Bit (1 : F2) = -1 := by simp [chiF2Bit, h1]
        rw [if_pos hcond]
        norm_num [hchi0, hchi1]
      · rw [ha, hb, hc]
        have hsum : (1 : F2) + (1 : F2) = 0 := by
          simpa using (ZMod.natCast_self 2)
        have h1 : (1 : F2) ≠ 0 := one_ne_zero
        have hcond : ¬ (1 : F2) = (1 : F2) + (1 : F2) := by
          intro h
          rw [hsum] at h
          exact h1 h
        have hchi1 : chiF2Bit (1 : F2) = -1 := by simp [chiF2Bit, h1]
        rw [if_neg hcond]
        norm_num [hchi1]

/--
The pointwise identity behind Theorem 1.30:
the BLR accept indicator is `(1 + f(x) f(y) f(x+y)) / 2` after `{-1,1}`
encoding.
-/
theorem blrAcceptIndicator_eq_half_add_triple {n : Nat}
    (f : F2BooleanFunction n) (x y : CubeF2 n) :
    blrAcceptIndicator f x y =
      (1 / 2 : Real) + (1 / 2 : Real) * blrTripleProduct f x y := by
  unfold blrAcceptIndicator blrAcceptsAt blrTripleProduct f2OutputToSignReal
  by_cases h : f (addCubeF2 x y) = f x + f y
  · rw [if_pos h]
    have hbit :=
      blrAcceptIndicatorBit_eq_half_add_triple (f x) (f y) (f (addCubeF2 x y))
    rw [if_pos h] at hbit
    exact hbit
  · rw [if_neg h]
    have hbit :=
      blrAcceptIndicatorBit_eq_half_add_triple (f x) (f y) (f (addCubeF2 x y))
    rw [if_neg h] at hbit
    exact hbit

/-! ## The local-correction algebra -/

/--
If a queried function agrees with a linear target at the two queried points
`y` and `x+y`, the BLR local-correction output recovers the target value at
`x`.
-/
theorem blrLocalCorrectionOutput_eq_target_of_agree {n : Nat}
    (f target : F2BooleanFunction n) (htarget : IsLinearF2Function target)
    (x y : CubeF2 n)
    (hy : f y = target y)
    (hxy : f (addCubeF2 x y) = target (addCubeF2 x y)) :
    blrLocalCorrectionOutput f x y = target x := by
  unfold blrLocalCorrectionOutput
  rw [hy, hxy, htarget x y]
  calc
    target y + (target x + target y) =
        target x + (target y + target y) := by ring
    _ = target x := by simp [blr_f2_add_self]

/-- A genuinely linear function locally corrects itself at every query. -/
theorem blrLocalCorrectionOutput_linear {n : Nat}
    (target : F2BooleanFunction n) (htarget : IsLinearF2Function target)
    (x y : CubeF2 n) :
    blrLocalCorrectionOutput target x y = target x :=
  blrLocalCorrectionOutput_eq_target_of_agree target target htarget x y rfl rfl

end BooleanFunctions
