import BooleanFunctions.Fourierexpansion
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# O'Donnell, Section 1.5

This file formalizes the basic results about probability densities and
convolution on the additive cube `F_2^n`.

The definitions from the book live in `Fourierexpansion.lean`; this file contains the
facts, propositions, and theorem from Section 1.5.
-/

namespace BooleanFunctions

/-! ## Elementary algebra on `F_2^n` -/

/-- Every element of `F_2` is either `0` or `1`. -/
lemma f2_eq_zero_or_one (a : F2) : a = 0 ∨ a = 1 := by
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
lemma f2_add_self (a : F2) : a + a = 0 := by
  have htwo : (2 : F2) = 0 := ZMod.natCast_self 2
  calc
    a + a = a * (2 : F2) := by ring
    _ = 0 := by rw [htwo, mul_zero]

/-- Adding the same `F_2^n` vector twice cancels it. -/
lemma addCubeF2_add_self_right {n : Nat} (x y : CubeF2 n) :
    addCubeF2 (addCubeF2 x y) y = x := by
  funext i
  calc
    x i + y i + y i = x i + (y i + y i) := by ring
    _ = x i := by simp [f2_add_self]

/-- The map `x |-> x + y` is a permutation of `F_2^n`. -/
def addCubeF2RightEquiv {n : Nat} (y : CubeF2 n) :
    Equiv (CubeF2 n) (CubeF2 n) where
  toFun := fun x => addCubeF2 x y
  invFun := fun x => addCubeF2 x y
  left_inv := by
    intro x
    exact addCubeF2_add_self_right x y
  right_inv := by
    intro x
    exact addCubeF2_add_self_right x y

/-- Translating all points of `F_2^n` does not change a finite sum. -/
lemma sum_addCubeF2_right {n : Nat} (y : CubeF2 n)
    (h : RealValuedF2Function n) :
    Finset.univ.sum (fun x : CubeF2 n => h (addCubeF2 x y)) =
      Finset.univ.sum (fun x : CubeF2 n => h x) := by
  simpa using (addCubeF2RightEquiv y).sum_comp h

/-- The one-bit `F_2` character is multiplicative under addition. -/
lemma chiF2Bit_add (a b : F2) :
    chiF2Bit (a + b) = chiF2Bit a * chiF2Bit b := by
  rcases f2_eq_zero_or_one a with ha | ha
  · subst a
    rcases f2_eq_zero_or_one b with hb | hb
    · subst b
      simp [chiF2Bit]
    · subst b
      have h : (1 : F2) ≠ 0 := one_ne_zero
      simp [chiF2Bit, h]
  · subst a
    rcases f2_eq_zero_or_one b with hb | hb
    · subst b
      have h : (1 : F2) ≠ 0 := one_ne_zero
      simp [chiF2Bit, h]
    · subst b
      have h11 : (1 : F2) + (1 : F2) = 0 := by
        simpa using (ZMod.natCast_self 2)
      have h1 : (1 : F2) ≠ 0 := one_ne_zero
      simp [chiF2Bit, h11, h1]

/-- Characters on `F_2^n` turn addition into multiplication. -/
lemma chiF2_add {n : Nat} (S : CoordinateSet n) (x y : CubeF2 n) :
    chiF2 S (addCubeF2 x y) = chiF2 S x * chiF2 S y := by
  classical
  unfold chiF2
  calc
    S.prod (fun i => chiF2Bit ((addCubeF2 x y) i)) =
        S.prod (fun i => chiF2Bit (x i) * chiF2Bit (y i)) := by
      apply Finset.prod_congr rfl
      intro i _hi
      simp [addCubeF2, chiF2Bit_add]
    _ = S.prod (fun i => chiF2Bit (x i)) *
        S.prod (fun i => chiF2Bit (y i)) := by
      rw [Finset.prod_mul_distrib]

/-- Every character has value `1` at the zero vector. -/
lemma chiF2_zero {n : Nat} (S : CoordinateSet n) :
    chiF2 S (zeroCubeF2 : CubeF2 n) = 1 := by
  simp [chiF2, zeroCubeF2, chiF2Bit]

/-! ## Fact 1.21 -/

/--
Fact 1.21: expectation with respect to a density is the inner product with
that density.
-/
theorem fact_1_21 {n : Nat} (phi g : RealValuedF2Function n)
    (_hphi : IsProbabilityDensityF2 phi) :
    densityExpectationF2 phi g = f2Inner phi g := by
  rfl

/-! ## Fact 1.23 -/

/-- The Fourier coefficients of the density of `{0}` are all `1`. -/
theorem fact_1_23_fourierCoeff_singletonZero {n : Nat} (S : CoordinateSet n) :
    f2FourierCoeff (singletonZeroDensityF2 : RealValuedF2Function n) S = 1 := by
  classical
  have hsum :
      (Finset.univ.sum (fun x : CubeF2 n =>
        singletonZeroDensityF2 x * chiF2 S x)) = (2 : Real) ^ n := by
    unfold singletonZeroDensityF2 singletonDensityF2
    rw [Finset.sum_eq_single (zeroCubeF2 : CubeF2 n)]
    · simp [chiF2_zero]
    · intro b _hb hb
      simp [hb]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))
  rw [f2FourierCoeff, f2Expectation, hsum]
  exact inv_mul_cancel₀ (pow_ne_zero n (by exact two_ne_zero : (2 : Real) ≠ 0))

/-- Fact 1.23: `phi_{0}` is the sum of all characters. -/
theorem fact_1_23_singletonZero_expansion {n : Nat} (x : CubeF2 n) :
    evalF2FourierExpansion (fun _ : CoordinateSet n => 1) x =
      singletonZeroDensityF2 x := by
  classical
  have huniv :
      (Finset.univ : Finset (CoordinateSet n)) =
        (Finset.univ : Finset (Fin n)).powerset := by
    ext S
    simp [CoordinateSet]
  have hsum_product :
      evalF2FourierExpansion (fun _ : CoordinateSet n => 1) x =
        ∏ i ∈ (Finset.univ : Finset (Fin n)), (chiF2Bit (x i) + 1) := by
    calc
      evalF2FourierExpansion (fun _ : CoordinateSet n => 1) x =
          Finset.univ.sum (fun S : CoordinateSet n => chiF2 S x) := by
        simp [evalF2FourierExpansion]
      _ = ((Finset.univ : Finset (Fin n)).powerset).sum
            (fun S : CoordinateSet n => chiF2 S x) := by
        rw [huniv]
      _ = ∏ i ∈ (Finset.univ : Finset (Fin n)), (chiF2Bit (x i) + 1) := by
        simpa [chiF2] using
          (Finset.prod_add_one (s := (Finset.univ : Finset (Fin n)))
            (f := fun i : Fin n => chiF2Bit (x i))).symm
  by_cases hx : x = (zeroCubeF2 : CubeF2 n)
  · subst x
    rw [hsum_product]
    simp [singletonZeroDensityF2, singletonDensityF2, zeroCubeF2, chiF2Bit]
    norm_num
  · have hcoord : ∃ i : Fin n, x i ≠ 0 := by
      by_contra h
      apply hx
      funext i
      by_contra hi
      exact h ⟨i, hi⟩
    rcases hcoord with ⟨i, hi⟩
    have hi_one : x i = 1 := by
      rcases f2_eq_zero_or_one (x i) with h0 | h1
      · exact False.elim (hi h0)
      · exact h1
    have hfactor : chiF2Bit (x i) + 1 = 0 := by
      rw [hi_one]
      have h1 : (1 : F2) ≠ 0 := one_ne_zero
      simp [chiF2Bit, h1]
    rw [hsum_product]
    have hprod :
        (∏ j ∈ (Finset.univ : Finset (Fin n)), (chiF2Bit (x j) + 1)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hfactor
    rw [hprod]
    simp [singletonZeroDensityF2, singletonDensityF2, hx]

/-! ## Proposition 1.25 -/

/--
Proposition 1.25: convolving a function with a density means averaging shifted
copies of the function with respect to that density.
-/
theorem proposition_1_25 {n : Nat} (phi g : RealValuedF2Function n)
    (_hphi : IsProbabilityDensityF2 phi) (x : CubeF2 n) :
    convolutionF2 phi g x =
      densityExpectationF2 phi (fun y => g (addCubeF2 x y)) := by
  rfl

/-- The expectation under `phi` is the convolution value at the zero vector. -/
theorem proposition_1_25_at_zero {n : Nat}
    (phi g : RealValuedF2Function n) (_hphi : IsProbabilityDensityF2 phi) :
    densityExpectationF2 phi g = convolutionF2 phi g (zeroCubeF2 : CubeF2 n) := by
  unfold densityExpectationF2 convolutionF2 f2Expectation
  congr 1
  apply Finset.sum_congr rfl
  intro y _hy
  have hy : addCubeF2 (zeroCubeF2 : CubeF2 n) y = y := by
    funext i
    simp [addCubeF2, zeroCubeF2]
  change phi y * g y = phi y * g (addCubeF2 (zeroCubeF2 : CubeF2 n) y)
  rw [hy]

/-! ## Proposition 1.26 -/

/-- The expectation of a convolution is the product of expectations. -/
lemma f2Expectation_convolutionF2 {n : Nat}
    (f g : RealValuedF2Function n) :
    f2Expectation (convolutionF2 f g) = f2Expectation f * f2Expectation g := by
  classical
  simp [f2Expectation, convolutionF2, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _hy
  calc
    Finset.univ.sum (fun x : CubeF2 n =>
        ((2 : Real) ^ n)⁻¹ *
          (((2 : Real) ^ n)⁻¹ * (f y * g (addCubeF2 x y)))) =
        Finset.univ.sum (fun x : CubeF2 n =>
          ((2 : Real) ^ n)⁻¹ * f y *
            (((2 : Real) ^ n)⁻¹ * g (addCubeF2 x y))) := by
      apply Finset.sum_congr rfl
      intro x _hx
      ring
    _ = Finset.univ.sum (fun x : CubeF2 n =>
          ((2 : Real) ^ n)⁻¹ * f y * (((2 : Real) ^ n)⁻¹ * g x)) := by
      simpa using sum_addCubeF2_right y
        (fun z : CubeF2 n =>
          ((2 : Real) ^ n)⁻¹ * f y * (((2 : Real) ^ n)⁻¹ * g z))

/--
Proposition 1.26: the convolution of two probability densities is again a
probability density.
-/
theorem proposition_1_26 {n : Nat} (phi psi : RealValuedF2Function n)
    (hphi : IsProbabilityDensityF2 phi) (hpsi : IsProbabilityDensityF2 psi) :
    IsProbabilityDensityF2 (convolutionF2 phi psi) := by
  constructor
  · intro x
    unfold convolutionF2 f2Expectation
    apply mul_nonneg
    · exact inv_nonneg.mpr (pow_nonneg (zero_le_two : (0 : Real) ≤ 2) n)
    · apply Finset.sum_nonneg
      intro y _hy
      exact mul_nonneg (hphi.1 y) (hpsi.1 (addCubeF2 x y))
  · rw [f2Expectation_convolutionF2, hphi.2, hpsi.2, one_mul]

/-! ## Theorem 1.27 -/

/--
Translating a function inside a character-weighted sum pulls out the character
of the translating vector.
-/
lemma sum_translate_mul_chiF2 {n : Nat} (S : CoordinateSet n)
    (g : RealValuedF2Function n) (y : CubeF2 n) :
    Finset.univ.sum (fun x : CubeF2 n =>
      g (addCubeF2 x y) * chiF2 S x) =
        chiF2 S y * Finset.univ.sum (fun x : CubeF2 n => g x * chiF2 S x) := by
  classical
  calc
    Finset.univ.sum (fun x : CubeF2 n =>
        g (addCubeF2 x y) * chiF2 S x) =
        Finset.univ.sum (fun x : CubeF2 n =>
          g (addCubeF2 x y) * chiF2 S (addCubeF2 (addCubeF2 x y) y)) := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [addCubeF2_add_self_right]
    _ = Finset.univ.sum (fun z : CubeF2 n =>
          g z * chiF2 S (addCubeF2 z y)) := by
      simpa using sum_addCubeF2_right y
        (fun z : CubeF2 n => g z * chiF2 S (addCubeF2 z y))
    _ = Finset.univ.sum (fun z : CubeF2 n =>
          g z * (chiF2 S z * chiF2 S y)) := by
      apply Finset.sum_congr rfl
      intro z _hz
      rw [chiF2_add]
    _ = Finset.univ.sum (fun z : CubeF2 n =>
          chiF2 S y * (g z * chiF2 S z)) := by
      apply Finset.sum_congr rfl
      intro z _hz
      ring
    _ = chiF2 S y * Finset.univ.sum (fun x : CubeF2 n => g x * chiF2 S x) := by
      rw [Finset.mul_sum]

/--
Theorem 1.27: the Fourier transform of a convolution is the pointwise product
of the Fourier transforms.
-/
theorem theorem_1_27 {n : Nat} (f g : RealValuedF2Function n)
    (S : CoordinateSet n) :
    f2FourierCoeff (convolutionF2 f g) S =
      f2FourierCoeff f S * f2FourierCoeff g S := by
  classical
  simp [f2FourierCoeff, convolutionF2, f2Expectation,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _hy
  calc
    Finset.univ.sum (fun x : CubeF2 n =>
        ((2 : Real) ^ n)⁻¹ *
          (((2 : Real) ^ n)⁻¹ * (f y * g (addCubeF2 x y)) * chiF2 S x)) =
        ((2 : Real) ^ n)⁻¹ * Finset.univ.sum (fun x : CubeF2 n =>
          (((2 : Real) ^ n)⁻¹ * f y) *
            (g (addCubeF2 x y) * chiF2 S x)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      ring
    _ = ((2 : Real) ^ n)⁻¹ * ((((2 : Real) ^ n)⁻¹ * f y) *
          Finset.univ.sum (fun x : CubeF2 n =>
            g (addCubeF2 x y) * chiF2 S x)) := by
      congr 1
      rw [Finset.mul_sum]
    _ = ((2 : Real) ^ n)⁻¹ * (((2 : Real) ^ n)⁻¹ * f y) *
          Finset.univ.sum (fun x : CubeF2 n =>
            g (addCubeF2 x y) * chiF2 S x) := by
      ring
    _ = ((2 : Real) ^ n)⁻¹ * (((2 : Real) ^ n)⁻¹ * f y) *
          (chiF2 S y * Finset.univ.sum (fun x : CubeF2 n =>
            g x * chiF2 S x)) := by
      rw [sum_translate_mul_chiF2]
    _ = ((2 : Real) ^ n)⁻¹ * (f y * chiF2 S y) *
          (((2 : Real) ^ n)⁻¹ * Finset.univ.sum (fun x : CubeF2 n =>
            g x * chiF2 S x)) := by
      ring
    _ = ((2 : Real) ^ n)⁻¹ * (f y * chiF2 S y) *
          Finset.univ.sum (fun x : CubeF2 n =>
            ((2 : Real) ^ n)⁻¹ * (g x * chiF2 S x)) := by
      rw [Finset.mul_sum]
    _ = Finset.univ.sum (fun x : CubeF2 n =>
          ((2 : Real) ^ n)⁻¹ * (f y * chiF2 S y) *
            (((2 : Real) ^ n)⁻¹ * (g x * chiF2 S x))) := by
      rw [Finset.mul_sum]

end BooleanFunctions
