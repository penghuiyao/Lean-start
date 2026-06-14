import BooleanFunctions.«Thm Inf Core»
import Mathlib.Tactic.Linarith

/-!
# Poincare inequality on the Boolean cube

This file proves the Section 2.3 Poincare inequality in Fourier form:

`Var[f] = sum_{S ≠ ∅} fhat(S)^2 ≤ sum_S |S| fhat(S)^2 = I[f]`.

The final theorem `poincare_inequality_from_cubeVariance_formula` is the
standard variance statement, assuming the Fourier variance formula from
Section 1.4.
-/

namespace BooleanFunctions

/-- The Fourier expression for variance: all nonempty Fourier weights. -/
noncomputable def fourierVariance {n : Nat}
    (f : RealValuedBooleanFunction n) : Real :=
  Finset.univ.sum (fun S : CoordinateSet n =>
    if S = ∅ then 0 else fourierWeight f S)

lemma fourierVariance_term_le_totalInfluence_term {n : Nat}
    (f : RealValuedBooleanFunction n) (S : CoordinateSet n) :
    (if S = ∅ then 0 else fourierWeight f S) ≤
      (S.card : Real) * functionFourierCoeff f S ^ 2 := by
  classical
  by_cases hS : S = ∅
  · simp [hS]
  · have hnonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
    have hcard_pos : 0 < S.card := Finset.card_pos.mpr hnonempty
    have hcard_ge_one_nat : 1 ≤ S.card := Nat.succ_le_of_lt hcard_pos
    have hcard_ge_one : (1 : Real) ≤ (S.card : Real) := by
      exact_mod_cast hcard_ge_one_nat
    have hsq_nonneg : 0 ≤ functionFourierCoeff f S ^ 2 :=
      sq_nonneg (functionFourierCoeff f S)
    simp [hS, fourierWeight]
    nlinarith

/-- Poincare inequality in Fourier form. -/
theorem poincare_inequality_fourier {n : Nat}
    (f : RealValuedBooleanFunction n) :
    fourierVariance f ≤ fourierTotalInfluence f := by
  classical
  unfold fourierVariance fourierTotalInfluence
  apply Finset.sum_le_sum
  intro S _hS
  exact fourierVariance_term_le_totalInfluence_term f S

/--
Poincare inequality using the project's `totalInfluence` name.

Here variance is written in its Fourier form; the next theorem gives the usual
`cubeVariance` version once the Section 1.4 variance formula is supplied.
-/
theorem poincare_inequality {n : Nat}
    (f : RealValuedBooleanFunction n) :
    fourierVariance f ≤ totalInfluence f := by
  rw [theorem_2_38_totalInfluence_fourier f]
  exact poincare_inequality_fourier f

/--
Standard Poincare inequality, reduced to the already-proved Fourier variance
formula from Section 1.4.
-/
theorem poincare_inequality_from_cubeVariance_formula {n : Nat}
    (f : RealValuedBooleanFunction n)
    (hvar : cubeVariance f = fourierVariance f) :
    cubeVariance f ≤ totalInfluence f := by
  rw [hvar]
  exact poincare_inequality f

end BooleanFunctions
