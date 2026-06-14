import BooleanFunctions.Fourierexpansion

/-!
# Plancherel's Theorem on the Boolean cube

This file contains the character-basis inner-product calculation used to prove
Plancherel's Theorem:

`<f, g> = sum_S fhat(S) * ghat(S)`.
-/

namespace BooleanFunctions

public section

/-- The basis vector indexed by `S` is the parity function `chi_S`. -/
lemma fourierCharacterBasis_eq_fourierCharacters {n : Nat} (S : CoordinateSet n) :
    fourierCharacterBasis n S = fourierCharacters n S := by
  funext x
  simp [fourierCharacterBasis_apply, fourierCharacters]

/-- The unnormalized inner product of two basis characters. -/
lemma cubeSumInner_fourierCharacterBasis {n : Nat} (S T : CoordinateSet n) :
    (cubeSumInner n (fourierCharacterBasis n S) (fourierCharacterBasis n T)) =
      if S = T then (2 : Real) ^ n else 0 := by
  classical
  have hsum :
      (Finset.univ.sum (fun x : SignCube n =>
        fourierCharacterBasis n S x * fourierCharacterBasis n T x)) =
      (Finset.univ.sum (fun x : SignCube n => chiSign S x * chiSign T x)) := by
    apply Finset.sum_congr rfl
    intro x _hx
    rw [fourierCharacterBasis_apply, fourierCharacterBasis_apply]
  by_cases h : S = T
  · subst T
    change (Finset.univ.sum (fun x : SignCube n =>
        fourierCharacterBasis n S x * fourierCharacterBasis n S x)) =
      (if S = S then (2 : Real) ^ n else 0)
    rw [hsum]
    simp [character_inner_self]
  · change (Finset.univ.sum (fun x : SignCube n =>
        fourierCharacterBasis n S x * fourierCharacterBasis n T x)) =
      (if S = T then (2 : Real) ^ n else 0)
    rw [hsum]
    simp [h, character_inner_ne h]

/-- Plancherel for the unnormalized sum inner product. -/
lemma cubeSumInner_plancherel {n : Nat} (f g : RealValuedBooleanFunction n) :
    (cubeSumInner n f g) =
      (2 : Real) ^ n *
        Finset.univ.sum (fun S : CoordinateSet n =>
          functionFourierCoeff f S * functionFourierCoeff g S) := by
  classical
  have h := (LinearMap.BilinForm.sum_repr_mul_repr_mul (B := cubeSumInner n)
    (fourierCharacterBasis n) f g).symm
  simpa [functionFourierCoeff, cubeSumInner_fourierCharacterBasis, Finsupp.sum_fintype,
    Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm] using h

/--
Plancherel's Theorem.

For any two real-valued Boolean functions, their normalized inner product is
the dot product of their Fourier coefficient vectors.
-/
theorem plancherel_theorem {n : Nat} (f g : RealValuedBooleanFunction n) :
    cubeInner f g =
      Finset.univ.sum (fun S : CoordinateSet n =>
        functionFourierCoeff f S * functionFourierCoeff g S) := by
  classical
  have hpow : ((2 : Real) ^ n) ≠ 0 :=
    pow_ne_zero n (by exact (two_ne_zero : (2 : Real) ≠ 0))
  rw [cubeInner, cubeExpectation]
  change (((2 : Real) ^ n)⁻¹) * (cubeSumInner n f g) =
    Finset.univ.sum (fun S : CoordinateSet n =>
      functionFourierCoeff f S * functionFourierCoeff g S)
  rw [cubeSumInner_plancherel f g]
  rw [← mul_assoc, inv_mul_cancel₀ hpow, one_mul]

end

end BooleanFunctions
