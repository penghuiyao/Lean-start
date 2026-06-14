import BooleanFunctions.Plancherel

/-!
# Parseval's Theorem on the Boolean cube

This file derives Parseval's Theorem from Plancherel's Theorem.
-/

namespace BooleanFunctions

public section

/--
Parseval's Theorem.

The squared `L^2` norm of `f` is the sum of squares of its Fourier coefficients.
-/
theorem parseval_theorem {n : Nat} (f : RealValuedBooleanFunction n) :
    cubeInner f f =
      Finset.univ.sum (fun S : CoordinateSet n => functionFourierCoeff f S ^ 2) := by
  simpa [pow_two] using plancherel_theorem f f

/--
Boolean-valued special case of Parseval: the total Fourier weight is `1`.
-/
theorem parseval_boolean {n : Nat} (f : BooleanFunctionSign n) :
    Finset.univ.sum (fun S : CoordinateSet n =>
      fourierWeight (signFunctionToReal f) S) = 1 := by
  classical
  have hsum :
      (Finset.univ.sum (fun x : SignCube n =>
        signFunctionToReal f x * signFunctionToReal f x)) =
        (2 : Real) ^ n := by
    simp [signFunctionToReal, SignBit.toReal_mul_self]
  have hinner : cubeInner (signFunctionToReal f) (signFunctionToReal f) = 1 := by
    have hpow : ((2 : Real) ^ n) ≠ 0 :=
      pow_ne_zero n (by exact (two_ne_zero : (2 : Real) ≠ 0))
    rw [cubeInner, cubeExpectation, hsum]
    exact inv_mul_cancel₀ hpow
  have hparse := parseval_theorem (signFunctionToReal f)
  rw [hinner] at hparse
  simpa [fourierWeight] using hparse.symm

end

end BooleanFunctions
