import BooleanFunctions.Fourierexpansion

/-!
# O'Donnell, Theorem 1.1

This file proves the finite-dimensional form of Theorem 1.1 from Section 1.2:
every real-valued function on the sign cube has a unique multilinear expansion
in the parity functions `chiSign S`.

Most linear-algebra infrastructure now lives in `Fourierexpansion.lean`; this file keeps
only the theorem-specific coefficient table and uniqueness argument.

The final textbook-facing statement is `theorem_1_1`.
-/

namespace BooleanFunctions

/-!
## Coefficients in the character basis

The coefficient table for `f` is its coordinate vector in the character basis.
In mathlib, the coordinate vector of a basis is written `basis.repr f`.
-/

/-- The coefficient table of `f` in the character basis. -/
noncomputable def theoremOneOneCoefficients {n : Nat}
    (f : RealValuedBooleanFunction n) : MultilinearPolynomial n :=
  fun S => (fourierCharacterBasis n).repr f S

/--
A finite linear combination of character basis vectors is exactly the
evaluation of the corresponding multilinear polynomial.
-/
lemma linearCombination_eq_eval {n : Nat} (p : MultilinearPolynomial n) :
    Finset.univ.sum
        (fun S : CoordinateSet n => SMul.smul (p S) (fourierCharacterBasis n S)) =
      (fun x : SignCube n => evalMultilinearPolynomial p x) := by
  classical
  funext x
  calc
    (Finset.univ.sum
        (fun S : CoordinateSet n => SMul.smul (p S) (fourierCharacterBasis n S))) x =
        Finset.univ.sum (fun S : CoordinateSet n =>
          (SMul.smul (p S) (fourierCharacterBasis n S)) x) := by
      rw [Finset.sum_apply]
    _ = Finset.univ.sum (fun S : CoordinateSet n => p S * chiSign S x) := by
      apply Finset.sum_congr rfl
      intro S _hS
      change p S * (fourierCharacterBasis n S x) = p S * chiSign S x
      rw [fourierCharacterBasis_apply]
    _ = evalMultilinearPolynomial p x := rfl

/-- The coefficient table `theoremOneOneCoefficients f` evaluates back to `f`. -/
lemma theoremOneOneCoefficients_eval {n : Nat} (f : RealValuedBooleanFunction n) :
    ∀ x : SignCube n, evalMultilinearPolynomial (theoremOneOneCoefficients f) x = f x := by
  classical
  have h := Module.Basis.sum_repr (fourierCharacterBasis n) f
  change Finset.univ.sum (fun S : CoordinateSet n =>
    SMul.smul (theoremOneOneCoefficients f S) (fourierCharacterBasis n S)) = f at h
  rw [linearCombination_eq_eval (theoremOneOneCoefficients f)] at h
  intro x
  exact congrFun h x

/--
If a coefficient table evaluates to `f`, then it must be the coefficient table
coming from the character basis.
-/
lemma eq_theoremOneOneCoefficients_of_eval_eq {n : Nat} (p : MultilinearPolynomial n)
    (f : RealValuedBooleanFunction n)
    (hp : ∀ x : SignCube n, evalMultilinearPolynomial p x = f x) :
    p = theoremOneOneCoefficients f := by
  classical
  have hcomb :
      Finset.univ.sum
          (fun S : CoordinateSet n => SMul.smul (p S) (fourierCharacterBasis n S)) = f := by
    rw [linearCombination_eq_eval p]
    funext x
    exact hp x
  have hrepr : ((fourierCharacterBasis n).repr
      (Finset.univ.sum
        (fun S : CoordinateSet n => SMul.smul (p S) (fourierCharacterBasis n S))) :
        CoordinateSet n -> Real) = p :=
    Module.Basis.repr_sum_self (fourierCharacterBasis n) p
  rw [hcomb] at hrepr
  exact hrepr.symm

/--
Every function `f : {-1,1}^n -> Real` has a unique multilinear expansion
`sum_S p(S) * chi_S(x)`.
-/
theorem existsUnique_evalMultilinearPolynomial (n : Nat) (f : RealValuedBooleanFunction n) :
    ExistsUnique (fun p : MultilinearPolynomial n =>
      ∀ x : SignCube n, evalMultilinearPolynomial p x = f x) := by
  classical
  exact ExistsUnique.intro (theoremOneOneCoefficients f)
    (theoremOneOneCoefficients_eval f)
    (fun p hp => eq_theoremOneOneCoefficients_of_eval_eq p f hp)

/--
O'Donnell Theorem 1.1, formalized for the sign cube.

This is a textbook-facing alias for `existsUnique_evalMultilinearPolynomial`.
-/
theorem theorem_1_1 (n : Nat) (f : RealValuedBooleanFunction n) :
    ExistsUnique (fun p : MultilinearPolynomial n =>
      ∀ x : SignCube n, evalMultilinearPolynomial p x = f x) :=
  existsUnique_evalMultilinearPolynomial n f

end BooleanFunctions
