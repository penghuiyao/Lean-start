import BooleanFunctions.Fourierexpansion

/-!
# O'Donnell, Section 1.3

This file formalizes the numbered results from Section 1.3 of
*Analysis of Boolean Functions*:

* Theorem 1.5: the parity functions form an orthonormal basis.
* Fact 1.6: `chi_S * chi_T = chi_{S symmetric-difference T}`.
* Fact 1.7: the expectation of `chi_S` is `1` for `S = empty` and `0`
  otherwise.

The definitions used here, including the normalized inner product
`cubeInner`, live in `Fourierexpansion.lean`.
-/

namespace BooleanFunctions

/--
Fact 1.6.

For every cube point `x`, multiplying the two parity functions cancels the
coordinates appearing twice, leaving exactly the symmetric difference.
-/
theorem fact_1_6 {n : Nat} (S T : CoordinateSet n) (x : SignCube n) :
    chiSign S x * chiSign T x = chiSign (symmDiff S T) x :=
  chiSign_mul_symmDiff S T x

/--
Fact 1.7.

The uniform expectation of a parity function is `1` for the empty parity and
`0` for every nonempty parity.
-/
theorem fact_1_7 {n : Nat} (S : CoordinateSet n) :
    cubeExpectation (fun x : SignCube n => chiSign S x) =
      if S = ∅ then 1 else 0 :=
  cubeExpectation_chiSign S

/-- The orthonormality part of Theorem 1.5. -/
theorem theorem_1_5_orthonormal {n : Nat} (S T : CoordinateSet n) :
    cubeInner (fourierCharacters n S) (fourierCharacters n T) =
      if S = T then 1 else 0 :=
  fourierCharacters_orthonormal S T

/-- The basis part of Theorem 1.5. -/
theorem theorem_1_5_basis (n : Nat) :
    ∃ b : Module.Basis (CoordinateSet n) Real (RealValuedBooleanFunction n),
      ∀ (S : CoordinateSet n) (x : SignCube n), b S x = chiSign S x :=
  ⟨fourierCharacterBasis n, fun S x => fourierCharacterBasis_apply S x⟩

/--
Theorem 1.5.

The parity functions `chi_S : {-1,1}^n -> {-1,1}` form an orthonormal basis
for the real vector space of all functions `{-1,1}^n -> R`.
-/
theorem theorem_1_5 (n : Nat) :
    (∀ S T : CoordinateSet n,
      cubeInner (fourierCharacters n S) (fourierCharacters n T) =
        if S = T then 1 else 0) ∧
    ∃ b : Module.Basis (CoordinateSet n) Real (RealValuedBooleanFunction n),
      ∀ (S : CoordinateSet n) (x : SignCube n), b S x = chiSign S x := by
  constructor
  · intro S T
    exact theorem_1_5_orthonormal S T
  · exact theorem_1_5_basis n

end BooleanFunctions
