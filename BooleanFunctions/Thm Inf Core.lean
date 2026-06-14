import BooleanFunctions.Influence
import BooleanFunctions.Plancherel
import BooleanFunctions.Parseval
import Mathlib.Tactic.NormNum

/-!
# Theorems of influence

This file contains the propositions, facts, and theorems from O'Donnell,
Sections 2.2 and 2.3.  The definition file `Influence.lean` keeps the named
objects; this file keeps the proof layer.
-/

namespace BooleanFunctions

/-! ## Section 2.2. Influences and derivatives -/

/-- Fact 2.14: influence is the dimension-`i` boundary-edge fraction. -/
theorem fact_2_14_boundary_edges {n : Nat}
    (f : BooleanFunctionSign n) (i : Fin n) :
    booleanInfluence f i = dimensionBoundaryEdgeFraction f i := by
  rfl

/-- Setting a coordinate outside `S` does not change the character `χ_S`. -/
lemma chiSign_setCoord_not_mem {n : Nat} {S : CoordinateSet n} {i : Fin n}
    (h : i ∉ S) (x : SignCube n) (b : SignBit) :
    chiSign S (setCoordSign x i b) = chiSign S x := by
  unfold chiSign
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := by
    intro h_eq
    subst j
    exact h hj
  simp [setCoordSign, hji]

/-- Setting coordinate `i ∈ S` factors `χ_S` into the new sign times `χ_{S\{i}}`. -/
lemma chiSign_setCoord_mem {n : Nat} {S : CoordinateSet n} {i : Fin n}
    (h : i ∈ S) (x : SignCube n) (b : SignBit) :
    chiSign S (setCoordSign x i b) = b.toReal * chiSign (S.erase i) x := by
  calc
    chiSign S (setCoordSign x i b)
        = chiSign (insert i (S.erase i)) (setCoordSign x i b) := by
      rw [Finset.insert_erase h]
    _ = b.toReal * chiSign (S.erase i) x := by
      rw [chiSign]
      rw [Finset.prod_insert]
      · rw [setCoordSign_same]
        congr 1
        unfold chiSign
        apply Finset.prod_congr rfl
        intro j hj
        have hji : j ≠ i := Finset.ne_of_mem_erase hj
        simp [setCoordSign, hji]
      · simp

/-- The discrete derivative of a character. -/
lemma chiSign_derivative_formula {n : Nat}
    (S : CoordinateSet n) (i : Fin n) (x : SignCube n) :
    ((chiSign S (setCoordSign x i SignBit.posOne) -
          chiSign S (setCoordSign x i SignBit.negOne)) / 2) =
      if i ∈ S then chiSign (S.erase i) x else 0 := by
  classical
  by_cases h : i ∈ S
  · rw [if_pos h]
    rw [chiSign_setCoord_mem h, chiSign_setCoord_mem h]
    simp [SignBit.toReal]
  · simp [h, chiSign_setCoord_not_mem]

/-- Pointwise Fourier expansion of a real-valued Boolean function. -/
lemma fourier_expansion_apply {n : Nat}
    (f : RealValuedBooleanFunction n) (x : SignCube n) :
    f x =
      Finset.univ.sum (fun S : CoordinateSet n =>
        functionFourierCoeff f S * chiSign S x) := by
  have h := congrFun (Module.Basis.sum_repr (fourierCharacterBasis n) f) x
  symm
  simpa [functionFourierCoeff, fourierCharacterBasis_apply] using h

lemma cubeExpectation_add' {n : Nat}
    (f g : RealValuedBooleanFunction n) :
    cubeExpectation (fun x : SignCube n => f x + g x) =
      cubeExpectation f + cubeExpectation g := by
  unfold cubeExpectation
  simp [Finset.sum_add_distrib, mul_add]

lemma cubeExpectation_const_mul {n : Nat}
    (a : Real) (f : RealValuedBooleanFunction n) :
    cubeExpectation (fun x : SignCube n => a * f x) =
      a * cubeExpectation f := by
  unfold cubeExpectation
  rw [← Finset.mul_sum]
  ring

lemma cubeExpectation_const {n : Nat} (a : Real) :
    cubeExpectation (fun _ : SignCube n => a) = a := by
  classical
  unfold cubeExpectation
  simp [SignCube, StringOver]

lemma cubeExpectation_finset_sum {n : Nat} {ι : Type}
    (s : Finset ι) (g : ι → RealValuedBooleanFunction n) :
    cubeExpectation (fun x : SignCube n => s.sum (fun i => g i x)) =
      s.sum (fun i => cubeExpectation (g i)) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp [cubeExpectation]
  · intro a s has ih
    simp [has, cubeExpectation_add', ih]

/--
Proposition 2.19.

The discrete derivative deletes coordinate `i` from every Fourier character
whose support contains `i`.
-/
theorem proposition_2_19 {n : Nat}
    (f : RealValuedBooleanFunction n) (i : Fin n) :
    discreteDerivative f i = derivativeFourierExpansion f i := by
  funext x
  rw [discreteDerivative, derivativeFourierExpansion]
  rw [fourier_expansion_apply f (setCoordSign x i SignBit.posOne)]
  rw [fourier_expansion_apply f (setCoordSign x i SignBit.negOne)]
  rw [← Finset.sum_sub_distrib]
  rw [div_eq_mul_inv]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro S _hS
  calc
    (functionFourierCoeff f S * chiSign S (setCoordSign x i SignBit.posOne) -
          functionFourierCoeff f S * chiSign S (setCoordSign x i SignBit.negOne)) *
        2⁻¹
        = functionFourierCoeff f S *
          ((chiSign S (setCoordSign x i SignBit.posOne) -
              chiSign S (setCoordSign x i SignBit.negOne)) / 2) := by
      ring
    _ = functionFourierCoeff f S *
          (if i ∈ S then chiSign (S.erase i) x else 0) := by
      rw [chiSign_derivative_formula S i x]
    _ = if i ∈ S then functionFourierCoeff f S * chiSign (S.erase i) x else 0 := by
      by_cases h : i ∈ S <;> simp [h]

lemma erase_eq_empty_iff_eq_singleton_of_mem {n : Nat}
    {S : CoordinateSet n} {i : Fin n} (hi : i ∈ S) :
    S.erase i = ∅ ↔ S = ({i} : CoordinateSet n) := by
  rw [Finset.erase_eq_empty_iff]
  constructor
  · intro h
    rcases h with h | h
    · exfalso
      simp [h] at hi
    · exact h
  · intro h
    exact Or.inr h

lemma cubeExpectation_derivativeFourier_term {n : Nat}
    (f : RealValuedBooleanFunction n) (i : Fin n) (S : CoordinateSet n) :
    cubeExpectation
        (fun x : SignCube n =>
          if i ∈ S then functionFourierCoeff f S * chiSign (S.erase i) x else 0) =
      if S = ({i} : CoordinateSet n) then functionFourierCoeff f S else 0 := by
  classical
  by_cases hi : i ∈ S
  · simp [hi]
    rw [cubeExpectation_const_mul]
    rw [cubeExpectation_chiSign]
    have herase := erase_eq_empty_iff_eq_singleton_of_mem (S := S) (i := i) hi
    by_cases hS : S = ({i} : CoordinateSet n)
    · simp [hS]
    · have hne : S.erase i ≠ ∅ := by
        intro h
        exact hS (herase.mp h)
      simp [hS, hne]
  · simp [hi]
    by_cases hS : S = ({i} : CoordinateSet n)
    · subst S
      simp at hi
    · simp [hS, cubeExpectation]

/-- The expectation of `D_i f` is the singleton Fourier coefficient. -/
theorem cubeExpectation_discreteDerivative {n : Nat}
    (f : RealValuedBooleanFunction n) (i : Fin n) :
    cubeExpectation (discreteDerivative f i) =
      functionFourierCoeff f ({i} : CoordinateSet n) := by
  rw [proposition_2_19 f i]
  unfold derivativeFourierExpansion
  rw [cubeExpectation_finset_sum]
  calc
    Finset.univ.sum (fun S : CoordinateSet n =>
        cubeExpectation
          (fun x : SignCube n =>
            if i ∈ S then functionFourierCoeff f S * chiSign (S.erase i) x else 0))
        =
        Finset.univ.sum (fun S : CoordinateSet n =>
          if S = ({i} : CoordinateSet n) then functionFourierCoeff f S else 0) := by
      apply Finset.sum_congr rfl
      intro S _hS
      exact cubeExpectation_derivativeFourier_term f i S
    _ = functionFourierCoeff f ({i} : CoordinateSet n) := by
      simp

lemma functionFourierCoeff_character_delta {n : Nat}
    (S T : CoordinateSet n) :
    functionFourierCoeff (fourierCharacters n S) T =
      if S = T then 1 else 0 := by
  rw [← fourierCharacterBasis_eq_fourierCharacters (S := S)]
  exact Module.Basis.repr_self_apply (fourierCharacterBasis n) S T

theorem functionFourierCoeff_eq_cubeInner {n : Nat}
    (f : RealValuedBooleanFunction n) (S : CoordinateSet n) :
    functionFourierCoeff f S = cubeInner f (fourierCharacters n S) := by
  symm
  calc
    cubeInner f (fourierCharacters n S) =
        Finset.univ.sum (fun T : CoordinateSet n =>
          functionFourierCoeff f T *
            functionFourierCoeff (fourierCharacters n S) T) := by
      exact plancherel_theorem f (fourierCharacters n S)
    _ = functionFourierCoeff f S := by
      classical
      simp [functionFourierCoeff_character_delta]

lemma cubeExpectation_coord_mul_eq_fourierCoeff_singleton {n : Nat}
    (f : RealValuedBooleanFunction n) (i : Fin n) :
    cubeExpectation (fun x : SignCube n => (x i).toReal * f x) =
      functionFourierCoeff f ({i} : CoordinateSet n) := by
  rw [functionFourierCoeff_eq_cubeInner]
  unfold cubeInner
  congr
  funext x
  simp [fourierCharacters, chiSign, mul_comm]

/-- Theorem 2.20: the Fourier expression for the project's influence. -/
theorem theorem_2_20_fourierInfluence {n : Nat}
    (f : RealValuedBooleanFunction n) (i : Fin n) :
    influence f i =
      Finset.univ.sum (fun S : CoordinateSet n =>
        if i ∈ S then functionFourierCoeff f S ^ 2 else 0) := by
  rfl

/-- Coordinate permutation as an equivalence of the cube. -/
def permuteSignCubeEquiv {n : Nat} (π : Equiv.Perm (Fin n)) :
    SignCube n ≃ SignCube n where
  toFun := permuteSignCube π
  invFun := permuteSignCube π.symm
  left_inv := by
    intro x
    funext i
    simp [permuteSignCube]
  right_inv := by
    intro x
    funext i
    simp [permuteSignCube]

/-- Uniform cube expectation is invariant under coordinate permutations. -/
lemma cubeExpectation_permute {n : Nat}
    (π : Equiv.Perm (Fin n)) (g : RealValuedBooleanFunction n) :
    cubeExpectation (fun x : SignCube n => g (permuteSignCube π x)) =
      cubeExpectation g := by
  unfold cubeExpectation
  change ((2 : Real) ^ n)⁻¹ *
      Finset.univ.sum (fun x : SignCube n => g ((permuteSignCubeEquiv π) x)) =
    ((2 : Real) ^ n)⁻¹ * Finset.univ.sum (fun x : SignCube n => g x)
  rw [Equiv.sum_comp (permuteSignCubeEquiv π) g]

lemma setCoordSign_permute {n : Nat}
    (π : Equiv.Perm (Fin n)) (x : SignCube n) (i : Fin n) (b : SignBit) :
    setCoordSign (permuteSignCube π x) i b =
      permuteSignCube π (setCoordSign x (π i) b) := by
  funext j
  by_cases h : j = i
  · subst j
    simp [setCoordSign, permuteSignCube]
  · have hπ : π j ≠ π i := by
      intro h_eq
      exact h (π.injective h_eq)
    simp [setCoordSign, permuteSignCube, h, hπ]

lemma discreteDerivative_permute_of_invariant {n : Nat}
    (f : BooleanFunctionSign n) (π : Equiv.Perm (Fin n))
    (hfix : ∀ x : SignCube n, f (permuteSignCube π x) = f x)
    (i : Fin n) (x : SignCube n) :
    discreteDerivative (signFunctionToReal f) i (permuteSignCube π x) =
      discreteDerivative (signFunctionToReal f) (π i) x := by
  unfold discreteDerivative signFunctionToReal
  rw [setCoordSign_permute π x i SignBit.posOne]
  rw [setCoordSign_permute π x i SignBit.negOne]
  rw [hfix (setCoordSign x (π i) SignBit.posOne)]
  rw [hfix (setCoordSign x (π i) SignBit.negOne)]

lemma derivativeInfluence_eq_of_symmetry {n : Nat}
    (f : BooleanFunctionSign n) (π : Equiv.Perm (Fin n))
    (hfix : ∀ x : SignCube n, f (permuteSignCube π x) = f x)
    (i : Fin n) :
    derivativeInfluence (signFunctionToReal f) i =
      derivativeInfluence (signFunctionToReal f) (π i) := by
  unfold derivativeInfluence
  rw [← cubeExpectation_permute π
    (fun x : SignCube n => discreteDerivative (signFunctionToReal f) i x ^ 2)]
  congr
  funext x
  rw [discreteDerivative_permute_of_invariant f π hfix i x]

/-- The coordinate expectation of a character. -/
lemma chiSign_coordinateExpectation_formula {n : Nat}
    (S : CoordinateSet n) (i : Fin n) (x : SignCube n) :
    ((chiSign S (setCoordSign x i SignBit.posOne) +
          chiSign S (setCoordSign x i SignBit.negOne)) / 2) =
      if i ∈ S then 0 else chiSign S x := by
  classical
  by_cases h : i ∈ S
  · rw [if_pos h]
    rw [chiSign_setCoord_mem h, chiSign_setCoord_mem h]
    simp [SignBit.toReal]
  · rw [if_neg h]
    rw [chiSign_setCoord_not_mem h, chiSign_setCoord_not_mem h]
    ring

/-- Fourier formula for the coordinate expectation operator. -/
theorem coordinateExpectation_eq_fourier {n : Nat}
    (f : RealValuedBooleanFunction n) (i : Fin n) :
    coordinateExpectation f i = coordinateExpectationFourierExpansion f i := by
  funext x
  rw [coordinateExpectation, coordinateExpectationFourierExpansion]
  rw [fourier_expansion_apply f (setCoordSign x i SignBit.posOne)]
  rw [fourier_expansion_apply f (setCoordSign x i SignBit.negOne)]
  rw [← Finset.sum_add_distrib]
  rw [div_eq_mul_inv]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro S _hS
  calc
    (functionFourierCoeff f S * chiSign S (setCoordSign x i SignBit.posOne) +
          functionFourierCoeff f S * chiSign S (setCoordSign x i SignBit.negOne)) *
        2⁻¹
        = functionFourierCoeff f S *
          ((chiSign S (setCoordSign x i SignBit.posOne) +
              chiSign S (setCoordSign x i SignBit.negOne)) / 2) := by
      ring
    _ = functionFourierCoeff f S *
          (if i ∈ S then 0 else chiSign S x) := by
      rw [chiSign_coordinateExpectation_formula S i x]
    _ = if i ∈ S then 0 else functionFourierCoeff f S * chiSign S x := by
      by_cases h : i ∈ S <;> simp [h]

/-- Replacing a coordinate by its current value leaves the cube point unchanged. -/
lemma setCoordSign_self {n : Nat} (x : SignCube n) (i : Fin n) :
    setCoordSign x i (x i) = x := by
  funext j
  by_cases h : j = i
  · subst j
    simp [setCoordSign]
  · simp [setCoordSign, h]

/-- Proposition 2.24: coordinate expectation and derivative decomposition. -/
theorem proposition_2_24 {n : Nat}
    (f : RealValuedBooleanFunction n) (i : Fin n) :
    coordinateExpectation f i = coordinateExpectationFourierExpansion f i ∧
      ∀ x : SignCube n,
        f x = (x i).toReal * discreteDerivative f i x +
          coordinateExpectation f i x := by
  refine ⟨coordinateExpectation_eq_fourier f i, ?_⟩
  intro x
  rcases hxi : x i with _ | _
  · have hneg : setCoordSign x i SignBit.negOne = x := by
      rw [← hxi]
      exact setCoordSign_self x i
    simp [discreteDerivative, coordinateExpectation, SignBit.toReal, hneg]
    ring
  · have hpos : setCoordSign x i SignBit.posOne = x := by
      rw [← hxi]
      exact setCoordSign_self x i
    simp [discreteDerivative, coordinateExpectation, SignBit.toReal, hpos]
    ring

/-- Fourier expansion of the coordinate Laplacian. -/
noncomputable def coordinateLaplacianFourierExpansion {n : Nat}
    (f : RealValuedBooleanFunction n) (i : Fin n) :
    RealValuedBooleanFunction n :=
  fun x =>
    Finset.univ.sum (fun S : CoordinateSet n =>
      if i ∈ S then functionFourierCoeff f S * chiSign S x else 0)

/-- The coordinate Laplacian keeps exactly the Fourier levels containing `i`. -/
theorem coordinateLaplacian_eq_fourier {n : Nat}
    (f : RealValuedBooleanFunction n) (i : Fin n) :
    coordinateLaplacian f i = coordinateLaplacianFourierExpansion f i := by
  funext x
  rw [coordinateLaplacian, coordinateExpectation_eq_fourier f i]
  rw [coordinateExpectationFourierExpansion, coordinateLaplacianFourierExpansion]
  rw [fourier_expansion_apply f x]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S _hS
  by_cases h : i ∈ S <;> simp [h]

/-- Coordinate Laplacian as an explicit sum of Fourier basis vectors. -/
lemma coordinateLaplacian_eq_basis_sum {n : Nat}
    (f : RealValuedBooleanFunction n) (i : Fin n) :
    coordinateLaplacian f i =
      Finset.univ.sum (fun S : CoordinateSet n =>
        (if i ∈ S then functionFourierCoeff f S else 0) •
          fourierCharacterBasis n S) := by
  funext x
  rw [coordinateLaplacian_eq_fourier f i]
  rw [coordinateLaplacianFourierExpansion]
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro S _hS
  by_cases h : i ∈ S <;> simp [h, fourierCharacterBasis_apply, smul_eq_mul]

/-- Fourier coefficients of `L_i f`. -/
lemma functionFourierCoeff_coordinateLaplacian {n : Nat}
    (f : RealValuedBooleanFunction n) (i : Fin n) (S : CoordinateSet n) :
    functionFourierCoeff (coordinateLaplacian f i) S =
      if i ∈ S then functionFourierCoeff f S else 0 := by
  unfold functionFourierCoeff
  rw [coordinateLaplacian_eq_basis_sum f i]
  exact congrFun
    (Module.Basis.repr_sum_self (fourierCharacterBasis n)
      (fun S : CoordinateSet n => if i ∈ S then functionFourierCoeff f S else 0)) S

/-- Proposition 2.26: formulas for the coordinate Laplacian. -/
theorem proposition_2_26 {n : Nat}
    (f : RealValuedBooleanFunction n) (i : Fin n) :
    (∀ x : SignCube n,
      coordinateLaplacian f i x = (f x - f (flipCoordSign x i)) / 2) ∧
    (coordinateLaplacian f i =
      fun x : SignCube n => (x i).toReal * discreteDerivative f i x) ∧
    cubeInner f (coordinateLaplacian f i) = influence f i := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    rcases hxi : x i with _ | _
    · have hneg : setCoordSign x i SignBit.negOne = x := by
        rw [← hxi]
        exact setCoordSign_self x i
      simp [coordinateLaplacian, coordinateExpectation, flipCoordSign, negSignBit,
        hxi, hneg]
      ring
    · have hpos : setCoordSign x i SignBit.posOne = x := by
        rw [← hxi]
        exact setCoordSign_self x i
      simp [coordinateLaplacian, coordinateExpectation, flipCoordSign, negSignBit,
        hxi, hpos]
      ring
  · funext x
    rcases hxi : x i with _ | _
    · have hneg : setCoordSign x i SignBit.negOne = x := by
        rw [← hxi]
        exact setCoordSign_self x i
      simp [coordinateLaplacian, coordinateExpectation, discreteDerivative,
        SignBit.toReal, hneg]
      ring
    · have hpos : setCoordSign x i SignBit.posOne = x := by
        rw [← hxi]
        exact setCoordSign_self x i
      simp [coordinateLaplacian, coordinateExpectation, discreteDerivative,
        SignBit.toReal, hpos]
      ring
  · rw [plancherel_theorem f (coordinateLaplacian f i)]
    unfold influence fourierInfluence
    apply Finset.sum_congr rfl
    intro S _hS
    rw [functionFourierCoeff_coordinateLaplacian f i S]
    by_cases h : i ∈ S <;> simp [h, pow_two]

/-- The coordinate Laplacian has squared norm equal to the influence. -/
theorem coordinateLaplacian_inner_self_eq_influence {n : Nat}
    (f : RealValuedBooleanFunction n) (i : Fin n) :
    cubeInner (coordinateLaplacian f i) (coordinateLaplacian f i) =
      influence f i := by
  rw [plancherel_theorem (coordinateLaplacian f i) (coordinateLaplacian f i)]
  unfold influence fourierInfluence
  apply Finset.sum_congr rfl
  intro S _hS
  rw [functionFourierCoeff_coordinateLaplacian f i S]
  by_cases h : i ∈ S <;> simp [h, pow_two]

/-- The Fourier-normalized influence agrees with the derivative definition. -/
theorem influence_eq_derivativeInfluence {n : Nat}
    (f : RealValuedBooleanFunction n) (i : Fin n) :
    influence f i = derivativeInfluence f i := by
  rw [← coordinateLaplacian_inner_self_eq_influence f i]
  have hL := (proposition_2_26 f i).2.1
  rw [hL]
  unfold derivativeInfluence cubeInner
  congr
  funext x
  simp [pow_two, SignBit.toReal_mul_self, mul_left_comm, mul_comm]

lemma setCoordSign_negOne_le_posOne {n : Nat}
    (x : SignCube n) (i : Fin n) :
    ∀ j : Fin n,
      (setCoordSign x i SignBit.negOne j).toInt ≤
        (setCoordSign x i SignBit.posOne j).toInt := by
  intro j
  by_cases h : j = i
  · subst j
    simp [setCoordSign, SignBit.toInt]
  · simp [setCoordSign, h]

lemma signBit_derivative_sq_eq_self_of_le
    (a b : SignBit) (h : a.toInt ≤ b.toInt) :
    ((b.toReal - a.toReal) / 2) ^ 2 =
      (b.toReal - a.toReal) / 2 := by
  cases a <;> cases b
  · norm_num [SignBit.toReal]
  · norm_num [SignBit.toReal]
  · norm_num [SignBit.toInt] at h
  · norm_num [SignBit.toReal]

lemma discreteDerivative_sq_eq_self_of_monotone {n : Nat}
    (f : BooleanFunctionSign n) (hf : IsMonotoneSignFunction f)
    (i : Fin n) (x : SignCube n) :
    discreteDerivative (signFunctionToReal f) i x ^ 2 =
      discreteDerivative (signFunctionToReal f) i x := by
  unfold discreteDerivative signFunctionToReal
  exact signBit_derivative_sq_eq_self_of_le
    (f (setCoordSign x i SignBit.negOne))
    (f (setCoordSign x i SignBit.posOne))
    (hf (setCoordSign x i SignBit.negOne)
      (setCoordSign x i SignBit.posOne)
      (setCoordSign_negOne_le_posOne x i))

/-- Proposition 2.21: for monotone Boolean functions, influence is the degree-one coefficient. -/
theorem proposition_2_21 {n : Nat}
    (f : BooleanFunctionSign n) (hf : IsMonotoneSignFunction f) (i : Fin n) :
    influence (signFunctionToReal f) i =
      functionFourierCoeff (signFunctionToReal f) ({i} : CoordinateSet n) := by
  rw [influence_eq_derivativeInfluence (signFunctionToReal f) i]
  unfold derivativeInfluence
  have hsq :
      (fun x : SignCube n =>
          discreteDerivative (signFunctionToReal f) i x ^ 2) =
        discreteDerivative (signFunctionToReal f) i := by
    funext x
    exact discreteDerivative_sq_eq_self_of_monotone f hf i x
  rw [hsq]
  exact cubeExpectation_discreteDerivative (signFunctionToReal f) i

lemma influence_nonneg {n : Nat}
    (f : RealValuedBooleanFunction n) (i : Fin n) :
    0 ≤ influence f i := by
  classical
  unfold influence fourierInfluence
  apply Finset.sum_nonneg
  intro S _hS
  by_cases hi : i ∈ S <;> simp [hi, sq_nonneg]

lemma influence_eq_of_transitiveSymmetric {n : Nat}
    (f : BooleanFunctionSign n) (htrans : IsTransitiveSymmetricSignFunction f)
    (i j : Fin n) :
    influence (signFunctionToReal f) i =
      influence (signFunctionToReal f) j := by
  rcases htrans i j with ⟨π, hπ, hfix⟩
  rw [influence_eq_derivativeInfluence (signFunctionToReal f) i]
  rw [influence_eq_derivativeInfluence (signFunctionToReal f) j]
  rw [← hπ]
  exact derivativeInfluence_eq_of_symmetry f π hfix i

lemma singletonCoordinateSet_injective {n : Nat} :
    Function.Injective (fun i : Fin n => ({i} : CoordinateSet n)) := by
  intro i j h
  have hi : i ∈ ({i} : CoordinateSet n) := by simp
  have hij : i ∈ ({j} : CoordinateSet n) := by
    simpa [h] using hi
  simpa using hij

lemma singleton_fourierCoeff_sq_sum_le_one {n : Nat}
    (f : BooleanFunctionSign n) :
    Finset.univ.sum (fun i : Fin n =>
        functionFourierCoeff (signFunctionToReal f) ({i} : CoordinateSet n) ^ 2) ≤
      1 := by
  classical
  let single : Fin n → CoordinateSet n := fun i => ({i} : CoordinateSet n)
  have hinj : Function.Injective single := singletonCoordinateSet_injective
  have hsum_image :
      (Finset.univ.image single).sum
          (fun S : CoordinateSet n => fourierWeight (signFunctionToReal f) S) =
        Finset.univ.sum
          (fun i : Fin n => fourierWeight (signFunctionToReal f) (single i)) := by
    rw [Finset.sum_image]
    intro x _hx y _hy hxy
    exact hinj hxy
  have hsubset :
      Finset.univ.image single ⊆ (Finset.univ : Finset (CoordinateSet n)) := by
    intro S _hS
    simp
  have hle :
      (Finset.univ.image single).sum
          (fun S : CoordinateSet n => fourierWeight (signFunctionToReal f) S) ≤
        Finset.univ.sum
          (fun S : CoordinateSet n => fourierWeight (signFunctionToReal f) S) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro S _hS _hnot
    exact sq_nonneg (functionFourierCoeff (signFunctionToReal f) S)
  calc
    Finset.univ.sum (fun i : Fin n =>
        functionFourierCoeff (signFunctionToReal f) ({i} : CoordinateSet n) ^ 2)
        =
        (Finset.univ.image single).sum
          (fun S : CoordinateSet n => fourierWeight (signFunctionToReal f) S) := by
      rw [hsum_image]
      rfl
    _ ≤ Finset.univ.sum
          (fun S : CoordinateSet n => fourierWeight (signFunctionToReal f) S) := hle
    _ = 1 := parseval_boolean f

/-- Proposition 2.22: transitive-symmetric monotone functions have small influences. -/
theorem proposition_2_22 {n : Nat}
    (f : BooleanFunctionSign n)
    (hf : IsMonotoneSignFunction f)
    (htrans : IsTransitiveSymmetricSignFunction f)
    (i : Fin n) :
    influence (signFunctionToReal f) i ≤ 1 / Real.sqrt n := by
  classical
  let a := influence (signFunctionToReal f) i
  have hcoeff_eq :
      ∀ j : Fin n,
        functionFourierCoeff (signFunctionToReal f) ({j} : CoordinateSet n) = a := by
    intro j
    calc
      functionFourierCoeff (signFunctionToReal f) ({j} : CoordinateSet n)
          = influence (signFunctionToReal f) j := by
        rw [proposition_2_21 f hf j]
      _ = a := by
        exact influence_eq_of_transitiveSymmetric f htrans j i
  have hsum_eq :
      Finset.univ.sum (fun j : Fin n =>
          functionFourierCoeff (signFunctionToReal f) ({j} : CoordinateSet n) ^ 2) =
        (n : Real) * a ^ 2 := by
    calc
      Finset.univ.sum (fun j : Fin n =>
          functionFourierCoeff (signFunctionToReal f) ({j} : CoordinateSet n) ^ 2)
          = Finset.univ.sum (fun _j : Fin n => a ^ 2) := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [hcoeff_eq j]
      _ = (n : Real) * a ^ 2 := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have hsum_le := singleton_fourierCoeff_sq_sum_le_one f
  rw [hsum_eq] at hsum_le
  have ha_nonneg : 0 ≤ a := influence_nonneg (signFunctionToReal f) i
  have hn_pos_nat : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hn_pos : 0 < (n : Real) := by
    exact_mod_cast hn_pos_nat
  have hsqrt_pos : 0 < Real.sqrt (n : Real) := Real.sqrt_pos.mpr hn_pos
  have hprod_sq : (a * Real.sqrt (n : Real)) ^ 2 ≤ (1 : Real) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (le_of_lt hn_pos), one_pow]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsum_le
  have hprod_nonneg : 0 ≤ a * Real.sqrt (n : Real) :=
    mul_nonneg ha_nonneg (Real.sqrt_nonneg _)
  have hprod_le_abs := (sq_le_sq.mp hprod_sq)
  have hprod_le : a * Real.sqrt (n : Real) ≤ 1 := by
    rw [abs_of_nonneg hprod_nonneg, abs_of_nonneg (zero_le_one : (0 : Real) ≤ 1)]
      at hprod_le_abs
    exact hprod_le_abs
  exact (le_div_iff₀ hsqrt_pos).mpr hprod_le

/-- For sign-valued functions, `(D_i f)^2` is the pivotal-coordinate indicator. -/
lemma signFunction_discreteDerivative_sq_eq_pivotalIndicator {n : Nat}
    (f : BooleanFunctionSign n) (i : Fin n) (x : SignCube n)
    [Decidable (IsPivotal f i x)] :
    discreteDerivative (signFunctionToReal f) i x ^ 2 =
      if IsPivotal f i x then 1 else 0 := by
  classical
  rcases hxi : x i with _ | _
  · have hneg : setCoordSign x i SignBit.negOne = x := by
      rw [← hxi]
      exact setCoordSign_self x i
    rcases hposVal : f (setCoordSign x i SignBit.posOne) with _ | _ <;>
      rcases hxVal : f x with _ | _ <;>
        simp [discreteDerivative, signFunctionToReal, IsPivotal, flipCoordSign,
          negSignBit, hxi, hneg, hposVal, hxVal, SignBit.toReal]
    all_goals
      try ring_nf
      simp
  · have hpos : setCoordSign x i SignBit.posOne = x := by
      rw [← hxi]
      exact setCoordSign_self x i
    rcases hxVal : f x with _ | _ <;>
      rcases hnegVal : f (setCoordSign x i SignBit.negOne) with _ | _ <;>
        simp [discreteDerivative, signFunctionToReal, IsPivotal, flipCoordSign,
          negSignBit, hxi, hpos, hxVal, hnegVal, SignBit.toReal]
    all_goals
      try ring_nf
      simp

lemma finset_sum_indicator_eq_card_filter {ι : Type} [DecidableEq ι]
    (s : Finset ι) (p : ι → Prop) [DecidablePred p] :
    s.sum (fun i => if p i then (1 : Real) else 0) = ((s.filter p).card : Real) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s has ih
    by_cases hp : p a <;> simp

/-! ## Section 2.3. Total influence -/

/-- Proposition 2.28: total influence is expected sensitivity. -/
theorem proposition_2_28 {n : Nat}
    (f : BooleanFunctionSign n) :
    totalInfluence (signFunctionToReal f) =
      cubeExpectation (fun x : SignCube n => (sensitivity f x : Real)) := by
  classical
  unfold totalInfluence
  have hsens :
      (fun x : SignCube n => (sensitivity f x : Real)) =
        fun x : SignCube n =>
          Finset.univ.sum (fun i : Fin n =>
            if IsPivotal f i x then (1 : Real) else 0) := by
    funext x
    unfold sensitivity
    rw [← finset_sum_indicator_eq_card_filter Finset.univ
      (fun i : Fin n => IsPivotal f i x)]
  rw [hsens]
  rw [cubeExpectation_finset_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [influence_eq_derivativeInfluence (signFunctionToReal f) i]
  unfold derivativeInfluence
  congr
  funext x
  rw [signFunction_discreteDerivative_sq_eq_pivotalIndicator f i x]

/-- Fact 2.29: boundary-edge fraction is `I[f] / n`. -/
theorem fact_2_29_boundary_fraction {n : Nat}
    (f : BooleanFunctionSign n) :
    boundaryEdgeFraction f = totalInfluence (signFunctionToReal f) / n := by
  rfl

/-- Proposition 2.31: for monotone Boolean functions, total influence is the degree-one sum. -/
theorem proposition_2_31 {n : Nat}
    (f : BooleanFunctionSign n) (hf : IsMonotoneSignFunction f) :
    totalInfluence (signFunctionToReal f) = degreeOneFourierSum f := by
  unfold totalInfluence degreeOneFourierSum
  apply Finset.sum_congr rfl
  intro i _hi
  exact proposition_2_21 f hf i

lemma agreeingVoteIndicator_eq (a b : SignBit) :
    (if a = b then (1 : Real) else 0) =
      (1 + a.toReal * b.toReal) / 2 := by
  cases a <;> cases b <;> simp [SignBit.toReal]

lemma agreeingVoteCount_eq_sum {n : Nat}
    (f : BooleanFunctionSign n) (x : SignCube n) :
    (agreeingVoteCount f x : Real) =
      Finset.univ.sum (fun i : Fin n =>
        (1 + (x i).toReal * (f x).toReal) / 2) := by
  classical
  unfold agreeingVoteCount
  rw [← finset_sum_indicator_eq_card_filter Finset.univ
    (fun i : Fin n => x i = f x)]
  apply Finset.sum_congr rfl
  intro i _hi
  exact agreeingVoteIndicator_eq (x i) (f x)

lemma cubeExpectation_agreeingVoteTerm {n : Nat}
    (f : BooleanFunctionSign n) (i : Fin n) :
    cubeExpectation
        (fun x : SignCube n => (1 + (x i).toReal * (f x).toReal) / 2) =
      1 / 2 +
        (1 / 2) *
          functionFourierCoeff (signFunctionToReal f) ({i} : CoordinateSet n) := by
  calc
    cubeExpectation
        (fun x : SignCube n => (1 + (x i).toReal * (f x).toReal) / 2)
        =
        cubeExpectation
          (fun x : SignCube n =>
            (1 / 2 : Real) *
              (1 + (x i).toReal * signFunctionToReal f x)) := by
      congr
      funext x
      simp [signFunctionToReal]
      ring
    _ =
        (1 / 2 : Real) *
          cubeExpectation
            (fun x : SignCube n =>
              1 + (x i).toReal * signFunctionToReal f x) := by
      rw [cubeExpectation_const_mul]
    _ =
        (1 / 2 : Real) *
          (1 +
            functionFourierCoeff (signFunctionToReal f) ({i} : CoordinateSet n)) := by
      rw [cubeExpectation_add']
      rw [cubeExpectation_const]
      rw [cubeExpectation_coord_mul_eq_fourierCoeff_singleton]
    _ =
        1 / 2 +
          (1 / 2) *
            functionFourierCoeff (signFunctionToReal f) ({i} : CoordinateSet n) := by
      ring

/-- Proposition 2.32: expected number of voters agreeing with the outcome. -/
theorem proposition_2_32 {n : Nat}
    (f : BooleanFunctionSign n) :
    expectedAgreeingVotes f =
      (n : Real) / 2 + (1 / 2) * degreeOneFourierSum f := by
  unfold expectedAgreeingVotes
  have hpoint :
      (fun x : SignCube n => (agreeingVoteCount f x : Real)) =
        fun x : SignCube n =>
          Finset.univ.sum (fun i : Fin n =>
            (1 + (x i).toReal * (f x).toReal) / 2) := by
    funext x
    exact agreeingVoteCount_eq_sum f x
  rw [hpoint]
  rw [cubeExpectation_finset_sum]
  unfold degreeOneFourierSum
  calc
    Finset.univ.sum (fun i : Fin n =>
        cubeExpectation
          (fun x : SignCube n => (1 + (x i).toReal * (f x).toReal) / 2))
        =
        Finset.univ.sum (fun i : Fin n =>
          1 / 2 +
            (1 / 2) *
              functionFourierCoeff (signFunctionToReal f) ({i} : CoordinateSet n)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [cubeExpectation_agreeingVoteTerm f i]
    _ =
        (n : Real) / 2 +
          (1 / 2) *
            Finset.univ.sum (fun i : Fin n =>
              functionFourierCoeff (signFunctionToReal f) ({i} : CoordinateSet n)) := by
      rw [Finset.sum_add_distrib]
      rw [← Finset.mul_sum]
      simp [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Proposition 2.35: total influence is expected squared gradient norm. -/
theorem proposition_2_35 {n : Nat}
    (f : RealValuedBooleanFunction n) :
    totalInfluence f = cubeExpectation (fun x : SignCube n => gradientNormSq f x) := by
  unfold totalInfluence gradientNormSq gradient
  rw [cubeExpectation_finset_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [influence_eq_derivativeInfluence f i]
  rfl

lemma sum_if_mem_eq_card_mul {n : Nat}
    (S : CoordinateSet n) (a : Real) :
    Finset.univ.sum (fun i : Fin n => if i ∈ S then a else 0) =
      (S.card : Real) * a := by
  classical
  calc
    Finset.univ.sum (fun i : Fin n => if i ∈ S then a else 0)
        = (Finset.univ.filter (fun i : Fin n => i ∈ S)).sum
            (fun _ : Fin n => a) := by
      rw [Finset.sum_filter]
    _ = S.sum (fun _ : Fin n => a) := by
      congr
      ext i
      simp
    _ = (S.card : Real) * a := by
      simp [Finset.sum_const, nsmul_eq_mul]

/-- Theorem 2.38: total influence in Fourier form. -/
theorem theorem_2_38_totalInfluence_fourier {n : Nat}
    (f : RealValuedBooleanFunction n) :
    totalInfluence f = fourierTotalInfluence f := by
  classical
  unfold totalInfluence influence fourierInfluence fourierTotalInfluence
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _hS
  exact sum_if_mem_eq_card_mul S (functionFourierCoeff f S ^ 2)

/-- The cube Laplacian has Fourier multiplier `|S|` on character `χ_S`. -/
theorem laplacian_eq_fourier {n : Nat}
    (f : RealValuedBooleanFunction n) :
    laplacian f = laplacianFourierExpansion f := by
  funext x
  unfold laplacian laplacianFourierExpansion
  calc
    Finset.univ.sum (fun i : Fin n => coordinateLaplacian f i x)
        = Finset.univ.sum (fun i : Fin n =>
            Finset.univ.sum (fun S : CoordinateSet n =>
              if i ∈ S then functionFourierCoeff f S * chiSign S x else 0)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [coordinateLaplacian_eq_fourier f i]
      rfl
    _ = Finset.univ.sum (fun S : CoordinateSet n =>
          Finset.univ.sum (fun i : Fin n =>
            if i ∈ S then functionFourierCoeff f S * chiSign S x else 0)) := by
      rw [Finset.sum_comm]
    _ = Finset.univ.sum (fun S : CoordinateSet n =>
          (S.card : Real) * (functionFourierCoeff f S * chiSign S x)) := by
      apply Finset.sum_congr rfl
      intro S _hS
      exact sum_if_mem_eq_card_mul S (functionFourierCoeff f S * chiSign S x)
    _ = Finset.univ.sum (fun S : CoordinateSet n =>
          (S.card : Real) * functionFourierCoeff f S * chiSign S x) := by
      apply Finset.sum_congr rfl
      intro S _hS
      ring

/-- Laplacian as an explicit sum of Fourier basis vectors. -/
lemma laplacian_eq_basis_sum {n : Nat}
    (f : RealValuedBooleanFunction n) :
    laplacian f =
      Finset.univ.sum (fun S : CoordinateSet n =>
        ((S.card : Real) * functionFourierCoeff f S) •
          fourierCharacterBasis n S) := by
  funext x
  rw [laplacian_eq_fourier f]
  unfold laplacianFourierExpansion
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro S _hS
  simp [fourierCharacterBasis_apply, smul_eq_mul]

/-- Fourier coefficients of the cube Laplacian. -/
lemma functionFourierCoeff_laplacian {n : Nat}
    (f : RealValuedBooleanFunction n) (S : CoordinateSet n) :
    functionFourierCoeff (laplacian f) S =
      (S.card : Real) * functionFourierCoeff f S := by
  unfold functionFourierCoeff
  rw [laplacian_eq_basis_sum f]
  exact congrFun
    (Module.Basis.repr_sum_self (fourierCharacterBasis n)
      (fun S : CoordinateSet n => (S.card : Real) * functionFourierCoeff f S)) S

/-- Proposition 2.37: Fourier and inner-product formulas for the Laplacian. -/
theorem proposition_2_37 {n : Nat}
    (f : RealValuedBooleanFunction n) :
    laplacian f = laplacianFourierExpansion f ∧
      cubeInner f (laplacian f) = totalInfluence f := by
  refine ⟨laplacian_eq_fourier f, ?_⟩
  rw [plancherel_theorem f (laplacian f)]
  rw [theorem_2_38_totalInfluence_fourier f]
  unfold fourierTotalInfluence
  apply Finset.sum_congr rfl
  intro S _hS
  rw [functionFourierCoeff_laplacian f S]
  ring

/-- The level-weight form of Theorem 2.38. -/
theorem theorem_2_38_level {n : Nat}
    (f : RealValuedBooleanFunction n) :
    totalInfluence f =
      (Finset.range (n + 1)).sum
        (fun k => (k : Real) * totalFourierWeightAtDegree f k) := by
  classical
  rw [theorem_2_38_totalInfluence_fourier f]
  unfold fourierTotalInfluence totalFourierWeightAtDegree
  symm
  calc
    (Finset.range (n + 1)).sum
        (fun k =>
          (k : Real) *
            Finset.univ.sum (fun S : CoordinateSet n =>
              if S.card = k then functionFourierCoeff f S ^ 2 else 0))
        =
        (Finset.range (n + 1)).sum
          (fun k =>
            Finset.univ.sum (fun S : CoordinateSet n =>
              (k : Real) *
                (if S.card = k then functionFourierCoeff f S ^ 2 else 0))) := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.mul_sum]
    _ =
        Finset.univ.sum
          (fun S : CoordinateSet n =>
            (Finset.range (n + 1)).sum
              (fun k =>
                (k : Real) *
                  (if S.card = k then functionFourierCoeff f S ^ 2 else 0))) := by
      rw [Finset.sum_comm]
    _ =
        Finset.univ.sum (fun S : CoordinateSet n =>
          (S.card : Real) * functionFourierCoeff f S ^ 2) := by
      apply Finset.sum_congr rfl
      intro S _hS
      have hcard_le : S.card ≤ n := by
        simpa using (Finset.card_le_univ S)
      have hmem : S.card ∈ Finset.range (n + 1) := by
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le hcard_le)
      calc
        (Finset.range (n + 1)).sum
            (fun k =>
              (k : Real) *
                (if S.card = k then functionFourierCoeff f S ^ 2 else 0))
            =
            (S.card : Real) *
              (if S.card = S.card then functionFourierCoeff f S ^ 2 else 0) := by
          apply Finset.sum_eq_single S.card
          · intro k _hk hne
            have hneq : S.card ≠ k := by
              intro h
              exact hne h.symm
            simp [hneq]
          · intro hnot
            exact (hnot hmem).elim
        _ = (S.card : Real) * functionFourierCoeff f S ^ 2 := by
          simp

/-- Statement 2.39: the book's Theorem 2.39. -/
def Statement2_39 (n : Nat) : Prop :=
  ∀ f : BooleanFunctionSign n,
    let α := signValueProbability f SignBit.negOne
    α ≤ 1 / 2 →
      edgeIsoperimetricLowerBound α ≤ totalInfluence (signFunctionToReal f)

end BooleanFunctions
