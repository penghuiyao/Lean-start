import BooleanFunctions.«noise stability»
import BooleanFunctions.Parseval
import BooleanFunctions.«Thm Inf Core»
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.NormNum

/-!
# Theorems on noise stability

Formal statements and Fourier proofs from O'Donnell, Section 2.4.

Theorem 2.45 on majority is intentionally omitted, as requested.
-/

namespace BooleanFunctions

/-! ## Example 2.44 and Proposition 2.47 -/

/-- Proposition 2.47, pointwise Fourier expansion of the noise operator. -/
theorem proposition_2_47_fourier {n : Nat}
    (rho : Real) (f : RealValuedBooleanFunction n) (x : SignCube n) :
    noiseOperator rho f x =
      Finset.univ.sum (fun S : CoordinateSet n =>
        rho ^ S.card * functionFourierCoeff f S * chiSign S x) := by
  unfold noiseOperator
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro S _hS
  simp [fourierCharacterBasis_apply, mul_assoc]

/-- Fourier coefficients of the noise operator. -/
lemma functionFourierCoeff_noiseOperator {n : Nat}
    (rho : Real) (f : RealValuedBooleanFunction n) (S : CoordinateSet n) :
    functionFourierCoeff (noiseOperator rho f) S =
      rho ^ S.card * functionFourierCoeff f S := by
  unfold functionFourierCoeff noiseOperator
  exact congrFun
    (Module.Basis.repr_sum_self (fourierCharacterBasis n)
      (fun S : CoordinateSet n => rho ^ S.card * functionFourierCoeff f S)) S

/--
Proposition 2.47, level-decomposition form:
`T_rho f = sum_k rho^k f_=k`.
-/
theorem proposition_2_47_degree {n : Nat}
    (rho : Real) (f : RealValuedBooleanFunction n) (x : SignCube n) :
    noiseOperator rho f x =
      (Finset.range (n + 1)).sum
        (fun k => rho ^ k * degreePart f k x) := by
  classical
  rw [proposition_2_47_fourier]
  unfold degreePart
  symm
  calc
    (Finset.range (n + 1)).sum
        (fun k =>
          rho ^ k *
            Finset.univ.sum (fun S : CoordinateSet n =>
              if S.card = k then functionFourierCoeff f S * chiSign S x else 0))
        =
        (Finset.range (n + 1)).sum
          (fun k =>
            Finset.univ.sum (fun S : CoordinateSet n =>
              rho ^ k *
                (if S.card = k then functionFourierCoeff f S * chiSign S x else 0))) := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.mul_sum]
    _ =
        Finset.univ.sum
          (fun S : CoordinateSet n =>
            (Finset.range (n + 1)).sum
              (fun k =>
                rho ^ k *
                  (if S.card = k then functionFourierCoeff f S * chiSign S x else 0))) := by
      rw [Finset.sum_comm]
    _ =
        Finset.univ.sum (fun S : CoordinateSet n =>
          rho ^ S.card * functionFourierCoeff f S * chiSign S x) := by
      apply Finset.sum_congr rfl
      intro S _hS
      have hcard_le : S.card ≤ n := by
        simpa using (Finset.card_le_univ S)
      have hmem : S.card ∈ Finset.range (n + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le hcard_le)
      calc
        (Finset.range (n + 1)).sum
            (fun k =>
              rho ^ k *
                (if S.card = k then functionFourierCoeff f S * chiSign S x else 0))
            =
            rho ^ S.card *
              (if S.card = S.card then functionFourierCoeff f S * chiSign S x else 0) := by
          apply Finset.sum_eq_single S.card
          · intro k _hk hne
            have hneq : S.card ≠ k := by
              intro h
              exact hne h.symm
            simp [hneq]
          · intro hnot
            exact (hnot hmem).elim
        _ = rho ^ S.card * functionFourierCoeff f S * chiSign S x := by
          simp [mul_assoc]

/-- Example 2.44: the character `chi_S` has noise stability `rho ^ |S|`. -/
theorem example_2_44_character {n : Nat}
    (rho : Real) (S : CoordinateSet n) :
    noiseStability rho (fourierCharacters n S) = rho ^ S.card := by
  rw [noiseStability, plancherel_theorem]
  calc
    Finset.univ.sum (fun T : CoordinateSet n =>
        functionFourierCoeff (fourierCharacters n S) T *
          functionFourierCoeff (noiseOperator rho (fourierCharacters n S)) T)
        =
        Finset.univ.sum (fun T : CoordinateSet n =>
          (if S = T then 1 else 0) *
            (rho ^ T.card * (if S = T then 1 else 0))) := by
      apply Finset.sum_congr rfl
      intro T _hT
      rw [functionFourierCoeff_noiseOperator]
      simp [functionFourierCoeff_character_delta]
    _ = rho ^ S.card := by
      simp

/-! ## Fact 2.48 and Theorem 2.49 -/

/-- Fact 2.48: noise stability is the inner product with the noise operator. -/
theorem fact_2_48 {n : Nat}
    (rho : Real) (f : RealValuedBooleanFunction n) :
    noiseStability rho f = cubeInner f (noiseOperator rho f) := by
  rfl

/-- Theorem 2.49, Fourier formula for noise stability. -/
theorem theorem_2_49_fourier {n : Nat}
    (rho : Real) (f : RealValuedBooleanFunction n) :
    noiseStability rho f =
      Finset.univ.sum (fun S : CoordinateSet n =>
        rho ^ S.card * functionFourierCoeff f S ^ 2) := by
  rw [noiseStability, plancherel_theorem]
  apply Finset.sum_congr rfl
  intro S _hS
  rw [functionFourierCoeff_noiseOperator]
  ring

/-- Sum of Fourier weights over all levels equals the total Fourier weight. -/
lemma sum_fourierWeightAtDegree_range {n : Nat}
    (f : RealValuedBooleanFunction n) :
    (Finset.range (n + 1)).sum (fun k => fourierWeightAtDegree f k) =
      Finset.univ.sum (fun S : CoordinateSet n => fourierWeight f S) := by
  classical
  unfold fourierWeightAtDegree
  calc
    (Finset.range (n + 1)).sum
        (fun k =>
          Finset.univ.sum (fun S : CoordinateSet n =>
            if S.card = k then fourierWeight f S else 0))
        =
        Finset.univ.sum
          (fun S : CoordinateSet n =>
            (Finset.range (n + 1)).sum
              (fun k => if S.card = k then fourierWeight f S else 0)) := by
      rw [Finset.sum_comm]
    _ = Finset.univ.sum (fun S : CoordinateSet n => fourierWeight f S) := by
      apply Finset.sum_congr rfl
      intro S _hS
      have hcard_le : S.card ≤ n := by
        simpa using (Finset.card_le_univ S)
      have hmem : S.card ∈ Finset.range (n + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le hcard_le)
      calc
        (Finset.range (n + 1)).sum
            (fun k => if S.card = k then fourierWeight f S else 0)
            = (if S.card = S.card then fourierWeight f S else 0) := by
          apply Finset.sum_eq_single S.card
          · intro k _hk hne
            have hneq : S.card ≠ k := by
              intro h
              exact hne h.symm
            simp [hneq]
          · intro hnot
            exact (hnot hmem).elim
        _ = fourierWeight f S := by
          simp

/-- Theorem 2.49, level-weight formula. -/
theorem theorem_2_49_level {n : Nat}
    (rho : Real) (f : RealValuedBooleanFunction n) :
    noiseStability rho f =
      (Finset.range (n + 1)).sum
        (fun k => rho ^ k * fourierWeightAtDegree f k) := by
  classical
  rw [theorem_2_49_fourier]
  unfold fourierWeightAtDegree fourierWeight
  symm
  calc
    (Finset.range (n + 1)).sum
        (fun k =>
          rho ^ k *
            Finset.univ.sum (fun S : CoordinateSet n =>
              if S.card = k then functionFourierCoeff f S ^ 2 else 0))
        =
        (Finset.range (n + 1)).sum
          (fun k =>
            Finset.univ.sum (fun S : CoordinateSet n =>
              rho ^ k *
                (if S.card = k then functionFourierCoeff f S ^ 2 else 0))) := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.mul_sum]
    _ =
        Finset.univ.sum
          (fun S : CoordinateSet n =>
            (Finset.range (n + 1)).sum
              (fun k =>
                rho ^ k *
                  (if S.card = k then functionFourierCoeff f S ^ 2 else 0))) := by
      rw [Finset.sum_comm]
    _ =
        Finset.univ.sum (fun S : CoordinateSet n =>
          rho ^ S.card * functionFourierCoeff f S ^ 2) := by
      apply Finset.sum_congr rfl
      intro S _hS
      have hcard_le : S.card ≤ n := by
        simpa using (Finset.card_le_univ S)
      have hmem : S.card ∈ Finset.range (n + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le hcard_le)
      calc
        (Finset.range (n + 1)).sum
            (fun k =>
              rho ^ k * (if S.card = k then functionFourierCoeff f S ^ 2 else 0))
            =
            rho ^ S.card *
              (if S.card = S.card then functionFourierCoeff f S ^ 2 else 0) := by
          apply Finset.sum_eq_single S.card
          · intro k _hk hne
            have hneq : S.card ≠ k := by
              intro h
              exact hne h.symm
            simp [hneq]
          · intro hnot
            exact (hnot hmem).elim
        _ = rho ^ S.card * functionFourierCoeff f S ^ 2 := by
          simp

/-- Theorem 2.49, spectral-sample formula for Boolean-valued functions. -/
theorem theorem_2_49_spectralSample {n : Nat}
    (rho : Real) (f : BooleanFunctionSign n) :
    booleanNoiseStability rho f =
      Finset.univ.sum (fun S : CoordinateSet n =>
        spectralSampleWeight f S * rho ^ S.card) := by
  rw [booleanNoiseStability, theorem_2_49_fourier]
  apply Finset.sum_congr rfl
  intro S _hS
  simp [spectralSampleWeight, fourierWeight, mul_comm]

/-- Theorem 2.49, formula for noise sensitivity. -/
theorem theorem_2_49_noiseSensitivity {n : Nat}
    (delta : Real) (f : BooleanFunctionSign n) :
    noiseSensitivity delta f =
      (1 / 2) *
        (Finset.range (n + 1)).sum
          (fun k =>
            (1 - (1 - 2 * delta) ^ k) *
              fourierWeightAtDegree (signFunctionToReal f) k) := by
  classical
  rw [noiseSensitivity, booleanNoiseStability, theorem_2_49_level]
  have hsum :
      (Finset.range (n + 1)).sum
          (fun k => fourierWeightAtDegree (signFunctionToReal f) k) = 1 := by
    rw [sum_fourierWeightAtDegree_range]
    simpa [fourierWeight] using parseval_boolean f
  calc
    1 / 2 -
        1 / 2 *
          (Finset.range (n + 1)).sum
            (fun k =>
              (1 - 2 * delta) ^ k *
                fourierWeightAtDegree (signFunctionToReal f) k)
        =
        1 / 2 *
          (Finset.range (n + 1)).sum
            (fun k => fourierWeightAtDegree (signFunctionToReal f) k) -
        1 / 2 *
          (Finset.range (n + 1)).sum
            (fun k =>
              (1 - 2 * delta) ^ k *
                fourierWeightAtDegree (signFunctionToReal f) k) := by
      rw [hsum]
      ring
    _ =
        (1 / 2) *
          (Finset.range (n + 1)).sum
            (fun k =>
              (1 - (1 - 2 * delta) ^ k) *
                fourierWeightAtDegree (signFunctionToReal f) k) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      rw [← Finset.sum_sub_distrib]
      congr 1
      funext k
      ring

/-! ## Statements for the remaining Section 2.4 results -/

/--
Proposition 2.50.

The equality case uses Exercise 1.19(a), which is not yet part of the local
library, so the full proposition is recorded as a statement.
-/
def Statement2_50 (n : Nat) : Prop :=
  ∀ (rho : Real) (f : BooleanFunctionSign n),
    0 < rho → rho < 1 →
      IsUnbiased (signFunctionToReal f) →
        booleanNoiseStability rho f ≤ rho ∧
        (booleanNoiseStability rho f = rho ↔
          ∃ i : Fin n,
            f = dictatorFunction i ∨ f = negatedDictatorFunction i)

/-- The equality-case part of Proposition 2.50, isolated for later upgrading. -/
def Statement2_50_equality (n : Nat) : Prop :=
  ∀ (rho : Real) (f : BooleanFunctionSign n),
    0 < rho → rho < 1 →
      IsUnbiased (signFunctionToReal f) →
        (booleanNoiseStability rho f = rho ↔
          ∃ i : Fin n,
            f = dictatorFunction i ∨ f = negatedDictatorFunction i)

/-- Proposition 2.51, derivative interpretation of noise stability. -/
def Statement2_51 (n : Nat) : Prop :=
  ∀ f : RealValuedBooleanFunction n,
    deriv (fun rho : Real => noiseStability rho f) 0 =
        fourierWeightAtDegree f 1 ∧
      deriv (fun rho : Real => noiseStability rho f) 1 =
        totalInfluence f

/-- Fourier-side expression from Fact 2.53. -/
noncomputable def stableTotalInfluenceByDegree {n : Nat}
    (rho : Real) (f : RealValuedBooleanFunction n) : Real :=
  (Finset.range (n + 1)).sum
    (fun k => (k : Real) * rho ^ (k - 1) * fourierWeightAtDegree f k)

/-- Fact 2.53, Fourier-set form of total stable influence. -/
theorem fact_2_53_fourier {n : Nat}
    (rho : Real) (f : RealValuedBooleanFunction n) :
    stableTotalInfluence rho f =
      Finset.univ.sum (fun S : CoordinateSet n =>
        (S.card : Real) * rho ^ (S.card - 1) *
          functionFourierCoeff f S ^ 2) := by
  classical
  unfold stableTotalInfluence stableInfluence
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _hS
  rw [sum_if_mem_eq_card_mul]
  ring

/-- Fact 2.53, level-weight form of total stable influence. -/
theorem fact_2_53_level {n : Nat}
    (rho : Real) (f : RealValuedBooleanFunction n) :
    stableTotalInfluence rho f =
      stableTotalInfluenceByDegree rho f := by
  classical
  rw [fact_2_53_fourier]
  unfold stableTotalInfluenceByDegree fourierWeightAtDegree fourierWeight
  symm
  calc
    (Finset.range (n + 1)).sum
        (fun k =>
          (k : Real) * rho ^ (k - 1) *
            Finset.univ.sum (fun S : CoordinateSet n =>
              if S.card = k then functionFourierCoeff f S ^ 2 else 0))
        =
        (Finset.range (n + 1)).sum
          (fun k =>
            Finset.univ.sum (fun S : CoordinateSet n =>
              (k : Real) * rho ^ (k - 1) *
                (if S.card = k then functionFourierCoeff f S ^ 2 else 0))) := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.mul_sum]
    _ =
        Finset.univ.sum
          (fun S : CoordinateSet n =>
            (Finset.range (n + 1)).sum
              (fun k =>
                (k : Real) * rho ^ (k - 1) *
                  (if S.card = k then functionFourierCoeff f S ^ 2 else 0))) := by
      rw [Finset.sum_comm]
    _ =
        Finset.univ.sum (fun S : CoordinateSet n =>
          (S.card : Real) * rho ^ (S.card - 1) *
            functionFourierCoeff f S ^ 2) := by
      apply Finset.sum_congr rfl
      intro S _hS
      have hcard_le : S.card ≤ n := by
        simpa using (Finset.card_le_univ S)
      have hmem : S.card ∈ Finset.range (n + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le hcard_le)
      calc
        (Finset.range (n + 1)).sum
            (fun k =>
              (k : Real) * rho ^ (k - 1) *
                (if S.card = k then functionFourierCoeff f S ^ 2 else 0))
            =
            (S.card : Real) * rho ^ (S.card - 1) *
              (if S.card = S.card then functionFourierCoeff f S ^ 2 else 0) := by
          apply Finset.sum_eq_single S.card
          · intro k _hk hne
            have hneq : S.card ≠ k := by
              intro h
              exact hne h.symm
            simp [hneq]
          · intro hnot
            exact (hnot hmem).elim
        _ =
            (S.card : Real) * rho ^ (S.card - 1) *
              functionFourierCoeff f S ^ 2 := by
          simp

/-- Fact 2.53: the remaining derivative identity. -/
def Statement2_53_derivative (n : Nat) : Prop :=
  ∀ (rho : Real) (f : RealValuedBooleanFunction n),
    stableTotalInfluence rho f =
        deriv (fun r : Real => noiseStability r f) rho

/-- Proposition 2.54: only boundedly many coordinates are stably influential. -/
def Statement2_54 (n : Nat) : Prop :=
  ∀ (f : RealValuedBooleanFunction n) (delta epsilon : Real),
    cubeVariance f ≤ 1 →
      0 < delta → delta ≤ 1 →
        0 < epsilon → epsilon ≤ 1 →
          ((stableInfluentialCoordinates delta epsilon f).card : Real) ≤
            1 / (delta * epsilon)

end BooleanFunctions
