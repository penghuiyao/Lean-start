import InformationTheory.Kraft
import InformationTheory.Inequalities
import InformationTheory.thm_entropy

/-!
# Section 5.3: Optimal Codes

This file formalizes Cover and Thomas, Theorem 5.3.1: the expected length of
any instantaneous `D`-ary code is at least the entropy measured in base `D`,
with equality exactly when `p(x) = D^{-l(x)}` for every source symbol.
-/

open scoped BigOperators

namespace InformationTheory

universe u

variable {alpha : Type u}

namespace SourceCode

/-!
## OPTIMAL CODES
-/

/-- The Kraft weight `D^{-l(x)}` attached to a codeword. -/
private noncomputable def kraftWeight {D : Nat}
    (C : SourceCode alpha (DaryAlphabet D)) (x : alpha) : Real :=
  (1 / (D : Real)) ^ C.length x

private theorem kraftWeight_sum_eq_kraftSum [Fintype alpha] {D : Nat}
    (C : SourceCode alpha (DaryAlphabet D)) :
    Finset.univ.sum (fun x : alpha => kraftWeight C x) = C.kraftSum := by
  simp [kraftWeight, SourceCode.kraftSum, SourceCode.length, DaryAlphabet]

private theorem kraftWeight_nonneg {D : Nat}
    (C : SourceCode alpha (DaryAlphabet D)) (x : alpha) :
    0 <= kraftWeight C x := by
  unfold kraftWeight
  positivity

private theorem kraftWeight_pos {D : Nat} (hD : 1 < D)
    (C : SourceCode alpha (DaryAlphabet D)) (x : alpha) :
    0 < kraftWeight C x := by
  unfold kraftWeight
  have hDposNat : 0 < D := lt_trans Nat.zero_lt_one hD
  have hDpos : 0 < (D : Real) := by exact_mod_cast hDposNat
  exact pow_pos (one_div_pos.mpr hDpos) _

private theorem kraftWeight_ne_zero {D : Nat} (hD : 1 < D)
    (C : SourceCode alpha (DaryAlphabet D)) (x : alpha) :
    kraftWeight C x ≠ 0 := by
  exact (kraftWeight_pos hD C x).ne'

private theorem exists_prob_ne_zero [Fintype alpha] (P : PMF alpha) :
    ∃ x : alpha, P.prob x ≠ 0 := by
  by_contra h
  have hzero : Finset.univ.sum (fun x : alpha => P.prob x) = 0 := by
    exact Finset.sum_eq_zero fun x _ => by
      by_contra hx
      exact h ⟨x, hx⟩
  have hone : (1 : Real) = 0 := by
    rw [<- P.sum_eq_one, hzero]
  norm_num at hone

private theorem kraftWeight_sum_pos [Fintype alpha] {D : Nat} (hD : 1 < D)
    (P : PMF alpha) (C : SourceCode alpha (DaryAlphabet D)) :
    0 < Finset.univ.sum (fun x : alpha => kraftWeight C x) := by
  rcases exists_prob_ne_zero P with ⟨x, _⟩
  have hle :
      kraftWeight C x <= Finset.univ.sum (fun y : alpha => kraftWeight C y) :=
    Finset.single_le_sum
      (fun y _ => kraftWeight_nonneg C y) (Finset.mem_univ x)
  exact lt_of_lt_of_le (kraftWeight_pos hD C x) hle

private theorem relativeEntropyTerm_one_nonneg_of_nonneg_le_one
    {q : Real} (hq0 : 0 <= q) (hq1 : q <= 1) :
    0 <= relativeEntropyTermWithBase 2 1 q := by
  by_cases hq : q = 0
  · subst q
    simp [relativeEntropyTermWithBase, logBase]
  · have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hq)
    have hqinv : 1 <= q⁻¹ := (one_le_inv₀ hqpos).mpr hq1
    have hlog : 0 <= logBase 2 q⁻¹ :=
      Real.logb_nonneg (by norm_num : (1 : Real) < 2) hqinv
    simpa [relativeEntropyTermWithBase, logBase, one_div, hq] using hlog

private theorem relativeEntropyTerm_one_eq_zero_of_pos
    {q : Real} (hqpos : 0 < q)
    (hzero : relativeEntropyTermWithBase 2 1 q = 0) :
    q = 1 := by
  have hlog : Real.logb 2 q⁻¹ = 0 := by
    simpa [relativeEntropyTermWithBase, logBase, one_div] using hzero
  have hinvpos : 0 < q⁻¹ := inv_pos.mpr hqpos
  have hinv_eq : q⁻¹ = 1 :=
    Real.eq_one_of_pos_of_logb_eq_zero
      (by norm_num : (1 : Real) < 2) hinvpos hlog
  exact inv_eq_one.mp hinv_eq

private theorem relativeEntropyFromMass_kraftWeight_nonneg [Fintype alpha]
    {D : Nat} (hD : 1 < D) (P : PMF alpha)
    (C : SourceCode alpha (DaryAlphabet D)) (hK : C.kraftSum <= 1) :
    0 <= relativeEntropyFromMass P.prob (kraftWeight C) := by
  have hlogsum :=
    theorem_2_7_1_logSumInequality
      (a := P.prob) (b := kraftWeight C)
      P.nonneg
      (fun x => kraftWeight_nonneg C x)
      (fun x _ => kraftWeight_ne_zero hD C x)
  have hweight_sum_nonneg :
      0 <= Finset.univ.sum (fun x : alpha => kraftWeight C x) :=
    Finset.sum_nonneg fun x _ => kraftWeight_nonneg C x
  have hweight_sum_le_one :
      Finset.univ.sum (fun x : alpha => kraftWeight C x) <= 1 := by
    rw [kraftWeight_sum_eq_kraftSum]
    exact hK
  have hleft :
      0 <= relativeEntropyTermWithBase 2
        (Finset.univ.sum fun x : alpha => P.prob x)
        (Finset.univ.sum fun x : alpha => kraftWeight C x) := by
    rw [P.sum_eq_one]
    exact relativeEntropyTerm_one_nonneg_of_nonneg_le_one
      hweight_sum_nonneg hweight_sum_le_one
  exact le_trans hleft hlogsum

private theorem logBase_two_kraftWeight {D : Nat} (hD : 1 < D)
    (C : SourceCode alpha (DaryAlphabet D)) (x : alpha) :
    logBase 2 (kraftWeight C x) =
      -((C.length x : Real) * logBase 2 (D : Real)) := by
  have hDposNat : 0 < D := lt_trans Nat.zero_lt_one hD
  have hDpos : 0 < (D : Real) := by exact_mod_cast hDposNat
  calc
    logBase 2 (kraftWeight C x) =
        (C.length x : Real) * logBase 2 ((1 : Real) / D) := by
          simp [kraftWeight, logBase, Real.logb_pow]
    _ = (C.length x : Real) * (-logBase 2 (D : Real)) := by
          simp [one_div, logBase, Real.logb_inv]
    _ = -((C.length x : Real) * logBase 2 (D : Real)) := by
          ring

private theorem relativeEntropyTerm_kraftWeight_eq {D : Nat} (hD : 1 < D)
    (C : SourceCode alpha (DaryAlphabet D)) (x : alpha) (p : Real)
    (hp : 0 <= p) :
    relativeEntropyTermWithBase 2 p (kraftWeight C x) =
      logBase 2 (D : Real) * (p * (C.length x : Real)) -
        entropyTermWithBase 2 p := by
  by_cases hp0 : p = 0
  · subst p
    simp [relativeEntropyTermWithBase, entropyTermWithBase]
  · have hq0 : kraftWeight C x ≠ 0 := kraftWeight_ne_zero hD C x
    unfold relativeEntropyTermWithBase entropyTermWithBase
    simp [hp0]
    rw [Real.logb_div hp0 hq0]
    have hlogq :
        Real.logb 2 (kraftWeight C x) =
          -((C.length x : Real) * Real.logb 2 (D : Real)) := by
      simpa [logBase] using logBase_two_kraftWeight hD C x
    rw [hlogq]
    ring

private theorem relativeEntropyFromMass_kraftWeight_eq [Fintype alpha]
    {D : Nat} (hD : 1 < D) (P : PMF alpha)
    (C : SourceCode alpha (DaryAlphabet D)) :
    relativeEntropyFromMass P.prob (kraftWeight C) =
      logBase 2 (D : Real) * C.expectedLength P - entropy P := by
  unfold relativeEntropyFromMass relativeEntropyFromMassWithBase
    SourceCode.expectedLength entropy entropyWithBase
  calc
    Finset.univ.sum
        (fun x : alpha =>
          relativeEntropyTermWithBase 2 (P.prob x) (kraftWeight C x)) =
        Finset.univ.sum
          (fun x : alpha =>
            logBase 2 (D : Real) * (P.prob x * (C.length x : Real)) -
              entropyTermWithBase 2 (P.prob x)) := by
          exact Finset.sum_congr rfl fun x _ =>
            relativeEntropyTerm_kraftWeight_eq hD C x (P.prob x) (P.nonneg x)
    _ =
        logBase 2 (D : Real) *
            Finset.univ.sum (fun x : alpha => P.prob x * (C.length x : Real)) -
          Finset.univ.sum (fun x : alpha => entropyTermWithBase 2 (P.prob x)) := by
          rw [Finset.sum_sub_distrib, <- Finset.mul_sum]

/--
Theorem 5.3.1.  For every instantaneous `D`-ary code with nonempty codewords,
the expected length is bounded below by the source entropy in base `D`.
-/
theorem theorem_5_3_1_optimalCode_lower_bound [Fintype alpha]
    {D : Nat} (hD : 1 < D) (P : PMF alpha)
    (C : SourceCode alpha (DaryAlphabet D)) (hprefix : C.IsInstantaneous)
    (hnonempty : forall x, C x ≠ []) :
    entropyWithBase (D : Real) P <= C.expectedLength P := by
  letI : Nonempty (DaryAlphabet D) :=
    ⟨⟨0, lt_trans Nat.zero_lt_one hD⟩⟩
  have hK : C.kraftSum <= 1 :=
    theorem_5_2_1_kraft_inequality C hprefix hnonempty
  have hrel_nonneg :
      0 <= relativeEntropyFromMass P.prob (kraftWeight C) :=
    relativeEntropyFromMass_kraftWeight_nonneg hD P C hK
  rw [relativeEntropyFromMass_kraftWeight_eq hD P C] at hrel_nonneg
  have hDreal : (1 : Real) < (D : Real) := by exact_mod_cast hD
  have hlogDpos : 0 < logBase 2 (D : Real) :=
    Real.logb_pos (by norm_num : (1 : Real) < 2) hDreal
  have hH2_le :
      entropy P <= logBase 2 (D : Real) * C.expectedLength P := by
    linarith
  have hchange :
      entropy P = logBase 2 (D : Real) * entropyWithBase (D : Real) P := by
    simpa [entropy] using
      (entropyWithBase_change_base
        (a := (D : Real)) (b := 2) hDreal P)
  rw [hchange] at hH2_le
  nlinarith

/-- Equality case in Theorem 5.3.1. -/
theorem theorem_5_3_1_optimalCode_equality_iff [Fintype alpha]
    {D : Nat} (hD : 1 < D) (P : PMF alpha)
    (C : SourceCode alpha (DaryAlphabet D)) (hprefix : C.IsInstantaneous)
    (hnonempty : forall x, C x ≠ []) :
    C.expectedLength P = entropyWithBase (D : Real) P ↔
      forall x, P.prob x = (1 / (D : Real)) ^ C.length x := by
  letI : Nonempty (DaryAlphabet D) :=
    ⟨⟨0, lt_trans Nat.zero_lt_one hD⟩⟩
  have hDreal : (1 : Real) < (D : Real) := by exact_mod_cast hD
  have hlogDpos : 0 < logBase 2 (D : Real) :=
    Real.logb_pos (by norm_num : (1 : Real) < 2) hDreal
  constructor
  · intro hL
    have hK : C.kraftSum <= 1 :=
      theorem_5_2_1_kraft_inequality C hprefix hnonempty
    have hrel_eq :
        relativeEntropyFromMass P.prob (kraftWeight C) = 0 := by
      rw [relativeEntropyFromMass_kraftWeight_eq hD P C]
      have hchange :
          entropy P = logBase 2 (D : Real) * entropyWithBase (D : Real) P := by
        simpa [entropy] using
          (entropyWithBase_change_base
            (a := (D : Real)) (b := 2) hDreal P)
      rw [hchange, hL]
      ring
    have hlogsum :=
      theorem_2_7_1_logSumInequality
        (a := P.prob) (b := kraftWeight C)
        P.nonneg
        (fun x => kraftWeight_nonneg C x)
        (fun x _ => kraftWeight_ne_zero hD C x)
    have hweight_sum_nonneg :
        0 <= Finset.univ.sum (fun x : alpha => kraftWeight C x) :=
      Finset.sum_nonneg fun x _ => kraftWeight_nonneg C x
    have hweight_sum_le_one :
        Finset.univ.sum (fun x : alpha => kraftWeight C x) <= 1 := by
      rw [kraftWeight_sum_eq_kraftSum]
      exact hK
    have hleft_nonneg :
        0 <= relativeEntropyTermWithBase 2
          (Finset.univ.sum fun x : alpha => P.prob x)
          (Finset.univ.sum fun x : alpha => kraftWeight C x) := by
      rw [P.sum_eq_one]
      exact relativeEntropyTerm_one_nonneg_of_nonneg_le_one
        hweight_sum_nonneg hweight_sum_le_one
    have hleft_le_zero :
        relativeEntropyTermWithBase 2
          (Finset.univ.sum fun x : alpha => P.prob x)
          (Finset.univ.sum fun x : alpha => kraftWeight C x) <= 0 := by
      simpa [hrel_eq] using hlogsum
    have hleft_zero :
        relativeEntropyTermWithBase 2
          (Finset.univ.sum fun x : alpha => P.prob x)
          (Finset.univ.sum fun x : alpha => kraftWeight C x) = 0 :=
      le_antisymm hleft_le_zero hleft_nonneg
    have hweight_sum_eq_one :
        Finset.univ.sum (fun x : alpha => kraftWeight C x) = 1 := by
      have hterm :
          relativeEntropyTermWithBase 2 1
            (Finset.univ.sum fun x : alpha => kraftWeight C x) = 0 := by
        simpa [P.sum_eq_one] using hleft_zero
      exact relativeEntropyTerm_one_eq_zero_of_pos
        (kraftWeight_sum_pos hD P C) hterm
    have hprob :=
      (relativeEntropyFromMass_eq_zero_iff
        (p := P.prob) (q := kraftWeight C)
        P.nonneg
        (fun x => kraftWeight_nonneg C x)
        P.sum_eq_one
        hweight_sum_eq_one
        (fun x _ => kraftWeight_ne_zero hD C x)).mp hrel_eq
    intro x
    simpa [kraftWeight] using hprob x
  · intro hprob
    have hprob' : forall x, P.prob x = kraftWeight C x := by
      intro x
      simpa [kraftWeight] using hprob x
    have hrel_eq :
        relativeEntropyFromMass P.prob (kraftWeight C) = 0 := by
      unfold relativeEntropyFromMass relativeEntropyFromMassWithBase
      exact Finset.sum_eq_zero fun x _ => by
        unfold relativeEntropyTermWithBase
        by_cases hp0 : P.prob x = 0
        · simp [hp0]
        · have hratio : P.prob x / kraftWeight C x = 1 := by
            rw [hprob' x]
            exact div_self (kraftWeight_ne_zero hD C x)
          simp [hp0, hratio, logBase]
    rw [relativeEntropyFromMass_kraftWeight_eq hD P C] at hrel_eq
    have hchange :
        entropy P = logBase 2 (D : Real) * entropyWithBase (D : Real) P := by
      simpa [entropy] using
        (entropyWithBase_change_base
          (a := (D : Real)) (b := 2) hDreal P)
    rw [hchange] at hrel_eq
    nlinarith

/--
Theorem 5.3.1, bundled statement: lower bound plus equality characterization.
-/
theorem theorem_5_3_1_optimalCode [Fintype alpha]
    {D : Nat} (hD : 1 < D) (P : PMF alpha)
    (C : SourceCode alpha (DaryAlphabet D)) (hprefix : C.IsInstantaneous)
    (hnonempty : forall x, C x ≠ []) :
    entropyWithBase (D : Real) P <= C.expectedLength P ∧
      (C.expectedLength P = entropyWithBase (D : Real) P ↔
        forall x, P.prob x = (1 / (D : Real)) ^ C.length x) := by
  exact ⟨
    theorem_5_3_1_optimalCode_lower_bound hD P C hprefix hnonempty,
    theorem_5_3_1_optimalCode_equality_iff hD P C hprefix hnonempty⟩

end SourceCode

end InformationTheory
