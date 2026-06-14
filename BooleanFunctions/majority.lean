import BooleanFunctions.«sorry»
import BooleanFunctions.«Thm Inf Core»
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Fintype.Powerset
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Tactic.Linarith

/-!
# Majority: O'Donnell, Exercise 2.22

This file records the Lean formalization strategy for Exercise 2.22 and proves
the combinatorial odd-dimensional influence formula.  Analytic consequences
which are being deferred to Stirling or longer boundary counting arguments are
imported from `BooleanFunctions/sorry.lean`.

The exercise studies the influence of the majority function.  The recommended
Lean route is to work first with odd dimensions written as `2 * m + 1`, rather
than with an arbitrary `n` plus a proof of `Odd n`.  This keeps the binomial
coefficient and parity algebra much lighter.

## Main target statements

For `m : Nat`, set `n = 2 * m + 1`.  The first exact theorem should be:

```lean
theorem majority_influence_odd
    (m : Nat) (i : Fin (2 * m + 1)) :
    influence
        (signFunctionToReal
          (majorityFunction : BooleanFunctionSign (2 * m + 1))) i =
      (Nat.centralBinom m : Real) / (4 : Real) ^ m := by
  ...
```

This is Exercise 2.22(a), since
`Nat.centralBinom m = Nat.choose (2 * m) m`, and
`2 * m = n - 1`, `m = (n - 1) / 2`.

After that, prove:

```lean
theorem majority_influence_odd_antitone :
    Antitone fun m : Nat =>
      (Nat.centralBinom m : Real) / (4 : Real) ^ m := ...
```

or, more concretely, the strict step inequality for `m`:

```lean
lemma majority_influence_ratio_lt_one (m : Nat) :
    ((Nat.centralBinom (m + 1) : Real) / (4 : Real) ^ (m + 1)) <
      ((Nat.centralBinom m : Real) / (4 : Real) ^ m) := ...
```

This is Exercise 2.22(b).

For the asymptotic part, first prove the central-binomial version:

```lean
theorem centralBinom_div_four_pow_asymptotic :
    (fun m : Nat => (Nat.centralBinom m : Real) / (4 : Real) ^ m)
      ~[Filter.atTop]
    (fun m : Nat => 1 / Real.sqrt (Real.pi * (m : Real))) := ...
```

Then compose with the odd-dimension parametrization `n = 2 * m + 1`.
The stronger book statement with `O(n ^ (-3 / 2))` should be a later target;
plain Stirling equivalence gives the main term, but not automatically that
sharper error bound.

## Phase 1: combinatorial infrastructure

Add small helper definitions near the majority work, or move them later to
`BasicFunctions.lean` if they become generally useful:

```lean
def positiveCoordSet {n : Nat} (x : SignCube n) : Finset (Fin n) :=
  Finset.univ.filter fun i => x i = SignBit.posOne

def positiveCoordCount {n : Nat} (x : SignCube n) : Nat :=
  (positiveCoordSet x).card

def positiveCoordCountOn {n : Nat}
    (s : Finset (Fin n)) (x : SignCube n) : Nat :=
  (s.filter fun i => x i = SignBit.posOne).card
```

Useful lemmas:

* `positiveCoordCountOn_univ`
* `positiveCoordCountOn_erase`
* `card_univ_erase_fin`
* `signCubeSumInt_eq_posCount`
* `signCubeSumInt_setCoord_pos`
* `signCubeSumInt_setCoord_neg`

The key arithmetic lemma should say that for `n = 2 * m + 1`, coordinate `i`
is pivotal for majority exactly when the other `2 * m` coordinates split
evenly:

```lean
lemma majority_pivotal_iff_other_tie
    (m : Nat) (i : Fin (2 * m + 1)) (x : SignCube (2 * m + 1)) :
    IsPivotal
        (majorityFunction : BooleanFunctionSign (2 * m + 1)) i x
      ↔
    positiveCoordCountOn (Finset.univ.erase i) x = m := ...
```

Prove this by comparing the two sums
`signCubeSumInt (setCoordSign x i SignBit.posOne)` and
`signCubeSumInt (setCoordSign x i SignBit.negOne)`.

## Phase 2: counting the tie layer

Count assignments of the other coordinates with exactly `m` positives.

There are two good Lean approaches:

1. Work with the subtype `{j : Fin (2 * m + 1) // j != i}`.
   This makes the set of remaining coordinates a finite type of cardinality
   `2 * m`.

2. Work directly with `Finset.univ.erase i`.
   This avoids subtype equivalences, but requires more `Finset.card_filter`
   lemmas.

The target counting lemma:

```lean
lemma card_other_tie
    (m : Nat) (i : Fin (2 * m + 1)) :
    (Finset.univ.filter fun x : SignCube (2 * m + 1) =>
      positiveCoordCountOn (Finset.univ.erase i) x = m).card =
    2 * Nat.centralBinom m := ...
```

The factor `2` appears because the pivotal condition does not depend on the
value of coordinate `i` itself.

Then use:

```lean
Fintype.card (SignCube (2 * m + 1)) = 2 ^ (2 * m + 1)
```

and simplify:

```lean
(2 * Nat.centralBinom m : Real) / (2 : Real) ^ (2 * m + 1)
  =
(Nat.centralBinom m : Real) / (4 : Real) ^ m
```

This finishes Exercise 2.22(a).

## Phase 3: monotonicity in odd `n`

Use the existing mathlib recurrence:

```lean
Nat.succ_mul_centralBinom_succ
```

which states, morally,

```text
(m + 1) * centralBinom (m + 1)
  = 2 * (2 * m + 1) * centralBinom m.
```

After casting to `Real`, prove:

```text
a (m + 1) / a m = (2 * m + 1) / (2 * m + 2) < 1,
where a m = centralBinom m / 4^m.
```

The Lean proof should use:

* positivity of `centralBinom`
* `field_simp` for nonzero denominators
* `nlinarith` for the final inequality

This gives Exercise 2.22(b).

## Phase 4: Stirling and the main asymptotic

Start from:

```lean
Stirling.factorial_isEquivalent_stirling
```

and the identity:

```text
centralBinom m = (2 * m)! / (m! * m!)
```

The desired first asymptotic target is:

```text
centralBinom m / 4^m ~ 1 / sqrt(pi * m).
```

Then reparameterize from `m` to odd `n = 2 * m + 1` using:

```lean
IsEquivalent.comp_tendsto
StrictMono.tendsto_atTop
```

This proves the main term:

```text
Inf_1[Maj_n] ~ sqrt(2 / pi) / sqrt(n).
```

The sharper book statement

```text
Inf_1[Maj_n] = sqrt(2 / pi) / sqrt(n) + O(n^(-3/2))
```

requires a controlled-error version of Stirling, not just asymptotic
equivalence.  It should be its own later theorem.

## Phase 5: Fourier weight and total influence

Once `majority_influence_odd` is available, use symmetry to sum over all
coordinates:

```lean
theorem majority_totalInfluence_odd (m : Nat) :
    totalInfluence
        (signFunctionToReal
          (majorityFunction : BooleanFunctionSign (2 * m + 1))) =
      ((2 * m + 1 : Nat) : Real) *
        ((Nat.centralBinom m : Real) / (4 : Real) ^ m) := ...
```

For the degree-one Fourier weight, first prove majority is monotone, then use
the already formalized Proposition 2.21:

```lean
proposition_2_21
```

to rewrite first-level Fourier coefficients as influences.  The expected exact
formula is:

```text
W1[Maj_(2m+1)] = (2m+1) * (centralBinom m / 4^m)^2.
```

Its limit should then be `2 / pi`, using the asymptotic from Phase 4.

## Phase 6: even `n`

For Exercise 2.22(f), do not use only the project's `majorityFunction`, because
the book allows any even-`n` majority rule with arbitrary tie-breaking.

Use the predicate:

```lean
IsMajorityFunction
```

and prove that only tie-layer edges contribute.  The exact target should be:

```text
I[f] = I[Maj_(n-1)]
```

for even `n`, where `f` is any majority function on `n` bits.

The proof is again a counting proof:

* non-tie inputs cannot change winner when one coordinate flips unless the
  remaining coordinates are exactly tied;
* every tie assignment contributes exactly `n / 2` boundary edges;
* simplify the resulting binomial expression to the odd case `n - 1`.

This phase should come after the odd case, since it reuses most of the same
tie-layer counting infrastructure.
-/

namespace BooleanFunctions

/-! ## Formalization of Exercise 2.22(a) -/

/-- The set of coordinates on which a cube point is `+1`. -/
def positiveCoordSet {n : Nat} (x : SignCube n) : Finset (Fin n) :=
  Finset.univ.filter fun i => x i = SignBit.posOne

/-- The number of `+1` coordinates after ignoring coordinate `i`. -/
def positiveCoordCountOff {n : Nat} (i : Fin n) (x : SignCube n) : Nat :=
  ((positiveCoordSet x).erase i).card

@[simp]
lemma mem_positiveCoordSet {n : Nat} (x : SignCube n) (i : Fin n) :
    i ∈ positiveCoordSet x ↔ x i = SignBit.posOne := by
  simp [positiveCoordSet]

/--
The sign cube is equivalent to the finite set of coordinates on which the
point is `+1`.
-/
def signCubeEquivFinset (n : Nat) : SignCube n ≃ Finset (Fin n) where
  toFun := positiveCoordSet
  invFun := fun S i => if i ∈ S then SignBit.posOne else SignBit.negOne
  left_inv := by
    intro x
    funext i
    cases hxi : x i <;> simp [positiveCoordSet, hxi]
  right_inv := by
    intro S
    ext i
    simp [positiveCoordSet]

lemma not_mem_of_mem_univ_erase {α : Type} [DecidableEq α] [Fintype α]
    {i j : α} (h : j ∈ (Finset.univ.erase i : Finset α)) : j ≠ i := by
  simpa using (Finset.mem_erase.mp h).1

lemma not_mem_of_subset_univ_erase {α : Type} [DecidableEq α] [Fintype α]
    {i : α} {S : Finset α} (hS : S ⊆ Finset.univ.erase i) :
    i ∉ S := by
  intro hi
  exact (not_mem_of_mem_univ_erase (hS hi)) rfl

/--
Subsets whose erase at `i` has size `m` are two copies of the `m`-subsets of
the remaining coordinates: one copy without `i`, and one copy with `i`.
-/
def eraseCardEquivBoolPowersetCard {α : Type} [DecidableEq α] [Fintype α]
    (i : α) (m : Nat) :
    {S : Finset α // (S.erase i).card = m} ≃
      Bool × {T : Finset α // T ⊆ Finset.univ.erase i ∧ T.card = m} where
  toFun S :=
    (if i ∈ S.1 then true else false,
      ⟨S.1.erase i,
        by
          refine ⟨?_, S.2⟩
          intro j hj
          simp only [Finset.mem_erase, Finset.mem_univ] at hj ⊢
          exact ⟨hj.1, trivial⟩⟩)
  invFun p :=
    ⟨if p.1 then insert i p.2.1 else p.2.1, by
      have hsub : p.2.1 ⊆ Finset.univ.erase i := p.2.2.1
      have hcard : p.2.1.card = m := p.2.2.2
      have hi_not : i ∉ p.2.1 :=
        not_mem_of_subset_univ_erase hsub
      cases p.1
      · simpa [hi_not] using hcard
      · simpa [hi_not] using hcard⟩
  left_inv := by
    intro S
    ext j
    by_cases hiS : i ∈ S.1
    · simp [hiS, Finset.insert_erase hiS]
    · simp [hiS]
  right_inv := by
    rintro ⟨b, T⟩
    have hsub : T.1 ⊆ Finset.univ.erase i := T.2.1
    have hi_not : i ∉ T.1 :=
      not_mem_of_subset_univ_erase hsub
    cases b
    · ext <;> simp [hi_not]
    · ext <;> simp [hi_not]

lemma card_eraseCard_subtype_fin_odd (m : Nat) (i : Fin (2 * m + 1)) :
    Fintype.card
        {S : Finset (Fin (2 * m + 1)) // (S.erase i).card = m} =
      2 * Nat.centralBinom m := by
  classical
  let rest : Finset (Fin (2 * m + 1)) := Finset.univ.erase i
  have hrest_card : rest.card = 2 * m := by
    simp [rest]
  calc
    Fintype.card
        {S : Finset (Fin (2 * m + 1)) // (S.erase i).card = m}
        =
        Fintype.card
          (Bool × {T : Finset (Fin (2 * m + 1)) //
            T ⊆ Finset.univ.erase i ∧ T.card = m}) := by
      exact Fintype.card_congr (eraseCardEquivBoolPowersetCard i m)
    _ =
        2 *
          ((Finset.univ.erase i : Finset (Fin (2 * m + 1))).powersetCard m).card := by
      have hsubtype :
          Fintype.card
              {T : Finset (Fin (2 * m + 1)) //
                T ⊆ Finset.univ.erase i ∧ T.card = m} =
            ((Finset.univ.erase i : Finset (Fin (2 * m + 1))).powersetCard m).card := by
        rw [Fintype.card_subtype]
        congr 1
        ext T
        simp [Finset.mem_powersetCard]
      rw [Fintype.card_prod, Fintype.card_bool, hsubtype]
    _ = 2 * Nat.centralBinom m := by
      rw [Finset.card_powersetCard]
      simp [Nat.centralBinom, hrest_card, rest]

lemma card_positiveCoordCountOff_eq_middle (m : Nat)
    (i : Fin (2 * m + 1)) :
    (Finset.univ.filter
        (fun x : SignCube (2 * m + 1) => positiveCoordCountOff i x = m)).card =
      2 * Nat.centralBinom m := by
  classical
  let e :
      {x : SignCube (2 * m + 1) // positiveCoordCountOff i x = m} ≃
        {S : Finset (Fin (2 * m + 1)) // (S.erase i).card = m} :=
    (signCubeEquivFinset (2 * m + 1)).subtypeEquiv (by
      intro x
      rfl)
  calc
    (Finset.univ.filter
        (fun x : SignCube (2 * m + 1) => positiveCoordCountOff i x = m)).card =
        Fintype.card
          {x : SignCube (2 * m + 1) // positiveCoordCountOff i x = m} := by
      rw [Fintype.card_subtype]
    _ = Fintype.card
        {S : Finset (Fin (2 * m + 1)) // (S.erase i).card = m} := by
      exact Fintype.card_congr e
    _ = 2 * Nat.centralBinom m := by
      exact card_eraseCard_subtype_fin_odd m i

/-- A sign bit is `-1` if it is not `+1`. -/
lemma SignBit.eq_negOne_of_ne_posOne {b : SignBit}
    (h : b ≠ SignBit.posOne) : b = SignBit.negOne := by
  cases b <;> simp at h ⊢

/-- The integer cube sum is `2 * (# of +1 coordinates) - n`. -/
lemma signCubeSumInt_eq_two_mul_positiveCoordSet_card_sub {n : Nat}
    (x : SignCube n) :
    signCubeSumInt x = (2 * ((positiveCoordSet x).card : Int)) - (n : Int) := by
  classical
  unfold signCubeSumInt positiveCoordSet
  calc
    Finset.univ.sum (fun i : Fin n => (x i).toInt)
        =
        Finset.univ.sum
          (fun i : Fin n =>
            (if x i = SignBit.posOne then (2 : Int) else 0) - 1) := by
      apply Finset.sum_congr rfl
      intro i _hi
      cases x i <;> simp [SignBit.toInt]
    _ =
        Finset.univ.sum
            (fun i : Fin n => if x i = SignBit.posOne then (2 : Int) else 0) -
          Finset.univ.sum (fun _i : Fin n => (1 : Int)) := by
      rw [Finset.sum_sub_distrib]
    _ = (2 * ((Finset.univ.filter
            (fun i : Fin n => x i = SignBit.posOne)).card : Int)) - (n : Int) := by
      rw [Finset.sum_ite]
      simp [Finset.sum_const, mul_comm]

lemma odd_majority_nonneg_iff {m k : Nat} :
    0 ≤ (2 * (k : Int)) - ((2 * m + 1 : Nat) : Int) ↔ m < k := by
  constructor
  · intro h
    by_contra hnot
    have hk_le : k ≤ m := Nat.le_of_not_gt hnot
    have hk_le_int : (k : Int) ≤ m := by exact_mod_cast hk_le
    have hneg : (2 * (k : Int)) - ((2 * m + 1 : Nat) : Int) < 0 := by
      norm_num
      linarith
    exact (not_lt_of_ge h) hneg
  · intro h
    have hm_succ_le : m + 1 ≤ k := Nat.succ_le_of_lt h
    have hm_succ_le_int : ((m + 1 : Nat) : Int) ≤ k := by
      exact_mod_cast hm_succ_le
    norm_num
    linarith

lemma majorityFunction_odd_eq_posOne_iff (m : Nat)
    (x : SignCube (2 * m + 1)) :
    majorityFunction x = SignBit.posOne ↔
      m < (positiveCoordSet x).card := by
  unfold majorityFunction signOfIntWithPositiveTie
  rw [signCubeSumInt_eq_two_mul_positiveCoordSet_card_sub]
  by_cases h :
      0 ≤ (2 * ((positiveCoordSet x).card : Int)) -
        ((2 * m + 1 : Nat) : Int)
  · simp [(odd_majority_nonneg_iff (m := m)
      (k := (positiveCoordSet x).card)).mp h]
  · have hle :
        ¬ m < (positiveCoordSet x).card := by
      intro hm
      exact h ((odd_majority_nonneg_iff (m := m)
        (k := (positiveCoordSet x).card)).mpr hm)
    simp [hle]

@[simp]
lemma positiveCoordSet_setCoordSign_pos {n : Nat}
    (x : SignCube n) (i : Fin n) :
    positiveCoordSet (setCoordSign x i SignBit.posOne) =
      insert i (positiveCoordSet x) := by
  classical
  ext j
  by_cases hji : j = i <;> simp [positiveCoordSet, setCoordSign, hji]

@[simp]
lemma positiveCoordSet_setCoordSign_neg {n : Nat}
    (x : SignCube n) (i : Fin n) :
    positiveCoordSet (setCoordSign x i SignBit.negOne) =
      (positiveCoordSet x).erase i := by
  classical
  ext j
  by_cases hji : j = i <;> simp [positiveCoordSet, setCoordSign, hji]

lemma positiveCoordSet_card_setCoordSign_pos {n : Nat}
    (x : SignCube n) (i : Fin n) :
    (positiveCoordSet (setCoordSign x i SignBit.posOne)).card =
      positiveCoordCountOff i x + 1 := by
  classical
  rw [positiveCoordSet_setCoordSign_pos]
  unfold positiveCoordCountOff
  have hi_not : i ∉ (positiveCoordSet x).erase i := Finset.notMem_erase i (positiveCoordSet x)
  rw [show insert i (positiveCoordSet x) = insert i ((positiveCoordSet x).erase i) by
    ext j
    by_cases hji : j = i <;> simp [hji]]
  simp [hi_not]

lemma positiveCoordSet_card_setCoordSign_neg {n : Nat}
    (x : SignCube n) (i : Fin n) :
    (positiveCoordSet (setCoordSign x i SignBit.negOne)).card =
      positiveCoordCountOff i x := by
  simp [positiveCoordCountOff]

lemma majorityFunction_setCoord_pos_eq_if (m : Nat)
    (i : Fin (2 * m + 1)) (x : SignCube (2 * m + 1)) :
    majorityFunction (setCoordSign x i SignBit.posOne) =
      if m ≤ positiveCoordCountOff i x then SignBit.posOne else SignBit.negOne := by
  classical
  by_cases h : m ≤ positiveCoordCountOff i x
  · have hpos :
        majorityFunction (setCoordSign x i SignBit.posOne) = SignBit.posOne := by
      rw [majorityFunction_odd_eq_posOne_iff]
      rw [positiveCoordSet_card_setCoordSign_pos]
      exact Nat.lt_succ_of_le h
    simp [h, hpos]
  · have hnotpos :
        majorityFunction (setCoordSign x i SignBit.posOne) ≠ SignBit.posOne := by
      intro hpos
      have hm_lt :
          m < (positiveCoordSet (setCoordSign x i SignBit.posOne)).card :=
        (majorityFunction_odd_eq_posOne_iff m
          (setCoordSign x i SignBit.posOne)).mp hpos
      rw [positiveCoordSet_card_setCoordSign_pos] at hm_lt
      exact h (Nat.le_of_lt_succ hm_lt)
    have hneg :
        majorityFunction (setCoordSign x i SignBit.posOne) = SignBit.negOne :=
      SignBit.eq_negOne_of_ne_posOne hnotpos
    simp [h, hneg]

lemma majorityFunction_setCoord_neg_eq_if (m : Nat)
    (i : Fin (2 * m + 1)) (x : SignCube (2 * m + 1)) :
    majorityFunction (setCoordSign x i SignBit.negOne) =
      if m < positiveCoordCountOff i x then SignBit.posOne else SignBit.negOne := by
  classical
  by_cases h : m < positiveCoordCountOff i x
  · have hpos :
        majorityFunction (setCoordSign x i SignBit.negOne) = SignBit.posOne := by
      rw [majorityFunction_odd_eq_posOne_iff]
      rw [positiveCoordSet_card_setCoordSign_neg]
      exact h
    simp [h, hpos]
  · have hnotpos :
        majorityFunction (setCoordSign x i SignBit.negOne) ≠ SignBit.posOne := by
      intro hpos
      have hm_lt :
          m < (positiveCoordSet (setCoordSign x i SignBit.negOne)).card :=
        (majorityFunction_odd_eq_posOne_iff m
          (setCoordSign x i SignBit.negOne)).mp hpos
      rw [positiveCoordSet_card_setCoordSign_neg] at hm_lt
      exact h hm_lt
    have hneg :
        majorityFunction (setCoordSign x i SignBit.negOne) = SignBit.negOne :=
      SignBit.eq_negOne_of_ne_posOne hnotpos
    simp [h, hneg]

lemma pivotal_iff_setCoord_ne {n : Nat}
    (f : BooleanFunctionSign n) (i : Fin n) (x : SignCube n) :
    IsPivotal f i x ↔
      f (setCoordSign x i SignBit.posOne) ≠
        f (setCoordSign x i SignBit.negOne) := by
  classical
  rcases hxi : x i with _ | _
  · have hneg : setCoordSign x i SignBit.negOne = x := by
      rw [← hxi]
      exact setCoordSign_self x i
    simp [IsPivotal, flipCoordSign, negSignBit, hxi, hneg, ne_comm]
  · have hpos : setCoordSign x i SignBit.posOne = x := by
      rw [← hxi]
      exact setCoordSign_self x i
    simp [IsPivotal, flipCoordSign, negSignBit, hxi, hpos]

lemma majority_pivotal_iff_other_tie (m : Nat)
    (i : Fin (2 * m + 1)) (x : SignCube (2 * m + 1)) :
    IsPivotal (majorityFunction : BooleanFunctionSign (2 * m + 1)) i x ↔
      positiveCoordCountOff i x = m := by
  classical
  rw [pivotal_iff_setCoord_ne]
  rw [majorityFunction_setCoord_pos_eq_if m i x]
  rw [majorityFunction_setCoord_neg_eq_if m i x]
  by_cases hEq : positiveCoordCountOff i x = m
  · rw [hEq]
    simp
  · rcases lt_or_gt_of_ne hEq with hlt | hgt
    · have hnotle : ¬ m ≤ positiveCoordCountOff i x := by
        exact Nat.not_le.mpr hlt
      have hnotlt : ¬ m < positiveCoordCountOff i x := by
        exact Nat.not_lt.mpr hlt.le
      simp [hEq, hnotle, hnotlt]
    · have hle : m ≤ positiveCoordCountOff i x := hgt.le
      have hlt' : m < positiveCoordCountOff i x := hgt
      simp [hEq, hle, hlt']

lemma two_pow_two_mul_eq_four_pow (m : Nat) :
    (2 : Real) ^ (2 * m) = (4 : Real) ^ m := by
  induction m with
  | zero =>
      norm_num
  | succ m ih =>
      calc
        (2 : Real) ^ (2 * (m + 1)) =
            (2 : Real) ^ (2 * m + 2) := by
          rw [Nat.mul_succ]
        _ = (2 : Real) ^ (2 * m) * 2 ^ 2 := by
          rw [pow_add]
        _ = (4 : Real) ^ m * 4 := by
          rw [ih]
          norm_num
        _ = (4 : Real) ^ (m + 1) := by
          rw [pow_succ]

lemma two_pow_two_mul_add_one_eq_two_mul_four_pow (m : Nat) :
    (2 : Real) ^ (2 * m + 1) = 2 * (4 : Real) ^ m := by
  calc
    (2 : Real) ^ (2 * m + 1) = (2 : Real) ^ (2 * m) * 2 := by
      rw [pow_succ]
    _ = (4 : Real) ^ m * 2 := by
      rw [two_pow_two_mul_eq_four_pow]
    _ = 2 * (4 : Real) ^ m := by
      rw [mul_comm ((4 : Real) ^ m) (2 : Real)]

/--
Exercise 2.22(a), in the odd-dimensional form `n = 2 * m + 1`.

Every coordinate has influence equal to the probability that the other
`2 * m` coordinates split evenly.
-/
theorem exercise_2_22a_majority_influence_odd (m : Nat)
    (i : Fin (2 * m + 1)) :
    influence
        (signFunctionToReal
          (majorityFunction : BooleanFunctionSign (2 * m + 1))) i =
      (Nat.centralBinom m : Real) / (4 : Real) ^ m := by
  classical
  rw [influence_eq_derivativeInfluence
    (signFunctionToReal
      (majorityFunction : BooleanFunctionSign (2 * m + 1))) i]
  unfold derivativeInfluence cubeExpectation
  have hsum :
      Finset.univ.sum
          (fun x : SignCube (2 * m + 1) =>
            discreteDerivative
                (signFunctionToReal
                  (majorityFunction : BooleanFunctionSign (2 * m + 1))) i x ^ 2) =
        (2 : Real) * (Nat.centralBinom m : Real) := by
    calc
      Finset.univ.sum
          (fun x : SignCube (2 * m + 1) =>
            discreteDerivative
                (signFunctionToReal
                  (majorityFunction : BooleanFunctionSign (2 * m + 1))) i x ^ 2)
          =
          Finset.univ.sum
            (fun x : SignCube (2 * m + 1) =>
              if IsPivotal
                  (majorityFunction : BooleanFunctionSign (2 * m + 1)) i x then
                (1 : Real)
              else
                0) := by
        apply Finset.sum_congr rfl
        intro x _hx
        rw [signFunction_discreteDerivative_sq_eq_pivotalIndicator]
      _ =
          ((Finset.univ.filter
            (fun x : SignCube (2 * m + 1) =>
              IsPivotal
                (majorityFunction : BooleanFunctionSign (2 * m + 1)) i x)).card :
            Real) := by
        rw [finset_sum_indicator_eq_card_filter]
      _ =
          ((Finset.univ.filter
            (fun x : SignCube (2 * m + 1) => positiveCoordCountOff i x = m)).card :
            Real) := by
        have hfilter :
            Finset.univ.filter
                (fun x : SignCube (2 * m + 1) =>
                  IsPivotal
                    (majorityFunction : BooleanFunctionSign (2 * m + 1)) i x) =
              Finset.univ.filter
                (fun x : SignCube (2 * m + 1) =>
                  positiveCoordCountOff i x = m) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact majority_pivotal_iff_other_tie m i x
        rw [hfilter]
      _ = (2 * Nat.centralBinom m : Real) := by
        rw [card_positiveCoordCountOff_eq_middle]
        norm_num
      _ = (2 : Real) * (Nat.centralBinom m : Real) := by
        norm_num
  have hpow :
      (2 : Real) ^ (2 * m + 1) = 2 * (4 : Real) ^ m :=
    two_pow_two_mul_add_one_eq_two_mul_four_pow m
  rw [hsum]
  rw [hpow]
  calc
    (2 * (4 : Real) ^ m)⁻¹ *
          ((2 : Real) * (Nat.centralBinom m : Real)) =
        ((2 : Real) * (Nat.centralBinom m : Real)) *
          ((2 : Real) * (4 : Real) ^ m)⁻¹ := by
      exact mul_comm _ _
    _ = ((2 : Real) * (Nat.centralBinom m : Real)) /
          ((2 : Real) * (4 : Real) ^ m) := by
      exact (div_eq_mul_inv
        ((2 : Real) * (Nat.centralBinom m : Real))
        ((2 : Real) * (4 : Real) ^ m)).symm
    _ = (Nat.centralBinom m : Real) / (4 : Real) ^ m := by
      exact mul_div_mul_left (Nat.centralBinom m : Real) ((4 : Real) ^ m)
        (by norm_num : (2 : Real) ≠ 0)

/-! ## Exercise 2.22, organized by part -/

/-- The first coordinate in the odd cube of dimension `2 * m + 1`. -/
def firstOddCoord (m : Nat) : Fin (2 * m + 1) :=
  ⟨0, by
    simp⟩

/--
Exercise 2.22(a), restated with the scalar formula used by the later parts.
-/
theorem exercise_2_22a_majority_influence_odd_formula (m : Nat)
    (i : Fin (2 * m + 1)) :
    influence
        (signFunctionToReal
          (majorityFunction : BooleanFunctionSign (2 * m + 1))) i =
      majorityInfluenceOddFormula m := by
  simpa [majorityInfluenceOddFormula] using
    exercise_2_22a_majority_influence_odd m i

/--
The central-binomial scalar `centralBinom m / 4^m` strictly decreases from
`m` to `m + 1`.  This is the ratio computation in Exercise 2.22(b).
-/
theorem exercise_2_22b_majorityInfluenceOddFormula_decreasing_step
    (m : Nat) :
    majorityInfluenceOddFormula (m + 1) < majorityInfluenceOddFormula m := by
  have hrec := Nat.succ_mul_centralBinom_succ m
  have hlt_nat :
      Nat.centralBinom (m + 1) < 4 * Nat.centralBinom m := by
    have hcpos : 0 < Nat.centralBinom m := Nat.centralBinom_pos m
    have hmul :
        (m + 1) * Nat.centralBinom (m + 1) <
          (m + 1) * (4 * Nat.centralBinom m) := by
      calc
        (m + 1) * Nat.centralBinom (m + 1)
            = 2 * (2 * m + 1) * Nat.centralBinom m := hrec
        _ < 4 * (m + 1) * Nat.centralBinom m := by
          nlinarith
        _ = (m + 1) * (4 * Nat.centralBinom m) := by
          ring
    exact Nat.lt_of_mul_lt_mul_left hmul
  have hlt_real :
      (Nat.centralBinom (m + 1) : Real) <
        (4 : Real) * (Nat.centralBinom m : Real) := by
    exact_mod_cast hlt_nat
  have hpow_pos : 0 < (4 : Real) ^ m := pow_pos (by norm_num) m
  have hden_pos : 0 < (4 : Real) ^ m * 4 :=
    mul_pos hpow_pos (by norm_num)
  unfold majorityInfluenceOddFormula
  calc
    (Nat.centralBinom (m + 1) : Real) / (4 : Real) ^ (m + 1)
        =
        (Nat.centralBinom (m + 1) : Real) / ((4 : Real) ^ m * 4) := by
      rw [pow_succ]
    _ < ((4 : Real) * (Nat.centralBinom m : Real)) /
          ((4 : Real) ^ m * 4) := by
      exact div_lt_div_of_pos_right hlt_real hden_pos
    _ =
        ((Nat.centralBinom m : Real) * 4) /
          ((4 : Real) ^ m * 4) := by
      ring
    _ = (Nat.centralBinom m : Real) / (4 : Real) ^ m := by
      exact mul_div_mul_right (Nat.centralBinom m : Real) ((4 : Real) ^ m)
        (by norm_num : (4 : Real) ≠ 0)

/--
Exercise 2.22(b), stated literally for the first coordinate of odd majority.
-/
theorem exercise_2_22b_majority_first_influence_decreasing_step (m : Nat) :
    influence
        (signFunctionToReal
          (majorityFunction : BooleanFunctionSign (2 * (m + 1) + 1)))
        (firstOddCoord (m + 1)) <
      influence
        (signFunctionToReal
          (majorityFunction : BooleanFunctionSign (2 * m + 1)))
        (firstOddCoord m) := by
  rw [exercise_2_22a_majority_influence_odd_formula]
  rw [exercise_2_22a_majority_influence_odd_formula]
  exact exercise_2_22b_majorityInfluenceOddFormula_decreasing_step m

/--
Exercise 2.22(c), along the odd subsequence `n = 2 * m + 1`.

The proof is the controlled-error Stirling calculation, isolated in
`BooleanFunctions/sorry.lean`.
-/
theorem exercise_2_22c_majority_influence_asymptotic_odd :
    Asymptotics.IsBigO Filter.atTop
      (fun m : Nat =>
        influence
            (signFunctionToReal
              (majorityFunction : BooleanFunctionSign (2 * m + 1)))
            (firstOddCoord m) -
          Real.sqrt (2 / Real.pi) /
            Real.sqrt (((2 * m + 1 : Nat) : Real)))
      majorityOddErrorScale := by
  have hfun :
      (fun m : Nat =>
        influence
            (signFunctionToReal
              (majorityFunction : BooleanFunctionSign (2 * m + 1)))
            (firstOddCoord m) -
          Real.sqrt (2 / Real.pi) /
            Real.sqrt (((2 * m + 1 : Nat) : Real))) =
        (fun m : Nat =>
          majorityInfluenceOddFormula m -
            Real.sqrt (2 / Real.pi) /
              Real.sqrt (((2 * m + 1 : Nat) : Real))) := by
    funext m
    rw [exercise_2_22a_majority_influence_odd_formula]
  rw [hfun]
  exact sorry_exercise_2_22c_stirling_influence_asymptotic_odd

/--
Exercise 2.22(d), exact first-level Fourier weight formula for odd majority.

The Fourier bookkeeping is currently collected in `BooleanFunctions/sorry.lean`.
-/
theorem exercise_2_22d_firstLevelWeight_formula_odd (m : Nat) :
    fourierWeightAtDegree
        (signFunctionToReal
          (majorityFunction : BooleanFunctionSign (2 * m + 1))) 1 =
      majorityFirstLevelWeightOddFormula m :=
  sorry_exercise_2_22d_firstLevelWeight_formula_odd m

/--
Exercise 2.22(d), lower bound and `O(n^{-1})` upper-error statement, expressed
for the closed formula for `W^1[Maj_n]`.
-/
theorem exercise_2_22d_firstLevelWeight_bounds_odd :
    (∀ m : Nat, 2 / Real.pi ≤ majorityFirstLevelWeightOddFormula m) ∧
      Asymptotics.IsBigO Filter.atTop
        (fun m : Nat => majorityFirstLevelWeightOddFormula m - 2 / Real.pi)
        (fun m : Nat => 1 / (((2 * m + 1 : Nat) : Real))) :=
  sorry_exercise_2_22d_firstLevelWeight_bounds_odd

/-- Exercise 2.22(d), the lower bound for the actual `fourierWeightAtDegree`. -/
theorem exercise_2_22d_firstLevelWeight_lower_odd (m : Nat) :
    2 / Real.pi ≤
      fourierWeightAtDegree
        (signFunctionToReal
          (majorityFunction : BooleanFunctionSign (2 * m + 1))) 1 := by
  rw [exercise_2_22d_firstLevelWeight_formula_odd]
  exact exercise_2_22d_firstLevelWeight_bounds_odd.1 m

/--
Exercise 2.22(d), the `O(n^{-1})` statement for the actual first-level Fourier
weight.
-/
theorem exercise_2_22d_firstLevelWeight_asymptotic_odd :
    Asymptotics.IsBigO Filter.atTop
      (fun m : Nat =>
        fourierWeightAtDegree
            (signFunctionToReal
              (majorityFunction : BooleanFunctionSign (2 * m + 1))) 1 -
          2 / Real.pi)
      (fun m : Nat => 1 / (((2 * m + 1 : Nat) : Real))) := by
  have hfun :
      (fun m : Nat =>
        fourierWeightAtDegree
            (signFunctionToReal
              (majorityFunction : BooleanFunctionSign (2 * m + 1))) 1 -
          2 / Real.pi) =
        (fun m : Nat => majorityFirstLevelWeightOddFormula m - 2 / Real.pi) := by
    funext m
    rw [exercise_2_22d_firstLevelWeight_formula_odd]
  rw [hfun]
  exact exercise_2_22d_firstLevelWeight_bounds_odd.2

/--
Exercise 2.22(e), the exact total influence formula for odd majority.
-/
theorem exercise_2_22e_totalInfluence_formula_odd (m : Nat) :
    totalInfluence
        (signFunctionToReal
          (majorityFunction : BooleanFunctionSign (2 * m + 1))) =
      majorityTotalInfluenceOddFormula m := by
  classical
  unfold totalInfluence majorityTotalInfluenceOddFormula
  calc
    Finset.univ.sum
        (fun i : Fin (2 * m + 1) =>
          influence
            (signFunctionToReal
              (majorityFunction : BooleanFunctionSign (2 * m + 1))) i)
        =
        Finset.univ.sum
          (fun _i : Fin (2 * m + 1) => majorityInfluenceOddFormula m) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact exercise_2_22a_majority_influence_odd_formula m i
    _ = (((2 * m + 1 : Nat) : Real) * majorityInfluenceOddFormula m) := by
      simp [Finset.sum_const, nsmul_eq_mul]

/--
Exercise 2.22(e), lower bound and asymptotic upper-error statement, expressed
for the closed total-influence formula.
-/
theorem exercise_2_22e_totalInfluence_bounds_odd :
    (∀ m : Nat,
      Real.sqrt (2 / Real.pi) *
          Real.sqrt (((2 * m + 1 : Nat) : Real)) ≤
        majorityTotalInfluenceOddFormula m) ∧
      Asymptotics.IsBigO Filter.atTop
        (fun m : Nat =>
          majorityTotalInfluenceOddFormula m -
            Real.sqrt (2 / Real.pi) *
              Real.sqrt (((2 * m + 1 : Nat) : Real)))
        (fun m : Nat =>
          1 / Real.sqrt (((2 * m + 1 : Nat) : Real))) :=
  sorry_exercise_2_22e_totalInfluence_bounds_odd

/-- Exercise 2.22(e), the lower bound for the actual total influence. -/
theorem exercise_2_22e_totalInfluence_lower_odd (m : Nat) :
    Real.sqrt (2 / Real.pi) *
        Real.sqrt (((2 * m + 1 : Nat) : Real)) ≤
      totalInfluence
        (signFunctionToReal
          (majorityFunction : BooleanFunctionSign (2 * m + 1))) := by
  rw [exercise_2_22e_totalInfluence_formula_odd]
  exact exercise_2_22e_totalInfluence_bounds_odd.1 m

/--
Exercise 2.22(e), the `O(n^{-1/2})` upper-error statement for the actual total
influence.
-/
theorem exercise_2_22e_totalInfluence_asymptotic_odd :
    Asymptotics.IsBigO Filter.atTop
      (fun m : Nat =>
        totalInfluence
            (signFunctionToReal
              (majorityFunction : BooleanFunctionSign (2 * m + 1))) -
          Real.sqrt (2 / Real.pi) *
            Real.sqrt (((2 * m + 1 : Nat) : Real)))
      (fun m : Nat =>
        1 / Real.sqrt (((2 * m + 1 : Nat) : Real))) := by
  have hfun :
      (fun m : Nat =>
        totalInfluence
            (signFunctionToReal
              (majorityFunction : BooleanFunctionSign (2 * m + 1))) -
          Real.sqrt (2 / Real.pi) *
            Real.sqrt (((2 * m + 1 : Nat) : Real))) =
        (fun m : Nat =>
          majorityTotalInfluenceOddFormula m -
            Real.sqrt (2 / Real.pi) *
              Real.sqrt (((2 * m + 1 : Nat) : Real))) := by
    funext m
    rw [exercise_2_22e_totalInfluence_formula_odd]
  rw [hfun]
  exact exercise_2_22e_totalInfluence_bounds_odd.2

/--
Exercise 2.22(f), exact equality for even-dimensional majority functions with
arbitrary tie-breaking.

Here even dimensions are written as `2 * (m + 1)`, so the corresponding odd
dimension is `2 * m + 1`.
-/
theorem exercise_2_22f_even_majority_totalInfluence_eq_odd
    (m : Nat) (f : BooleanFunctionSign (2 * (m + 1)))
    (hf : IsMajorityFunction f) :
    totalInfluence (signFunctionToReal f) =
      totalInfluence
        (signFunctionToReal
          (majorityFunction : BooleanFunctionSign (2 * m + 1))) :=
  sorry_exercise_2_22f_even_majority_totalInfluence_eq_odd m f hf

/--
Exercise 2.22(f), exact closed formula for even-dimensional majority functions.
-/
theorem exercise_2_22f_even_majority_totalInfluence_formula
    (m : Nat) (f : BooleanFunctionSign (2 * (m + 1)))
    (hf : IsMajorityFunction f) :
    totalInfluence (signFunctionToReal f) =
      majorityTotalInfluenceOddFormula m := by
  calc
    totalInfluence (signFunctionToReal f)
        =
        totalInfluence
          (signFunctionToReal
            (majorityFunction : BooleanFunctionSign (2 * m + 1))) :=
      exercise_2_22f_even_majority_totalInfluence_eq_odd m f hf
    _ = majorityTotalInfluenceOddFormula m :=
      exercise_2_22e_totalInfluence_formula_odd m

/--
Exercise 2.22(f), the even-dimensional asymptotic conclusion for any sequence
of even-dimensional majority functions.
-/
theorem exercise_2_22f_even_majority_asymptotic
    (f : (m : Nat) → BooleanFunctionSign (2 * (m + 1)))
    (hf : ∀ m : Nat, IsMajorityFunction (f m)) :
    Asymptotics.IsBigO Filter.atTop
      (fun m : Nat =>
        totalInfluence (signFunctionToReal (f m)) -
          Real.sqrt (2 / Real.pi) *
            Real.sqrt (((2 * (m + 1) : Nat) : Real)))
      (fun m : Nat =>
        1 / Real.sqrt (((2 * (m + 1) : Nat) : Real))) :=
  sorry_exercise_2_22f_even_majority_asymptotic f hf

end BooleanFunctions
