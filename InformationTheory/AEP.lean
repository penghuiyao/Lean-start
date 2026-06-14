import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import InformationTheory.Entropy

/-!
# Chapter 3: Asymptotic Equipartition Property

This file starts the formalization of Cover and Thomas, Chapter 3.  Mathlib
already contains the standard measure-theoretic notion needed for the first
definition:

* `MeasureTheory.TendstoInMeasure` is convergence in measure, which is
  convergence in probability when the ambient measure is a probability measure.

We expose textbook-facing names for the three convergence modes listed before
Theorem 3.1.1.
-/

namespace InformationTheory

open Filter MeasureTheory

open scoped ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-!
## ASYMPTOTIC EQUIPARTITION PROPERTY THEOREM
-/

/--
Definition, convergence of random variables in probability.

This is mathlib's `MeasureTheory.TendstoInMeasure` specialized to sequences
indexed by `ℕ`.  For probability measures this is exactly the textbook
condition `Pr {|Xₙ - X| > ε} → 0` for every `ε > 0`.
-/
abbrev ConvergesInProbability
    (μ : Measure Ω) (X : ℕ -> Ω -> ℝ) (Y : Ω -> ℝ) : Prop :=
  TendstoInMeasure μ X atTop Y

/--
Textbook real-distance form of convergence in probability, using real-valued
measures.  Mathlib's underlying definition uses `edist`; this theorem is the
standard bridge to the familiar `Pr{dist(Xₙ, X) ≥ ε} → 0` formulation.
-/
theorem convergesInProbability_iff_measureReal_dist
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : ℕ -> Ω -> ℝ) (Y : Ω -> ℝ) :
    ConvergesInProbability μ X Y ↔
      ∀ ε : ℝ, 0 < ε ->
        Tendsto
          (fun n : ℕ => μ.real {ω : Ω | ε ≤ dist (X n ω) (Y ω)})
          atTop (𝓝 0) := by
  simpa [ConvergesInProbability] using
    (tendstoInMeasure_iff_measureReal_dist
      (μ := μ) (f := X) (l := atTop) (g := Y))

/--
Mean-square error of two real-valued random variables, written with the
nonnegative extended integral so the definition has no separate integrability
side condition.
-/
noncomputable def meanSquareError
    (μ : Measure Ω) (X Y : Ω -> ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal ((X ω - Y ω) ^ 2) ∂μ

/--
Definition, convergence in mean square: `E[(Xₙ - X)^2] → 0`.

The expectation is represented by `meanSquareError`, an extended nonnegative
integral.
-/
def ConvergesInMeanSquare
    (μ : Measure Ω) (X : ℕ -> Ω -> ℝ) (Y : Ω -> ℝ) : Prop :=
  Tendsto (fun n : ℕ => meanSquareError μ (X n) Y) atTop (𝓝 0)

/--
Definition, convergence with probability one, also called almost sure
convergence.
-/
def ConvergesAlmostSurely
    (μ : Measure Ω) (X : ℕ -> Ω -> ℝ) (Y : Ω -> ℝ) : Prop :=
  ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => X n ω) atTop (𝓝 (Y ω))

/--
Mathlib result, exposed under the textbook names: almost sure convergence
implies convergence in probability on a finite measure space.
-/
theorem convergesInProbability_of_convergesAlmostSurely
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : ℕ -> Ω -> ℝ) (Y : Ω -> ℝ)
    (hX : ∀ n, AEStronglyMeasurable (X n) μ)
    (h : ConvergesAlmostSurely μ X Y) :
    ConvergesInProbability μ X Y :=
  tendstoInMeasure_of_tendsto_ae hX h

/-!
## TYPICAL SETS
-/

/-- A length-`n` block over an alphabet. -/
abbrev Block (α : Type u) (n : Nat) :=
  Fin n -> α

/-- The iid product mass `p(x₁, ..., xₙ) = ∏ᵢ p(xᵢ)`. -/
noncomputable def iidBlockProbability {α : Type u} [Fintype α]
    (P : PMF α) {n : Nat} (x : Block α n) : ℝ :=
  Finset.univ.prod (fun i : Fin n => P.prob (x i))

/-- The sample entropy `-(1/n) log p(xⁿ)` of a block. -/
noncomputable def sampleEntropyOfBlock {α : Type u} [Fintype α]
    (P : PMF α) {n : Nat} (x : Block α n) : ℝ :=
  -((n : ℝ)⁻¹) * logBase 2 (iidBlockProbability P x)

/--
Section 3.1 definition: the typical set `A⁽ⁿ⁾_ε`, written as a predicate on
length-`n` blocks and using the probability bounds in equation (3.6).
-/
def IsTypical {α : Type u} [Fintype α]
    (P : PMF α) (ε : ℝ) {n : Nat} (x : Block α n) : Prop :=
  (2 : ℝ) ^ (-(n : ℝ) * (entropy P + ε)) ≤ iidBlockProbability P x ∧
    iidBlockProbability P x ≤ (2 : ℝ) ^ (-(n : ℝ) * (entropy P - ε))

/-- The typical set `A⁽ⁿ⁾_ε` as a subtype. -/
abbrev TypicalSet (α : Type u) [Fintype α] (P : PMF α) (ε : ℝ) (n : Nat) :=
  {x : Block α n // IsTypical P ε x}

/-- The typical set as a finset, convenient for finite sums. -/
noncomputable def typicalSetFinset {α : Type u} [Fintype α]
    (P : PMF α) (ε : ℝ) (n : Nat) : Finset (Block α n) :=
  by
    classical
    exact Finset.univ.filter (fun x : Block α n => IsTypical P ε x)

/-- Probability mass of the typical set under the iid block law. -/
noncomputable def typicalSetMass {α : Type u} [Fintype α]
    (P : PMF α) (ε : ℝ) (n : Nat) : ℝ :=
  (typicalSetFinset P ε n).sum (fun x : Block α n => iidBlockProbability P x)

/-- The cardinality of the typical set. -/
noncomputable def typicalSetCard {α : Type u} [Fintype α]
    (P : PMF α) (ε : ℝ) (n : Nat) : Nat :=
  (typicalSetFinset P ε n).card

end InformationTheory
