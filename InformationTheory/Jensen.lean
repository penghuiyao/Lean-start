import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import InformationTheory.Entropy

/-!
# Theorems for Section 2.6: Jensen's Inequality and Its Consequences

Mathlib already provides the convexity vocabulary and finite Jensen
inequality used in Cover and Thomas, Section 2.6:

* `ConvexOn` and `ConcaveOn` are the convex/concave definitions;
* `convexOn_of_deriv2_nonneg'` and `strictConvexOn_of_deriv2_pos'`
  give the second-derivative criterion;
* `ConvexOn.map_sum_le` and `StrictConvexOn.map_sum_eq_iff'` give finite
  Jensen and its equality case.

This file records the textbook-facing finite-PMF forms used by the
information-theory development.
-/

namespace InformationTheory

universe u

variable {α : Type u}

/-!
## JENSEN'S INEQUALITY AND ITS CONSEQUENCES
-/

/-- Textbook convexity over a real set, using mathlib's `ConvexOn`. -/
abbrev TextbookConvexOn (s : Set ℝ) (f : ℝ -> ℝ) : Prop :=
  ConvexOn ℝ s f

/-- Textbook concavity over a real set, using mathlib's `ConcaveOn`. -/
abbrev TextbookConcaveOn (s : Set ℝ) (f : ℝ -> ℝ) : Prop :=
  ConcaveOn ℝ s f

/--
Theorem 2.6.1, non-strict part: a twice differentiable real function with
nonnegative second derivative on a convex domain is convex there.
-/
theorem theorem_2_6_1_convex_of_deriv2_nonneg
    {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ -> ℝ}
    (hf' : DifferentiableOn ℝ f D)
    (hf'' : DifferentiableOn ℝ (deriv f) D)
    (hf''_nonneg : ∀ x ∈ D, 0 ≤ (deriv^[2] f) x) :
    ConvexOn ℝ D f :=
  convexOn_of_deriv2_nonneg' hD hf' hf'' hf''_nonneg

/--
Theorem 2.6.1, strict part: a continuous real function with positive second
derivative on a convex domain is strictly convex there.
-/
theorem theorem_2_6_1_strictConvex_of_deriv2_pos
    {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ -> ℝ}
    (hf : ContinuousOn f D)
    (hf''_pos : ∀ x ∈ D, 0 < (deriv^[2] f) x) :
    StrictConvexOn ℝ D f :=
  strictConvexOn_of_deriv2_pos' hD hf hf''_pos

/--
Theorem 2.6.2, Jensen's inequality for a finite random variable:
`f (E X) ≤ E (f X)` for convex `f`.
-/
theorem theorem_2_6_2_jensen
    [Fintype α] (P : PMF α) {s : Set ℝ} {f : ℝ -> ℝ} {X : α -> ℝ}
    (hf : ConvexOn ℝ s f) (hX : ∀ a, X a ∈ s) :
    f (expectation P X) ≤ expectation P (fun a => f (X a)) := by
  simpa [expectation, smul_eq_mul] using
    hf.map_sum_le (t := Finset.univ) (w := P.prob) (p := X)
      (fun a _ => P.nonneg a) P.sum_eq_one (fun a _ => hX a)

/--
Theorem 2.6.2, equality case for strictly convex `f`: equality in Jensen
forces `X` to equal its expectation on every atom of nonzero probability.
-/
theorem theorem_2_6_2_jensen_strictConvex_eq_iff
    [Fintype α] (P : PMF α) {s : Set ℝ} {f : ℝ -> ℝ} {X : α -> ℝ}
    (hf : StrictConvexOn ℝ s f) (hX : ∀ a, X a ∈ s) :
    f (expectation P X) = expectation P (fun a => f (X a)) ↔
      ∀ a, P.prob a ≠ 0 -> X a = expectation P X := by
  simpa [expectation, smul_eq_mul] using
    hf.map_sum_eq_iff' (t := Finset.univ) (w := P.prob) (p := X)
      (fun a _ => P.nonneg a) P.sum_eq_one (fun a _ => hX a)

/-- Jensen's inequality for concave functions, the order-dual form. -/
theorem jensen_concave
    [Fintype α] (P : PMF α) {s : Set ℝ} {f : ℝ -> ℝ} {X : α -> ℝ}
    (hf : ConcaveOn ℝ s f) (hX : ∀ a, X a ∈ s) :
    expectation P (fun a => f (X a)) ≤ f (expectation P X) := by
  simpa [expectation, smul_eq_mul] using
    hf.le_map_sum (t := Finset.univ) (w := P.prob) (p := X)
      (fun a _ => P.nonneg a) P.sum_eq_one (fun a _ => hX a)

end InformationTheory
