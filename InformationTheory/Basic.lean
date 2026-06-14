import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Real.Basic

/-!
# Basic project setup

This file contains the lightweight common vocabulary for formalizing Thomas
Cover and Joy Thomas's *Elements of Information Theory*.

The first convention is deliberately classical and finite:

* alphabets are finite nonempty types;
* probability mass functions are bundled real-valued functions with
  nonnegativity and total mass one;
* channels are stochastic kernels between finite alphabets.

Mathlib also has a general `PMF` for countable, `ENNReal`-valued probability
mass functions.  This project keeps the finite, real-valued wrapper above so
the chapter formulas stay close to the textbook's finite sums; bridge lemmas can
be added later where interoperability is useful.
-/

namespace InformationTheory

universe u v

/-- A finite nonempty alphabet, matching the textbook's discrete setting. -/
structure Alphabet (α : Type u) where
  fintype : Fintype α
  nonempty : Nonempty α

/-- A probability mass function on a finite alphabet. -/
structure PMF (α : Type u) [Fintype α] where
  prob : α -> ℝ
  nonneg : ∀ a, 0 ≤ prob a
  sum_eq_one : Finset.univ.sum (fun a => prob a) = 1

namespace PMF

/-- Every atom of a finite PMF has mass at most one. -/
theorem prob_le_one {α : Type u} [Fintype α] (P : PMF α) (a : α) : P.prob a ≤ 1 := by
  classical
  have hrest : 0 ≤ Finset.sum (Finset.univ.erase a) (fun b => P.prob b) :=
    Finset.sum_nonneg fun b _ => P.nonneg b
  calc
    P.prob a ≤ P.prob a + Finset.sum (Finset.univ.erase a) (fun b => P.prob b) :=
      le_add_of_nonneg_right hrest
    _ = Finset.univ.sum (fun b => P.prob b) :=
      Finset.add_sum_erase Finset.univ (fun b => P.prob b) (Finset.mem_univ a)
    _ = 1 := P.sum_eq_one

end PMF

/-- Joint distributions are PMFs on product alphabets. -/
abbrev JointPMF (α : Type u) (β : Type v) [Fintype α] [Fintype β] :=
  PMF (α × β)

/-- A stochastic kernel, or discrete channel, from `α` to `β`. -/
abbrev Channel (α : Type u) (β : Type v) [Fintype β] :=
  α -> PMF β

/-- A random variable with sample space `Ω` and value alphabet `α`. -/
abbrev RandomVariable (Ω : Type u) (α : Type v) :=
  Ω -> α

end InformationTheory
