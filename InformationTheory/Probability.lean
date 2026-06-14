import InformationTheory.Basic

/-!
# Finite probability vocabulary

This file collects the finite-distribution operations needed before entropy and
coding theorems: marginals, product laws, channel-induced joint laws, and
independence predicates.
-/

namespace InformationTheory

universe u v

variable {α : Type u} {β : Type v}

/-- The left marginal mass function of a joint law, currently as an unbundled
function so that proof obligations can be added only when needed. -/
noncomputable def marginalLeftMass [Fintype α] [Fintype β]
    (P : JointPMF α β) : α -> ℝ :=
  fun a => Finset.univ.sum (fun b : β => P.prob (a, b))

/-- The right marginal mass function of a joint law, currently unbundled. -/
noncomputable def marginalRightMass [Fintype α] [Fintype β]
    (P : JointPMF α β) : β -> ℝ :=
  fun b => Finset.univ.sum (fun a : α => P.prob (a, b))

/-- The product mass function associated to two marginal laws, unbundled. -/
def productMass [Fintype α] [Fintype β] (P : PMF α) (Q : PMF β) :
    α × β -> ℝ :=
  fun ab => P.prob ab.1 * Q.prob ab.2

/-- The joint mass induced by an input distribution and a channel. -/
def jointMassOfChannel [Fintype α] [Fintype β]
    (P : PMF α) (W : Channel α β) : α × β -> ℝ :=
  fun ab => P.prob ab.1 * (W ab.1).prob ab.2

/-- Independence of two finite random quantities, expressed through a joint law. -/
def Independent [Fintype α] [Fintype β]
    (P : PMF α) (Q : PMF β) (R : JointPMF α β) : Prop :=
  ∀ a b, R.prob (a, b) = P.prob a * Q.prob b

end InformationTheory
