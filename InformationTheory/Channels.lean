import InformationTheory.Divergence

/-!
# Discrete memoryless channels

This file tracks channel laws, output distributions, and channel information
quantities for finite alphabets.
-/

namespace InformationTheory

universe u v

variable {α : Type u} {β : Type v}

/-- A discrete memoryless channel, named as in information theory. -/
abbrev DiscreteMemorylessChannel (α : Type u) (β : Type v) [Fintype β] :=
  Channel α β

/-- The output mass induced by an input law and a channel. -/
noncomputable def outputMass [Fintype α] [Fintype β]
    (P : PMF α) (W : Channel α β) : β -> ℝ :=
  fun b => Finset.univ.sum (fun a : α => P.prob a * (W a).prob b)

/-- Mutual information `I(P, W)` induced by an input distribution and channel. -/
noncomputable def channelMutualInformation [Fintype α] [Fintype β]
    (P : PMF α) (W : Channel α β) : ℝ :=
  mutualInformationFromMass (jointMassOfChannel P W)

/-- A placeholder interface for channel capacity over a finite input alphabet. -/
abbrev CapacityFunctional (α : Type u) (β : Type v)
    [Fintype α] [Fintype β] :=
  Channel α β -> ℝ

end InformationTheory
