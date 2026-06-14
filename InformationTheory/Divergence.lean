import InformationTheory.Entropy

/-!
# Divergence and relative information

This file records the finite-alphabet expression for Kullback-Leibler
divergence.  It will later host cross entropy, relative entropy identities, and
Gibbs' inequality.

Mathlib's `InformationTheory.klDiv` is the general measure-theoretic
`ENNReal`-valued divergence.  The names here are textbook-facing aliases for
the finite, real-valued definitions in `Entropy.lean`.
-/

namespace InformationTheory

universe u

variable {α : Type u}

/-- The KL summand `p log₂ (p/q)`, with the conventional zero value at `p = 0`. -/
noncomputable abbrev divergenceTerm (p q : ℝ) : ℝ :=
  relativeEntropyTermWithBase 2 p q

/-- Kullback-Leibler divergence `D(P || Q)` over a finite alphabet. -/
noncomputable abbrev KL [Fintype α] (P Q : PMF α) : ℝ :=
  relativeEntropy P Q

end InformationTheory
