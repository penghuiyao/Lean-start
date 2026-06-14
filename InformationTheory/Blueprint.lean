import InformationTheory.Inequalities
import InformationTheory.SourceCoding
import InformationTheory.ChannelCoding
import InformationTheory.Examples

/-!
# Blueprint

This file is the roadmap for formalizing Cover and Thomas's *Elements of
Information Theory*.  As in `BooleanFunctions` and `TQI`, this file may name
target objects before the polished proofs are moved into the chapter files.

## Milestone 0: project infrastructure

1. Keep the existing Lake workspace and add `InformationTheory` as a third Lean
   library.
2. Record the global convention: all alphabets are finite nonempty types unless
   a later chapter explicitly needs a more general measurable space.
3. Establish bundled PMFs, joint PMFs, stochastic kernels, and random variables.
4. Use base-two logarithms by default.

## Milestone 1: finite probability and entropy

1. Define marginals, products, conditional laws, independence, and Markov
   chains.
2. Define entropy, joint entropy, conditional entropy, mutual information, and
   KL divergence.
3. Prove basic identities: chain rules, `I(X;Y) = H(X) - H(X|Y)`, and
   nonnegativity statements.
4. Stabilize notation for `H`, `I`, and `D`.

## Milestone 2: core inequalities

1. Prove Jensen's inequality instances needed for entropy.
2. Prove Gibbs' inequality and the log-sum inequality.
3. Prove data processing for Markov chains.
4. Formalize Fano's inequality.

## Milestone 3: typicality and source coding

1. Define product distributions and iid block sources.
2. Formalize typical sets and the asymptotic equipartition property.
3. Prove Kraft's inequality and the noiseless coding theorem.
4. State and prove source coding achievability and converse results.

## Milestone 4: channel coding

1. Define discrete memoryless channels and `n`-fold channel products.
2. Define block codes, decoding regions, average and maximal error probability.
3. Prove the channel coding theorem for finite alphabets.
4. Formalize channel capacity as `sup_P I(P, W)`.

## Milestone 5: later chapters

1. Differential entropy and Gaussian examples.
2. Rate distortion theory.
3. Network information theory.
4. Connections to statistics, universal coding, and portfolio theory.
-/

namespace InformationTheory

section Roadmap

universe u v

variable (α : Type u) (β : Type v)
variable [Fintype α] [Fintype β]

/-- The default discrete source object for the first chapters. -/
abbrev DiscreteSource :=
  PMF α

/-- The default channel object for the channel-coding chapters. -/
abbrev FiniteChannel :=
  Channel α β

/-- The first entropy target: `H(X)` for a finite source. -/
abbrev SourceEntropy :=
  DiscreteSource α -> ℝ

/-- The first channel target: `I(P, W)` for a finite input law and channel. -/
abbrev ChannelInformation :=
  DiscreteSource α -> FiniteChannel α β -> ℝ

end Roadmap

end InformationTheory
