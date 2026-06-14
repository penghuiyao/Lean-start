# InformationTheory

This is a Lean 4 project for formalizing Thomas Cover and Joy Thomas's
*Elements of Information Theory*.

The local reference copy of the book is:

```text
C:\Users\phyao\Documents\Lean start\InformationTheory\elements of information theory_Unknown Author.pdf
```

## Project Goal

The long-term goal is to build a Lean companion to the textbook:

1. Formalize finite alphabets, probability mass functions, joint distributions,
   random variables, and stochastic kernels.
2. Formalize entropy, conditional entropy, mutual information, and divergence.
3. Prove the core identities and inequalities: chain rules, Gibbs' inequality,
   log-sum inequality, data processing, and Fano's inequality.
4. Formalize typical sequences and the asymptotic equipartition property.
5. Formalize source coding, channel coding, and capacity theorems for finite
   alphabets.

## Directory Map

```text
InformationTheory.lean       Library entry point.
InformationTheory/
  Basic.lean                 Shared imports and core conventions.
  Probability.lean           Marginals, products, induced joint laws.
  Entropy.lean               Entropy and mutual information expressions.
  Divergence.lean            KL divergence and related quantities.
  Channels.lean              Discrete memoryless channels and capacity targets.
  Typicality.lean            Blocks and typical-set interfaces.
  SourceCoding.lean          Source coding roadmap.
  ChannelCoding.lean         Channel coding roadmap.
  Inequalities.lean          Named inequality target propositions.
  Examples.lean              Binary alphabets and textbook examples.
  Blueprint.lean             The project roadmap.
```

## First Milestone

The first useful milestone is the finite-discrete core:

1. Stabilize `PMF`, `JointPMF`, `Channel`, and marginal conventions.
2. Decide how much to reuse from mathlib's probability APIs versus keeping a
   small finite-alphabet layer.
3. Prove that marginals and channel-induced laws are valid bundled PMFs.
4. Prove the entropy chain rules and nonnegativity of KL divergence.
5. Use those results to state data processing and Fano's inequality cleanly.

## Working Style

As in `BooleanFunctions`, this project uses two tracks:

* `Blueprint.lean` records the mathematical roadmap and names target objects.
* The chapter files hold the proved library, with placeholders removed over
  time.

For now, the early files intentionally favor stable names and compiling
interfaces over ambitious theorem statements.  The first proof-heavy step will
be turning unbundled marginal and channel masses into bundled `PMF`s.
