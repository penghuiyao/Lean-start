# TQI

This is a Lean 4 project for formalizing John Watrous's *The Theory of
Quantum Information*.

The local reference copy of the book is:

```text
C:\Users\phyao\Documents\Lean start\TQI\The Theory of Quantum Information.pdf
```

## Project Goal

The long-term goal is to build a Lean companion to the textbook:

1. Reuse mathlib for finite-dimensional linear algebra: finite types, matrices,
   adjoints, traces, tensor products, direct sums, rank, and spectra.
2. Reuse Physlib's `QuantumInfo` library for quantum states, channels,
   measurements, ensembles, trace distance, fidelity, entropy, and capacities.
3. Add Watrous-specific organization, theorem statements, references, and
   missing lemmas only where the existing libraries do not already provide
   them.
4. State and gradually prove the later results on entanglement, symmetry, and
   channel capacities.

## Directory Map

```text
TQI.lean              Library entry point.
TQI/
  Basic.lean          Shared imports and core conventions.
  Spaces.lean         Chapter 1.1.1: complex Euclidean spaces.
  Operators.lean      Chapter 1.1.2: operators and operator predicates.
  States.lean         Chapter 2.1: registers and states.
  Channels.lean       Chapter 2.2: quantum channels.
  Measurements.lean   Chapter 2.3: measurements and ensembles.
  Distances.lean      Chapter 3 roadmap.
  Majorization.lean   Chapter 4 roadmap.
  Entropy.lean        Chapter 5 roadmap.
  Entanglement.lean   Chapter 6 roadmap.
  Symmetry.lean       Chapter 7 roadmap.
  Capacities.lean     Chapter 8 roadmap.
  Blueprint.lean      The project roadmap.
```

## First Milestone

The first useful milestone is Chapter 1 plus the basic objects of Chapter 2:

1. Stabilize the representation of `C^Sigma` as `Sigma -> Complex`.
2. Stabilize matrices as operators `Operator Sigma Gamma`.
3. Use Physlib `HermitianMat`, `MState`, `Ket`, `CPTPMap`, `POVM`,
   `MEnsemble`, and `PEnsemble` instead of local copies.
4. Prove only the Watrous-facing trace, adjoint, and indexing lemmas missing
   from mathlib/Physlib.
5. Map each textbook definition/theorem to the corresponding mathlib or
   Physlib object before adding new code.

## Working Style

As in `BooleanFunctions`, this project uses two tracks:

* `Blueprint.lean` records the mathematical roadmap and names target objects.
* The chapter files hold the proved library, with placeholders removed over
  time.

For now, advanced chapters are intentionally roadmap files.  The default rule
is: search mathlib and Physlib first, then add only the missing Watrous-facing
glue.

Useful Physlib modules for the next steps:

```text
QuantumInfo.States.Pure.Braket
QuantumInfo.States.Mixed.MState
QuantumInfo.States.Ensemble
QuantumInfo.Channels.CPTP
QuantumInfo.Channels.MatrixMap
QuantumInfo.Measurements.POVM
QuantumInfo.States.Mixed.TraceDistance
QuantumInfo.States.Mixed.Fidelity
QuantumInfo.Entropy.VonNeumann
QuantumInfo.Entropy.Relative
QuantumInfo.Capacity.Capacity
```
