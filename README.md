# BooleanFunctions

This is a Lean 4 project for learning formalization by working through
Ryan O'Donnell's *Analysis of Boolean Functions*.

The workspace now also contains `TQI`, a second Lean library for formalizing
John Watrous's *The Theory of Quantum Information*.  Its local roadmap is in
`TQI/README.md`, and the library entry point is `TQI.lean`.

`TQI` depends on both mathlib and Physlib.  The intended style is to reuse
mathlib's finite-dimensional linear algebra and Physlib's `QuantumInfo`
definitions, rather than introducing parallel local definitions for states,
channels, POVMs, entropy, fidelity, and related notions.

The workspace also contains `InformationTheory`, a third Lean library for
formalizing Cover and Thomas's *Elements of Information Theory*.  Its local
roadmap is in `InformationTheory/README.md`, and the library entry point is
`InformationTheory.lean`.

The local reference copy of the book is in:

```text
D:\Dropbox\books\theoretical computer science
```

## Project Goal

The long-term goal is to build a Lean companion to the textbook:

1. Formalize the Boolean cube and Boolean-valued / real-valued functions on it.
2. Formalize expectation, inner product, variance, and finite sums.
3. Formalize Fourier characters and Fourier coefficients.
4. Prove orthonormality, Fourier expansion, Parseval, and Plancherel.
5. Formalize influence, noise operators, and noise stability.
6. State and gradually prove the major theorems: hypercontractivity, KKL, and
   Friedgut's junta theorem.

## Directory Map

```text
BooleanFunctions/
  Basic.lean              Project-wide basic imports and notation.
  Fourierexpansion.lean   `Cube01` for `{0,1}^n` and `SignCube` for `{-1,1}^n`.
  Expectation.lean        Uniform expectation and inner products.
  Fourier.lean            Characters and Fourier coefficients.
  Influence.lean          Coordinate flips, derivatives, and influence.
  Noise.lean              Noise operators and stability.
  Examples.lean           Dictator, parity, AND/OR, majority, tribes.
  Hypercontractivity.lean Long-term target: Bonami-Beckner inequality.
  KKL.lean                Long-term target: KKL theorem.
  Friedgut.lean           Long-term target: junta theorem.
  Blueprint.lean          The roadmap: theorem statements may use `sorry`.
```

## Working Style

This project intentionally uses two tracks:

* `Blueprint.lean` records definitions and theorem statements from the book,
  even before all proofs are known.
* The other files contain the proved library, with `sorry` removed over time.

For now, it is fine if some advanced files only contain imports and comments.
The first real milestone is `Fourierexpansion.lean` + `Expectation.lean`.

## Setup Notes

The project uses Lean `4.30.0` and a local copy of mathlib `v4.30.0`.

The mathlib source and its dependencies are installed under:

```text
.lake/packages/
```

The project is configured to use these local package directories, so normal
builds should not try to clone from GitHub.

To build the project:

```powershell
lake build
```

Do not run `lake update` unless Git access to GitHub is working. The local
mathlib install came from downloaded zip archives, so `lake update` may try to
treat them as Git repositories.

Some useful mathlib modules have already been built from source:

```text
Mathlib.Init
Mathlib.Data.Real.Basic
Mathlib.Data.Finset.Basic
Mathlib.Algebra.BigOperators.Group.Finset.Basic
```
