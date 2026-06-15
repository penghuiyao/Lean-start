# Codex QIT Project Summary

This note summarizes the current Lean project for formalizing John Watrous's
*The Theory of Quantum Information* (TQI), with emphasis on project layout,
Lake dependencies, recent issues, completed changes, and suggested next steps.

## Project Structure

The workspace is a single Lean/Lake repository containing multiple Lean
libraries:

```text
Lean start/
  lakefile.toml
  lean-toolchain
  lake-manifest.json

  BooleanFunctions.lean
  BooleanFunctions/

  InformationTheory.lean
  InformationTheory/

  TQI.lean
  TQI/
    Basic.lean
    Spaces.lean
    Operators.lean
    States.lean
    Channels.lean
    Measurements.lean
    Distances.lean
    Majorization.lean
    Entropy.lean
    Entanglement.lean
    Symmetry.lean
    Capacities.lean
    Blueprint.lean
    README.md
    The Theory of Quantum Information.pdf
```

The TQI library is organized by Watrous's textbook:

- `Basic.lean`: shared finite-dimensional conventions, currently mathlib-level.
- `Spaces.lean`: Chapter 1.1.1, complex Euclidean spaces.
- `Operators.lean`: Chapter 1.1.2, operators and operator vocabulary.
- `States.lean`: Chapter 2.1 roadmap for registers and states.
- `Channels.lean`: Chapter 2.2 roadmap for quantum channels.
- `Measurements.lean`: Chapter 2.3 roadmap for POVMs and ensembles.
- `Distances.lean`: Chapter 3 roadmap.
- `Majorization.lean`: Chapter 4 roadmap.
- `Entropy.lean`: Chapter 5 roadmap.
- `Entanglement.lean`: Chapter 6 roadmap.
- `Symmetry.lean`: Chapter 7 roadmap.
- `Capacities.lean`: Chapter 8 roadmap.
- `Blueprint.lean`: global formalization plan and milestones.

## Lean and Lake Dependencies

The project uses Lean 4.30.0:

```text
leanprover/lean4:v4.30.0
```

The active Lake configuration is:

```toml
name = "BooleanFunctions"
version = "0.1.0"
keywords = ["math", "formalization"]
defaultTargets = ["BooleanFunctions", "TQI", "InformationTheory"]

[leanOptions]
pp.unicode.fun = true
relaxedAutoImplicit = false
maxSynthPendingDepth = 3

[[require]]
name = "mathlib"
path = ".lake/packages/mathlib"

[[require]]
name = "Physlib"
path = ".lake/packages/PhysLean"

[[lean_lib]]
name = "BooleanFunctions"

[[lean_lib]]
name = "TQI"

[[lean_lib]]
name = "InformationTheory"
```

The dependency strategy for TQI is:

- Use mathlib for the general finite-dimensional linear algebra layer:
  matrices, traces, adjoints, determinants, rank, finite-dimensional vector
  spaces, bases, inner product spaces, Hermitian matrices, unitary groups, and
  related matrix APIs.
- Use Physlib's `QuantumInfo` library for quantum-information objects:
  `Ket`, `MState`, `CPTPMap`, `POVM`, `MEnsemble`, `PEnsemble`, trace
  distance, fidelity, entropy, and channel-capacity infrastructure.
- Avoid local duplicate definitions for density operators, channels, POVMs,
  entropy, fidelity, etc. TQI should mainly provide Watrous-specific
  organization, naming, theorem statements, and missing glue lemmas.

Important Physlib modules for future imports:

```lean
QuantumInfo.ForMathlib.HermitianMat
QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
QuantumInfo.States.Pure.Braket
QuantumInfo.States.Mixed.MState
QuantumInfo.States.Mixed.TraceDistance
QuantumInfo.States.Mixed.Fidelity
QuantumInfo.States.Ensemble
QuantumInfo.Channels.CPTP
QuantumInfo.Channels.MatrixMap
QuantumInfo.Channels.Unbundled
QuantumInfo.Measurements.POVM
QuantumInfo.Entropy.VonNeumann
QuantumInfo.Entropy.Relative
QuantumInfo.Capacity.Capacity
```

## Recent Issues

### Physlib Connection

Physlib itself was cloned successfully into:

```text
.lake/packages/PhysLean
```

The actual network problem was with Physlib's documentation dependency
`doc-gen4`, declared in Physlib's own `lakefile.toml`:

```toml
[[require]]
name = "«doc-gen4»"
git = "https://github.com/leanprover/doc-gen4"
rev = "v4.30.0"
```

Attempts to run `lake update Physlib` failed because the connection to
`https://github.com/leanprover/doc-gen4` was reset. Since TQI does not import
DocGen4, a minimal local stub was used so Lake can resolve Physlib's dependency
graph while network access to the real documentation package is unavailable.

### Heavy Physlib Imports

Directly importing high-level Physlib modules such as
`QuantumInfo.States.Pure.Braket` pulls in a very large portion of mathlib and
Physlib. Building from source took a long time and repeatedly hit command
timeouts, although it continued making progress and caching `.olean` files.

To keep the default TQI skeleton usable, the current TQI files do not import
heavy QuantumInfo modules by default. Instead, they document which Physlib
module should be imported when a chapter actually needs the concrete object.

### Existing Worktree State

At the time this summary was written, the worktree had unrelated local changes
in `BooleanFunctions` and `InformationTheory`. Those should be treated as
separate work and not mixed into TQI commits unless intentionally requested.

## Changes Already Made

### TQI Library Added

Added the `TQI` Lean library with a chapter-oriented skeleton:

```text
TQI.lean
TQI/Basic.lean
TQI/Spaces.lean
TQI/Operators.lean
TQI/States.lean
TQI/Channels.lean
TQI/Measurements.lean
TQI/Distances.lean
TQI/Majorization.lean
TQI/Entropy.lean
TQI/Entanglement.lean
TQI/Symmetry.lean
TQI/Capacities.lean
TQI/Blueprint.lean
TQI/README.md
```

The local copy of Watrous's PDF is stored at:

```text
TQI/The Theory of Quantum Information.pdf
```

### Lake Configuration Updated

The Lake project now has three default targets:

```text
BooleanFunctions
TQI
InformationTheory
```

The project now has path dependencies on local copies of:

```text
.lake/packages/mathlib
.lake/packages/PhysLean
```

### TQI Design Adjusted

The initial TQI skeleton briefly introduced local aliases/placeholders for
states, channels, POVMs, and positivity predicates. This was revised after
checking Physlib:

- `TQI.Basic` now stays lightweight and only records mathlib-level conventions.
- Chapter files explain which Physlib modules to use instead of defining local
  replacements.
- `TQI.Blueprint` and `TQI/README.md` explicitly state the rule:
  search mathlib and Physlib first, then add only missing Watrous-facing glue.

### Build Status

The following builds have passed after the dependency and skeleton changes:

```powershell
lake build TQI
lake build
```

## Next Steps

### 1. Choose the First Formalization Surface

Start with Chapter 1.1 and decide which representation will be primary for
Watrous's `C^Sigma`:

- mathlib functions: `Sigma -> Complex`;
- mathlib matrices: `Matrix Gamma Sigma Complex`;
- Physlib's matrix/Hermitian matrix layer when positivity is involved.

The current `TQI.Basic` uses:

```lean
abbrev EuclideanSpace (Sigma : Type u) := Sigma -> Complex
abbrev Operator (Sigma : Type u) (Gamma : Type v) := Matrix Gamma Sigma Complex
abbrev End (Sigma : Type u) := Operator Sigma Sigma
```

### 2. Map Watrous Chapter 1 Definitions to Existing APIs

Create a small table or Lean comments mapping:

- alphabet -> finite type;
- `C^Sigma` -> `Sigma -> Complex`;
- matrix/operator -> `Matrix Gamma Sigma Complex`;
- adjoint -> `Matrix.conjTranspose`;
- trace -> `Matrix.trace`;
- Hermitian -> `Matrix.IsHermitian` or Physlib `HermitianMat`;
- PSD -> Physlib `HermitianMat` order or appropriate mathlib matrix order;
- unitary -> `Matrix.unitaryGroup`.

### 3. Add Lightweight Glue Lemmas

Only add lemmas that make Watrous statements ergonomic. Likely early examples:

- entry-wise formula for the standard basis vector;
- inner product expansion on `Sigma -> Complex`;
- trace of elementary matrices;
- compatibility between Watrous-style matrix entries and mathlib notation;
- simple tensor/product alphabet equivalences.

### 4. Bring in Physlib Modules One at a Time

Do not import all of `QuantumInfo.lean` at once. For each chapter:

- Chapter 2.1 states: import `QuantumInfo.States.Mixed.MState` only when needed.
- Pure states: import `QuantumInfo.States.Pure.Braket` only when needed.
- Channels: import `QuantumInfo.Channels.CPTP` or `MatrixMap` only when needed.
- Measurements: import `QuantumInfo.Measurements.POVM` only when needed.

This avoids repeatedly triggering huge rebuilds during early skeleton work.

### 5. Replace the DocGen Stub Later

When GitHub access is stable, replace the local `doc-gen4` stub with the real
dependency by rerunning a proper Lake update for Physlib. Until then, the stub
is only there to satisfy Lake's dependency graph and should not be used for
documentation generation.

### 6. Keep Commits Narrow

The repository currently contains multiple projects. Future commits should
prefer narrow scopes, for example:

- `TQI: map chapter 1 linear algebra APIs`
- `TQI: add standard basis lemmas`
- `TQI: connect MState to Watrous states`
- `TQI: add channel roadmap using CPTPMap`

Avoid mixing unrelated `BooleanFunctions` and `InformationTheory` changes into
TQI commits unless the change is intentionally cross-project.
