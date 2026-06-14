import BooleanFunctions.Examples
import BooleanFunctions.Friedgut

/-!
# Blueprint

This file is the roadmap for formalizing Ryan O'Donnell's *Analysis of Boolean
Functions*.  It is allowed to contain theorem statements before full proofs are
available.  The proved versions should eventually move into the chapter files.

## First milestone

1. Define the Boolean cube.
2. Define uniform expectation over the cube.
3. Define Fourier characters.
4. Prove character orthonormality.
5. Prove Parseval.

## Later milestones

1. Influence and total influence.
2. Noise operator and noise stability.
3. Hypercontractivity.
4. KKL.
5. Friedgut junta theorem.
-/

namespace BooleanFunctions

section Roadmap

variable (n : Nat)

/-- The book's main Boolean cube convention: `{-1, 1}^n`. -/
abbrev BooleanCube := SignCube n

end Roadmap

end BooleanFunctions
