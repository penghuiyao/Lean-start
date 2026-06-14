import InformationTheory.Typicality
import InformationTheory.datacompression

/-!
# Source coding

Roadmap file for lossless source coding, prefix-free codes, Kraft's inequality,
the noiseless coding theorem, and the asymptotic equipartition property.
-/

namespace InformationTheory

universe u

/-- A block source over a finite alphabet. -/
abbrev SourceBlock (α : Type u) (n : Nat) :=
  Block α n

/-- A code over an output alphabet `β` for source symbols in `α`. -/
abbrev Code (α : Type u) (β : Type v) :=
  SourceCode α β

end InformationTheory
