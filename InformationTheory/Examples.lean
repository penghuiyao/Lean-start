import InformationTheory.Channels

/-!
# Examples

Small named examples from the textbook: binary alphabets, binary symmetric
channels, erasure-style channels, and simple source models.
-/

namespace InformationTheory

/-- The standard binary alphabet. -/
abbrev BinaryAlphabet :=
  Bool

/-- The unbundled law of a binary symmetric channel with crossover mass `p`. -/
def binarySymmetricChannelMass (p : ℝ) : Bool -> Bool -> ℝ :=
  fun x y => if x = y then 1 - p else p

end InformationTheory
