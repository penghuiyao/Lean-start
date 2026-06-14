import InformationTheory.Channels
import InformationTheory.Typicality

/-!
# Channel coding

Roadmap file for channel codes, decoding rules, probability of error, Fano's
inequality, achievability, converse statements, and capacity theorems.
-/

namespace InformationTheory

universe u v w

/-- A block encoder for messages in `M` over channel input alphabet `α`. -/
abbrev Encoder (M : Type u) (α : Type v) (n : Nat) :=
  M -> Block α n

/-- A block decoder from channel output blocks to messages. -/
abbrev Decoder (β : Type v) (M : Type u) (n : Nat) :=
  Block β n -> M

end InformationTheory
