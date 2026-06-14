import Mathlib.InformationTheory.Coding.UniquelyDecodable
import InformationTheory.Entropy

/-!
# Section 5.1: Examples of Codes

This file gives the source-code definitions from Cover and Thomas, Section 5.1.
Mathlib already provides the codeword-set predicate
`InformationTheory.UniquelyDecodable` and the later Kraft-McMillan theorem; the
definitions below add the textbook-facing layer where a source code is a map
from source symbols to finite strings over a code alphabet.
-/

namespace InformationTheory

universe u v

/-!
## EXAMPLES OF CODES
-/

/-- A concrete `D`-ary alphabet, modeled as the finite type `{0, ..., D - 1}`. -/
abbrev DaryAlphabet (D : Nat) :=
  Fin D

/-- The set `D*` of finite strings over an alphabet. -/
abbrev CodeString (beta : Type v) :=
  List beta

/-- A finite source string over the source alphabet. -/
abbrev SourceString (alpha : Type u) :=
  List alpha

/--
Definition, source code: a map from source symbols to finite strings over the
code alphabet.
-/
abbrev SourceCode (alpha : Type u) (beta : Type v) :=
  alpha -> CodeString beta

namespace SourceCode

variable {alpha : Type u} {beta : Type v}

/-- The codeword `C(x)` associated with a source symbol `x`. -/
def codeword (C : SourceCode alpha beta) (x : alpha) : CodeString beta :=
  C x

/-- The codeword length `l(x)`. -/
def length (C : SourceCode alpha beta) (x : alpha) : Nat :=
  (C.codeword x).length

/--
Definition (5.1), expected length of a source code under a finite PMF.
-/
noncomputable def expectedLength [Fintype alpha]
    (P : PMF alpha) (C : SourceCode alpha beta) : ℝ :=
  Finset.univ.sum (fun x : alpha => P.prob x * (C.length x : ℝ))

/--
Definition, nonsingular code: distinct source symbols have distinct codewords.
-/
def IsNonsingular (C : SourceCode alpha beta) : Prop :=
  Function.Injective C

/--
Definition, extension `C*`: encode a finite source string by concatenating the
corresponding codewords.
-/
def extension (C : SourceCode alpha beta) : SourceString alpha -> CodeString beta :=
  fun xs => (xs.map C).flatten

@[simp]
theorem extension_nil (C : SourceCode alpha beta) :
    C.extension [] = [] := by
  simp [extension]

@[simp]
theorem extension_cons (C : SourceCode alpha beta) (x : alpha) (xs : SourceString alpha) :
    C.extension (x :: xs) = C x ++ C.extension xs := by
  simp [extension]

@[simp]
theorem extension_append
    (C : SourceCode alpha beta) (xs ys : SourceString alpha) :
    C.extension (xs ++ ys) = C.extension xs ++ C.extension ys := by
  simp [extension, List.map_append, List.flatten_append]

/--
Definition, uniquely decodable source code: the extension `C*` is nonsingular.
-/
def IsUniquelyDecodable (C : SourceCode alpha beta) : Prop :=
  Function.Injective C.extension

/-- The set of codewords associated with a source code. -/
def codewordSet (C : SourceCode alpha beta) : Set (CodeString beta) :=
  Set.range C

/--
The corresponding mathlib codeword-set predicate.  This is useful for later
Kraft-McMillan arguments, while `IsUniquelyDecodable` is the direct textbook
definition on source strings.
-/
def HasUniquelyDecodableCodewordSet (C : SourceCode alpha beta) : Prop :=
  UniquelyDecodable C.codewordSet

/--
Definition, prefix code or instantaneous code: no codeword is a prefix of a
different codeword.
-/
def IsPrefix (C : SourceCode alpha beta) : Prop :=
  forall {x y : alpha}, C x <+: C y -> x = y

/-- Synonym for `IsPrefix`, matching the textbook phrase "prefix code". -/
abbrev IsPrefixCode (C : SourceCode alpha beta) : Prop :=
  C.IsPrefix

/-- Synonym for `IsPrefix`, matching the textbook phrase "instantaneous code". -/
abbrev IsInstantaneous (C : SourceCode alpha beta) : Prop :=
  C.IsPrefix

/-- Synonym for instantaneous codes as self-punctuating codes. -/
abbrev IsSelfPunctuating (C : SourceCode alpha beta) : Prop :=
  C.IsInstantaneous

/-- The inclusion of instantaneous codes among nonsingular codes. -/
theorem isNonsingular_of_isPrefix
    {C : SourceCode alpha beta} (hC : C.IsPrefix) :
    C.IsNonsingular := by
  intro x y hxy
  exact hC (by simp [hxy])

end SourceCode

end InformationTheory
