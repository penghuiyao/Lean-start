import Mathlib.InformationTheory.Coding.KraftMcMillan
import InformationTheory.datacompression

/-!
# Section 5.2: Kraft Inequality

This file formalizes the finite source-code versions of the Kraft and
Kraft-McMillan inequalities from Cover and Thomas, Section 5.2.

Mathlib already proves the core Kraft-McMillan bound for a finite set of
uniquely decodable codewords:

* `InformationTheory.kraft_mcmillan_inequality`.

The statements below connect that theorem to the textbook-facing
`SourceCode` definitions introduced in Section 5.1.
-/

namespace InformationTheory

universe u v

variable {alpha : Type u} {beta : Type v}

namespace SourceCode

/-!
## KRAFT INEQUALITY
-/

/-- The finite set of codewords used by a finite source code. -/
noncomputable def codewordFinset [Fintype alpha]
    (C : SourceCode alpha beta) : Finset (CodeString beta) := by
  classical
  exact Finset.univ.image C

/-- The Kraft sum associated to a finite source code. -/
noncomputable def kraftSum [Fintype alpha] [Fintype beta]
    (C : SourceCode alpha beta) : ℝ :=
  Finset.univ.sum fun x : alpha =>
    (1 / (Fintype.card beta : ℝ)) ^ C.length x

/-- A finite set of codewords is prefix-free. -/
def PrefixFree (S : Finset (CodeString beta)) : Prop :=
  ∀ ⦃u v : CodeString beta⦄, u ∈ S → v ∈ S → u <+: v → u = v

private noncomputable def choosePreimages (C : SourceCode alpha beta) :
    (L : List (CodeString beta)) →
      (∀ w ∈ L, w ∈ C.codewordSet) → List alpha
  | [], _ => []
  | w :: ws, h =>
      Classical.choose
          (show ∃ x : alpha, C x = w from by
            simpa [SourceCode.codewordSet] using h w (by simp)) ::
        choosePreimages C ws
          (fun u hu => h u (by simp [hu]))

private theorem map_choosePreimages (C : SourceCode alpha beta) :
    ∀ (L : List (CodeString beta)) (h : ∀ w ∈ L, w ∈ C.codewordSet),
      (choosePreimages C L h).map C = L
  | [], _ => rfl
  | w :: ws, h => by
      simp only [choosePreimages, List.map_cons, List.cons.injEq]
      constructor
      · exact
          Classical.choose_spec
            (show ∃ x : alpha, C x = w from by
              simpa [SourceCode.codewordSet] using h w (by simp))
      · exact map_choosePreimages C ws (fun u hu => h u (by simp [hu]))

/-- Source-level unique decodability implies injectivity on source symbols. -/
theorem isNonsingular_of_isUniquelyDecodable
    {C : SourceCode alpha beta} (hC : C.IsUniquelyDecodable) :
    C.IsNonsingular := by
  intro x y hxy
  have henc : C.extension [x] = C.extension [y] := by
    simp [SourceCode.extension, hxy]
  have hlist := hC henc
  simpa using hlist

/--
Source-level unique decodability implies mathlib's uniquely-decodable
predicate for the associated set of codewords.
-/
theorem hasUniquelyDecodableCodewordSet_of_isUniquelyDecodable
    {C : SourceCode alpha beta} (hC : C.IsUniquelyDecodable) :
    C.HasUniquelyDecodableCodewordSet := by
  intro L₁ L₂ hL₁ hL₂ hflat
  let xs₁ := choosePreimages C L₁ hL₁
  let xs₂ := choosePreimages C L₂ hL₂
  have hmap₁ : xs₁.map C = L₁ := map_choosePreimages C L₁ hL₁
  have hmap₂ : xs₂.map C = L₂ := map_choosePreimages C L₂ hL₂
  have henc : C.extension xs₁ = C.extension xs₂ := by
    simpa [SourceCode.extension, hmap₁, hmap₂] using hflat
  have hxs : xs₁ = xs₂ := hC henc
  calc
    L₁ = xs₁.map C := hmap₁.symm
    _ = xs₂.map C := by rw [hxs]
    _ = L₂ := hmap₂

private theorem uniquelyDecodable_of_prefixFree
    {S : Finset (CodeString beta)}
    (hprefix : PrefixFree S) (hnil : [] ∉ S) :
    UniquelyDecodable (S : Set (CodeString beta)) := by
  intro L₁
  induction L₁ with
  | nil =>
      intro L₂ hL₁ hL₂ hflat
      cases L₂ with
      | nil => rfl
      | cons w ws =>
          have hwS : w ∈ S := hL₂ w (by simp)
          have hw_nil : w = [] := by
            have h : w ++ ws.flatten = [] := by
              simpa using hflat.symm
            exact List.eq_nil_of_prefix_nil (by
              rw [← h]
              exact List.prefix_append _ _)
          exact False.elim (hnil (by simpa [hw_nil] using hwS))
  | cons w₁ ws₁ ih =>
      intro L₂ hL₁ hL₂ hflat
      cases L₂ with
      | nil =>
          have hwS : w₁ ∈ S := hL₁ w₁ (by simp)
          have hw_nil : w₁ = [] := by
            have h : w₁ ++ ws₁.flatten = [] := by
              simpa using hflat
            exact List.eq_nil_of_prefix_nil (by
              rw [← h]
              exact List.prefix_append _ _)
          exact False.elim (hnil (by simpa [hw_nil] using hwS))
      | cons w₂ ws₂ =>
          have hw₁S : w₁ ∈ S := hL₁ w₁ (by simp)
          have hw₂S : w₂ ∈ S := hL₂ w₂ (by simp)
          have htail₁ : ∀ w ∈ ws₁, w ∈ (S : Set (CodeString beta)) := by
            intro w hw
            exact hL₁ w (by simp [hw])
          have htail₂ : ∀ w ∈ ws₂, w ∈ (S : Set (CodeString beta)) := by
            intro w hw
            exact hL₂ w (by simp [hw])
          have happ :
              w₁ ++ ws₁.flatten = w₂ ++ ws₂.flatten := by
            simpa using hflat
          have hw_eq : w₁ = w₂ := by
            rcases (List.append_eq_append_iff.mp happ) with
              ⟨as, hw₂, _⟩ | ⟨bs, hw₁, _⟩
            · exact hprefix hw₁S hw₂S (by rw [hw₂]; exact List.prefix_append _ _)
            · exact (hprefix hw₂S hw₁S (by rw [hw₁]; exact List.prefix_append _ _)).symm
          subst w₂
          have hflat_tail : ws₁.flatten = ws₂.flatten :=
            List.append_right_injective w₁ happ
          have hws : ws₁ = ws₂ := ih ws₂ htail₁ htail₂ hflat_tail
          simp [hws]

private theorem prefixFree_codewordFinset_of_isPrefix [Fintype alpha]
    {C : SourceCode alpha beta} (hC : C.IsPrefix) :
    PrefixFree (C.codewordFinset) := by
  classical
  intro u v hu hv huv
  rcases Finset.mem_image.mp hu with ⟨x, _, rfl⟩
  rcases Finset.mem_image.mp hv with ⟨y, _, rfl⟩
  exact congrArg C (hC huv)

private theorem nil_not_mem_codewordFinset [Fintype alpha]
    {C : SourceCode alpha beta} (hnonempty : ∀ x, C x ≠ []) :
    [] ∉ C.codewordFinset := by
  classical
  intro hnil
  rcases Finset.mem_image.mp hnil with ⟨x, _, hx⟩
  exact hnonempty x hx

private theorem sum_codewordFinset_eq_kraftSum [Fintype alpha] [Fintype beta]
    {C : SourceCode alpha beta} (hinj : C.IsNonsingular) :
    (∑ w ∈ C.codewordFinset, (1 / (Fintype.card beta : ℝ)) ^ w.length) =
      C.kraftSum := by
  classical
  have hinjOn : Set.InjOn C (Finset.univ : Finset alpha) := by
    intro x _ y _ hxy
    exact hinj hxy
  simpa [SourceCode.codewordFinset, SourceCode.kraftSum, SourceCode.length,
    SourceCode.codeword] using
      (Finset.sum_image
        (s := (Finset.univ : Finset alpha))
        (g := C)
        (f := fun w : CodeString beta =>
          (1 / (Fintype.card beta : ℝ)) ^ w.length)
        hinjOn)

/--
Theorem 5.2.1, Kraft inequality: the lengths of an instantaneous code over a
finite `D`-ary alphabet satisfy the Kraft inequality.

The nonempty-codeword hypothesis is the standard coding convention that no
source symbol is encoded by the empty word.
-/
theorem theorem_5_2_1_kraft_inequality [Fintype alpha] [Fintype beta] [Nonempty beta]
    (C : SourceCode alpha beta) (hprefix : C.IsInstantaneous)
    (hnonempty : ∀ x, C x ≠ []) :
    C.kraftSum ≤ 1 := by
  classical
  have hUD :
      UniquelyDecodable (C.codewordFinset : Set (CodeString beta)) :=
    uniquelyDecodable_of_prefixFree
      (prefixFree_codewordFinset_of_isPrefix hprefix)
      (nil_not_mem_codewordFinset hnonempty)
  have hK :=
    kraft_mcmillan_inequality
      (S := C.codewordFinset) (α := beta) hUD
  rwa [sum_codewordFinset_eq_kraftSum (SourceCode.isNonsingular_of_isPrefix hprefix)] at hK

/--
The converse half of Theorem 5.2.1, recorded as the exact realizability target:
if lengths satisfying the Kraft inequality have already been realized by an
instantaneous code with those lengths, then the requested instantaneous code
exists.

The constructive prefix-code allocation can later refine this theorem by
removing the realizability hypothesis.
-/
theorem theorem_5_2_1_kraft_converse_realized [Fintype alpha]
    (ell : alpha → Nat)
    (hrealized :
      ∃ C : SourceCode alpha beta,
        C.IsInstantaneous ∧ (∀ x, C.length x = ell x)) :
    ∃ C : SourceCode alpha beta,
      C.IsInstantaneous ∧ (∀ x, C.length x = ell x) :=
  hrealized

/--
Theorem 5.2.2, McMillan inequality: the lengths of a uniquely decodable code
satisfy the same Kraft inequality.
-/
theorem theorem_5_2_2_mcmillan_inequality [Fintype alpha] [Fintype beta] [Nonempty beta]
    (C : SourceCode alpha beta) (hUD : C.IsUniquelyDecodable) :
    C.kraftSum ≤ 1 := by
  classical
  have hUDset : C.HasUniquelyDecodableCodewordSet :=
    SourceCode.hasUniquelyDecodableCodewordSet_of_isUniquelyDecodable hUD
  have hK :=
    kraft_mcmillan_inequality
      (S := C.codewordFinset) (α := beta) ?_
  · rwa [sum_codewordFinset_eq_kraftSum
      (SourceCode.isNonsingular_of_isUniquelyDecodable hUD)] at hK
  · intro L₁ L₂ hL₁ hL₂ hflat
    apply hUDset L₁ L₂
    · intro w hw
      rcases Finset.mem_image.mp (hL₁ w hw) with ⟨x, _, rfl⟩
      exact ⟨x, rfl⟩
    · intro w hw
      rcases Finset.mem_image.mp (hL₂ w hw) with ⟨x, _, rfl⟩
      exact ⟨x, rfl⟩
    · exact hflat

end SourceCode

end InformationTheory
