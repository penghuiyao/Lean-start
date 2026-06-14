import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Algebra.BigOperators.Intervals
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

private theorem uniquelyDecodable_of_set_prefixFree
    {S : Set (CodeString beta)}
    (hprefix :
      ∀ ⦃u v : CodeString beta⦄, u ∈ S → v ∈ S → u <+: v → u = v)
    (hnil : [] ∉ S) :
    UniquelyDecodable S := by
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
          have htail₁ : ∀ w ∈ ws₁, w ∈ S := by
            intro w hw
            exact hL₁ w (by simp [hw])
          have htail₂ : ∀ w ∈ ws₂, w ∈ S := by
            intro w hw
            exact hL₂ w (by simp [hw])
          have happ :
              w₁ ++ ws₁.flatten = w₂ ++ ws₂.flatten := by
            simpa using hflat
          have hw_eq : w₁ = w₂ := by
            rcases (List.append_eq_append_iff.mp happ) with
              ⟨s, hw₂, _⟩ | ⟨s, hw₁, _⟩
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

private noncomputable def bigEndianDigits (D n k : Nat) : List Nat :=
  (Nat.digitsAppend D n k).reverse

private theorem bigEndianDigits_length {D n k : Nat} (hD : 1 < D)
    (hk : k < D ^ n) :
    (bigEndianDigits D n k).length = n := by
  simp [bigEndianDigits, Nat.length_digitsAppend hD n hk]

private theorem bigEndianDigits_mem_lt {D n k d : Nat} (hD : 1 < D)
    (hd : d ∈ bigEndianDigits D n k) :
    d < D := by
  rw [bigEndianDigits, List.mem_reverse] at hd
  exact Nat.lt_of_mem_digitsAppend hD n d hd

private theorem ofDigits_digitsAppend (D n k : Nat) :
    Nat.ofDigits D (Nat.digitsAppend D n k) = k := by
  simp [Nat.digitsAppend, Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]

private theorem ofDigits_bigEndian_reverse (D n k : Nat) :
    Nat.ofDigits D (bigEndianDigits D n k).reverse = k := by
  simp [bigEndianDigits, ofDigits_digitsAppend]

private noncomputable def finDigits {D n k : Nat} (hD : 1 < D) :
    List (DaryAlphabet D) :=
  (bigEndianDigits D n k).attach.map
    (fun d => ⟨d.1, bigEndianDigits_mem_lt hD d.2⟩)

private theorem finDigits_length {D n k : Nat} (hD : 1 < D)
    (hk : k < D ^ n) :
    (finDigits (D := D) (n := n) (k := k) hD).length = n := by
  simp [finDigits, bigEndianDigits_length hD hk]

private theorem finDigits_map_val {D n k : Nat} (hD : 1 < D) :
    (finDigits (D := D) (n := n) (k := k) hD).map
      (fun d : DaryAlphabet D => d.val) =
      bigEndianDigits D n k := by
  simp [finDigits]

private theorem bigEndianDigits_prefix_interval
    {D li lj qi qj : Nat} (hD : 1 < D)
    (hqi : qi < D ^ li) (hqj : qj < D ^ lj)
    (hp : bigEndianDigits D li qi <+: bigEndianDigits D lj qj) :
    qi * D ^ (lj - li) ≤ qj ∧
      qj < (qi + 1) * D ^ (lj - li) := by
  let xs := bigEndianDigits D li qi
  let ys := bigEndianDigits D lj qj
  let t := ys.drop xs.length
  have hxs_len : xs.length = li := bigEndianDigits_length hD hqi
  have hys_len : ys.length = lj := bigEndianDigits_length hD hqj
  have hli_le_lj : li ≤ lj := by
    have := hp.length_le
    simpa [xs, ys, hxs_len, hys_len] using this
  have hys_eq : ys = xs ++ t := by
    simpa [xs, ys, t] using List.prefix_append_drop hp
  have ht_len : t.length = lj - li := by
    calc
      t.length = ys.length - xs.length := by
        simp [t, List.length_drop]
      _ = lj - li := by simp [hxs_len, hys_len]
  have ht_digits : ∀ d ∈ t.reverse, d < D := by
    intro d hd
    have hd_t : d ∈ t := by simpa using (List.mem_reverse.mp hd)
    have hd_ys : d ∈ ys := by
      rw [hys_eq]
      exact List.mem_append_right xs hd_t
    exact bigEndianDigits_mem_lt hD (by simpa [ys] using hd_ys)
  have ht_bound : Nat.ofDigits D t.reverse < D ^ (lj - li) := by
    simpa [ht_len] using Nat.ofDigits_lt_base_pow_length hD ht_digits
  have hqj_eq :
      qj = Nat.ofDigits D t.reverse + D ^ (lj - li) * qi := by
    have hrev : ys.reverse = t.reverse ++ xs.reverse := by
      rw [hys_eq, List.reverse_append]
    calc
      qj = Nat.ofDigits D ys.reverse := by
        simpa [ys] using (ofDigits_bigEndian_reverse D lj qj).symm
      _ = Nat.ofDigits D (t.reverse ++ xs.reverse) := by rw [hrev]
      _ = Nat.ofDigits D t.reverse + D ^ t.reverse.length * Nat.ofDigits D xs.reverse := by
        rw [Nat.ofDigits_append]
      _ = Nat.ofDigits D t.reverse + D ^ (lj - li) * qi := by
        simp [List.length_reverse, ht_len, xs, ofDigits_bigEndian_reverse]
  constructor
  · rw [hqj_eq]
    simp [Nat.mul_comm]
  · rw [hqj_eq]
    have hpow_pos : 0 < D ^ (lj - li) := pow_pos (Nat.zero_lt_of_lt hD) _
    nlinarith

private noncomputable def canonicalIndex (D : Nat) {m : Nat}
    (ell : Fin m → Nat) (i : Fin m) : Nat :=
  ∑ j ∈ Finset.Iio i, D ^ (ell i - ell j)

private theorem canonicalIndex_add_one_eq_sum_Iic (D : Nat) {m : Nat}
    (ell : Fin m → Nat) (i : Fin m) :
    canonicalIndex D ell i + 1 =
      ∑ j ∈ Finset.Iic i, D ^ (ell i - ell j) := by
  classical
  rw [Finset.Iic_eq_cons_Iio, Finset.sum_cons]
  simp [canonicalIndex, Nat.add_comm]

private theorem real_pow_mul_inv_pow_eq_pow_sub {D a b : Nat}
    (hD : 1 < D) (hba : b ≤ a) :
    (D : ℝ) ^ a * (1 / (D : ℝ)) ^ b =
      (D : ℝ) ^ (a - b) := by
  have hD0 : (D : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.zero_lt_of_lt hD))
  have hbpow : (D : ℝ) ^ b ≠ 0 := pow_ne_zero _ hD0
  have ha : a = a - b + b := by omega
  calc
    (D : ℝ) ^ a * (1 / (D : ℝ)) ^ b
        = (D : ℝ) ^ a / (D : ℝ) ^ b := by
          rw [div_pow]
          ring
    _ = (D : ℝ) ^ (a - b) := by
      nth_rw 1 [ha]
      rw [pow_add]
      field_simp [hbpow]

private theorem canonicalIndex_lt_pow {D m : Nat} (hD : 1 < D)
    (ell : Fin m → Nat) (hmono : Monotone ell)
    (hK : (∑ i : Fin m, (1 / (D : ℝ)) ^ ell i) ≤ 1)
    (i : Fin m) :
    canonicalIndex D ell i < D ^ ell i := by
  classical
  let f : Fin m → ℝ := fun j => (1 / (D : ℝ)) ^ ell j
  have hpartial_univ :
      (∑ j ∈ Finset.Iic i, f j) ≤ ∑ j : Fin m, f j := by
    simpa using
      (Finset.sum_le_sum_of_subset_of_nonneg
        (s := Finset.Iic i) (t := Finset.univ) (f := f)
        (by intro j hj; simp)
        (by intro j hj hnot; positivity))
  have hpartial : (∑ j ∈ Finset.Iic i, f j) ≤ 1 :=
    hpartial_univ.trans hK
  have hmul :
      (D : ℝ) ^ ell i * (∑ j ∈ Finset.Iic i, f j) ≤
        (D : ℝ) ^ ell i * 1 :=
    mul_le_mul_of_nonneg_left hpartial (by positivity)
  have hreal_eq :
      ((canonicalIndex D ell i + 1 : Nat) : ℝ) =
        (D : ℝ) ^ ell i * (∑ j ∈ Finset.Iic i, f j) := by
    rw [canonicalIndex_add_one_eq_sum_Iic]
    simp only [Nat.cast_sum, Nat.cast_pow]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≤ i := (Finset.mem_Iic.mp hj)
    have hell : ell j ≤ ell i := hmono hji
    change (D : ℝ) ^ (ell i - ell j) =
      (D : ℝ) ^ ell i * (1 / (D : ℝ)) ^ ell j
    exact (real_pow_mul_inv_pow_eq_pow_sub hD hell).symm
  have hreal_le :
      ((canonicalIndex D ell i + 1 : Nat) : ℝ) ≤ (D : ℝ) ^ ell i := by
    calc
      ((canonicalIndex D ell i + 1 : Nat) : ℝ)
          = (D : ℝ) ^ ell i * (∑ j ∈ Finset.Iic i, f j) := hreal_eq
      _ ≤ (D : ℝ) ^ ell i * 1 := hmul
      _ = (D : ℝ) ^ ell i := by ring
  have hreal_le' :
      ((canonicalIndex D ell i + 1 : Nat) : ℝ) ≤
        ((D ^ ell i : Nat) : ℝ) := by
    simpa [Nat.cast_pow] using hreal_le
  have hnat_le : canonicalIndex D ell i + 1 ≤ D ^ ell i := by
    exact_mod_cast hreal_le'
  exact Nat.lt_of_succ_le hnat_le

private theorem pow_sub_mul_pow_sub {D a b c : Nat}
    (hab : a ≤ b) (hbc : b ≤ c) :
    D ^ (b - a) * D ^ (c - b) = D ^ (c - a) := by
  rw [← pow_add]
  congr 1
  omega

private theorem canonicalIndex_lower_of_lt {D m : Nat}
    (ell : Fin m → Nat) (hmono : Monotone ell)
    {i j : Fin m} (hij : i < j) :
    (canonicalIndex D ell i + 1) * D ^ (ell j - ell i) ≤
      canonicalIndex D ell j := by
  classical
  have hsubset : Finset.Iic i ⊆ Finset.Iio j := by
    intro k hk
    exact (Finset.mem_Iio.mpr (lt_of_le_of_lt (Finset.mem_Iic.mp hk) hij))
  calc
    (canonicalIndex D ell i + 1) * D ^ (ell j - ell i)
        = (∑ k ∈ Finset.Iic i, D ^ (ell i - ell k)) *
            D ^ (ell j - ell i) := by
          rw [canonicalIndex_add_one_eq_sum_Iic]
    _ = ∑ k ∈ Finset.Iic i, D ^ (ell j - ell k) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      have hki : k ≤ i := Finset.mem_Iic.mp hk
      have hell_ki : ell k ≤ ell i := hmono hki
      have hell_ij : ell i ≤ ell j := hmono (le_of_lt hij)
      exact pow_sub_mul_pow_sub hell_ki hell_ij
    _ ≤ ∑ k ∈ Finset.Iio j, D ^ (ell j - ell k) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (by intro k hk hnot; positivity)
    _ = canonicalIndex D ell j := by
      rfl

private noncomputable def canonicalKraftCode {D m : Nat} (hD : 1 < D)
    (ell : Fin m → Nat) :
    SourceCode (Fin m) (DaryAlphabet D) :=
  fun i =>
    finDigits (D := D) (n := ell i) (k := canonicalIndex D ell i) hD

private theorem canonicalKraftCode_length {D m : Nat} (hD : 1 < D)
    (ell : Fin m → Nat) (hmono : Monotone ell)
    (hK : (∑ i : Fin m, (1 / (D : ℝ)) ^ ell i) ≤ 1)
    (i : Fin m) :
    (canonicalKraftCode hD ell).length i = ell i := by
  simp [canonicalKraftCode, SourceCode.length, SourceCode.codeword,
    finDigits_length hD (canonicalIndex_lt_pow hD ell hmono hK i)]

private theorem canonicalKraftCode_isInstantaneous {D m : Nat} (hD : 1 < D)
    (ell : Fin m → Nat) (hmono : Monotone ell)
    (hK : (∑ i : Fin m, (1 / (D : ℝ)) ^ ell i) ≤ 1) :
    (canonicalKraftCode hD ell).IsInstantaneous := by
  intro i j hp
  let qi := canonicalIndex D ell i
  let qj := canonicalIndex D ell j
  have hqi : qi < D ^ ell i := canonicalIndex_lt_pow hD ell hmono hK i
  have hqj : qj < D ^ ell j := canonicalIndex_lt_pow hD ell hmono hK j
  have hpNat :
      bigEndianDigits D (ell i) qi <+:
        bigEndianDigits D (ell j) qj := by
    have hmap := hp.map (fun d : DaryAlphabet D => d.val)
    simpa [canonicalKraftCode, qi, qj,
      finDigits_map_val (D := D) (n := ell i) (k := qi) hD,
      finDigits_map_val (D := D) (n := ell j) (k := qj) hD] using hmap
  by_cases hij : i < j
  · have hinterval := bigEndianDigits_prefix_interval hD hqi hqj hpNat
    have hlower :
        (qi + 1) * D ^ (ell j - ell i) ≤ qj :=
      canonicalIndex_lower_of_lt ell hmono hij
    exact False.elim ((not_le_of_gt hinterval.2) hlower)
  · by_cases hji : j < i
    · have hlen_le : ell i ≤ ell j := by
        have := hp.length_le
        simpa [canonicalKraftCode, SourceCode.length, SourceCode.codeword,
          finDigits_length hD hqi, finDigits_length hD hqj] using this
      have hlen_ge : ell j ≤ ell i := hmono (le_of_lt hji)
      have hell_eq : ell i = ell j := le_antisymm hlen_le hlen_ge
      have hinterval := bigEndianDigits_prefix_interval hD hqi hqj hpNat
      have hlower :
          (qj + 1) * D ^ (ell i - ell j) ≤ qi :=
        canonicalIndex_lower_of_lt ell hmono hji
      have hscale1 : D ^ (ell i - ell j) = 1 := by
        rw [hell_eq, Nat.sub_self, pow_zero]
      have hqj_succ_le_qi : qj + 1 ≤ qi := by
        simpa [hscale1] using hlower
      have hqi_le_qj : qi ≤ qj := by
        simpa [hell_eq, Nat.sub_self, pow_zero] using hinterval.1
      omega
    · exact le_antisymm (not_lt.mp hji) (not_lt.mp hij)

/--
The converse half of Theorem 5.2.1, in the textbook's sorted-length form:
if a nondecreasing list of requested lengths satisfies Kraft's inequality,
then there is an instantaneous `D`-ary source code with exactly those lengths.

The construction is the canonical prefix-code allocation: the `i`-th codeword
is the fixed-length `D`-ary representation of the cumulative Kraft interval
assigned to earlier codewords.
-/
theorem theorem_5_2_1_kraft_converse {D m : Nat} (hD : 1 < D)
    (ell : Fin m → Nat) (hmono : Monotone ell)
    (hK : (∑ i : Fin m, (1 / (D : ℝ)) ^ ell i) ≤ 1) :
    ∃ C : SourceCode (Fin m) (DaryAlphabet D),
      C.IsInstantaneous ∧ (∀ i, C.length i = ell i) := by
  refine ⟨canonicalKraftCode hD ell, ?_, ?_⟩
  · exact canonicalKraftCode_isInstantaneous hD ell hmono hK
  · exact canonicalKraftCode_length hD ell hmono hK

/--
A nonempty instantaneous source code is uniquely decodable.

The nonempty-codeword hypothesis is necessary for the source-level definition:
otherwise the empty source string and a one-symbol string encoded by `[]` would
have the same extension.
-/
theorem isUniquelyDecodable_of_isPrefix_nonempty
    {C : SourceCode alpha beta} (hprefix : C.IsPrefix)
    (hnonempty : ∀ x, C x ≠ []) :
    C.IsUniquelyDecodable := by
  classical
  have hUDset :
      UniquelyDecodable C.codewordSet := by
    apply uniquelyDecodable_of_set_prefixFree
    · intro u v hu hv huv
      rcases hu with ⟨x, rfl⟩
      rcases hv with ⟨y, rfl⟩
      exact congrArg C (hprefix huv)
    · intro hnil
      rcases hnil with ⟨x, hx⟩
      exact hnonempty x hx
  intro xs ys hflat
  have hmap : xs.map C = ys.map C := by
    apply hUDset
    · intro w hw
      rcases List.mem_map.mp hw with ⟨x, _, rfl⟩
      exact ⟨x, rfl⟩
    · intro w hw
      rcases List.mem_map.mp hw with ⟨x, _, rfl⟩
      exact ⟨x, rfl⟩
    · simpa [SourceCode.extension] using hflat
  exact (SourceCode.isNonsingular_of_isPrefix hprefix).list_map hmap

/--
Finite-prefix version of Theorem 5.2.2, used as the counting step in the
countably infinite statement below.
-/
theorem theorem_5_2_2_mcmillan_inequality_finite
    [Fintype alpha] [Fintype beta] [Nonempty beta]
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

/--
Theorem 5.2.2, McMillan inequality for a countably infinite family of
codewords: the lengths of a uniquely decodable `D`-ary code indexed by `ℕ`
satisfy the infinite Kraft inequality.

Every finite prefix is a finite uniquely decodable code, so the finite
McMillan bound holds for each partial sum.  The real infinite-sum API then
turns these uniformly bounded nonnegative partial sums into the `tsum` bound.
-/
theorem theorem_5_2_2_mcmillan_inequality {D : Nat} (hD : 1 < D)
    (C : SourceCode Nat (DaryAlphabet D)) (hUD : C.IsUniquelyDecodable) :
    (∑' i : Nat, (1 / (D : ℝ)) ^ C.length i) ≤ 1 := by
  classical
  haveI : Nonempty (DaryAlphabet D) := ⟨⟨0, Nat.zero_lt_of_lt hD⟩⟩
  apply Real.tsum_le_of_sum_range_le
  · intro i
    positivity
  · intro n
    let Cn : SourceCode (Fin n) (DaryAlphabet D) := fun i => C i.val
    have hUDn : Cn.IsUniquelyDecodable := by
      intro xs ys hflat
      have hNat :
          C.extension (xs.map (fun i : Fin n => i.val)) =
            C.extension (ys.map (fun i : Fin n => i.val)) := by
        simpa [SourceCode.extension, Cn] using hflat
      have hxs := hUD hNat
      exact Fin.val_injective.list_map hxs
    have hfinite := theorem_5_2_2_mcmillan_inequality_finite (C := Cn) hUDn
    rw [← Fin.sum_univ_eq_sum_range
      (fun i => (1 / (D : ℝ)) ^ C.length i) n]
    simpa [SourceCode.kraftSum, SourceCode.length, SourceCode.codeword, Cn,
      DaryAlphabet, Fintype.card_fin] using hfinite

private noncomputable def canonicalIndexCountable (D : Nat)
    (ell : Nat → Nat) (i : Nat) : Nat :=
  ∑ j ∈ Finset.range i, D ^ (ell i - ell j)

private theorem canonicalIndexCountable_add_one_eq_sum_range_succ
    (D : Nat) (ell : Nat → Nat) (i : Nat) :
    canonicalIndexCountable D ell i + 1 =
      ∑ j ∈ Finset.range (i + 1), D ^ (ell i - ell j) := by
  rw [Finset.sum_range_succ]
  simp [canonicalIndexCountable, Nat.add_comm]

private theorem canonicalIndexCountable_lt_pow {D : Nat} (hD : 1 < D)
    (ell : Nat → Nat) (hmono : Monotone ell)
    (hsummable : Summable fun i : Nat => (1 / (D : ℝ)) ^ ell i)
    (hK : (∑' i : Nat, (1 / (D : ℝ)) ^ ell i) ≤ 1)
    (i : Nat) :
    canonicalIndexCountable D ell i < D ^ ell i := by
  classical
  let f : Nat → ℝ := fun j => (1 / (D : ℝ)) ^ ell j
  have hpartial_univ :
      (∑ j ∈ Finset.range (i + 1), f j) ≤ ∑' j : Nat, f j := by
    exact Summable.sum_le_tsum
      (s := Finset.range (i + 1)) (f := f)
      (by intro j hj; positivity) hsummable
  have hpartial : (∑ j ∈ Finset.range (i + 1), f j) ≤ 1 :=
    hpartial_univ.trans hK
  have hmul :
      (D : ℝ) ^ ell i * (∑ j ∈ Finset.range (i + 1), f j) ≤
        (D : ℝ) ^ ell i * 1 :=
    mul_le_mul_of_nonneg_left hpartial (by positivity)
  have hreal_eq :
      ((canonicalIndexCountable D ell i + 1 : Nat) : ℝ) =
        (D : ℝ) ^ ell i * (∑ j ∈ Finset.range (i + 1), f j) := by
    rw [canonicalIndexCountable_add_one_eq_sum_range_succ]
    simp only [Nat.cast_sum, Nat.cast_pow]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hell : ell j ≤ ell i := hmono hji
    change (D : ℝ) ^ (ell i - ell j) =
      (D : ℝ) ^ ell i * (1 / (D : ℝ)) ^ ell j
    exact (real_pow_mul_inv_pow_eq_pow_sub hD hell).symm
  have hreal_le :
      ((canonicalIndexCountable D ell i + 1 : Nat) : ℝ) ≤
        (D : ℝ) ^ ell i := by
    calc
      ((canonicalIndexCountable D ell i + 1 : Nat) : ℝ)
          = (D : ℝ) ^ ell i * (∑ j ∈ Finset.range (i + 1), f j) := hreal_eq
      _ ≤ (D : ℝ) ^ ell i * 1 := hmul
      _ = (D : ℝ) ^ ell i := by ring
  have hreal_le' :
      ((canonicalIndexCountable D ell i + 1 : Nat) : ℝ) ≤
        ((D ^ ell i : Nat) : ℝ) := by
    simpa [Nat.cast_pow] using hreal_le
  have hnat_le : canonicalIndexCountable D ell i + 1 ≤ D ^ ell i := by
    exact_mod_cast hreal_le'
  exact Nat.lt_of_succ_le hnat_le

private theorem canonicalIndexCountable_lower_of_lt {D : Nat}
    (ell : Nat → Nat) (hmono : Monotone ell)
    {i j : Nat} (hij : i < j) :
    (canonicalIndexCountable D ell i + 1) * D ^ (ell j - ell i) ≤
      canonicalIndexCountable D ell j := by
  classical
  have hsubset : Finset.range (i + 1) ⊆ Finset.range j := by
    intro k hk
    exact Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hk) (Nat.succ_le_of_lt hij))
  calc
    (canonicalIndexCountable D ell i + 1) * D ^ (ell j - ell i)
        = (∑ k ∈ Finset.range (i + 1), D ^ (ell i - ell k)) *
            D ^ (ell j - ell i) := by
          rw [canonicalIndexCountable_add_one_eq_sum_range_succ]
    _ = ∑ k ∈ Finset.range (i + 1), D ^ (ell j - ell k) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      have hki : k ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hell_ki : ell k ≤ ell i := hmono hki
      have hell_ij : ell i ≤ ell j := hmono (le_of_lt hij)
      exact pow_sub_mul_pow_sub hell_ki hell_ij
    _ ≤ ∑ k ∈ Finset.range j, D ^ (ell j - ell k) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (by intro k hk hnot; positivity)
    _ = canonicalIndexCountable D ell j := by
      rfl

private noncomputable def canonicalKraftCodeCountable {D : Nat} (hD : 1 < D)
    (ell : Nat → Nat) :
    SourceCode Nat (DaryAlphabet D) :=
  fun i =>
    finDigits (D := D) (n := ell i) (k := canonicalIndexCountable D ell i) hD

private theorem canonicalKraftCodeCountable_length {D : Nat} (hD : 1 < D)
    (ell : Nat → Nat) (hmono : Monotone ell)
    (hsummable : Summable fun i : Nat => (1 / (D : ℝ)) ^ ell i)
    (hK : (∑' i : Nat, (1 / (D : ℝ)) ^ ell i) ≤ 1)
    (i : Nat) :
    (canonicalKraftCodeCountable hD ell).length i = ell i := by
  simp [canonicalKraftCodeCountable, SourceCode.length, SourceCode.codeword,
    finDigits_length hD
      (canonicalIndexCountable_lt_pow hD ell hmono hsummable hK i)]

private theorem canonicalKraftCodeCountable_isInstantaneous {D : Nat} (hD : 1 < D)
    (ell : Nat → Nat) (hmono : Monotone ell)
    (hsummable : Summable fun i : Nat => (1 / (D : ℝ)) ^ ell i)
    (hK : (∑' i : Nat, (1 / (D : ℝ)) ^ ell i) ≤ 1) :
    (canonicalKraftCodeCountable hD ell).IsInstantaneous := by
  intro i j hp
  let qi := canonicalIndexCountable D ell i
  let qj := canonicalIndexCountable D ell j
  have hqi : qi < D ^ ell i :=
    canonicalIndexCountable_lt_pow hD ell hmono hsummable hK i
  have hqj : qj < D ^ ell j :=
    canonicalIndexCountable_lt_pow hD ell hmono hsummable hK j
  have hpNat :
      bigEndianDigits D (ell i) qi <+:
        bigEndianDigits D (ell j) qj := by
    have hmap := hp.map (fun d : DaryAlphabet D => d.val)
    simpa [canonicalKraftCodeCountable, qi, qj,
      finDigits_map_val (D := D) (n := ell i) (k := qi) hD,
      finDigits_map_val (D := D) (n := ell j) (k := qj) hD] using hmap
  by_cases hij : i < j
  · have hinterval := bigEndianDigits_prefix_interval hD hqi hqj hpNat
    have hlower :
        (qi + 1) * D ^ (ell j - ell i) ≤ qj :=
      canonicalIndexCountable_lower_of_lt ell hmono hij
    exact False.elim ((not_le_of_gt hinterval.2) hlower)
  · by_cases hji : j < i
    · have hlen_le : ell i ≤ ell j := by
        have := hp.length_le
        simpa [canonicalKraftCodeCountable, SourceCode.length, SourceCode.codeword,
          finDigits_length hD hqi, finDigits_length hD hqj] using this
      have hlen_ge : ell j ≤ ell i := hmono (le_of_lt hji)
      have hell_eq : ell i = ell j := le_antisymm hlen_le hlen_ge
      have hinterval := bigEndianDigits_prefix_interval hD hqi hqj hpNat
      have hlower :
          (qj + 1) * D ^ (ell i - ell j) ≤ qi :=
        canonicalIndexCountable_lower_of_lt ell hmono hji
      have hscale1 : D ^ (ell i - ell j) = 1 := by
        rw [hell_eq, Nat.sub_self, pow_zero]
      have hqj_succ_le_qi : qj + 1 ≤ qi := by
        simpa [hscale1] using hlower
      have hqi_le_qj : qi ≤ qj := by
        simpa [hell_eq, Nat.sub_self, pow_zero] using hinterval.1
      omega
    · exact le_antisymm (not_lt.mp hji) (not_lt.mp hij)

/--
The converse half of Theorem 5.2.2, in the same sorted-length form as the
Kraft converse: if positive requested lengths satisfy Kraft's inequality, then
there is a uniquely decodable `D`-ary source code with exactly those lengths.

The proof uses Theorem 5.2.1 converse to construct an instantaneous code, then
uses the standard fact that nonempty instantaneous codes are uniquely
decodable.
-/
theorem theorem_5_2_2_mcmillan_converse_finite {D m : Nat} (hD : 1 < D)
    (ell : Fin m → Nat) (hmono : Monotone ell)
    (hpositive : ∀ i, 0 < ell i)
    (hK : (∑ i : Fin m, (1 / (D : ℝ)) ^ ell i) ≤ 1) :
    ∃ C : SourceCode (Fin m) (DaryAlphabet D),
      C.IsUniquelyDecodable ∧ (∀ i, C.length i = ell i) := by
  rcases theorem_5_2_1_kraft_converse hD ell hmono hK with
    ⟨C, hprefix, hlength⟩
  refine ⟨C, ?_, hlength⟩
  apply isUniquelyDecodable_of_isPrefix_nonempty hprefix
  intro i hnil
  have hlen_zero : C.length i = 0 := by
    simp [SourceCode.length, SourceCode.codeword, hnil]
  have hell_zero : ell i = 0 := by
    rw [← hlength i]
    exact hlen_zero
  exact (Nat.ne_of_gt (hpositive i)) hell_zero

/--
The converse half of Theorem 5.2.2 for a countably infinite set of requested
lengths.  The lengths are given as a nondecreasing enumeration `ell 0, ell 1,
...`; this is the formal version of the textbook's countable sequence of
lengths after reindexing by nondecreasing length.

If the positive requested lengths have a summable Kraft series with total at
most `1`, then there exists a uniquely decodable `D`-ary source code indexed by
`ℕ` with exactly those lengths.
-/
theorem theorem_5_2_2_mcmillan_converse {D : Nat} (hD : 1 < D)
    (ell : Nat → Nat) (hmono : Monotone ell)
    (hpositive : ∀ i, 0 < ell i)
    (hsummable : Summable fun i : Nat => (1 / (D : ℝ)) ^ ell i)
    (hK : (∑' i : Nat, (1 / (D : ℝ)) ^ ell i) ≤ 1) :
    ∃ C : SourceCode Nat (DaryAlphabet D),
      C.IsUniquelyDecodable ∧ (∀ i, C.length i = ell i) := by
  refine ⟨canonicalKraftCodeCountable hD ell, ?_, ?_⟩
  · apply isUniquelyDecodable_of_isPrefix_nonempty
      (canonicalKraftCodeCountable_isInstantaneous hD ell hmono hsummable hK)
    intro i hnil
    have hlen_zero : (canonicalKraftCodeCountable hD ell).length i = 0 := by
      simp [SourceCode.length, SourceCode.codeword, hnil]
    have hell_zero : ell i = 0 := by
      rw [← canonicalKraftCodeCountable_length hD ell hmono hsummable hK i]
      exact hlen_zero
    exact (Nat.ne_of_gt (hpositive i)) hell_zero
  · intro i
    exact canonicalKraftCodeCountable_length hD ell hmono hsummable hK i

end SourceCode

end InformationTheory
