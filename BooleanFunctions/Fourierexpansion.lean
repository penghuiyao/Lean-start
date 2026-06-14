import BooleanFunctions.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.DeriveFintype

/-!
# Boolean cubes

This file records the concepts from Section 1.1 of Ryan O'Donnell's
*Analysis of Boolean Functions*.

The book starts with Boolean functions

`f : {0, 1}^n -> {0, 1}`,

then quickly switches between several bit representations: `True`/`False`,
`0`/`1`, and `-1`/`1`.  We model the first representation with Lean's `Bool`,
and we introduce a small type `SignBit` for the `{-1, 1}` representation.

The project keeps only two cube names:

* `Cube01 n` for `{0, 1}^n`;
* `SignCube n` for `{-1, 1}^n`.

The book also calls `SignCube n` the Hamming cube, hypercube, `n`-cube,
Boolean cube, or discrete cube.  We record those as comments instead of extra
Lean names, to keep the early code easy to read.
-/

namespace BooleanFunctions

/-! ## Bit representations -/

/-- A bit in the `{0, 1}` or `True`/`False` representation. -/
abbrev Bit01 := Bool

/-- Interpret a `Bool` as a `0`/`1` natural number. -/
def bit01AsNat (b : Bit01) : Nat :=
  if b then 1 else 0

/-- The `{-1, 1}` representation of a bit. -/
inductive SignBit where
  | negOne
  | posOne
  deriving DecidableEq, Repr, BEq, Fintype

namespace SignBit

/-- Interpret a sign bit as an integer. -/
def toInt : SignBit -> Int
  | negOne => -1
  | posOne => 1

/-- Interpret a sign bit as a real number. -/
def toReal : SignBit -> Real
  | negOne => -1
  | posOne => 1

/-- Every sign bit squares to `1` after interpreting it as a real number. -/
@[simp] lemma toReal_mul_self (b : SignBit) :
    b.toReal * b.toReal = (1 : Real) := by
  cases b <;> simp [toReal]

/-- The sign bit corresponding to Boolean false. -/
def falseSign : SignBit :=
  negOne

/-- The sign bit corresponding to Boolean true. -/
def trueSign : SignBit :=
  posOne

/-- Convert a `Bool` into a sign bit using `false |-> -1`, `true |-> 1`. -/
def ofBool (b : Bool) : SignBit :=
  if b then trueSign else falseSign

end SignBit

/-- There are exactly two sign bits. -/
@[simp] lemma card_signBit : Fintype.card SignBit = 2 := by
  rfl

/-! ## Cubes and Boolean functions -/

/-- A length-`n` string over an alphabet `alpha`. -/
abbrev StringOver (alpha : Type) (n : Nat) := Fin n -> alpha

/-- The `{0, 1}^n` Boolean cube. -/
abbrev Cube01 (n : Nat) := StringOver Bit01 n

/--
The `{-1, 1}^n` Boolean cube, the book's most frequent convention.

O'Donnell also calls this the Hamming cube, hypercube, `n`-cube, Boolean cube,
or discrete cube.
-/
abbrev SignCube (n : Nat) := StringOver SignBit n

/-- A function on strings over an alphabet. -/
abbrev CubeFunction (alpha beta : Type) (n : Nat) :=
  StringOver alpha n -> beta

/-- A Boolean function in the `{0, 1}` convention. -/
abbrev BooleanFunction01 (n : Nat) :=
  CubeFunction Bit01 Bit01 n

/-- A Boolean function in the `{-1, 1}` convention. -/
abbrev BooleanFunctionSign (n : Nat) :=
  CubeFunction SignBit SignBit n

/-- The project's default Boolean function convention for now. -/
abbrev BooleanFunction (n : Nat) := BooleanFunction01 n

/-! ## Coordinates and Hamming distance -/

/-- The `i`th coordinate of a string, corresponding to the book's notation `x_i`. -/
def coord {alpha : Type} {n : Nat} (x : StringOver alpha n) (i : Fin n) : alpha :=
  x i

/--
The Hamming distance between two length-`n` strings:
the number of coordinates on which they differ.
-/
def hammingDistance {alpha : Type} [DecidableEq alpha] {n : Nat}
    (x y : StringOver alpha n) : Nat :=
  ((Finset.univ : Finset (Fin n)).filter (fun i => x i ≠ y i)).card

/-- Hamming distance on the `{0, 1}` cube. -/
def hammingDistance01 {n : Nat} (x y : Cube01 n) : Nat :=
  hammingDistance x y

/-- Hamming distance on the `{-1, 1}` cube. -/
def hammingDistanceSign {n : Nat} (x y : SignCube n) : Nat :=
  hammingDistance x y

/-!
## Section 1.2. Fourier expansion: functions as multilinear polynomials

O'Donnell next works mainly with the `{-1, 1}` cube and real-valued functions
`f : {-1, 1}^n -> R`.

Now that mathlib is available, we use its standard `Real`, `Finset`, finite
products, and finite sums.
-/

/-! ### Subsets of coordinates and monomials -/

/--
A subset `S` of `[n]`, represented as a finite set of coordinates.

In the book this indexes the monomial `x_S = prod_{i in S} x_i`.
-/
abbrev CoordinateSet (n : Nat) := Finset (Fin n)

/-- The empty subset of `[n]`. -/
def emptyCoordinateSet {n : Nat} : CoordinateSet n :=
  ∅

/-- The full subset of `[n]`. -/
def fullCoordinateSet {n : Nat} : CoordinateSet n :=
  Finset.univ

/-- The singleton subset `{i}` of `[n]`. -/
def singletonCoordinateSet {n : Nat} (i : Fin n) : CoordinateSet n :=
  {i}

/-- Membership of a coordinate in a coordinate subset. -/
def coordinateMem {n : Nat} (i : Fin n) (S : CoordinateSet n) : Prop :=
  i ∈ S

/--
The real-valued character/monomial `chi_S(x) = prod_{i in S} x_i`.

The empty product is `1`, so this includes the convention `x_empty = 1`.
-/
def chiSign {n : Nat} (S : CoordinateSet n) (x : SignCube n) : Real :=
  S.prod (fun i => (x i).toReal)

/-- ASCII alias for `chiSign`, matching the book's notation `x_S`. -/
def monomialReal {n : Nat} (S : CoordinateSet n) (x : SignCube n) : Real :=
  chiSign S x

/-! ### Functions, coefficients, and spectra -/

/-- A real-valued function on the `{-1, 1}` cube. -/
abbrev RealValuedBooleanFunction (n : Nat) := SignCube n -> Real

/--
A multilinear polynomial on `n` sign variables, represented by its coefficient
table. The value at `S` is the coefficient of the monomial `x_S`.
-/
abbrev MultilinearPolynomial (n : Nat) := CoordinateSet n -> Real

/-- The Fourier expansion of a function, represented as its coefficient table. -/
abbrev FourierExpansion (n : Nat) := MultilinearPolynomial n

/-- The Fourier coefficient `fhat(S)` attached to a coordinate subset `S`. -/
def fourierCoeff {n : Nat} (p : FourierExpansion n) (S : CoordinateSet n) : Real :=
  p S

/-- The Fourier spectrum: the whole table of Fourier coefficients. -/
def fourierSpectrum {n : Nat} (p : FourierExpansion n) : CoordinateSet n -> Real :=
  p

/--
Evaluate the multilinear polynomial `p` at a cube point `x`:
`sum_S p(S) * chi_S(x)`.
-/
def evalMultilinearPolynomial {n : Nat}
    (p : MultilinearPolynomial n) (x : SignCube n) : Real :=
  Finset.univ.sum (fun S : CoordinateSet n => p S * chiSign S x)

/-! ### The point-indicator interpolation polynomial -/

/--
The factor `(1 + a_i x_i) / 2` from the interpolation polynomial for a point
`a` in `{-1, 1}^n`.
-/
noncomputable def pointIndicatorFactor (a x : SignBit) : Real :=
  (1 + a.toReal * x.toReal) / 2

/--
The indicator polynomial `1_a(x) = prod_i (1 + a_i x_i) / 2`.

On cube inputs it evaluates to `1` when `x = a` and to `0` otherwise. We only
define the expression here; the proof of this property belongs in a later file.
-/
noncomputable def pointIndicatorPolynomial {n : Nat} (a x : SignCube n) : Real :=
  Finset.univ.prod (fun i : Fin n => pointIndicatorFactor (a i) (x i))

/-! ### Encoding `F_2` bits by signs -/

/-- The field `F_2`, represented by mathlib as integers modulo `2`. -/
abbrev F2 := ZMod 2

/-- The cube `F_2^n`. -/
abbrev CubeF2 (n : Nat) := StringOver F2 n

/--
The one-bit character `chi : F_2 -> Real` from the book:
`chi(0) = 1` and `chi(1) = -1`.
-/
def chiF2Bit (b : F2) : Real :=
  if b = 0 then 1 else -1

/-- Coordinatewise addition on `F_2^n`. -/
def addCubeF2 {n : Nat} (x y : CubeF2 n) : CubeF2 n :=
  fun i => x i + y i

/--
The character `chi_S : F_2^n -> Real`, defined by
`chi_S(x) = prod_{i in S} chi(x_i)`.
-/
def chiF2 {n : Nat} (S : CoordinateSet n) (x : CubeF2 n) : Real :=
  S.prod (fun i => chiF2Bit (x i))

/-! ### Running examples from Section 1.2 -/

/-- The two-bit maximum function in the `{-1, 1}` convention. -/
def max2 (x : SignCube 2) : SignBit :=
  if x 0 = SignBit.negOne && x 1 = SignBit.negOne then
    SignBit.negOne
  else
    SignBit.posOne

/-- Real-valued version of `max2`. -/
def max2Real (x : SignCube 2) : Real :=
  (max2 x).toReal

/-- The three-bit majority function in the `{-1, 1}` convention. -/
def maj3 (x : SignCube 3) : SignBit :=
  if 0 < (x 0).toInt + (x 1).toInt + (x 2).toInt then
    SignBit.posOne
  else
    SignBit.negOne

/-- Real-valued version of `maj3`. -/
def maj3Real (x : SignCube 3) : Real :=
  (maj3 x).toReal


/-!
## Section 1.3. The Orthonormal Basis of Parity Functions

Section 1.3 views the parity functions `chi_S` as vectors in the real vector
space of all functions `{-1, 1}^n -> R`.  The book introduces the normalized
inner product

`<f, g> = 2^{-n} * sum_x f x * g x`.

The unnormalized bilinear form `cubeSumInner` is also useful internally, since
it avoids carrying the factor `2^{-n}` in linear independence proofs.
-/

/-! ### The vector space of functions and the parity family -/

/-- The parity function indexed by `S`, viewed as a vector in function space. -/
def parityFunction {n : Nat} (S : CoordinateSet n) : RealValuedBooleanFunction n :=
  fun x => chiSign S x

/-- The family `S |-> chi_S`, indexed by subsets of `[n]`. -/
noncomputable def fourierCharacters (n : Nat) :
    CoordinateSet n -> RealValuedBooleanFunction n :=
  fun S x => chiSign S x

/-! ### Expectations and inner products on the uniform cube -/

/--
The uniform expectation over the sign cube:
`E[f] = 2^{-n} * sum_x f x`.

This formalizes the notation `x ~ {-1, 1}^n` and `E_x[f x]` from Notation 1.4.
-/
noncomputable def cubeExpectation {n : Nat} (f : RealValuedBooleanFunction n) : Real :=
  ((2 : Real) ^ n)⁻¹ * Finset.univ.sum (fun x : SignCube n => f x)

/--
The normalized inner product from Definition 1.3:
`<f, g> = E[f g]`.
-/
noncomputable def cubeInner {n : Nat}
    (f g : RealValuedBooleanFunction n) : Real :=
  cubeExpectation (fun x : SignCube n => f x * g x)

/-- The `L^2` norm from Definition 1.3. -/
noncomputable def cubeL2Norm {n : Nat} (f : RealValuedBooleanFunction n) : Real :=
  Real.sqrt (cubeInner f f)

/--
The `p`th absolute moment `E[|f|^p]`, the inside of the book's `L^p` norm.

For this early file we keep `p : Nat` to avoid importing the heavier real-power
API.  Later chapters can wrap this with real powers when `L^p` inequalities
are needed.
-/
noncomputable def cubeLpMoment {n : Nat} (p : Nat)
    (f : RealValuedBooleanFunction n) : Real :=
  cubeExpectation (fun x : SignCube n => |f x| ^ p)

/--
The unnormalized bilinear form `sum_x f x * g x`.

This is not the book's normalized inner product, but it is convenient for
finite-dimensional linear algebra proofs.  Multiplying it by `2^{-n}` gives
`cubeInner`.
-/
noncomputable def cubeSumInner (n : Nat) :
    LinearMap.BilinForm Real (RealValuedBooleanFunction n) where
  toFun := fun f =>
    { toFun := fun g => Finset.univ.sum (fun x : SignCube n => f x * g x)
      map_add' := by
        intro g h
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a g
        change Finset.univ.sum (fun x : SignCube n => f x * (a * g x)) =
          a * Finset.univ.sum (fun x : SignCube n => f x * g x)
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _hx
        simp [mul_left_comm] }
  map_add' := by
    intro f g
    apply LinearMap.ext
    intro h
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro a f
    apply LinearMap.ext
    intro g
    change Finset.univ.sum (fun x : SignCube n => (a * f x) * g x) =
      a * Finset.univ.sum (fun x : SignCube n => f x * g x)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _hx
    simp [mul_assoc]

/-! ### Products and expectations of parity functions -/

/--
The one-coordinate factor in `chi_S(x) * chi_T(x)`.

It is `x_i` when `i` lies in the symmetric difference of `S` and `T`, and `1`
otherwise.
-/
def characterProductFactor {n : Nat} (S T : CoordinateSet n) (i : Fin n)
    (b : SignBit) : Real :=
  if i ∈ symmDiff S T then b.toReal else 1

/-- Multiplying the two coordinate factors gives `characterProductFactor`. -/
lemma sign_factor_mul {n : Nat} (S T : CoordinateSet n) (i : Fin n)
    (b : SignBit) :
    (if i ∈ S then b.toReal else 1) * (if i ∈ T then b.toReal else 1) =
      characterProductFactor S T i b := by
  classical
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
    simp [characterProductFactor, Finset.mem_symmDiff, hS, hT]

/--
Rewrite `chiSign S x`, originally a product over `S`, as a product over all
coordinates with trivial factors outside `S`.
-/
lemma chiSign_eq_prod_univ {n : Nat} (S : CoordinateSet n) (x : SignCube n) :
    chiSign S x =
      Finset.univ.prod (fun i : Fin n => if i ∈ S then (x i).toReal else 1) := by
  classical
  simp [chiSign]

/-- Factor `chi_S(x) * chi_T(x)` coordinate by coordinate. -/
lemma chiSign_mul_eq_prod_factor {n : Nat} (S T : CoordinateSet n)
    (x : SignCube n) :
    chiSign S x * chiSign T x =
      Finset.univ.prod (fun i : Fin n => characterProductFactor S T i (x i)) := by
  classical
  rw [chiSign_eq_prod_univ S x, chiSign_eq_prod_univ T x]
  rw [<- Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _hi
  exact sign_factor_mul S T i (x i)

/--
Fact 1.6 at the level of functions:
`chi_S(x) * chi_T(x) = chi_{S ∆ T}(x)`.
-/
lemma chiSign_mul_symmDiff {n : Nat} (S T : CoordinateSet n)
    (x : SignCube n) :
    chiSign S x * chiSign T x = chiSign (symmDiff S T) x := by
  classical
  rw [chiSign_mul_eq_prod_factor S T x, chiSign_eq_prod_univ (symmDiff S T) x]
  apply Finset.prod_congr rfl
  intro i _hi
  by_cases h : i ∈ symmDiff S T <;>
    simp [characterProductFactor, h]

/--
The sum of a one-coordinate factor over the two signs is `0` when the
coordinate lies in `S ∆ T`, and `2` otherwise.
-/
lemma sign_factor_sum {n : Nat} (S T : CoordinateSet n) (i : Fin n) :
    (Finset.univ.sum (fun b : SignBit => characterProductFactor S T i b)) =
      (if i ∈ symmDiff S T then 0 else 2) := by
  classical
  change (({SignBit.negOne, SignBit.posOne} : Finset SignBit).sum
      (fun b : SignBit => characterProductFactor S T i b)) =
    (if i ∈ symmDiff S T then 0 else 2)
  by_cases h : i ∈ symmDiff S T <;> simp [characterProductFactor, h, SignBit.toReal]

/--
Turn a sum over all cube points of a product of coordinate factors into a
product of one-coordinate sums.

This is the finite-product version of independence of coordinates.
-/
lemma sum_prod_factor {n : Nat} (S T : CoordinateSet n) :
    (Finset.univ.sum (fun x : SignCube n =>
      Finset.univ.prod (fun i : Fin n => characterProductFactor S T i (x i)))) =
    Finset.univ.prod (fun i : Fin n =>
      Finset.univ.sum (fun b : SignBit => characterProductFactor S T i b)) := by
  classical
  rw [<- Fintype.piFinset_univ]
  exact Finset.sum_prod_piFinset (s := (Finset.univ : Finset SignBit))
    (g := fun i b => characterProductFactor S T i b)

/-- The unnormalized inner product of two characters factors into coordinates. -/
lemma character_inner_factor {n : Nat} (S T : CoordinateSet n) :
    (Finset.univ.sum (fun x : SignCube n => chiSign S x * chiSign T x)) =
    Finset.univ.prod (fun i : Fin n =>
      Finset.univ.sum (fun b : SignBit => characterProductFactor S T i b)) := by
  classical
  calc
    (Finset.univ.sum (fun x : SignCube n => chiSign S x * chiSign T x)) =
        Finset.univ.sum (fun x : SignCube n =>
          Finset.univ.prod (fun i : Fin n => characterProductFactor S T i (x i))) := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact chiSign_mul_eq_prod_factor S T x
    _ = Finset.univ.prod (fun i : Fin n =>
          Finset.univ.sum (fun b : SignBit => characterProductFactor S T i b)) :=
      sum_prod_factor S T

/-- If `S ≠ T`, some coordinate lies in their symmetric difference. -/
lemma exists_mem_symmDiff_of_ne {n : Nat} {S T : CoordinateSet n} (hST : S ≠ T) :
    ∃ i : Fin n, i ∈ symmDiff S T := by
  simpa [Finset.Nonempty] using (Finset.symmDiff_nonempty (s := S) (t := T)).2 hST

/-- Distinct characters are orthogonal for the unnormalized sum. -/
lemma character_inner_ne {n : Nat} {S T : CoordinateSet n} (hST : S ≠ T) :
    (Finset.univ.sum (fun x : SignCube n => chiSign S x * chiSign T x)) = 0 := by
  classical
  rcases exists_mem_symmDiff_of_ne hST with ⟨i, hi⟩
  rw [character_inner_factor S T]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by
    rw [sign_factor_sum]
    simp [hi])

/-- A character has unnormalized squared norm `2^n`. -/
lemma character_inner_self {n : Nat} (S : CoordinateSet n) :
    (Finset.univ.sum (fun x : SignCube n => chiSign S x * chiSign S x)) =
      (2 : Real) ^ n := by
  classical
  rw [character_inner_factor S S]
  simp [sign_factor_sum]

/--
Fact 1.7:
the uniform expectation of `chi_S` is `1` for `S = ∅` and `0` otherwise.
-/
lemma cubeExpectation_chiSign {n : Nat} (S : CoordinateSet n) :
    cubeExpectation (fun x : SignCube n => chiSign S x) =
      if S = ∅ then 1 else 0 := by
  classical
  by_cases hS : S = ∅
  · subst S
    have hsum :
        (Finset.univ.sum (fun x : SignCube n => chiSign (∅ : CoordinateSet n) x)) =
          (2 : Real) ^ n := by
      simp [chiSign]
    rw [cubeExpectation, hsum]
    exact inv_mul_cancel₀ (pow_ne_zero n (by exact two_ne_zero : (2 : Real) ≠ 0))
  · have hsum :
        (Finset.univ.sum (fun x : SignCube n => chiSign S x)) = 0 := by
      have h := character_inner_ne (S := S) (T := (∅ : CoordinateSet n)) hS
      simpa [chiSign] using h
    simp [cubeExpectation, hsum, hS]

/-- The parity functions are orthonormal for the normalized inner product. -/
lemma fourierCharacters_orthonormal {n : Nat} (S T : CoordinateSet n) :
    cubeInner (fourierCharacters n S) (fourierCharacters n T) =
      if S = T then 1 else 0 := by
  classical
  by_cases hST : S = T
  · subst T
    have hsum :
        (Finset.univ.sum (fun x : SignCube n => chiSign S x * chiSign S x)) =
          (2 : Real) ^ n :=
      character_inner_self S
    simp [cubeInner, cubeExpectation, fourierCharacters, hsum]
  · have hsum :
        (Finset.univ.sum (fun x : SignCube n => chiSign S x * chiSign T x)) = 0 :=
      character_inner_ne hST
    simp [cubeInner, cubeExpectation, fourierCharacters, hsum, hST]

/-! ### The character basis -/

/-- The characters `chi_S` are linearly independent. -/
lemma fourierCharacters_linearIndependent (n : Nat) :
    LinearIndependent Real (fourierCharacters n) := by
  classical
  exact LinearMap.BilinForm.linearIndependent_of_iIsOrtho
    (B := cubeSumInner n)
    (by
      intro S T hST
      change (Finset.univ.sum (fun x : SignCube n => chiSign S x * chiSign T x)) = 0
      exact character_inner_ne hST)
    (by
      intro S hS
      change (Finset.univ.sum (fun x : SignCube n => chiSign S x * chiSign S x)) = 0 at hS
      rw [character_inner_self S] at hS
      exact (pow_ne_zero n (by exact two_ne_zero : (2 : Real) ≠ 0)) hS)

/--
The character basis of all real-valued functions on `{-1,1}^n`.

The dimension count is:
`#(subsets of [n]) = 2^n = #({-1,1}^n)`.
-/
noncomputable def fourierCharacterBasis (n : Nat) :
    Module.Basis (CoordinateSet n) Real (RealValuedBooleanFunction n) :=
  basisOfLinearIndependentOfCardEqFinrank'
    (fourierCharacters n)
    (fourierCharacters_linearIndependent n)
    (by
      rw [Module.finrank_fintype_fun_eq_card]
      simp [CoordinateSet, SignCube, StringOver])

/-- Evaluating the basis vector indexed by `S` gives the character `chi_S`. -/
lemma fourierCharacterBasis_apply {n : Nat} (S : CoordinateSet n)
    (x : SignCube n) :
    fourierCharacterBasis n S x = chiSign S x := by
  simp [fourierCharacterBasis, fourierCharacters]


/-!
## Section 1.4. Basic Fourier Formulas

Section 1.4 collects the basic formulas following from the orthonormal parity
basis.  The definitions below name the objects that appear in those formulas:
Fourier coefficients of functions, Boolean distance, mean, variance,
covariance, and Fourier weights.
-/

/-! ### Fourier coefficients of functions -/

/--
The Fourier coefficient `fhat(S)` of a real-valued function `f`.

This is the `S` coordinate of `f` in the character basis.  Proposition 1.8 will
show that this is also `<f, chi_S>`.
-/
noncomputable def functionFourierCoeff {n : Nat}
    (f : RealValuedBooleanFunction n) (S : CoordinateSet n) : Real :=
  (fourierCharacterBasis n).repr f S

/-- The full Fourier spectrum of a real-valued function. -/
noncomputable def functionFourierSpectrum {n : Nat}
    (f : RealValuedBooleanFunction n) : CoordinateSet n -> Real :=
  fun S => functionFourierCoeff f S

/-! ### Boolean distances and probabilities -/

/-- A cube event, measured with the uniform probability on `{-1, 1}^n`. -/
noncomputable def cubeProbability {n : Nat} (event : SignCube n -> Prop)
    [DecidablePred event] : Real :=
  cubeExpectation (fun x : SignCube n => if event x then 1 else 0)

/-- Interpret a `{-1, 1}`-valued Boolean function as a real-valued function. -/
def signFunctionToReal {n : Nat} (f : BooleanFunctionSign n) :
    RealValuedBooleanFunction n :=
  fun x => (f x).toReal

/-- The constant `{-1, 1}`-valued Boolean function. -/
def constantSignFunction {n : Nat} (b : SignBit) : BooleanFunctionSign n :=
  fun _ => b

/-- The probability that two sign-valued Boolean functions agree. -/
noncomputable def signFunctionAgreeProbability {n : Nat}
    (f g : BooleanFunctionSign n) : Real :=
  cubeProbability (fun x : SignCube n => f x = g x)

/-- The probability that two sign-valued Boolean functions disagree. -/
noncomputable def signFunctionDisagreeProbability {n : Nat}
    (f g : BooleanFunctionSign n) : Real :=
  cubeProbability (fun x : SignCube n => f x ≠ g x)

/-- Definition 1.10: relative Hamming distance between Boolean functions. -/
noncomputable def signFunctionDistance {n : Nat}
    (f g : BooleanFunctionSign n) : Real :=
  signFunctionDisagreeProbability f g

/-- The probability that a sign-valued Boolean function takes a given sign. -/
noncomputable def signValueProbability {n : Nat}
    (f : BooleanFunctionSign n) (b : SignBit) : Real :=
  cubeProbability (fun x : SignCube n => f x = b)

/-- Distance from `f` to the constant function with value `b`. -/
noncomputable def signFunctionDistanceToConstant {n : Nat}
    (f : BooleanFunctionSign n) (b : SignBit) : Real :=
  signFunctionDistance f (constantSignFunction b)

/--
The smaller distance from `f` to one of the two constant sign functions.

This is the `epsilon` appearing in Proposition 1.15.
-/
noncomputable def signFunctionDistanceFromConstant {n : Nat}
    (f : BooleanFunctionSign n) : Real :=
  min (signFunctionDistanceToConstant f SignBit.posOne)
      (signFunctionDistanceToConstant f SignBit.negOne)

/-! ### Mean, variance, and covariance -/

/-- Definition 1.11: the mean of a real-valued Boolean function. -/
noncomputable def cubeMean {n : Nat} (f : RealValuedBooleanFunction n) : Real :=
  cubeExpectation f

/-- A function is unbiased, or balanced, when its mean is zero. -/
def IsUnbiased {n : Nat} (f : RealValuedBooleanFunction n) : Prop :=
  cubeMean f = 0

/-- Definition 1.11 synonym: balanced means unbiased. -/
abbrev IsBalanced {n : Nat} (f : RealValuedBooleanFunction n) : Prop :=
  IsUnbiased f

/-- The centered version `f - E[f]`. -/
noncomputable def centeredFunction {n : Nat}
    (f : RealValuedBooleanFunction n) : RealValuedBooleanFunction n :=
  fun x => f x - cubeMean f

/-- Proposition 1.13 definition: variance as the squared norm of `f - E[f]`. -/
noncomputable def cubeVariance {n : Nat} (f : RealValuedBooleanFunction n) : Real :=
  cubeInner (centeredFunction f) (centeredFunction f)

/-- Proposition 1.16 definition: covariance as an inner product of centered functions. -/
noncomputable def cubeCovariance {n : Nat}
    (f g : RealValuedBooleanFunction n) : Real :=
  cubeInner (centeredFunction f) (centeredFunction g)

/-! ### Fourier weights and level decompositions -/

/-- Definition 1.17: Fourier weight on a set `S`, namely `fhat(S)^2`. -/
noncomputable def fourierWeight {n : Nat}
    (f : RealValuedBooleanFunction n) (S : CoordinateSet n) : Real :=
  functionFourierCoeff f S ^ 2

/--
Definition 1.18: the spectral sample weight table of a Boolean function.

For Boolean-valued functions, Parseval says this table sums to `1`, so it is a
probability distribution on coordinate subsets.
-/
noncomputable def spectralSampleWeight {n : Nat}
    (f : BooleanFunctionSign n) (S : CoordinateSet n) : Real :=
  fourierWeight (signFunctionToReal f) S

/-- Definition 1.19: Fourier weight at degree `k`. -/
noncomputable def fourierWeightAtDegree {n : Nat}
    (f : RealValuedBooleanFunction n) (k : Nat) : Real :=
  Finset.univ.sum (fun S : CoordinateSet n =>
    if S.card = k then fourierWeight f S else 0)

/-- The degree-`k` part `f_{=k}` of a function. -/
noncomputable def degreePart {n : Nat}
    (f : RealValuedBooleanFunction n) (k : Nat) : RealValuedBooleanFunction n :=
  fun x => Finset.univ.sum (fun S : CoordinateSet n =>
    if S.card = k then functionFourierCoeff f S * chiSign S x else 0)

/-- Fourier weight above degree `k`, written `W_{>k}[f]` in the book. -/
noncomputable def fourierWeightAboveDegree {n : Nat}
    (f : RealValuedBooleanFunction n) (k : Nat) : Real :=
  Finset.univ.sum (fun S : CoordinateSet n =>
    if k < S.card then fourierWeight f S else 0)

/-- The low-degree part `f_{<=k}` of a function. -/
noncomputable def degreeAtMostPart {n : Nat}
    (f : RealValuedBooleanFunction n) (k : Nat) : RealValuedBooleanFunction n :=
  fun x => Finset.univ.sum (fun S : CoordinateSet n =>
    if S.card ≤ k then functionFourierCoeff f S * chiSign S x else 0)

/-!
## Section 1.5. Probability Densities and Convolution

Section 1.5 switches to the additive cube `F_2^n`.  Addition in `F_2^n`
models subtraction as well, since every element is its own negative.
-/

/-! ### Real-valued functions and expectations on `F_2^n` -/

/-- A real-valued function on the additive cube `F_2^n`. -/
abbrev RealValuedF2Function (n : Nat) := CubeF2 n -> Real

/-- Uniform expectation over `F_2^n`. -/
noncomputable def f2Expectation {n : Nat} (f : RealValuedF2Function n) : Real :=
  ((2 : Real) ^ n)⁻¹ * Finset.univ.sum (fun x : CubeF2 n => f x)

/-- The normalized inner product on functions `F_2^n -> R`. -/
noncomputable def f2Inner {n : Nat}
    (f g : RealValuedF2Function n) : Real :=
  f2Expectation (fun x => f x * g x)

/-! ### Probability densities -/

/--
Definition 1.20: a probability density on `F_2^n`.

The value `phi x` is a density relative to the uniform measure, so the actual
probability mass at `x` is `phi x / 2^n`.
-/
def IsProbabilityDensityF2 {n : Nat} (phi : RealValuedF2Function n) : Prop :=
  (∀ x, 0 ≤ phi x) ∧ f2Expectation phi = 1

/-- The probability mass assigned to one point by a density. -/
noncomputable def densityPointProbabilityF2 {n : Nat}
    (phi : RealValuedF2Function n) (y : CubeF2 n) : Real :=
  phi y * ((2 : Real) ^ n)⁻¹

/-- Expectation with respect to a density `phi`. -/
noncomputable def densityExpectationF2 {n : Nat}
    (phi g : RealValuedF2Function n) : Real :=
  f2Expectation (fun y => phi y * g y)

/-! ### Indicators and subset densities -/

/-- The indicator function of a finite subset of `F_2^n`. -/
def indicatorF2Set {n : Nat} (A : Finset (CubeF2 n)) :
    RealValuedF2Function n :=
  fun x => if x ∈ A then 1 else 0

/--
Definition 1.22: the density associated to a nonempty subset `A`.

When `A` is nonempty, this is `(1 / E[1_A]) * 1_A`, i.e. the uniform
distribution on the points of `A`, expressed as a density relative to the
uniform measure on the whole cube.
-/
noncomputable def uniformSubsetDensityF2 {n : Nat}
    (A : Finset (CubeF2 n)) : RealValuedF2Function n :=
  fun x => (f2Expectation (indicatorF2Set A))⁻¹ * indicatorF2Set A x

/-- The zero element of `F_2^n`. -/
def zeroCubeF2 {n : Nat} : CubeF2 n :=
  fun _ => 0

/-- The density of a singleton `{a}` in `F_2^n`. -/
noncomputable def singletonDensityF2 {n : Nat}
    (a : CubeF2 n) : RealValuedF2Function n :=
  fun x => if x = a then (2 : Real) ^ n else 0

/-- The density of the singleton `{0}` in `F_2^n`. -/
noncomputable def singletonZeroDensityF2 {n : Nat} : RealValuedF2Function n :=
  singletonDensityF2 zeroCubeF2

/-! ### Convolution and Fourier transform on `F_2^n` -/

/--
Definition 1.24: convolution on `F_2^n`.

The book writes `x - y`; in `F_2^n` this is the same point as `x + y`.
-/
noncomputable def convolutionF2 {n : Nat}
    (f g : RealValuedF2Function n) : RealValuedF2Function n :=
  fun x => f2Expectation (fun y => f y * g (addCubeF2 x y))

/-- The Fourier coefficient of a function on `F_2^n`. -/
noncomputable def f2FourierCoeff {n : Nat}
    (f : RealValuedF2Function n) (S : CoordinateSet n) : Real :=
  f2Expectation (fun x => f x * chiF2 S x)

/-- Evaluate a Fourier expansion on `F_2^n` from an arbitrary coefficient table. -/
noncomputable def evalF2FourierExpansion {n : Nat}
    (coeff : CoordinateSet n -> Real) (x : CubeF2 n) : Real :=
  Finset.univ.sum (fun S : CoordinateSet n => coeff S * chiF2 S x)

/-!
## Section 1.6. Almost Linear Functions and the BLR Test

Section 1.6 studies functions `f : F_2^n -> F_2`.  This part of
`Fourierexpansion.lean` records the basic definitions before the BLR test
itself: linear functions, relative distance, and `epsilon`-closeness to
linearity.
-/

/-! ### Linear functions over `F_2` -/

/-- A Boolean-valued function on the additive cube `F_2^n`. -/
abbrev F2BooleanFunction (n : Nat) := CubeF2 n -> F2

/-- The dot product `a . x` over `F_2`. -/
def dotF2 {n : Nat} (a x : CubeF2 n) : F2 :=
  Finset.univ.sum (fun i : Fin n => a i * x i)

/-- The linear function `x |-> a . x` over `F_2`. -/
def linearF2ByVector {n : Nat} (a : CubeF2 n) :
    F2BooleanFunction n :=
  fun x => dotF2 a x

/-- The linear function `x |-> sum_{i in S} x_i` over `F_2`. -/
def linearF2BySet {n : Nat} (S : CoordinateSet n) :
    F2BooleanFunction n :=
  fun x => S.sum (fun i => x i)

/-- Definition 1.28: linearity as additivity over `F_2^n`. -/
def IsLinearF2Function {n : Nat} (f : F2BooleanFunction n) : Prop :=
  ∀ x y : CubeF2 n, f (addCubeF2 x y) = f x + f y

/-- The property of being linear. -/
def LinearF2Property (n : Nat) : Set (F2BooleanFunction n) :=
  {f | IsLinearF2Function f}

/-! ### Distance and approximate linearity -/

/-- A uniform probability on `F_2^n`, written as an expectation of an indicator. -/
noncomputable def f2Probability {n : Nat} (event : CubeF2 n -> Prop)
    [DecidablePred event] : Real :=
  f2Expectation (fun x : CubeF2 n => if event x then 1 else 0)

/-- Relative Hamming distance between two `F_2`-valued Boolean functions. -/
noncomputable def f2BooleanDistance {n : Nat}
    (f g : F2BooleanFunction n) : Real :=
  by
    classical
    exact f2Probability (fun x : CubeF2 n => f x ≠ g x)

/-- A property of `F_2`-valued Boolean functions. -/
abbrev F2FunctionProperty (n : Nat) := Set (F2BooleanFunction n)

/-- Definition 1.29: `f` and `g` are `epsilon`-close. -/
def IsEpsilonCloseF2 {n : Nat} (epsilon : Real)
    (f g : F2BooleanFunction n) : Prop :=
  f2BooleanDistance f g ≤ epsilon

/-- Definition 1.29: `f` and `g` are `epsilon`-far. -/
def IsEpsilonFarF2 {n : Nat} (epsilon : Real)
    (f g : F2BooleanFunction n) : Prop :=
  epsilon < f2BooleanDistance f g

/--
Definition 1.29: distance from a function to a property.

The book assumes the property is nonempty.  Here the empty-property case is
given the harmless default value `0`, while all intended uses are nonempty
properties such as linearity.
-/
noncomputable def f2DistanceToProperty {n : Nat}
    (f : F2BooleanFunction n) (property : F2FunctionProperty n) : Real :=
  by
    classical
    let candidates : Finset (F2BooleanFunction n) :=
      Finset.univ.filter (fun g => g ∈ property)
    let distances : Finset Real :=
      candidates.image (fun g => f2BooleanDistance f g)
    exact if h : distances.Nonempty then
      distances.min' h
    else
      0

/-- `f` is `epsilon`-close to a property of Boolean functions. -/
def IsEpsilonCloseToPropertyF2 {n : Nat} (epsilon : Real)
    (f : F2BooleanFunction n) (property : F2FunctionProperty n) : Prop :=
  ∃ g ∈ property, f2BooleanDistance f g ≤ epsilon

/-- `f` is `epsilon`-far from a property of Boolean functions. -/
def IsEpsilonFarFromPropertyF2 {n : Nat} (epsilon : Real)
    (f : F2BooleanFunction n) (property : F2FunctionProperty n) : Prop :=
  ∀ g ∈ property, epsilon < f2BooleanDistance f g

/-- Approximate linearity: `f` is close to some linear function. -/
def IsEpsilonCloseToLinearF2 {n : Nat} (epsilon : Real)
    (f : F2BooleanFunction n) : Prop :=
  ∃ S : CoordinateSet n, f2BooleanDistance f (linearF2BySet S) ≤ epsilon

end BooleanFunctions
