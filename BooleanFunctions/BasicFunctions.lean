import BooleanFunctions.Fourierexpansion

/-!
# Basic Boolean functions

Definitions from O'Donnell, Section 2.1.

The book works mostly with the `{-1, 1}` convention.  In these files
`SignBit.negOne` represents `-1` and `SignBit.posOne` represents `1`.
-/

namespace BooleanFunctions

/-- Negation on `{-1, 1}`. -/
def negSignBit : SignBit → SignBit
  | SignBit.negOne => SignBit.posOne
  | SignBit.posOne => SignBit.negOne

@[simp]
lemma negSignBit_negOne : negSignBit SignBit.negOne = SignBit.posOne := rfl

@[simp]
lemma negSignBit_posOne : negSignBit SignBit.posOne = SignBit.negOne := rfl

/-- Coordinatewise negation on the discrete cube. -/
def negSignCube {n : Nat} (x : SignCube n) : SignCube n :=
  fun i => negSignBit (x i)

/-- The all-`1` point of the cube. -/
def allPosSignCube (n : Nat) : SignCube n :=
  fun _ => SignBit.posOne

/-- The all-`-1` point of the cube. -/
def allNegSignCube (n : Nat) : SignCube n :=
  fun _ => SignBit.negOne

/-- Sum of the coordinates, viewed as integers. -/
def signCubeSumInt {n : Nat} (x : SignCube n) : Int :=
  Finset.univ.sum (fun i => (x i).toInt)

/-- The sign of an integer, with ties sent to `1`. -/
def signOfIntWithPositiveTie (z : Int) : SignBit :=
  if 0 ≤ z then SignBit.posOne else SignBit.negOne

/-- Definition 2.1: the majority function, with ties sent to `1`. -/
def majorityFunction {n : Nat} : BooleanFunctionSign n :=
  fun x => signOfIntWithPositiveTie (signCubeSumInt x)

/--
Definition 2.1, predicate form: a function is a majority function when it
agrees with the sign of the coordinate sum away from ties.
-/
def IsMajorityFunction {n : Nat} (f : BooleanFunctionSign n) : Prop :=
  ∀ x : SignCube n,
    signCubeSumInt x ≠ 0 →
      f x =
        if 0 < signCubeSumInt x then SignBit.posOne else SignBit.negOne

/-- Definition 2.2: `AND_n`, using O'Donnell's `-1 = True` convention. -/
def andFunction {n : Nat} : BooleanFunctionSign n :=
  fun x => if x = allNegSignCube n then SignBit.negOne else SignBit.posOne

/-- Definition 2.2: `OR_n`, using O'Donnell's `-1 = True` convention. -/
def orFunction {n : Nat} : BooleanFunctionSign n :=
  fun x => if x = allPosSignCube n then SignBit.posOne else SignBit.negOne

/-- Definition 2.3: the dictator function `x ↦ x_i`. -/
def dictatorFunction {n : Nat} (i : Fin n) : BooleanFunctionSign n :=
  fun x => x i

/-- The negated dictator, a standard companion example to dictators. -/
def negatedDictatorFunction {n : Nat} (i : Fin n) : BooleanFunctionSign n :=
  fun x => negSignBit (x i)

/--
Definition 2.4: `f` is a `k`-junta if some set of at most `k` coordinates
determines its value.
-/
def IsKJunta {n : Nat} (k : Nat) (f : BooleanFunctionSign n) : Prop :=
  ∃ T : CoordinateSet n,
    T.card ≤ k ∧
      ∀ x y : SignCube n,
        (∀ i : Fin n, i ∈ T → x i = y i) → f x = f y

/-- A junta is a function depending on finitely many coordinates. -/
def IsJunta {n : Nat} (f : BooleanFunctionSign n) : Prop :=
  ∃ k : Nat, IsKJunta k f

/--
Definition 2.5: the weighted-majority/linear-threshold function determined
by an affine form.
-/
noncomputable def weightedMajorityFunction {n : Nat}
    (a₀ : Real) (a : Fin n → Real) : BooleanFunctionSign n :=
  fun x =>
    if 0 ≤ a₀ + Finset.univ.sum (fun i => a i * (x i).toReal) then
      SignBit.posOne
    else
      SignBit.negOne

/-- Definition 2.5, predicate form: `f` is a linear threshold function. -/
def IsLinearThresholdFunction {n : Nat} (f : BooleanFunctionSign n) : Prop :=
  ∃ (a₀ : Real) (a : Fin n → Real),
    ∀ x : SignCube n, f x = weightedMajorityFunction a₀ a x

/--
One recursion step in Definition 2.6: apply a Boolean function to each block
and then take majority of the resulting block outputs.
-/
def recursiveMajorityStep {n m : Nat}
    (g : BooleanFunctionSign m) (blocks : Fin n → SignCube m) : SignBit :=
  majorityFunction (fun i : Fin n => g (blocks i))

/-- A block presentation of inputs divided into `s` blocks of width `w`. -/
abbrev BlockSignCube (s w : Nat) :=
  Fin s → SignCube w

/--
Definition 2.7: the tribes function in block form.

The unflattened type `BlockSignCube s w` makes the `s` tribes of width `w`
explicit; it corresponds to the book's inputs in `{-1,1}^{s*w}`.
-/
def tribesFunction {w s : Nat} : BlockSignCube s w → SignBit :=
  fun blocks => orFunction (fun j : Fin s => andFunction (blocks j))

/-- Definition 2.8: monotonicity for functions on the `{-1,1}` cube. -/
def IsMonotoneSignFunction {n : Nat} (f : BooleanFunctionSign n) : Prop :=
  ∀ x y : SignCube n,
    (∀ i : Fin n, (x i).toInt ≤ (y i).toInt) →
      (f x).toInt ≤ (f y).toInt

/-- Definition 2.8: oddness, `f(-x) = -f(x)`. -/
def IsOddSignFunction {n : Nat} (f : BooleanFunctionSign n) : Prop :=
  ∀ x : SignCube n, f (negSignCube x) = negSignBit (f x)

/-- Definition 2.8: unanimity. -/
def IsUnanimousSignFunction {n : Nat} (f : BooleanFunctionSign n) : Prop :=
  f (allNegSignCube n) = SignBit.negOne ∧
    f (allPosSignCube n) = SignBit.posOne

/-- Permute the coordinates of a cube point. -/
def permuteSignCube {n : Nat} (π : Equiv.Perm (Fin n)) (x : SignCube n) :
    SignCube n :=
  fun i => x (π i)

/-- Definition 2.8: full symmetry under every coordinate permutation. -/
def IsSymmetricSignFunction {n : Nat} (f : BooleanFunctionSign n) : Prop :=
  ∀ (π : Equiv.Perm (Fin n)) (x : SignCube n),
    f (permuteSignCube π x) = f x

/--
Definition 2.10: transitive symmetry.  For any two coordinates, some
symmetry of the function maps the first coordinate to the second.
-/
def IsTransitiveSymmetricSignFunction {n : Nat}
    (f : BooleanFunctionSign n) : Prop :=
  ∀ i j : Fin n,
    ∃ π : Equiv.Perm (Fin n),
      π i = j ∧
        ∀ x : SignCube n, f (permuteSignCube π x) = f x

/--
Definition 2.11: expectation under the impartial-culture assumption.  This is
the same uniform expectation already used for the cube.
-/
noncomputable def impartialCultureExpectation {n : Nat}
    (f : RealValuedBooleanFunction n) : Real :=
  cubeExpectation f

/-- Probability of an event under impartial culture. -/
noncomputable def impartialCultureProbability {n : Nat}
    (event : SignCube n → Prop) [DecidablePred event] : Real :=
  cubeProbability event

end BooleanFunctions
