import QEC.Coding.AlgebraicGeometry.Towers.PlaceStep
import QEC.Coding.AlgebraicGeometry.Divisors.RationalBaseInfinityCancellation

import Mathlib.NumberTheory.FunctionField

/-!
# The recursive F256 Garcia--Stichtenoth fields

This file iterates the concrete degree-sixteen step at the distinguished
simple pole.  Every successor is the actual adjoining field from
`F256GarciaStichtenothStep`, equipped with the actual upper place constructed
in `F256GarciaStichtenothPlaceStep`.  No genus, rational-place count, divisor,
or asymptotic conclusion is stored in the recursion data.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

/-- Private construction data for one recursive level.  The only proposition
stored here is the simple-pole invariant needed to construct the next level;
all source-facing tower conclusions remain derived public theorems. -/
private structure LevelData where
  carrier : Type
  [field : _root_.Field carrier]
  [constantAlgebra : Algebra F256 carrier]
  [ratFuncAlgebra : Algebra (RatFunc F256) carrier]
  [constantTower : IsScalarTower F256 (RatFunc F256) carrier]
  [functionField : FiniteDimensional (RatFunc F256) carrier]
  [separable : Algebra.IsSeparable (RatFunc F256) carrier]
  place : GlobalPlace F256 carrier
  coordinate : carrier
  coordinate_order : place.order coordinate = -1

@[reducible] private noncomputable def baseLevelData : LevelData where
  carrier := RatFunc F256
  field := inferInstance
  constantAlgebra := inferInstance
  ratFuncAlgebra := inferInstance
  constantTower := inferInstance
  functionField := inferInstance
  separable := inferInstance
  place := GlobalPlace.rationalInfinity F256
  coordinate := RatFunc.X
  coordinate_order := by
    rw [RationalBaseInfinityCancellation.rationalInfinity_order_eq_neg_intDegree
      F256 RatFunc.X RatFunc.X_ne_zero, RatFunc.intDegree_X]

@[reducible] private noncomputable def successorLevelData
    (data : LevelData) : LevelData := by
  letI : _root_.Field data.carrier := data.field
  letI : Algebra F256 data.carrier := data.constantAlgebra
  letI : Algebra (RatFunc F256) data.carrier := data.ratFuncAlgebra
  letI : IsScalarTower F256 (RatFunc F256) data.carrier := data.constantTower
  letI : FiniteDimensional (RatFunc F256) data.carrier := data.functionField
  letI : Algebra.IsSeparable (RatFunc F256) data.carrier := data.separable
  let L := StepField data.place data.coordinate data.coordinate_order
  letI : FiniteDimensional (RatFunc F256) L :=
    FiniteDimensional.trans (RatFunc F256) data.carrier L
  letI : Algebra.IsSeparable (RatFunc F256) L :=
    Algebra.IsSeparable.trans (RatFunc F256) data.carrier L
  exact
    { carrier := L
      field := inferInstance
      constantAlgebra := inferInstance
      ratFuncAlgebra := inferInstance
      constantTower := inferInstance
      functionField := inferInstance
      separable := inferInstance
      place := stepAbovePlace data.place data.coordinate data.coordinate_order
      coordinate :=
        stepDistinguishedCoordinate data.place data.coordinate data.coordinate_order
      coordinate_order :=
        stepAbovePlace_order_stepDistinguishedCoordinate
          data.place data.coordinate data.coordinate_order }

@[reducible] private noncomputable def levelData : ℕ → LevelData
  | 0 => baseLevelData
  | n + 1 => successorLevelData (levelData n)

/-- The actual field at recursive level `i`, starting from `F256(X)` at
level zero. -/
abbrev Field (i : ℕ) : Type := (levelData i).carrier

noncomputable instance fieldField (i : ℕ) : _root_.Field (Field i) :=
  (levelData i).field

noncomputable instance fieldConstantAlgebra (i : ℕ) : Algebra F256 (Field i) :=
  (levelData i).constantAlgebra

noncomputable instance fieldRatFuncAlgebra (i : ℕ) :
    Algebra (RatFunc F256) (Field i) :=
  (levelData i).ratFuncAlgebra

noncomputable instance fieldConstantTower (i : ℕ) :
    IsScalarTower F256 (RatFunc F256) (Field i) :=
  (levelData i).constantTower

noncomputable instance fieldFunctionField (i : ℕ) :
    _root_.FunctionField F256 (Field i) :=
  (levelData i).functionField

/-- Successor-shaped access to finite-dimensionality, for the same unfolded
instance-lookup boundary as `fieldSuccessorSeparable`. -/
noncomputable instance fieldSuccessorFunctionField (i : ℕ) :
    _root_.FunctionField F256 (Field (i + 1)) :=
  (levelData (i + 1)).functionField

/-- Every recursive level is separable over the rational function field. -/
noncomputable instance fieldSeparable (i : ℕ) :
    Algebra.IsSeparable (RatFunc F256) (Field i) :=
  (levelData i).separable

/-- Successor-shaped access to recursive separability.  Since `Field` is an
abbreviation, a concrete successor unfolds to the adjoining field before
indexed instance lookup reaches `fieldSeparable`; this instance exposes the
same stored transitive proof at that unfolded shape. -/
noncomputable instance fieldSuccessorSeparable (i : ℕ) :
    Algebra.IsSeparable (RatFunc F256) (Field (i + 1)) :=
  (levelData (i + 1)).separable

/-- The recursively distinguished simple-pole place. -/
noncomputable def distinguishedPlace (i : ℕ) : GlobalPlace F256 (Field i) :=
  (levelData i).place

/-- The recursively distinguished coordinate. -/
noncomputable def distinguishedCoordinate (i : ℕ) : Field i :=
  (levelData i).coordinate

theorem distinguishedCoordinate_order (i : ℕ) :
    (distinguishedPlace i).order (distinguishedCoordinate i) = -1 :=
  (levelData i).coordinate_order

/-- The canonical inclusion of one recursive level into its successor. -/
noncomputable def stepEmbedding (i : ℕ) : Field i →ₐ[F256] Field (i + 1) :=
  (stepFieldEmbedding (distinguishedPlace i) (distinguishedCoordinate i)
    (distinguishedCoordinate_order i)).restrictScalars F256

/-- Every actual recursion step has degree sixteen. -/
theorem step_finrank (i : ℕ) :
    Module.finrank (Field i) (Field (i + 1)) = 16 := by
  exact stepField_finrank (distinguishedPlace i) (distinguishedCoordinate i)
    (distinguishedCoordinate_order i)

/-- The source auxiliary Artin--Schreier coordinate at one recursive step. -/
noncomputable def auxiliaryCoordinate (i : ℕ) : Field (i + 1) :=
  stepAuxiliaryCoordinate (distinguishedPlace i) (distinguishedCoordinate i)
    (distinguishedCoordinate_order i)

/-- The literal Garcia--Stichtenoth Artin--Schreier equation at every level. -/
theorem auxiliaryCoordinate_artinSchreier (i : ℕ) :
    auxiliaryCoordinate i ^ 16 + auxiliaryCoordinate i =
      stepEmbedding i (distinguishedCoordinate i) ^ 17 := by
  exact stepAuxiliaryCoordinate_artinSchreier
    (distinguishedPlace i) (distinguishedCoordinate i)
    (distinguishedCoordinate_order i)

/-- The successor distinguished coordinate is `z_(i+1) / x_i`. -/
theorem distinguishedCoordinate_succ (i : ℕ) :
    distinguishedCoordinate (i + 1) =
      auxiliaryCoordinate i / stepEmbedding i (distinguishedCoordinate i) := by
  rfl

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
