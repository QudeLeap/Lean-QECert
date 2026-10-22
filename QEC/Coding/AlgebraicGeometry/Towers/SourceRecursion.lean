import QEC.Coding.AlgebraicGeometry.Towers.SourceStep
import QEC.Coding.AlgebraicGeometry.Divisors.RationalBaseInfinityCancellation

import Mathlib.NumberTheory.FunctionField

/-!
# The source-facing F256 Garcia--Stichtenoth recursion

This file iterates the literal source recursion

`x_(i+1)^16 + x_(i+1) = x_i^16 / (x_i^15 + 1)`

from the rational coordinate `x_0 = X`.  Each successor is the actual
degree-sixteen field constructed in `F256GarciaStichtenothSourceStep`, and its
distinguished place is the actual upper place where the next coordinate again
has normalized order `-1`.

This is deliberately distinct from the earlier GS95 recursion through
`z_(i+1)^16 + z_(i+1) = x_i^17`.  No normal closure, global ramification
formula, divisor, genus, or asymptotic conclusion is stored in the recursion
data.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

private structure SourceLevelData where
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

@[reducible] private noncomputable def sourceBaseLevelData : SourceLevelData where
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

@[reducible] private noncomputable def sourceSuccessorLevelData
    (data : SourceLevelData) : SourceLevelData := by
  letI : _root_.Field data.carrier := data.field
  letI : Algebra F256 data.carrier := data.constantAlgebra
  letI : Algebra (RatFunc F256) data.carrier := data.ratFuncAlgebra
  letI : IsScalarTower F256 (RatFunc F256) data.carrier := data.constantTower
  letI : FiniteDimensional (RatFunc F256) data.carrier := data.functionField
  letI : Algebra.IsSeparable (RatFunc F256) data.carrier := data.separable
  let L := SourceStepField data.place data.coordinate data.coordinate_order
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
      place := sourceStepAbovePlace data.place data.coordinate data.coordinate_order
      coordinate := sourceStepCoordinate data.place data.coordinate data.coordinate_order
      coordinate_order :=
        sourceStepAbovePlace_order_coordinate
          data.place data.coordinate data.coordinate_order }

@[reducible] private noncomputable def sourceLevelData : ℕ → SourceLevelData
  | 0 => sourceBaseLevelData
  | i + 1 => sourceSuccessorLevelData (sourceLevelData i)

/-- The actual field at source-recursion level `i`, starting from `F256(X)`.
-/
abbrev SourceField (i : ℕ) : Type := (sourceLevelData i).carrier

noncomputable instance sourceFieldField (i : ℕ) :
    _root_.Field (SourceField i) :=
  (sourceLevelData i).field

noncomputable instance sourceFieldConstantAlgebra (i : ℕ) :
    Algebra F256 (SourceField i) :=
  (sourceLevelData i).constantAlgebra

noncomputable instance sourceFieldRatFuncAlgebra (i : ℕ) :
    Algebra (RatFunc F256) (SourceField i) :=
  (sourceLevelData i).ratFuncAlgebra

noncomputable instance sourceFieldConstantTower (i : ℕ) :
    IsScalarTower F256 (RatFunc F256) (SourceField i) :=
  (sourceLevelData i).constantTower

noncomputable instance sourceFieldFunctionField (i : ℕ) :
    _root_.FunctionField F256 (SourceField i) :=
  (sourceLevelData i).functionField

noncomputable instance sourceFieldSuccessorFunctionField (i : ℕ) :
    _root_.FunctionField F256 (SourceField (i + 1)) :=
  (sourceLevelData (i + 1)).functionField

noncomputable instance sourceFieldSeparable (i : ℕ) :
    Algebra.IsSeparable (RatFunc F256) (SourceField i) :=
  (sourceLevelData i).separable

noncomputable instance sourceFieldSuccessorSeparable (i : ℕ) :
    Algebra.IsSeparable (RatFunc F256) (SourceField (i + 1)) :=
  (sourceLevelData (i + 1)).separable

/-- The recursively distinguished simple-pole place. -/
noncomputable def sourceDistinguishedPlace (i : ℕ) :
    GlobalPlace F256 (SourceField i) :=
  (sourceLevelData i).place

/-- The recursively distinguished source coordinate. -/
noncomputable def sourceDistinguishedCoordinate (i : ℕ) : SourceField i :=
  (sourceLevelData i).coordinate

theorem sourceDistinguishedCoordinate_order (i : ℕ) :
    (sourceDistinguishedPlace i).order (sourceDistinguishedCoordinate i) = -1 :=
  (sourceLevelData i).coordinate_order

/-- The literal inclusion of one source-recursion level into its successor. -/
noncomputable def sourceRecursionEmbedding (i : ℕ) :
    SourceField i →ₐ[F256] SourceField (i + 1) :=
  sourceStepEmbedding (sourceDistinguishedPlace i)
    (sourceDistinguishedCoordinate i) (sourceDistinguishedCoordinate_order i)

/-- Every actual source-recursion step has degree sixteen. -/
theorem sourceRecursionStep_finrank (i : ℕ) :
    Module.finrank (SourceField i) (SourceField (i + 1)) = 16 :=
  sourceStep_finrank (sourceDistinguishedPlace i)
    (sourceDistinguishedCoordinate i) (sourceDistinguishedCoordinate_order i)

/-- The source-recursion level has degree `16^i` over the initial rational
function field. -/
theorem sourceField_finrank (i : ℕ) :
    Module.finrank (RatFunc F256) (SourceField i) = 16 ^ i := by
  induction i with
  | zero =>
      change Module.finrank (RatFunc F256) (RatFunc F256) = 1
      simp
  | succ i ih =>
      letI : IsScalarTower (RatFunc F256) (SourceField i)
          (SourceField (i + 1)) :=
        IsScalarTower.of_algebraMap_eq' rfl
      calc
        Module.finrank (RatFunc F256) (SourceField (i + 1)) =
            Module.finrank (RatFunc F256) (SourceField i) *
              Module.finrank (SourceField i) (SourceField (i + 1)) :=
          (Module.finrank_mul_finrank (RatFunc F256) (SourceField i)
            (SourceField (i + 1))).symm
        _ = 16 ^ i * 16 := by rw [ih, sourceRecursionStep_finrank]
        _ = 16 ^ (i + 1) := by rw [pow_succ]

/-- The successor coordinate is the literal coordinate constructed by the
one-step source recursion. -/
theorem sourceDistinguishedCoordinate_succ (i : ℕ) :
    sourceDistinguishedCoordinate (i + 1) =
      sourceStepCoordinate (sourceDistinguishedPlace i)
        (sourceDistinguishedCoordinate i)
        (sourceDistinguishedCoordinate_order i) := by
  rfl

/-- The source recursion equation holds at every actual level. -/
theorem sourceRecursion_equation (i : ℕ) :
    sourceDistinguishedCoordinate (i + 1) ^ 16 +
        sourceDistinguishedCoordinate (i + 1) =
      sourceRecursionEmbedding i
        (sourceStepRhs (sourceDistinguishedCoordinate i)) := by
  exact sourceStepCoordinate_equation (sourceDistinguishedPlace i)
    (sourceDistinguishedCoordinate i) (sourceDistinguishedCoordinate_order i)

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
