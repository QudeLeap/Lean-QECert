import QEC.Coding.AlgebraicGeometry.Places.RatFuncInverseInfinityValuation
import QEC.Coding.AlgebraicGeometry.Places.TwoChartGlobalPlace

namespace QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces

open scoped Polynomial RatFunc WithZero
open RatFuncInverseInfinityValuation

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

noncomputable local instance fixtureOldRationalAlgebra : Algebra K⟮X⟯ F :=
  RatFuncFixturePlaces.oldRationalAlgebra
noncomputable local instance fixtureOldPolynomialAlgebra : Algebra K[X] F :=
  RatFuncFixturePlaces.oldPolynomialAlgebra
noncomputable local instance fixtureOldScalarTower : IsScalarTower K[X] K⟮X⟯ F :=
  RatFuncFixturePlaces.oldScalarTower
noncomputable local instance fixtureOldFunctionField : _root_.FunctionField K F :=
  RatFuncFixturePlaces.oldFunctionField
noncomputable local instance fixtureOldSeparable : Algebra.IsSeparable K⟮X⟯ F :=
  RatFuncFixturePlaces.oldSeparable

private abbrev inverseScalarTowerType : Prop :=
  @IsScalarTower K[X] K⟮X⟯ F RatFunc.instSMulOfFractionRingPolynomial
    (InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := fixtureOldRationalAlgebra) K F).toSMul
    (InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := fixtureOldRationalAlgebra) K F).toSMul

/-- The actual inverse-chart fibre over `(X)` is rational, and its valuation is
the rational-function valuation at infinity.  The generic chart transport
therefore makes the canonical global residue degree at infinity equal to one. -/
theorem rationalInfinity_residueDegree_eq_one :
    GlobalPlace.residueDegree (k := K) (F := F) (GlobalPlace.rationalInfinity K) = 1 := by
  rw [GlobalPlace.residueDegree_eq_inverseFibre
    (P := GlobalPlace.rationalInfinity K) (D := inverseXFibrePoint) (by
      change (GlobalPlace.rationalInfinity K).valuation = inverseXFibreValuation
      exact (congrArg GlobalPlace.valuation
        inverseXFibreGlobalPlace_eq_rationalInfinity).symm)]
  letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := fixtureOldRationalAlgebra) K F
  letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := fixtureOldRationalAlgebra) K F
  letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := fixtureOldRationalAlgebra) K F
  letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := fixtureOldRationalAlgebra)
    (oldFunctionField := fixtureOldFunctionField) K F
  letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := fixtureOldRationalAlgebra)
    (oldSeparable := fixtureOldSeparable) K F
  change
    AffinePlace.residueDegree K F inverseXFibrePoint.1 = 1
  exact inverseXFibrePoint_residueDegree_eq_one

end QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces
