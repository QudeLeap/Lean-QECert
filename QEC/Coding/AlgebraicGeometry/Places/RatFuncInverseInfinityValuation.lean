import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.RatFunc.Valuation
import QEC.Coding.AlgebraicGeometry.Places.RationalFieldPlaces

namespace QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation

open scoped Polynomial RatFunc WithZero
open RatFuncFixturePlaces

abbrev K : Type := RatFuncFixturePlaces.K
abbrev F : Type := RatFuncFixturePlaces.F

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

noncomputable local instance oldRationalAlgebra : Algebra K⟮X⟯ F :=
  RatFuncFixturePlaces.oldRationalAlgebra
noncomputable local instance oldPolynomialAlgebra : Algebra K[X] F :=
  RatFuncFixturePlaces.oldPolynomialAlgebra
noncomputable local instance oldScalarTower : IsScalarTower K[X] K⟮X⟯ F :=
  RatFuncFixturePlaces.oldScalarTower
noncomputable local instance oldFunctionField : _root_.FunctionField K F :=
  RatFuncFixturePlaces.oldFunctionField
noncomputable local instance oldSeparable : Algebra.IsSeparable K⟮X⟯ F :=
  RatFuncFixturePlaces.oldSeparable
noncomputable local instance oldFractionRing :
    @IsFractionRing K[X] _ F _ oldPolynomialAlgebra := inferInstance
noncomputable local instance ratFuncDecidableEq : DecidableEq K⟮X⟯ := Classical.decEq _

private abbrev inverseScalarTowerType : Prop :=
  @IsScalarTower K[X] K⟮X⟯ F RatFunc.instSMulOfFractionRingPolynomial
    (InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) K F).toSMul
    (InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) K F).toSMul

theorem inverseXIdeal_eq_span_imageX :
    letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
    letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
    inverseXIdeal = Ideal.span {inverseIntegralClosureEquiv Polynomial.X} := by
  letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
  letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
  rw [inverseXIdeal, Polynomial.idealX_span, Ideal.map_span]
  simp

theorem inverseIntegralClosureEquiv_X_ne_zero :
    letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
    letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
    inverseIntegralClosureEquiv Polynomial.X ≠ 0 := by
  letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
  letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
  intro h
  apply (Polynomial.X_ne_zero : (Polynomial.X : K[X]) ≠ 0)
  apply inverseIntegralClosureEquiv.injective
  simpa only [map_zero] using h

theorem inverseXAffinePlace_intValuation_imageX :
    letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
    letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
    inverseXAffinePlace.intValuation (inverseIntegralClosureEquiv Polynomial.X) =
      WithZero.exp (-1 : Int) := by
  letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
  letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
  exact inverseXAffinePlace.intValuation_singleton
    inverseIntegralClosureEquiv_X_ne_zero inverseXIdeal_eq_span_imageX

theorem transportedPolynomialMap_X_eq_original_X_inv :
    InverseAffinePlace.transportedPolynomialMap (oldRationalAlgebra := oldRationalAlgebra) K F Polynomial.X =
      (RatFunc.X : F)⁻¹ := by
  simp [InverseAffinePlace.transportedPolynomialMap,
    InverseAffinePlace.transportedRationalMap_X, InverseChart.inverseCoordinate,
    InverseChart.coordinate]

noncomputable def inverseXFibreValuation : Valuation F ℤᵐ⁰ := by
  letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
  letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
  letI : Algebra K F := AffinePlace.constantAlgebra K F
  exact (InverseAffinePlace.globalPlace
    (oldRationalAlgebra := RatFuncFixturePlaces.oldRationalAlgebra)
    (oldFunctionField := RatFuncFixturePlaces.oldFunctionField)
    (oldSeparable := RatFuncFixturePlaces.oldSeparable)
    K F inverseXFibrePoint).valuation

theorem inverseXFibreValuation_surjective :
    Function.Surjective inverseXFibreValuation := by
  letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
  letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
  letI : Algebra K F := AffinePlace.constantAlgebra K F
  unfold inverseXFibreValuation
  exact InverseAffinePlace.globalPlace_surjective
    (oldPolynomialAlgebra := RatFuncFixturePlaces.oldPolynomialAlgebra)
    (oldRationalAlgebra := RatFuncFixturePlaces.oldRationalAlgebra)
    (oldScalarTower := RatFuncFixturePlaces.oldScalarTower)
    (oldFunctionField := RatFuncFixturePlaces.oldFunctionField)
    (oldSeparable := RatFuncFixturePlaces.oldSeparable)
    K F inverseXFibrePoint

noncomputable def inverseXFibreGlobalPlace : GlobalPlace K F where
  valuation := inverseXFibreValuation
  normalized := inverseXFibreValuation_surjective

theorem inverseXFibreValuation_X_inv :
    inverseXFibreValuation ((RatFunc.X : F)⁻¹) = WithZero.exp (-1 : Int) := by
  letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
  letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
  have hintegral : inverseXFibreValuation
      (inverseIntegralClosureEquiv Polynomial.X).1 = WithZero.exp (-1 : Int) := by
    unfold inverseXFibreValuation
    rw [InverseAffinePlace.globalPlace_valuation
      (oldPolynomialAlgebra := RatFuncFixturePlaces.oldPolynomialAlgebra)
      (oldRationalAlgebra := RatFuncFixturePlaces.oldRationalAlgebra)
      (oldScalarTower := RatFuncFixturePlaces.oldScalarTower)
      (oldFunctionField := RatFuncFixturePlaces.oldFunctionField)
      (oldSeparable := RatFuncFixturePlaces.oldSeparable)
      K F inverseXFibrePoint,
      AffinePlace.valuation_of_integral]
    change inverseXAffinePlace.intValuation (inverseIntegralClosureEquiv Polynomial.X) = _
    exact inverseXAffinePlace_intValuation_imageX
  have hmap : (inverseIntegralClosureEquiv Polynomial.X).1 =
      InverseAffinePlace.transportedPolynomialMap
        (oldRationalAlgebra := oldRationalAlgebra) K F Polynomial.X := by
    exact algebraMap_inverseIntegralClosureEquiv Polynomial.X
  rw [hmap,
    transportedPolynomialMap_X_eq_original_X_inv] at hintegral
  exact hintegral

theorem inverseXFibreValuation_X :
    inverseXFibreValuation RatFunc.X = WithZero.exp (1 : Int) := by
  calc
    inverseXFibreValuation RatFunc.X =
        (inverseXFibreValuation ((RatFunc.X : F)⁻¹))⁻¹ := by
          rw [(inverseXFibreValuation).map_inv, inv_inv]
    _ = (WithZero.exp (-1 : Int))⁻¹ := by rw [inverseXFibreValuation_X_inv]
    _ = WithZero.exp (1 : Int) := by simp

private theorem valuation_eq_infty_of_X_eq_exp_one
    (v : Valuation F ℤᵐ⁰) [v.IsTrivialOn K]
    (hx : v RatFunc.X = WithZero.exp (1 : Int)) :
    v = RatFunc.inftyValuation K := by
  classical
  ext f
  induction f using RatFunc.induction_on with
  | f p q hq =>
      rw [map_div₀, map_div₀]
      by_cases hp : p = 0
      · simp [hp]
      have hlt : 1 < v RatFunc.X := by
        rw [hx, ← WithZero.exp_zero]
        exact WithZero.exp_lt_exp.mpr (by norm_num)
      have hltInfinity : 1 < RatFunc.inftyValuation K RatFunc.X := by
        rw [RatFunc.inftyValuation.X, ← WithZero.exp_zero]
        exact WithZero.exp_lt_exp.mpr (by norm_num)
      change v (p : F) / v (q : F) =
        RatFunc.inftyValuation K (p : F) / RatFunc.inftyValuation K (q : F)
      rw [Polynomial.valuation_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X
          K (v := v) hlt hp,
        Polynomial.valuation_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X
          K (v := v) hlt hq,
        Polynomial.valuation_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X
          K (v := RatFunc.inftyValuation K) hltInfinity hp,
        Polynomial.valuation_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X
          K (v := RatFunc.inftyValuation K) hltInfinity hq]
      simp [hx, RatFunc.inftyValuation.X]

private theorem globalPlace_eq_of_valuation_eq
    {P Q : GlobalPlace K F} (hvaluation : P.valuation = Q.valuation) : P = Q := by
  cases P
  cases Q
  cases hvaluation
  rfl

theorem inverseXFibreGlobalPlace_eq_rationalInfinity :
    inverseXFibreGlobalPlace = GlobalPlace.rationalInfinity K := by
  apply globalPlace_eq_of_valuation_eq
  letI : inverseXFibreValuation.IsTrivialOn K :=
    GlobalPlace.trivialOnConstants inverseXFibreGlobalPlace
  exact valuation_eq_infty_of_X_eq_exp_one inverseXFibreValuation inverseXFibreValuation_X

end QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation
