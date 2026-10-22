import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.RatFunc.Valuation
import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Polynomial.Quotient
import QEC.Coding.AlgebraicGeometry.Places.AffineGlobalPlace
import QEC.Coding.AlgebraicGeometry.Places.AffinePlaceDegree
import QEC.Coding.AlgebraicGeometry.Places.InverseInfinityFibre
import QEC.Coding.AlgebraicGeometry.Places.RationalIntegralClosure

namespace QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces

open scoped Polynomial RatFunc WithZero
open RatFuncFixtureDirectIntegralClosure

abbrev K : Type := RatFuncFixtureDirectIntegralClosure.K

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev F : Type := RatFuncFixtureDirectIntegralClosure.F
abbrev DirectB : Type := RatFuncFixtureDirectIntegralClosure.B

noncomputable local instance oldRationalAlgebra : Algebra K⟮X⟯ F := inferInstance
noncomputable local instance oldPolynomialAlgebra : Algebra K[X] F := inferInstance
noncomputable local instance oldScalarTower : IsScalarTower K[X] K⟮X⟯ F := inferInstance
noncomputable local instance oldFunctionField : _root_.FunctionField K F := inferInstance
noncomputable local instance oldSeparable : Algebra.IsSeparable K⟮X⟯ F := inferInstance
noncomputable local instance oldFractionRing :
    @IsFractionRing K[X] _ F _ oldPolynomialAlgebra := inferInstance

section Direct

noncomputable local instance directConstantAlgebra : Algebra K F :=
  AffinePlace.constantAlgebra K F

noncomputable def xZeroIdeal : Ideal DirectB :=
  Ideal.map directIntegralClosureEquiv.toRingEquiv (Polynomial.idealX K).asIdeal

theorem xZeroIdeal_isPrime : xZeroIdeal.IsPrime := by
  unfold xZeroIdeal
  infer_instance

theorem xZeroIdeal_ne_bot : xZeroIdeal ≠ ⊥ := by
  intro h
  apply (Polynomial.idealX K).ne_bot
  exact (Ideal.map_eq_bot_iff_of_injective directIntegralClosureEquiv.injective).mp h

noncomputable def xZeroAffinePlace : AffinePlace.carrier K F :=
  { asIdeal := xZeroIdeal
    isPrime := xZeroIdeal_isPrime
    ne_bot := xZeroIdeal_ne_bot }

theorem xZeroIdeal_eq_span_imageX :
    xZeroIdeal = Ideal.span {directIntegralClosureEquiv Polynomial.X} := by
  rw [xZeroIdeal, Polynomial.idealX_span, Ideal.map_span]
  simp

theorem directIntegralClosureEquiv_X_ne_zero :
    directIntegralClosureEquiv Polynomial.X ≠ 0 := by
  intro h
  apply (Polynomial.X_ne_zero : (Polynomial.X : K[X]) ≠ 0)
  apply directIntegralClosureEquiv.injective
  simpa only [map_zero] using h

theorem xZeroAffinePlace_intValuation_imageX :
    xZeroAffinePlace.intValuation (directIntegralClosureEquiv Polynomial.X) =
      WithZero.exp (-1 : Int) :=
  xZeroAffinePlace.intValuation_singleton
    directIntegralClosureEquiv_X_ne_zero xZeroIdeal_eq_span_imageX

theorem xZeroAffinePlace_order_X :
    GlobalPlace.order (AffinePlace.globalPlace K F xZeroAffinePlace) RatFunc.X = 1 := by
  rw [← RatFunc.algebraMap_X, ← algebraMap_directIntegralClosureEquiv]
  rw [AffinePlace.globalPlace_order_of_integral,
    xZeroAffinePlace_intValuation_imageX, WithZero.log_exp]
  norm_num

theorem order_xZero_X :
    GlobalPlace.order (AffinePlace.globalPlace K F xZeroAffinePlace) RatFunc.X = 1 :=
  xZeroAffinePlace_order_X

end Direct

private abbrev inverseScalarTowerType : Prop :=
  @IsScalarTower K[X] K⟮X⟯ F RatFunc.instSMulOfFractionRingPolynomial
    (InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) K F).toSMul
    (InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) K F).toSMul

@[reducible] private noncomputable def inverseFractionRing :
    @IsFractionRing K[X] _ F _
      (InverseAffinePlace.transportedPolynomialAlgebra
        (oldRationalAlgebra := oldRationalAlgebra) K F) := by
  letI : Algebra K[X] F := oldPolynomialAlgebra
  exact (IsLocalization.isLocalization_iff_of_ringEquiv
    (M := nonZeroDivisors K[X]) (InverseAffinePlace.rationalInvolution K).toRingEquiv).mp
    inferInstance

private noncomputable abbrev inverseBSubalgebra :
    @Subalgebra K[X] F _ _
      (InverseAffinePlace.transportedPolynomialAlgebra
        (oldRationalAlgebra := oldRationalAlgebra) K F) :=
  @_root_.FunctionField.ringOfIntegers K F _ _
    (InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) K F)

private noncomputable abbrev inverseB : Type _ := ↥inverseBSubalgebra

private noncomputable abbrev inverseBToFAlgebra : Algebra inverseB F :=
  @Subalgebra.toAlgebra F K[X] F _ _ _
    (InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) K F)
    (Algebra.id F) inverseBSubalgebra

noncomputable def inverseIntegralClosureEquiv :
    letI : @IsFractionRing K[X] _ F _
        (InverseAffinePlace.transportedPolynomialAlgebra
          (oldRationalAlgebra := oldRationalAlgebra) K F) := inverseFractionRing
    K[X] ≃ₐ[K[X]] inverseB := by
  letI inverseBAlgebra : Algebra K[X] inverseB := inferInstance
  letI inverseBToF : Algebra inverseB F := inferInstance
  letI inverseBTower : @IsScalarTower K[X] inverseB F inverseBAlgebra.toSMul
      inverseBToF.toSMul
      (InverseAffinePlace.transportedPolynomialAlgebra
        (oldRationalAlgebra := oldRationalAlgebra) K F).toSMul :=
    @IsScalarTower.of_algebraMap_eq K[X] inverseB F _ _ _ inverseBAlgebra inverseBToF
      (InverseAffinePlace.transportedPolynomialAlgebra
        (oldRationalAlgebra := oldRationalAlgebra) K F)
      (fun _ => rfl)
  letI inverseBClosure : @IsIntegralClosure inverseB K[X] F _ _ _
      (InverseAffinePlace.transportedPolynomialAlgebra
        (oldRationalAlgebra := oldRationalAlgebra) K F) inverseBToF :=
    @integralClosure.isIntegralClosure K[X] F _ _
      (InverseAffinePlace.transportedPolynomialAlgebra
        (oldRationalAlgebra := oldRationalAlgebra) K F)
  letI inverseXSelfAlgebra : Algebra K[X] K[X] := Algebra.id K[X]
  letI inverseXToFTower : @IsScalarTower K[X] K[X] F inverseXSelfAlgebra.toSMul
      (InverseAffinePlace.transportedPolynomialAlgebra
        (oldRationalAlgebra := oldRationalAlgebra) K F).toSMul
      (InverseAffinePlace.transportedPolynomialAlgebra
        (oldRationalAlgebra := oldRationalAlgebra) K F).toSMul :=
    @IsScalarTower.of_algebraMap_eq K[X] K[X] F _ _ _ inverseXSelfAlgebra
      (InverseAffinePlace.transportedPolynomialAlgebra
        (oldRationalAlgebra := oldRationalAlgebra) K F)
      (InverseAffinePlace.transportedPolynomialAlgebra
        (oldRationalAlgebra := oldRationalAlgebra) K F)
      (fun _ => rfl)
  letI inverseXClosure : @IsIntegralClosure K[X] K[X] F _ _ _
      (InverseAffinePlace.transportedPolynomialAlgebra
        (oldRationalAlgebra := oldRationalAlgebra) K F)
      (InverseAffinePlace.transportedPolynomialAlgebra
        (oldRationalAlgebra := oldRationalAlgebra) K F) :=
    @IsIntegralClosure.of_isIntegrallyClosed K[X] K[X] _ _ F _
      (InverseAffinePlace.transportedPolynomialAlgebra
        (oldRationalAlgebra := oldRationalAlgebra) K F)
      inverseFractionRing _ inverseXSelfAlgebra
      (InverseAffinePlace.transportedPolynomialAlgebra
        (oldRationalAlgebra := oldRationalAlgebra) K F)
      inverseXToFTower _
  exact (@IsIntegralClosure.equiv K[X] inverseB F _ _ _
    (InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) K F)
    inverseBToF inverseBClosure K[X] _
    (InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) K F)
    inverseXClosure inverseBAlgebra inverseXSelfAlgebra inverseBTower inverseXToFTower).symm

theorem algebraMap_inverseIntegralClosureEquiv (p : K[X]) :
    letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
    letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
    @algebraMap inverseB F _ _ inverseBToFAlgebra
        (inverseIntegralClosureEquiv p) =
      InverseAffinePlace.transportedPolynomialMap
        (oldRationalAlgebra := oldRationalAlgebra) K F p := by
  letI inverseBAlgebra : Algebra K[X] inverseB := inferInstance
  letI inverseBToF : Algebra inverseB F := inverseBToFAlgebra
  letI inverseBTower : @IsScalarTower K[X] inverseB F inverseBAlgebra.toSMul
      inverseBToF.toSMul
      (InverseAffinePlace.transportedPolynomialAlgebra
        (oldRationalAlgebra := oldRationalAlgebra) K F).toSMul :=
    @IsScalarTower.of_algebraMap_eq K[X] inverseB F _ _ _ inverseBAlgebra inverseBToF
      (InverseAffinePlace.transportedPolynomialAlgebra
        (oldRationalAlgebra := oldRationalAlgebra) K F)
      (fun _ => rfl)
  have he : inverseIntegralClosureEquiv p = algebraMap K[X] inverseB p := by
    simpa using inverseIntegralClosureEquiv.commutes p
  calc
    @algebraMap inverseB F _ _ inverseBToFAlgebra (inverseIntegralClosureEquiv p) =
        @algebraMap inverseB F _ _ inverseBToFAlgebra (algebraMap K[X] inverseB p) := by
      rw [he]
    _ = @algebraMap K[X] F _ _
        (InverseAffinePlace.transportedPolynomialAlgebra
          (oldRationalAlgebra := oldRationalAlgebra) K F) p :=
      (@IsScalarTower.algebraMap_apply K[X] inverseB F _ _ _ inverseBAlgebra inverseBToF
        (InverseAffinePlace.transportedPolynomialAlgebra
          (oldRationalAlgebra := oldRationalAlgebra) K F) inverseBTower p).symm
    _ = InverseAffinePlace.transportedPolynomialMap
        (oldRationalAlgebra := oldRationalAlgebra) K F p := rfl

noncomputable def inverseXIdeal :
    letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
    letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
    Ideal inverseB := by
  letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
  letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
  exact Ideal.map inverseIntegralClosureEquiv.toRingEquiv (Polynomial.idealX K).asIdeal

theorem inverseXIdeal_eq_definingLift :
    letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
    letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
    inverseXIdeal = Ideal.map
      (algebraMap K[X] (_root_.FunctionField.ringOfIntegers K F))
      (Polynomial.idealX K).asIdeal := by
  letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
  letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
  have hmap : inverseIntegralClosureEquiv.toRingEquiv.toRingHom =
      algebraMap K[X] (_root_.FunctionField.ringOfIntegers K F) := by
    apply DFunLike.ext _ _
    intro p
    simpa using inverseIntegralClosureEquiv.commutes p
  rw [inverseXIdeal]
  change Ideal.map inverseIntegralClosureEquiv.toRingEquiv.toRingHom
      (Polynomial.idealX K).asIdeal = _
  rw [hmap]

theorem inverseXIdeal_isPrime :
    letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
    letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
    inverseXIdeal.IsPrime := by
  letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
  letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
  unfold inverseXIdeal
  infer_instance

noncomputable local instance inverseXIdealPrime : inverseXIdeal.IsPrime :=
  inverseXIdeal_isPrime

theorem inverseXIdeal_ne_bot :
    letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
    letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
    inverseXIdeal ≠ ⊥ := by
  letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
  letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
  intro h
  apply (Polynomial.idealX K).ne_bot
  exact (Ideal.map_eq_bot_iff_of_injective inverseIntegralClosureEquiv.injective).mp h

noncomputable def inverseXAffinePlace :
    letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
    letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
    InverseAffinePlace.carrier
      (oldRationalAlgebra := oldRationalAlgebra) K F := by
  letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
  letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
  exact { asIdeal := inverseXIdeal, isPrime := inverseXIdeal_isPrime, ne_bot := inverseXIdeal_ne_bot }

noncomputable def inverseXFibrePoint :
    letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
    letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
    InverseAffinePlace.infinityFibre
      (oldRationalAlgebra := oldRationalAlgebra) K F := by
  letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
  letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
  refine ⟨inverseXAffinePlace, ?_⟩
  change inverseXIdeal ∣ _
  rw [inverseXIdeal_eq_definingLift]

noncomputable def polynomialXResidueEquiv :
    K[X] ⧸ (Polynomial.idealX K).asIdeal ≃+* K :=
  (Ideal.quotEquivOfEq (by rw [Polynomial.idealX_span]; simp)).trans
    (Polynomial.quotientSpanXSubCAlgEquiv (0 : K)).toRingEquiv

noncomputable def inverseXQuotientEquiv :
    letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
    letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
    (K[X] ⧸ (Polynomial.idealX K).asIdeal) ≃+*
      ((_root_.FunctionField.ringOfIntegers K F) ⧸ inverseXIdeal) := by
  letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
  letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
  exact Ideal.quotientEquiv (Polynomial.idealX K).asIdeal inverseXIdeal
    inverseIntegralClosureEquiv.toRingEquiv rfl

noncomputable def inverseXQuotientToResidueEquiv :
    letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
    letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
    letI : inverseXIdeal.IsPrime := inverseXIdeal_isPrime
    letI : inverseXIdeal.IsMaximal :=
      inverseXIdeal_isPrime.isMaximal inverseXIdeal_ne_bot
    ((_root_.FunctionField.ringOfIntegers K F) ⧸ inverseXIdeal) ≃+*
      inverseXIdeal.ResidueField := by
  letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
  letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
  letI : inverseXIdeal.IsPrime := inverseXIdeal_isPrime
  letI : inverseXIdeal.IsMaximal :=
    inverseXIdeal_isPrime.isMaximal inverseXIdeal_ne_bot
  exact RingEquiv.ofBijective (algebraMap _ _)
    inverseXIdeal.bijective_algebraMap_quotient_residueField

noncomputable def inverseXConstantsEquiv :
    letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
    letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
    K ≃+* AffinePlace.residueField K F inverseXAffinePlace := by
  letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
  letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
  exact polynomialXResidueEquiv.symm.trans
    (inverseXQuotientEquiv.trans inverseXQuotientToResidueEquiv)

theorem inverseXConstantsEquiv_apply (a : K) :
    letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
    letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
    inverseXConstantsEquiv a = AffinePlace.constantsToResidue K F inverseXAffinePlace a := by
  letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
  letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
  letI : inverseXIdeal.IsPrime := inverseXIdeal_isPrime
  letI : inverseXIdeal.IsMaximal :=
    inverseXIdeal_isPrime.isMaximal inverseXIdeal_ne_bot
  letI inverseQuotientResidueAlgebra :
      Algebra ((_root_.FunctionField.ringOfIntegers K F) ⧸ inverseXIdeal)
        inverseXIdeal.ResidueField := inferInstance
  have hpoly : polynomialXResidueEquiv.symm a =
      Ideal.Quotient.mk (Polynomial.idealX K).asIdeal (Polynomial.C a) := by
    rw [polynomialXResidueEquiv, RingEquiv.symm_trans_apply]
    change (Ideal.quotEquivOfEq _).symm
      ((Polynomial.quotientSpanXSubCAlgEquiv (0 : K)).symm a) = _
    rw [Polynomial.quotientSpanXSubCAlgEquiv_symm_apply,
      Ideal.quotEquivOfEq_symm]
    change (Ideal.quotEquivOfEq _)
      (Ideal.Quotient.mk (Ideal.span {Polynomial.X - Polynomial.C 0})
        (Polynomial.C a)) = _
    rw [Ideal.quotEquivOfEq_mk]
  rw [inverseXConstantsEquiv, RingEquiv.trans_apply, hpoly]
  change inverseXQuotientToResidueEquiv
    (inverseXQuotientEquiv
      (Ideal.Quotient.mk (Polynomial.idealX K).asIdeal (Polynomial.C a))) = _
  change inverseXQuotientToResidueEquiv
    (Ideal.Quotient.mk inverseXIdeal (inverseIntegralClosureEquiv (Polynomial.C a))) = _
  have hres := Ideal.algebraMap_quotient_residueField_mk
    (I := inverseXIdeal) (inverseIntegralClosureEquiv (Polynomial.C a))
  rw [inverseXQuotientToResidueEquiv]
  change @algebraMap ((_root_.FunctionField.ringOfIntegers K F) ⧸ inverseXIdeal)
    inverseXIdeal.ResidueField _ _ inverseQuotientResidueAlgebra
    (Ideal.Quotient.mk inverseXIdeal
      (inverseIntegralClosureEquiv (Polynomial.C a))) = _
  rw [hres,
    AffinePlace.constantsToResidue_apply]
  rw [show inverseIntegralClosureEquiv (Polynomial.C a) =
    algebraMap K[X] (_root_.FunctionField.ringOfIntegers K F) (Polynomial.C a) by
      exact inverseIntegralClosureEquiv.commutes (Polynomial.C a)]
  rfl

noncomputable def inverseXFibrePointRational :
    letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
    letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
    AffinePlace.Rational K F inverseXFibrePoint.1 := by
  letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
  letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
  refine ⟨inverseXConstantsEquiv, ?_⟩
  intro a
  exact inverseXConstantsEquiv_apply a

theorem inverseXFibrePoint_residueDegree_eq_one :
    letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
    letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
    AffinePlace.residueDegree K F inverseXFibrePoint.1 = 1 := by
  letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
  letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
  exact AffinePlace.Rational.residueDegree_eq_one K F inverseXFibrePointRational

end QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces
