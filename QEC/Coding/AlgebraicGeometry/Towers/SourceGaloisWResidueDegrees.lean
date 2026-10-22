import QEC.Coding.AlgebraicGeometry.Towers.SourceGaloisWGlobalPlaces
import QEC.Coding.AlgebraicGeometry.Places.HeightOneQuotientResidue
import QEC.Coding.AlgebraicGeometry.Residues.Rational.InfinityResidue
import QEC.Coding.AlgebraicGeometry.Places.ResidueFinrankInertia
import QEC.Coding.AlgebraicGeometry.RiemannRoch.PlaceIncrement

import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Residue degrees in the zero and infinity fibres over F256(w)

The actual upper-prime quotient is identified with the residue field of the
corresponding normalized global place.  Since the transported zero and
infinity places of `F256(w)` are rational over `F256`, the upper residue
degree is exactly the common Galois inertia degree of its fibre.

This is a compositional certificate over the already-compiled upper-place
construction.  No ramification value, divisor, different, genus, or
canonical differential is asserted here.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

private abbrev W (m : ℕ) := SourceGaloisWClosureField m
private abbrev E (m : ℕ) := SourceGaloisClosureField m

private noncomputable local instance (priority := 3000)
    wClosureAlgebra (m : ℕ) : Algebra (W m) (E m) :=
  (W m).val.toRingHom.toAlgebra

private noncomputable local instance (priority := 3000)
    wClosureSMul (m : ℕ) : SMul (W m) (E m) :=
  (wClosureAlgebra m).toSMul

private noncomputable local instance (priority := 3000)
    wClosureModule (m : ℕ) : Module (W m) (E m) :=
  @Algebra.toModule (W m) (E m) _ _ (wClosureAlgebra m)

private noncomputable local instance (priority := 3000)
    wClosureFree (m : ℕ) : Module.Free (W m) (E m) :=
  Module.Free.of_divisionRing (W m) (E m)

private noncomputable local instance (priority := 3000)
    wBaseFree (m : ℕ) : Module.Free GaloisBaseField (W m) :=
  Module.Free.of_divisionRing GaloisBaseField (W m)

private noncomputable local instance (priority := 3000)
    wClosureFaithfulSMul (m : ℕ) : FaithfulSMul (W m) (E m) :=
  (faithfulSMul_iff_algebraMap_injective (W m) (E m)).2 (W m).val.injective

private noncomputable local instance wClosureScalarTower (m : ℕ) :
    IsScalarTower GaloisBaseField (W m) (E m) :=
  IsScalarTower.of_algebraMap_eq' rfl

private noncomputable local instance wClosureTorsionFree (m : ℕ) :
    Module.IsTorsionFree (W m) (E m) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr (W m).val.injective

private noncomputable local instance wClosureFiniteDimensional (m : ℕ) :
    FiniteDimensional (W m) (E m) :=
  FiniteDimensional.right GaloisBaseField (W m) (E m)

private noncomputable local instance wClosureIsGalois (m : ℕ) :
    IsGalois (W m) (E m) :=
  IsGalois.tower_top_of_isGalois GaloisBaseField (W m) (E m)

private noncomputable local instance closurePolynomialAlgebra (m : ℕ) :
    Algebra (Polynomial F256) (E m) :=
  ((algebraMap (RatFunc F256) (E m)).comp
    (algebraMap (Polynomial F256) (RatFunc F256))).toAlgebra

private noncomputable local instance closurePolynomialRatFuncScalarTower (m : ℕ) :
    IsScalarTower (Polynomial F256) (RatFunc F256) (E m) :=
  IsScalarTower.of_algebraMap_eq' rfl

private noncomputable local instance closureRatFuncIsSeparable (m : ℕ) :
    Algebra.IsSeparable (RatFunc F256) (E m) :=
  IsGalois.to_isSeparable

private abbrev O (m : ℕ) (Q : GlobalPlace F256 (W m)) := Q.valuationRing

private noncomputable local instance (priority := 2000)
    oBaseModule (m : ℕ) (Q : GlobalPlace F256 (W m)) :
    Module (O m Q) (W m) :=
  @Algebra.toModule (O m Q) (W m) _ _
    (inferInstance : Algebra (O m Q) (W m))

private noncomputable local instance (priority := 2000)
    oBaseFaithfulSMul (m : ℕ) (Q : GlobalPlace F256 (W m)) :
    FaithfulSMul (O m Q) (W m) :=
  (faithfulSMul_iff_algebraMap_injective (O m Q) (W m)).2
    (ValuationSubring.subtype_injective Q.valuationRing)

private noncomputable local instance (priority := 2000)
    oClosureAlgebra (m : ℕ) (Q : GlobalPlace F256 (W m)) :
    Algebra (O m Q) (E m) :=
  ((algebraMap (W m) (E m)).comp (algebraMap (O m Q) (W m))).toAlgebra

private noncomputable local instance (priority := 2000)
    oClosureSMul (m : ℕ) (Q : GlobalPlace F256 (W m)) :
    SMul (O m Q) (E m) :=
  (oClosureAlgebra m Q).toSMul

private noncomputable local instance (priority := 2000)
    oClosureModule (m : ℕ) (Q : GlobalPlace F256 (W m)) :
    Module (O m Q) (E m) :=
  @Algebra.toModule (O m Q) (E m) _ _ (oClosureAlgebra m Q)

private noncomputable local instance oBaseScalarTower (m : ℕ)
    (Q : GlobalPlace F256 (W m)) : IsScalarTower (O m Q) (W m) (E m) :=
  IsScalarTower.of_algebraMap_eq' rfl

private abbrev C (m : ℕ) (Q : GlobalPlace F256 (W m)) :=
  integralClosure (O m Q) (E m)

private noncomputable local instance oIntegralClosureFractionTower (m : ℕ)
    (Q : GlobalPlace F256 (W m)) : IsScalarTower (O m Q) (C m Q) (E m) :=
  IsScalarTower.of_algebraMap_eq' rfl

private noncomputable local instance oIntegralClosureTorsionFree (m : ℕ)
    (Q : GlobalPlace F256 (W m)) : Module.IsTorsionFree (O m Q) (C m Q) := by
  letI : Module.IsTorsionFree (O m Q) (E m) :=
    Module.IsTorsionFree.trans_faithfulSMul (O m Q) (W m) (E m)
  exact IsIntegralClosure.isTorsionFree (O m Q) (E m)

private noncomputable local instance oIntegralClosureFinite (m : ℕ)
    (Q : GlobalPlace F256 (W m)) : Module.Finite (O m Q) (C m Q) := by
  letI : IsDiscreteValuationRing (O m Q) :=
    Q.valuationRing_isDiscreteValuationRing
  exact IsIntegralClosure.finite (O m Q) (W m) (E m) (C m Q)

private noncomputable local instance oIntegralClosureIsFractionRing (m : ℕ)
    (Q : GlobalPlace F256 (W m)) : IsFractionRing (C m Q) (E m) :=
  integralClosure.isFractionRing_of_finite_extension (W m) (E m)

private noncomputable local instance oIntegralClosureIsDedekind (m : ℕ)
    (Q : GlobalPlace F256 (W m)) : IsDedekindDomain (C m Q) := by
  letI : IsDiscreteValuationRing (O m Q) :=
    Q.valuationRing_isDiscreteValuationRing
  exact integralClosure.isDedekindDomain (O m Q) (W m) (E m)

private noncomputable local instance wRelativeGalFinite (m : ℕ) :
    Finite Gal((E m) / (W m)) :=
  Fintype.finite (AlgEquiv.fintype (W m) (E m))

private noncomputable local instance oIntegralClosureAction (m : ℕ)
    (Q : GlobalPlace F256 (W m)) :
    MulSemiringAction Gal((E m) / (W m)) (C m Q) :=
  IsIntegralClosure.MulSemiringAction (O m Q) (W m) (E m) (C m Q)

private noncomputable local instance oIntegralClosureIsGaloisGroup (m : ℕ)
    (Q : GlobalPlace F256 (W m)) :
    IsGaloisGroup Gal((E m) / (W m)) (O m Q) (C m Q) :=
  IsGaloisGroup.of_isFractionRing Gal((E m) / (W m))
    (O m Q) (C m Q) (W m) (E m)

private noncomputable def comapValuationRingEquiv
    {k K L : Type*} [_root_.Field k] [Finite k] [_root_.Field K] [Algebra k K]
    [_root_.Field L] [Algebra k L] (e : K ≃ₐ[k] L) (Q : GlobalPlace k L) :
    (GlobalPlace.comapAlgEquiv e Q).valuationRing ≃+* Q.valuationRing where
  toFun x := ⟨e x, x.property⟩
  invFun x := ⟨e.symm x, by
    change Q.valuation (e (e.symm x)) ≤ 1
    rw [e.apply_symm_apply]
    exact x.property⟩
  left_inv x := by
    apply Subtype.ext
    exact e.symm_apply_apply x
  right_inv x := by
    apply Subtype.ext
    exact e.apply_symm_apply x
  map_mul' _ _ := by
    apply Subtype.ext
    exact map_mul e _ _
  map_add' _ _ := by
    apply Subtype.ext
    exact map_add e _ _

private instance comapValuationRingEquiv_isLocalHom
    {k K L : Type*} [_root_.Field k] [Finite k] [_root_.Field K] [Algebra k K]
    [_root_.Field L] [Algebra k L] (e : K ≃ₐ[k] L) (Q : GlobalPlace k L) :
    IsLocalHom (comapValuationRingEquiv e Q).toRingHom :=
  ⟨fun x hx => by
    simpa using hx.map (comapValuationRingEquiv e Q).symm.toRingHom⟩

private noncomputable def comapResidueEquiv
    {k K L : Type*} [_root_.Field k] [Finite k] [_root_.Field K] [Algebra k K]
    [_root_.Field L] [Algebra k L] (e : K ≃ₐ[k] L) (Q : GlobalPlace k L) :
    GlobalPlace.residueField (GlobalPlace.comapAlgEquiv e Q) ≃+*
      GlobalPlace.residueField Q :=
  IsLocalRing.ResidueField.mapEquiv (comapValuationRingEquiv e Q)

private theorem comapResidueEquiv_residue
    {k K L : Type*} [_root_.Field k] [Finite k] [_root_.Field K] [Algebra k K]
    [_root_.Field L] [Algebra k L] (e : K ≃ₐ[k] L) (Q : GlobalPlace k L)
    (z : (GlobalPlace.comapAlgEquiv e Q).valuationRing) :
    comapResidueEquiv e Q ((GlobalPlace.comapAlgEquiv e Q).residue z) =
      Q.residue (comapValuationRingEquiv e Q z) := by
  unfold comapResidueEquiv
  exact IsLocalRing.ResidueField.map_residue
    (comapValuationRingEquiv e Q).toRingHom z

private theorem comapResidueEquiv_constants
    {k K L : Type*} [_root_.Field k] [Finite k] [_root_.Field K] [Algebra k K]
    [_root_.Field L] [Algebra k L] (e : K ≃ₐ[k] L) (Q : GlobalPlace k L)
    (a : k) :
    comapResidueEquiv e Q
        (GlobalPlace.constantsToResidue (GlobalPlace.comapAlgEquiv e Q) a) =
      GlobalPlace.constantsToResidue Q a := by
  change comapResidueEquiv e Q
      ((GlobalPlace.comapAlgEquiv e Q).residue
        (GlobalPlace.constantsToValuationRing
          (GlobalPlace.comapAlgEquiv e Q) a)) =
    Q.residue (GlobalPlace.constantsToValuationRing Q a)
  rw [comapResidueEquiv_residue]
  apply congrArg Q.residue
  apply Subtype.ext
  exact e.commutes a

private noncomputable def rationalPlaceComapAlgEquiv
    {k K L : Type*} [_root_.Field k] [Finite k] [_root_.Field K] [Algebra k K]
    [_root_.Field L] [Algebra k L] (e : K ≃ₐ[k] L)
    (Q : RationalPlace k L) : RationalPlace k K where
  place := GlobalPlace.comapAlgEquiv e Q.place
  constantsEquiv := Q.constantsEquiv.trans (comapResidueEquiv e Q.place).symm
  constantsEquiv_apply a := by
    apply (comapResidueEquiv e Q.place).injective
    change comapResidueEquiv e Q.place
        ((comapResidueEquiv e Q.place).symm (Q.constantsEquiv a)) = _
    rw [RingEquiv.apply_symm_apply, Q.constantsEquiv_apply,
      comapResidueEquiv_constants]

private noncomputable def rationalInfinityRationalPlace :
    RationalPlace F256 (RatFunc F256) where
  place := GlobalPlace.rationalInfinity F256
  constantsEquiv := RingEquiv.ofBijective
    (GlobalPlace.constantsToResidue (GlobalPlace.rationalInfinity F256))
    ⟨RingHom.injective _,
      GlobalPlace.rationalInfinity_constantsToResidue_surjective⟩
  constantsEquiv_apply _ := rfl

private noncomputable local instance sourceGaloisWFieldConstantTower :
    IsScalarTower F256 GaloisBaseField SourceGaloisWField :=
  IsScalarTower.of_algebraMap_eq' rfl

private noncomputable local instance sourceGaloisWClosureFieldConstantTower (m : ℕ) :
    IsScalarTower F256 GaloisBaseField (W m) :=
  IsScalarTower.of_algebraMap_eq' rfl

private noncomputable def wFieldEquivClosureOverF256 (m : ℕ) :
    SourceGaloisWField ≃ₐ[F256] W m :=
  (sourceGaloisWFieldEquivClosureField m).restrictScalars F256

private noncomputable def sourceGaloisWClosureZeroRationalPlace (m : ℕ) :
    RationalPlace F256 (W m) :=
  rationalPlaceComapAlgEquiv (wFieldEquivClosureOverF256 m).symm
    (rationalPlaceComapAlgEquiv sourceGaloisWFieldEquivRatFunc.symm
      zeroBaseRationalPlace)

private noncomputable def sourceGaloisWClosureInfinityRationalPlace (m : ℕ) :
    RationalPlace F256 (W m) :=
  rationalPlaceComapAlgEquiv (wFieldEquivClosureOverF256 m).symm
    (rationalPlaceComapAlgEquiv sourceGaloisWFieldEquivRatFunc.symm
      rationalInfinityRationalPlace)

private theorem sourceGaloisWClosureZero_constantsToResidue_bijective (m : ℕ) :
    Function.Bijective
      (GlobalPlace.constantsToResidue (sourceGaloisWClosureZeroPlace m)) := by
  exact (sourceGaloisWClosureZeroRationalPlace m).constantsToResidue_bijective

private theorem sourceGaloisWClosureInfinity_constantsToResidue_bijective (m : ℕ) :
    Function.Bijective
      (GlobalPlace.constantsToResidue (sourceGaloisWClosureInfinityPlace m)) := by
  exact (sourceGaloisWClosureInfinityRationalPlace m).constantsToResidue_bijective

/-- The actual residue degree at a zero-fibre place is the common inertia
degree of that Galois fibre. -/
theorem sourceGaloisWZeroPlace_residueDegree_eq_inertia (m : ℕ)
    (P : SourceGaloisWZeroPrime m) :
    GlobalPlace.residueDegree
        (π := closurePolynomialAlgebra m)
        (ρ := sourceGaloisClosureRatFuncAlgebra m)
        (τ := closurePolynomialRatFuncScalarTower m)
        (φ := sourceGaloisClosureFunctionField m)
        (σ := closureRatFuncIsSeparable m)
        (κ := sourceGaloisClosureConstantAlgebra m)
        (sourceGaloisWZeroPlaceOfPrime m P) =
      sourceGaloisWZeroInertiaDegree m := by
  let Q := sourceGaloisWClosureZeroPlace m
  let O₀ := Q.valuationRing
  let C₀ := C m Q
  let p : Ideal O₀ := IsLocalRing.maximalIdeal O₀
  let H := sourceGaloisWZeroUpperHeightOne m P
  letI : IsDiscreteValuationRing O₀ :=
    Q.valuationRing_isDiscreteValuationRing
  have hH : H.asIdeal.LiesOver p := by
    change P.1.LiesOver
      (IsLocalRing.maximalIdeal (sourceGaloisWClosureZeroPlace m).valuationRing)
    exact P.2.2
  let baseEquiv : F256 ≃+* (O₀ ⧸ p) :=
    RingEquiv.ofBijective (GlobalPlace.constantsToResidue Q)
      (sourceGaloisWClosureZero_constantsToResidue_bijective m)
  let U := sourceGaloisWZeroPlaceOfPrime m P
  have hvaluation : H.valuation (E m) = U.valuation := rfl
  letI : Algebra F256 (GlobalPlace.residueField U) :=
    GlobalPlace.residueAlgebra U
  letI : FiniteDimensional F256 (GlobalPlace.residueField U) :=
    GlobalPlace.residueField_finiteDimensional
      (π := closurePolynomialAlgebra m)
      (ρ := sourceGaloisClosureRatFuncAlgebra m)
      (τ := closurePolynomialRatFuncScalarTower m)
      (φ := sourceGaloisClosureFunctionField m)
      (σ := closureRatFuncIsSeparable m)
      U
  rw [GlobalPlace.residueDegree_eq_finrank
    (π := closurePolynomialAlgebra m)
    (ρ := sourceGaloisClosureRatFuncAlgebra m)
    (τ := closurePolynomialRatFuncScalarTower m)
    (φ := sourceGaloisClosureFunctionField m)
    (σ := closureRatFuncIsSeparable m)]
  simpa only [sourceGaloisWZeroInertiaDegree] using
    (Ideal.finrank_residueField_eq_inertiaDegIn_of_heightOne
      (G := Gal((E m) / (W m))) p H hH U.valuation baseEquiv hvaluation)

/-- The actual residue degree at an infinity-fibre place is the common
inertia degree of that Galois fibre. -/
theorem sourceGaloisWInfinityPlace_residueDegree_eq_inertia (m : ℕ)
    (P : SourceGaloisWInfinityPrime m) :
    GlobalPlace.residueDegree
        (π := closurePolynomialAlgebra m)
        (ρ := sourceGaloisClosureRatFuncAlgebra m)
        (τ := closurePolynomialRatFuncScalarTower m)
        (φ := sourceGaloisClosureFunctionField m)
        (σ := closureRatFuncIsSeparable m)
        (κ := sourceGaloisClosureConstantAlgebra m)
        (sourceGaloisWInfinityPlaceOfPrime m P) =
      sourceGaloisWInfinityInertiaDegree m := by
  let Q := sourceGaloisWClosureInfinityPlace m
  let O₀ := Q.valuationRing
  let C₀ := C m Q
  let p : Ideal O₀ := IsLocalRing.maximalIdeal O₀
  let H := sourceGaloisWInfinityUpperHeightOne m P
  letI : IsDiscreteValuationRing O₀ :=
    Q.valuationRing_isDiscreteValuationRing
  have hH : H.asIdeal.LiesOver p := by
    change P.1.LiesOver
      (IsLocalRing.maximalIdeal (sourceGaloisWClosureInfinityPlace m).valuationRing)
    exact P.2.2
  let baseEquiv : F256 ≃+* (O₀ ⧸ p) :=
    RingEquiv.ofBijective (GlobalPlace.constantsToResidue Q)
      (sourceGaloisWClosureInfinity_constantsToResidue_bijective m)
  let U := sourceGaloisWInfinityPlaceOfPrime m P
  have hvaluation : H.valuation (E m) = U.valuation := rfl
  letI : Algebra F256 (GlobalPlace.residueField U) :=
    GlobalPlace.residueAlgebra U
  letI : FiniteDimensional F256 (GlobalPlace.residueField U) :=
    GlobalPlace.residueField_finiteDimensional
      (π := closurePolynomialAlgebra m)
      (ρ := sourceGaloisClosureRatFuncAlgebra m)
      (τ := closurePolynomialRatFuncScalarTower m)
      (φ := sourceGaloisClosureFunctionField m)
      (σ := closureRatFuncIsSeparable m)
      U
  rw [GlobalPlace.residueDegree_eq_finrank
    (π := closurePolynomialAlgebra m)
    (ρ := sourceGaloisClosureRatFuncAlgebra m)
    (τ := closurePolynomialRatFuncScalarTower m)
    (φ := sourceGaloisClosureFunctionField m)
    (σ := closureRatFuncIsSeparable m)]
  simpa only [sourceGaloisWInfinityInertiaDegree] using
    (Ideal.finrank_residueField_eq_inertiaDegIn_of_heightOne
      (G := Gal((E m) / (W m))) p H hH U.valuation baseEquiv hvaluation)

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
