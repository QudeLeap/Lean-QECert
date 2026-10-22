import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import QEC.Coding.AlgebraicGeometry.Schemes.CharZeroCurveSmoothness
import QEC.Coding.ExpanderCodes.LPSOriginalIntegerFlatModel
import QEC.Coding.ExpanderCodes.LPSOriginalLocalKaehlerInjective
import QEC.Coding.ExpanderCodes.LPSOriginalGlobalNormalizationComparison

/-!
# LPSOriginalCharacteristicZeroSmooth

The actual original complex normalization and the complete rational fibre of
its integer model are smooth. Their literal integral-closure charts have
finite type and are Dedekind domains; the genuine chart comparisons and
open covers preserve their actual scalar maps and projections. The actual
meromorphic valuation rings are formally smooth as well.

This arithmetic prerequisite supports pinned PK22 ex:Xpq, main.tex:484-486,
and th:qLDPC, main.tex:231-238. Uniform smooth reduction in positive
characteristic, Hecke/Frobenius/Weil identities, the LPS spectrum and the exact
explicit quantum family remain unproved. No smoothness assumption is used.
-/

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry
namespace QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section

lemma lpsOriginalMeromorphicValuationRing_formallySmooth
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
    (x : LPSOriginalFilledCurve N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    let V := Valuation.valuationSubring
      (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x))
    letI : Algebra ℂ V :=
      (lpsOriginalComplexConstantsToMeromorphicValuationRing N hpos hN x).toAlgebra
    Algebra.FormallySmooth ℂ V := by
  let := lpsOriginalJFractionEmbedding.toAlgebra
  let V := Valuation.valuationSubring
    (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x))
  let : Algebra ℂ V :=
    (lpsOriginalComplexConstantsToMeromorphicValuationRing N hpos hN x).toAlgebra
  let : IsDiscreteValuationRing V :=
    lpsOriginalMeromorphicValuationRing_isDiscreteValuationRing N hpos hN x
  let : Algebra.EssFiniteType ℂ V :=
    lpsOriginalMeromorphicValuationRing_essFiniteType N hpos hN x
  exact QEC.Coding.AlgebraicGeometry.dvr_formallySmoothCharZero ℂ V

end
end QEC.Coding.TannerLiftedProduct

namespace QEC.Coding.TannerLiftedProduct
noncomputable section
lemma lpsOriginalZeroChart_smooth (N : ℕ) [NeZero N] (hpos : 0 < N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    letI : Algebra ℂ (lpsOriginalComplexNormalZeroChart N hpos) :=
      (lpsOriginalComplexZeroConstantRingHom N hpos).toAlgebra
    Algebra.Smooth ℂ (lpsOriginalComplexNormalZeroChart N hpos) := by
  let := lpsOriginalJFractionEmbedding.toAlgebra
  let R := lpsOriginalComplexNormalZeroChart N hpos
  let : Algebra ℂ R := (lpsOriginalComplexZeroConstantRingHom N hpos).toAlgebra
  let : IsDedekindDomain R := lpsOriginalZeroChart_isDedekindDomain N hpos
  let : Algebra.FiniteType ℂ R := lpsOriginalZeroChart_finiteType N hpos
  exact QEC.Coding.AlgebraicGeometry.dedekindFiniteType_smoothCharZero ℂ R

lemma lpsOriginalInfinityChart_smooth (N : ℕ) [NeZero N] (hpos : 0 < N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    letI : Algebra ℂ (lpsOriginalComplexNormalInfinityChart N hpos) :=
      (lpsOriginalComplexInfinityConstantRingHom N hpos).toAlgebra
    Algebra.Smooth ℂ (lpsOriginalComplexNormalInfinityChart N hpos) := by
  let := lpsOriginalJFractionEmbedding.toAlgebra
  let R := lpsOriginalComplexNormalInfinityChart N hpos
  let : Algebra ℂ R := (lpsOriginalComplexInfinityConstantRingHom N hpos).toAlgebra
  let : IsDedekindDomain R := lpsOriginalInfinityChart_isDedekindDomain N hpos
  let : Algebra.FiniteType ℂ R := lpsOriginalInfinityChart_finiteType N hpos
  exact QEC.Coding.AlgebraicGeometry.dedekindFiniteType_smoothCharZero ℂ R
end
end QEC.Coding.TannerLiftedProduct

open CategoryTheory AlgebraicGeometry
namespace QEC.Coding.TannerLiftedProduct
noncomputable section
lemma lpsOriginalComplexChartToSpecC_smooth
    (N : ℕ) [NeZero N] (hpos : 0 < N) (b : Bool) :
    Smooth (lpsOriginalComplexChartToSpecC N hpos b) := by
  let := lpsOriginalJFractionEmbedding.toAlgebra
  cases b with
  | false =>
    let : Algebra ℂ (lpsOriginalComplexNormalZeroChart N hpos) :=
      (lpsOriginalComplexZeroConstantRingHom N hpos).toAlgebra
    let : Algebra.Smooth ℂ (lpsOriginalComplexNormalZeroChart N hpos) :=
      lpsOriginalZeroChart_smooth N hpos
    change Smooth (Spec.map (CommRingCat.ofHom
      (lpsOriginalComplexZeroConstantRingHom N hpos)))
    apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    change (algebraMap ℂ _).Smooth
    rw [RingHom.smooth_algebraMap]
    infer_instance
  | true =>
    let : Algebra ℂ (lpsOriginalComplexNormalInfinityChart N hpos) :=
      (lpsOriginalComplexInfinityConstantRingHom N hpos).toAlgebra
    let : Algebra.Smooth ℂ (lpsOriginalComplexNormalInfinityChart N hpos) :=
      lpsOriginalInfinityChart_smooth N hpos
    change Smooth (Spec.map (CommRingCat.ofHom
      (lpsOriginalComplexInfinityConstantRingHom N hpos)))
    apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    change (algebraMap ℂ _).Smooth
    rw [RingHom.smooth_algebraMap]
    infer_instance

lemma lpsOriginalComplexNormalGluedToSpecC_smooth
    (N : ℕ) [NeZero N] (hpos : 0 < N) :
    Smooth (lpsOriginalComplexNormalGluedToSpecC N hpos) := by
  let : IsZariskiLocalAtSource (@AlgebraicGeometry.Smooth.{0}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @AlgebraicGeometry.Smooth.{0})
      (Q := @RingHom.Smooth.{0, 0})
  apply (IsZariskiLocalAtSource.iff_of_openCover (P := @AlgebraicGeometry.Smooth.{0})
    (f := lpsOriginalComplexNormalGluedToSpecC N hpos)
    (lpsOriginalComplexNormalSchemeGlueData N hpos).openCover).mpr
  intro b
  change Bool at b
  change Smooth (lpsOriginalComplexNormalGluedChartMap N hpos b ≫
    lpsOriginalComplexNormalGluedToSpecC N hpos)
  rw [lpsOriginalComplexNormalGluedToSpecC_chart]
  exact lpsOriginalComplexChartToSpecC_smooth N hpos b
end
end QEC.Coding.TannerLiftedProduct

namespace QEC.Coding.TannerLiftedProduct
noncomputable section
lemma lpsOriginalIntegerZeroChart_rationalSmooth
    (N : ℕ) [NeZero N] (hpos : 0 < N) :
    letI : Algebra ℤ (lpsOriginalIntegerNormalZeroChart N hpos) :=
      Ring.toIntAlgebra _
    letI : SMul ℤ (lpsOriginalIntegerNormalZeroChart N hpos) := Algebra.toSMul
    letI : Module ℤ (lpsOriginalIntegerNormalZeroChart N hpos) := Algebra.toModule
    Algebra.Smooth ℚ (ℚ ⊗[ℤ] lpsOriginalIntegerNormalZeroChart N hpos) := by
  let : Algebra ℤ (lpsOriginalIntegerNormalZeroChart N hpos) := Ring.toIntAlgebra _
  let : SMul ℤ (lpsOriginalIntegerNormalZeroChart N hpos) := Algebra.toSMul
  let : Module ℤ (lpsOriginalIntegerNormalZeroChart N hpos) := Algebra.toModule
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let J := FractionRing (Polynomial ℚ)
  let F := lpsOriginalGeneratedFunctionFieldQ N hpos
  let : Algebra (Polynomial ℚ) F :=
    ((algebraMap J F).comp (algebraMap (Polynomial ℚ) J)).toAlgebra
  let : IsScalarTower (Polynomial ℚ) J F := .of_algebraMap_eq' rfl
  let : IsScalarTower ℚ (Polynomial ℚ) F := inferInstance
  let : FiniteDimensional J F := lpsOriginalGeneratedFunctionFieldQ_finiteDimensional N hpos
  let R := integralClosure (Polynomial ℚ) F
  let : Algebra ℚ R := (R.restrictScalars ℚ).algebra
  let : IsDedekindDomain R := integralClosure.isDedekindDomain (Polynomial ℚ) J F
  let : Module.Finite (Polynomial ℚ) R :=
    IsIntegralClosure.finite (A := Polynomial ℚ) («K» := J) (L := F) R
  let : Algebra.FiniteType ℚ R := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType ℚ (Polynomial ℚ))
    (inferInstance : Algebra.FiniteType (Polynomial ℚ) R)
  let : Algebra.Smooth ℚ R :=
    QEC.Coding.AlgebraicGeometry.dedekindFiniteType_smoothCharZero ℚ R
  exact Algebra.Smooth.of_equiv
    (lpsOriginalIntegerZeroNormalizationRationalTensorAlgEquiv N hpos).symm

lemma lpsOriginalIntegerInfinityChart_rationalSmooth
    (N : ℕ) [NeZero N] (hpos : 0 < N) :
    letI : Algebra ℤ (lpsOriginalIntegerNormalInfinityChart N hpos) :=
      Ring.toIntAlgebra _
    letI : SMul ℤ (lpsOriginalIntegerNormalInfinityChart N hpos) := Algebra.toSMul
    letI : Module ℤ (lpsOriginalIntegerNormalInfinityChart N hpos) := Algebra.toModule
    Algebra.Smooth ℚ (ℚ ⊗[ℤ] lpsOriginalIntegerNormalInfinityChart N hpos) := by
  let : Algebra ℤ (lpsOriginalIntegerNormalInfinityChart N hpos) := Ring.toIntAlgebra _
  let : SMul ℤ (lpsOriginalIntegerNormalInfinityChart N hpos) := Algebra.toSMul
  let : Module ℤ (lpsOriginalIntegerNormalInfinityChart N hpos) := Algebra.toModule
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let J := FractionRing (Polynomial ℚ)
  let F := lpsOriginalGeneratedFunctionFieldQ N hpos
  let : Algebra (Polynomial ℚ) J := lpsOriginalReciprocalBaseQAlgebra
  let : SMul (Polynomial ℚ) J := Algebra.toSMul
  let : Module (Polynomial ℚ) J := Algebra.toModule
  let : IsFractionRing (Polynomial ℚ) J := lpsOriginalReciprocalBaseQ_isFractionRing
  let : Algebra (Polynomial ℚ) F :=
    (lpsOriginalReciprocalRationalFieldPolynomialMap N hpos).toAlgebra
  let : IsScalarTower (Polynomial ℚ) J F := .of_algebraMap_eq' rfl
  let : IsScalarTower ℚ (Polynomial ℚ) F := inferInstance
  let : FiniteDimensional J F := lpsOriginalGeneratedFunctionFieldQ_finiteDimensional N hpos
  let R := integralClosure (Polynomial ℚ) F
  let : Algebra ℚ R := (R.restrictScalars ℚ).algebra
  let : IsDedekindDomain R := integralClosure.isDedekindDomain (Polynomial ℚ) J F
  let : Module.Finite (Polynomial ℚ) R :=
    IsIntegralClosure.finite (A := Polynomial ℚ) («K» := J) (L := F) R
  let : Algebra.FiniteType ℚ R := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType ℚ (Polynomial ℚ))
    (inferInstance : Algebra.FiniteType (Polynomial ℚ) R)
  let : Algebra.Smooth ℚ R :=
    QEC.Coding.AlgebraicGeometry.dedekindFiniteType_smoothCharZero ℚ R
  exact Algebra.Smooth.of_equiv
    (lpsOriginalIntegerInfinityNormalizationRationalTensorAlgEquiv N hpos).symm
end
end QEC.Coding.TannerLiftedProduct

open CategoryTheory.Limits
namespace QEC.Coding.TannerLiftedProduct
noncomputable section
set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerNormalRationalChart_smooth
    (N : ℕ) [NeZero N] (hpos : 0 < N) (b : Bool) :
    Smooth (pullback.fst
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))
      (lpsOriginalIntegerNormalGluedChartMap N hpos b ≫
        lpsOriginalIntegerNormalGluedToSpecZ N hpos)) := by
  cases b with
  | false =>
    let A := lpsOriginalIntegerNormalZeroChart N hpos
    let : Algebra ℤ A := Ring.toIntAlgebra A
    let : SMul ℤ A := Algebra.toSMul
    let : Module ℤ A := Algebra.toModule
    let : Algebra.Smooth ℚ (ℚ ⊗[ℤ] A) :=
      lpsOriginalIntegerZeroChart_rationalSmooth N hpos
    have hm := lpsOriginalIntegerSpecZ_hom_unique A
      (lpsOriginalIntegerNormalGluedChartMap N hpos false ≫
        lpsOriginalIntegerNormalGluedToSpecZ N hpos)
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ A)))
    rw [hm]
    let e := QEC.Coding.AlgebraicGeometry.NormalizationBaseChange.normalizationTensorSpecIso
      (R := ℤ) (S := ℚ) (AlgEquiv.refl (R := ℚ) (A₁ := ℚ ⊗[ℤ] A))
    have he := QEC.Coding.AlgebraicGeometry.NormalizationBaseChange.normalizationTensorSpecIso_constantRingHomProjection
      (R := ℤ) (S := ℚ) (AlgEquiv.refl (R := ℚ) (A₁ := ℚ ⊗[ℤ] A))
    have hs : Smooth (e.hom ≫ pullback.fst _ _) := by
      rw [he]
      apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
      change (algebraMap ℚ (ℚ ⊗[ℤ] A)).Smooth
      exact RingHom.smooth_algebraMap.mpr inferInstance
    let : Smooth (e.hom ≫ pullback.fst _ _) := hs
    rw [← e.inv_hom_id_assoc (pullback.fst _ _)]
    infer_instance
  | true =>
    let A := lpsOriginalIntegerNormalInfinityChart N hpos
    let : Algebra ℤ A := Ring.toIntAlgebra A
    let : SMul ℤ A := Algebra.toSMul
    let : Module ℤ A := Algebra.toModule
    let : Algebra.Smooth ℚ (ℚ ⊗[ℤ] A) :=
      lpsOriginalIntegerInfinityChart_rationalSmooth N hpos
    have hm := lpsOriginalIntegerSpecZ_hom_unique A
      (lpsOriginalIntegerNormalGluedChartMap N hpos true ≫
        lpsOriginalIntegerNormalGluedToSpecZ N hpos)
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ A)))
    rw [hm]
    let e := QEC.Coding.AlgebraicGeometry.NormalizationBaseChange.normalizationTensorSpecIso
      (R := ℤ) (S := ℚ) (AlgEquiv.refl (R := ℚ) (A₁ := ℚ ⊗[ℤ] A))
    have he := QEC.Coding.AlgebraicGeometry.NormalizationBaseChange.normalizationTensorSpecIso_constantRingHomProjection
      (R := ℤ) (S := ℚ) (AlgEquiv.refl (R := ℚ) (A₁ := ℚ ⊗[ℤ] A))
    have hs : Smooth (e.hom ≫ pullback.fst _ _) := by
      rw [he]
      apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
      change (algebraMap ℚ (ℚ ⊗[ℤ] A)).Smooth
      exact RingHom.smooth_algebraMap.mpr inferInstance
    let : Smooth (e.hom ≫ pullback.fst _ _) := hs
    rw [← e.inv_hom_id_assoc (pullback.fst _ _)]
    infer_instance

set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerNormalRationalFibre_smooth
    (N : ℕ) [NeZero N] (hpos : 0 < N) :
    Smooth (pullback.fst
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))
      (lpsOriginalIntegerNormalGluedToSpecZ N hpos)) := by
  let : IsZariskiLocalAtSource (@AlgebraicGeometry.Smooth.{0}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @AlgebraicGeometry.Smooth.{0})
      (Q := @RingHom.Smooth.{0, 0})
  apply (IsZariskiLocalAtSource.iff_of_openCover (P := @AlgebraicGeometry.Smooth.{0})
    (f := pullback.fst _ _)
    (Scheme.Pullback.openCoverOfRight
      (lpsOriginalIntegerNormalSchemeGlueData N hpos).openCover
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))
      (lpsOriginalIntegerNormalGluedToSpecZ N hpos))).mpr
  intro b
  change Bool at b
  change Smooth (pullback.map
    (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))
    (lpsOriginalIntegerNormalGluedChartMap N hpos b ≫
      lpsOriginalIntegerNormalGluedToSpecZ N hpos)
    (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))
    (lpsOriginalIntegerNormalGluedToSpecZ N hpos)
    (𝟙 _) (lpsOriginalIntegerNormalGluedChartMap N hpos b) (𝟙 _)
    (by simp) (by simp) ≫ pullback.fst _ _)
  simp only [pullback.map, pullback.lift_fst, Category.comp_id]
  exact lpsOriginalIntegerNormalRationalChart_smooth N hpos b
end
end QEC.Coding.TannerLiftedProduct
