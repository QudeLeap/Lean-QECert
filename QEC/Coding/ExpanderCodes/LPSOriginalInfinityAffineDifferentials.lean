import QEC.Coding.AlgebraicGeometry.Differentials.AffineKaehlerImage
import QEC.Coding.ExpanderCodes.LPSOriginalInfinityPointCoverage
import QEC.Coding.ExpanderCodes.LPSOriginalNormalizationStalkDifferentialComparison

/-!
# Original reciprocal-chart differential preimages

Actual reciprocal point coverage and genuine local differential comparison construct Kahler preimages exactly for native covectors without poles on the actual inverse-j regular-point domain.

Derived internal PK22 ex:Xpq closure, pinned main.tex484–486, for parent #449.
This proves actual affine preimages; overlap compatibility, torsion/smoothness,
global differential/sheaf/GAGA comparison, good reduction, Hecke/Frobenius/Weil
and the exact public quantum-family theorem remain further proof obligations.
-/

namespace QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance LPSOriginalInfinityAffineDifferentialsDictionary001 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => lpsOriginalComplexNormalInfinityChart N hpos
local notation "S" => lpsOriginalInfinityRegularPoints N hpos hN
local instance LPSOriginalInfinityAffineDifferentialsDictionary002 : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance LPSOriginalInfinityAffineDifferentialsDictionary003 : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance LPSOriginalInfinityAffineDifferentialsDictionary004 : IsScalarTower ℂ P K := .of_algebraMap_eq' rfl
local instance LPSOriginalInfinityAffineDifferentialsDictionary005 : Algebra ℂ R := (lpsOriginalComplexInfinityConstantRingHom N hpos).toAlgebra
local instance LPSOriginalInfinityAffineDifferentialsDictionary006 : SMul ℂ R := Algebra.toSMul
local instance LPSOriginalInfinityAffineDifferentialsDictionary007 : Module ℂ R := Algebra.toModule
local instance LPSOriginalInfinityAffineDifferentialsDictionary008 : SMulCommClass ℂ R R where
  smul_comm c a b := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalInfinityAffineDifferentialsDictionary009 : SMul R (KaehlerDifferential ℂ R) := instSMulKaehlerDifferentialOfSMulCommClass ℂ R
local instance LPSOriginalInfinityAffineDifferentialsDictionary010 : Module R (KaehlerDifferential ℂ R) := instModuleKaehlerDifferentialOfSMulCommClass ℂ R
local instance LPSOriginalInfinityAffineDifferentialsDictionary011 : IsScalarTower ℂ R K := .of_algebraMap_eq fun c =>
  (lpsOriginalInfinityConstant_value N hpos c).symm
local instance LPSOriginalInfinityAffineDifferentialsDictionary012 : SMulCommClass ℂ R K where
  smul_comm c r k := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalInfinityAffineDifferentialsDictionary013 : SMul R (KaehlerDifferential ℂ K) := instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalInfinityAffineDifferentialsDictionary014 : Module R (KaehlerDifferential ℂ K) := instModuleKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalInfinityAffineDifferentialsDictionary015 : IsDedekindDomain R := lpsOriginalInfinityChart_isDedekindDomain N hpos
local instance LPSOriginalInfinityAffineDifferentialsDictionary016 : IsFractionRing R K := lpsOriginalInfinityChart_isFractionRing N hpos

section localPoint
variable (x : LPSOriginalFilledCurve N)
local notation "V" => Valuation.valuationSubring
  (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x))
local instance LPSOriginalInfinityAffineDifferentialsDictionary017 : Algebra V K := (ValuationSubring.subtype V).toAlgebra
local instance LPSOriginalInfinityAffineDifferentialsDictionary018 : SMul V K := Algebra.toSMul
local instance LPSOriginalInfinityAffineDifferentialsDictionary019 : Module V K := Algebra.toModule
local instance LPSOriginalInfinityAffineDifferentialsDictionary020 : SMulCommClass ℂ V K where
  smul_comm c f g := by
    change algebraMap ℂ K c * (f.val * g) = f.val * (algebraMap ℂ K c * g)
    ring
local instance LPSOriginalInfinityAffineDifferentialsDictionary021 : SMul V (KaehlerDifferential ℂ K) := instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalInfinityAffineDifferentialsDictionary022 : Module V (KaehlerDifferential ℂ K) := instModuleKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalInfinityAffineDifferentialsDictionary023 : Algebra ℂ V :=
  (lpsOriginalComplexConstantsToMeromorphicValuationRing N hpos hN x).toAlgebra
local instance LPSOriginalInfinityAffineDifferentialsDictionary024 : IsScalarTower ℂ V K := .of_algebraMap_eq fun c => by rfl

/-- Actual reciprocal-chart affine differential preimages have no native pole at each point of that chart. -/
lemma lpsOriginalInfinityAffineKaehler_nativeNoPole
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹)
    (omega : KaehlerDifferential ℂ K)
    (h : omega ∈ (KaehlerDifferential.map ℂ ℂ R K).range) :
    0 ≤ meromorphicOrderValuation (lpsOriginalLocalChartCenter N hN x)
      (lpsOriginalNativeCovectorToLocal N hN x
        (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN omega)) := by
  apply (lpsOriginalLocalKaehlerRange_iff_nativeNoPole N hpos hN x omega).mp
  exact kaehler_field_map_range_le_heightOne ℂ R K
    (lpsOriginalInfinityHeightOneCentre N hpos hN x hj) V
    (lpsOriginalInfinityHeightOneCentre_valuationRing N hpos hN x hj) (fun _ => rfl) omega h

/-- A native differential without a local pole has a clearing scalar outside the actual reciprocal evaluation kernel. -/
lemma lpsOriginalInfinityAffineKaehler_localClear
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹)
    (omega : KaehlerDifferential ℂ K)
    (h : 0 ≤ meromorphicOrderValuation (lpsOriginalLocalChartCenter N hN x)
      (lpsOriginalNativeCovectorToLocal N hN x
        (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN omega))) :
    ∃ s : R, s ∉ RingHom.ker (lpsOriginalInfinityNormalChartEvaluation N hpos hN x hj) ∧
      s • omega ∈ (KaehlerDifferential.map ℂ ℂ R K).range := by
  have hv := (lpsOriginalLocalKaehlerRange_iff_nativeNoPole N hpos hN x omega).mpr h
  exact kaehler_field_map_range_heightOne_clear ℂ R K
    (lpsOriginalInfinityHeightOneCentre N hpos hN x hj) V
    (lpsOriginalInfinityHeightOneCentre_valuationRing N hpos hN x hj) (fun _ => rfl) omega hv
end localPoint

/-- The actual reciprocal affine Kahler image consists exactly of native differentials without poles on the genuine reciprocal domain. -/
lemma lpsOriginalInfinityAffineKaehlerRange_iff_nativeNoPole
    (omega : KaehlerDifferential ℂ K) :
    omega ∈ (KaehlerDifferential.map ℂ ℂ R K).range ↔
      ∀ x : S, 0 ≤ meromorphicOrderValuation (lpsOriginalLocalChartCenter N hN x.val)
        (lpsOriginalNativeCovectorToLocal N hN x.val
          (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN omega)) := by
  constructor
  · intro h x
    exact lpsOriginalInfinityAffineKaehler_nativeNoPole N hpos hN x.val x.property omega h
  · intro h
    apply submodule_mem_of_forall_maximal_clear R (KaehlerDifferential ℂ K)
      (KaehlerDifferential.map ℂ ℂ R K).range omega
    intro M hM
    obtain ⟨x,hx⟩ := lpsOriginalInfinityNormalChart_allMaximalPoints N hpos hN M
    obtain ⟨s,hs,hsomega⟩ := lpsOriginalInfinityAffineKaehler_localClear N hpos hN
      x.val x.property omega (h x)
    exact ⟨s,by rwa [hx],hsomega⟩
end
end QEC.Coding.TannerLiftedProduct
