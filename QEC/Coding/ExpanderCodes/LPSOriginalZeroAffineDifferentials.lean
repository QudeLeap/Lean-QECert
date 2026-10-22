import QEC.Coding.AlgebraicGeometry.Differentials.AffineKaehlerImage
import QEC.Coding.ExpanderCodes.LPSOriginalZeroPointCoverage
import QEC.Coding.ExpanderCodes.LPSOriginalNormalizationStalkDifferentialComparison

/-!
# Original zero-chart differential preimages

Actual point coverage and the genuine local differential comparison construct affine Kahler preimages exactly for native covectors without interior poles.

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
local instance LPSOriginalZeroAffineDifferentialsDictionary001 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => lpsOriginalComplexNormalZeroChart N hpos
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
local instance LPSOriginalZeroAffineDifferentialsDictionary002 : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance LPSOriginalZeroAffineDifferentialsDictionary003 : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance LPSOriginalZeroAffineDifferentialsDictionary004 : IsScalarTower ℂ P K := .of_algebraMap_eq' rfl
local instance LPSOriginalZeroAffineDifferentialsDictionary005 : Algebra ℂ R := (lpsOriginalComplexZeroConstantRingHom N hpos).toAlgebra
local instance LPSOriginalZeroAffineDifferentialsDictionary006 : SMul ℂ R := Algebra.toSMul
local instance LPSOriginalZeroAffineDifferentialsDictionary007 : Module ℂ R := Algebra.toModule
local instance LPSOriginalZeroAffineDifferentialsDictionary008 : SMulCommClass ℂ R R where
  smul_comm c a b := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalZeroAffineDifferentialsDictionary009 : SMul R (KaehlerDifferential ℂ R) := instSMulKaehlerDifferentialOfSMulCommClass ℂ R
local instance LPSOriginalZeroAffineDifferentialsDictionary010 : Module R (KaehlerDifferential ℂ R) := instModuleKaehlerDifferentialOfSMulCommClass ℂ R
local instance LPSOriginalZeroAffineDifferentialsDictionary011 : IsScalarTower ℂ R K := .of_algebraMap_eq fun c =>
  (lpsOriginalZeroConstant_value N hpos c).symm
local instance LPSOriginalZeroAffineDifferentialsDictionary012 : SMulCommClass ℂ R K where
  smul_comm c r k := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalZeroAffineDifferentialsDictionary013 : SMul R (KaehlerDifferential ℂ K) := instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalZeroAffineDifferentialsDictionary014 : Module R (KaehlerDifferential ℂ K) := instModuleKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalZeroAffineDifferentialsDictionary015 : IsDedekindDomain R := lpsOriginalZeroChart_isDedekindDomain N hpos
local instance LPSOriginalZeroAffineDifferentialsDictionary016 : IsFractionRing R K := lpsOriginalZeroChart_isFractionRing N hpos

section localPoint
variable (x : LPSOriginalFilledCurve N)
local notation "V" => Valuation.valuationSubring
  (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x))
local instance LPSOriginalZeroAffineDifferentialsDictionary017 : Algebra V K := (ValuationSubring.subtype V).toAlgebra
local instance LPSOriginalZeroAffineDifferentialsDictionary018 : SMul V K := Algebra.toSMul
local instance LPSOriginalZeroAffineDifferentialsDictionary019 : Module V K := Algebra.toModule
local instance LPSOriginalZeroAffineDifferentialsDictionary020 : SMulCommClass ℂ V K where
  smul_comm c f g := by
    change algebraMap ℂ K c * (f.val * g) = f.val * (algebraMap ℂ K c * g)
    ring
local instance LPSOriginalZeroAffineDifferentialsDictionary021 : SMul V (KaehlerDifferential ℂ K) := instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalZeroAffineDifferentialsDictionary022 : Module V (KaehlerDifferential ℂ K) := instModuleKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalZeroAffineDifferentialsDictionary023 : Algebra ℂ V :=
  (lpsOriginalComplexConstantsToMeromorphicValuationRing N hpos hN x).toAlgebra
local instance LPSOriginalZeroAffineDifferentialsDictionary024 : IsScalarTower ℂ V K := .of_algebraMap_eq fun c => by rfl

/-- Actual zero-chart affine differential preimages have no native pole at each point of that chart. -/
lemma lpsOriginalZeroAffineKaehler_nativeNoPole
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X))
    (omega : KaehlerDifferential ℂ K)
    (h : omega ∈ (KaehlerDifferential.map ℂ ℂ R K).range) :
    0 ≤ meromorphicOrderValuation (lpsOriginalLocalChartCenter N hN x)
      (lpsOriginalNativeCovectorToLocal N hN x
        (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN omega)) := by
  apply (lpsOriginalLocalKaehlerRange_iff_nativeNoPole N hpos hN x omega).mp
  exact kaehler_field_map_range_le_heightOne ℂ R K
    (lpsOriginalZeroHeightOneCentre N hpos hN x hj) V
    (lpsOriginalZeroHeightOneCentre_valuationRing N hpos hN x hj) (fun _ => rfl) omega h

/-- A native differential without a local pole has a clearing scalar outside the actual zero evaluation kernel. -/
lemma lpsOriginalZeroAffineKaehler_localClear
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X))
    (omega : KaehlerDifferential ℂ K)
    (h : 0 ≤ meromorphicOrderValuation (lpsOriginalLocalChartCenter N hN x)
      (lpsOriginalNativeCovectorToLocal N hN x
        (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN omega))) :
    ∃ s : R, s ∉ RingHom.ker (lpsOriginalZeroNormalChartEvaluation N hpos hN x hj) ∧
      s • omega ∈ (KaehlerDifferential.map ℂ ℂ R K).range := by
  have hv := (lpsOriginalLocalKaehlerRange_iff_nativeNoPole N hpos hN x omega).mpr h
  exact kaehler_field_map_range_heightOne_clear ℂ R K
    (lpsOriginalZeroHeightOneCentre N hpos hN x hj) V
    (lpsOriginalZeroHeightOneCentre_valuationRing N hpos hN x hj) (fun _ => rfl) omega hv
end localPoint

/-- The actual zero affine Kahler image consists exactly of native differentials without interior poles. -/
lemma lpsOriginalZeroAffineKaehlerRange_iff_interiorNativeNoPole
    (omega : KaehlerDifferential ℂ K) :
    omega ∈ (KaehlerDifferential.map ℂ ℂ R K).range ↔
      ∀ x : Q, 0 ≤ meromorphicOrderValuation (lpsOriginalLocalChartCenter N hN (Sum.inl x))
        (lpsOriginalNativeCovectorToLocal N hN (Sum.inl x)
          (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN omega)) := by
  constructor
  · intro h x
    exact lpsOriginalZeroAffineKaehler_nativeNoPole N hpos hN (Sum.inl x)
      (lpsOriginalFieldJ_interior_order_nonnegative N hpos hN x) omega h
  · intro h
    apply submodule_mem_of_forall_maximal_clear R (KaehlerDifferential ℂ K)
      (KaehlerDifferential.map ℂ ℂ R K).range omega
    intro M hM
    obtain ⟨x,hx⟩ := lpsOriginalZeroNormalChart_allMaximalPoints N hpos hN M
    obtain ⟨s,hs,hsomega⟩ := lpsOriginalZeroAffineKaehler_localClear N hpos hN (Sum.inl x)
      (lpsOriginalFieldJ_interior_order_nonnegative N hpos hN x) omega (h x)
    exact ⟨s,by rwa [hx],hsomega⟩
end
end QEC.Coding.TannerLiftedProduct
