import QEC.Coding.ExpanderCodes.LPSOriginalZeroAffineDifferentials
import QEC.Coding.ExpanderCodes.LPSOriginalInfinityAffineDifferentials

/-!
# Original two-chart differential preimages

Native no poles at every actual filled point are equivalent to membership in both genuine affine Kahler images. Construct both actual preimages using the original interior and cusp cover.

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
local instance LPSOriginalTwoChartDifferentialsDictionary001 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => lpsOriginalComplexNormalZeroChart N hpos
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
local instance LPSOriginalTwoChartDifferentialsDictionary002 : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance LPSOriginalTwoChartDifferentialsDictionary003 : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance LPSOriginalTwoChartDifferentialsDictionary004 : IsScalarTower ℂ P K := .of_algebraMap_eq' rfl
local instance LPSOriginalTwoChartDifferentialsDictionary005 : Algebra ℂ R := (lpsOriginalComplexZeroConstantRingHom N hpos).toAlgebra
local instance LPSOriginalTwoChartDifferentialsDictionary006 : SMul ℂ R := Algebra.toSMul
local instance LPSOriginalTwoChartDifferentialsDictionary007 : Module ℂ R := Algebra.toModule
local instance LPSOriginalTwoChartDifferentialsDictionary008 : SMulCommClass ℂ R R where
  smul_comm c a b := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalTwoChartDifferentialsDictionary009 : SMul R (KaehlerDifferential ℂ R) := instSMulKaehlerDifferentialOfSMulCommClass ℂ R
local instance LPSOriginalTwoChartDifferentialsDictionary010 : Module R (KaehlerDifferential ℂ R) := instModuleKaehlerDifferentialOfSMulCommClass ℂ R
local instance LPSOriginalTwoChartDifferentialsDictionary011 : IsScalarTower ℂ R K := .of_algebraMap_eq fun c =>
  (lpsOriginalZeroConstant_value N hpos c).symm
local instance LPSOriginalTwoChartDifferentialsDictionary012 : SMulCommClass ℂ R K where
  smul_comm c r k := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalTwoChartDifferentialsDictionary013 : SMul R (KaehlerDifferential ℂ K) := instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalTwoChartDifferentialsDictionary014 : Module R (KaehlerDifferential ℂ K) := instModuleKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalTwoChartDifferentialsDictionary015 : IsDedekindDomain R := lpsOriginalZeroChart_isDedekindDomain N hpos
local instance LPSOriginalTwoChartDifferentialsDictionary016 : IsFractionRing R K := lpsOriginalZeroChart_isFractionRing N hpos

local notation "I" => lpsOriginalComplexNormalInfinityChart N hpos
local instance LPSOriginalTwoChartDifferentialsDictionary017 : Algebra ℂ I := (lpsOriginalComplexInfinityConstantRingHom N hpos).toAlgebra
local instance LPSOriginalTwoChartDifferentialsDictionary018 : SMul ℂ I := Algebra.toSMul
local instance LPSOriginalTwoChartDifferentialsDictionary019 : Module ℂ I := Algebra.toModule
local instance LPSOriginalTwoChartDifferentialsDictionary020 : SMulCommClass ℂ I I where
  smul_comm c a b := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalTwoChartDifferentialsDictionary021 : SMul I (KaehlerDifferential ℂ I) := instSMulKaehlerDifferentialOfSMulCommClass ℂ I
local instance LPSOriginalTwoChartDifferentialsDictionary022 : Module I (KaehlerDifferential ℂ I) := instModuleKaehlerDifferentialOfSMulCommClass ℂ I
local instance LPSOriginalTwoChartDifferentialsDictionary023 : IsScalarTower ℂ I K := .of_algebraMap_eq fun c =>
  (lpsOriginalInfinityConstant_value N hpos c).symm
local instance LPSOriginalTwoChartDifferentialsDictionary024 : SMulCommClass ℂ I K where
  smul_comm c r k := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalTwoChartDifferentialsDictionary025 : SMul I (KaehlerDifferential ℂ K) := instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalTwoChartDifferentialsDictionary026 : Module I (KaehlerDifferential ℂ K) := instModuleKaehlerDifferentialOfSMulCommClass ℂ K

/-- Membership in both actual affine Kahler images is exactly native no poles at every filled-curve point. -/
lemma lpsOriginalTwoAffineKaehlerRanges_iff_allNativeNoPole
    (omega : KaehlerDifferential ℂ K) :
    (omega ∈ (KaehlerDifferential.map ℂ ℂ R K).range ∧
      omega ∈ (KaehlerDifferential.map ℂ ℂ I K).range) ↔
      ∀ x : LPSOriginalFilledCurve N,
        0 ≤ meromorphicOrderValuation (lpsOriginalLocalChartCenter N hN x)
          (lpsOriginalNativeCovectorToLocal N hN x
            (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN omega)) := by
  rw [lpsOriginalZeroAffineKaehlerRange_iff_interiorNativeNoPole N hpos hN,
    lpsOriginalInfinityAffineKaehlerRange_iff_nativeNoPole N hpos hN]
  constructor
  · rintro ⟨hz,hi⟩ (x | c)
    · exact hz x
    · exact hi ⟨Sum.inr c,lpsOriginalFieldJ_inverse_cusp_order_nonnegative N hpos hN c⟩
  · intro h
    exact ⟨fun x => h (Sum.inl x), fun x => h x.val⟩

/-- Construct actual zero and reciprocal affine differential preimages from native no poles at every actual filled point. -/
lemma lpsOriginalNativeNoPole_exists_twoAffineKaehlerPreimages
    (omega : KaehlerDifferential ℂ K)
    (h : ∀ x : LPSOriginalFilledCurve N,
      0 ≤ meromorphicOrderValuation (lpsOriginalLocalChartCenter N hN x)
        (lpsOriginalNativeCovectorToLocal N hN x
          (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN omega))) :
    ∃ (tauZero : KaehlerDifferential ℂ R) (tauInfinity : KaehlerDifferential ℂ I),
      KaehlerDifferential.map ℂ ℂ R K tauZero = omega ∧
      KaehlerDifferential.map ℂ ℂ I K tauInfinity = omega := by
  obtain ⟨⟨tauZero,hz⟩,⟨tauInfinity,hi⟩⟩ :=
    (lpsOriginalTwoAffineKaehlerRanges_iff_allNativeNoPole N hpos hN omega).mpr h
  exact ⟨tauZero,tauInfinity,hz,hi⟩
end
end QEC.Coding.TannerLiftedProduct
