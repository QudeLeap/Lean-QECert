import QEC.Coding.ExpanderCodes.LPSOriginalAffineKaehlerInjective
import QEC.Coding.AlgebraicGeometry.Differentials.AffineKaehlerInjective
import QEC.Coding.ExpanderCodes.LPSOriginalTwoChartDifferentials

/-!
# Compatible original affine differentials

Prove actual Laurent differential injection through genuine localization and literal complex scalar diagrams. Construct the unique pair of actual affine preimages whose restrictions agree on this real overlap.

Derived internal PK22 ex:Xpq machinery, pinned main.tex484–486, for parent #449.
This proves actual differential injection and compatible affine preimages.
Genuine global differential sheaf/gluing/GAGA, good reduction, Hecke/Frobenius/Weil
and the exact arbitrary-finite-field public quantum family remain outstanding.
No public node changes status.
-/

namespace QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance LPSOriginalAffineKaehlerCompatibilityDictionary001 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => lpsOriginalComplexNormalZeroChart N hpos
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
local instance LPSOriginalAffineKaehlerCompatibilityDictionary002 : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance LPSOriginalAffineKaehlerCompatibilityDictionary003 : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance LPSOriginalAffineKaehlerCompatibilityDictionary004 : IsScalarTower ℂ P K := .of_algebraMap_eq' rfl
local instance LPSOriginalAffineKaehlerCompatibilityDictionary005 : Algebra ℂ R := (lpsOriginalComplexZeroConstantRingHom N hpos).toAlgebra
local instance LPSOriginalAffineKaehlerCompatibilityDictionary006 : SMul ℂ R := Algebra.toSMul
local instance LPSOriginalAffineKaehlerCompatibilityDictionary007 : Module ℂ R := Algebra.toModule
local instance LPSOriginalAffineKaehlerCompatibilityDictionary008 : SMulCommClass ℂ R R where
  smul_comm c a b := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalAffineKaehlerCompatibilityDictionary009 : SMul R (KaehlerDifferential ℂ R) := instSMulKaehlerDifferentialOfSMulCommClass ℂ R
local instance LPSOriginalAffineKaehlerCompatibilityDictionary010 : Module R (KaehlerDifferential ℂ R) := instModuleKaehlerDifferentialOfSMulCommClass ℂ R
local instance LPSOriginalAffineKaehlerCompatibilityDictionary011 : IsScalarTower ℂ R K := .of_algebraMap_eq fun c =>
  (lpsOriginalZeroConstant_value N hpos c).symm
local instance LPSOriginalAffineKaehlerCompatibilityDictionary012 : SMulCommClass ℂ R K where
  smul_comm c r k := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalAffineKaehlerCompatibilityDictionary013 : SMul R (KaehlerDifferential ℂ K) := instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalAffineKaehlerCompatibilityDictionary014 : Module R (KaehlerDifferential ℂ K) := instModuleKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalAffineKaehlerCompatibilityDictionary015 : IsDedekindDomain R := lpsOriginalZeroChart_isDedekindDomain N hpos
local instance LPSOriginalAffineKaehlerCompatibilityDictionary016 : IsFractionRing R K := lpsOriginalZeroChart_isFractionRing N hpos

local notation "I" => lpsOriginalComplexNormalInfinityChart N hpos
local instance LPSOriginalAffineKaehlerCompatibilityDictionary017 : Algebra ℂ I := (lpsOriginalComplexInfinityConstantRingHom N hpos).toAlgebra
local instance LPSOriginalAffineKaehlerCompatibilityDictionary018 : SMul ℂ I := Algebra.toSMul
local instance LPSOriginalAffineKaehlerCompatibilityDictionary019 : Module ℂ I := Algebra.toModule
local instance LPSOriginalAffineKaehlerCompatibilityDictionary020 : SMulCommClass ℂ I I where
  smul_comm c a b := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalAffineKaehlerCompatibilityDictionary021 : SMul I (KaehlerDifferential ℂ I) := instSMulKaehlerDifferentialOfSMulCommClass ℂ I
local instance LPSOriginalAffineKaehlerCompatibilityDictionary022 : Module I (KaehlerDifferential ℂ I) := instModuleKaehlerDifferentialOfSMulCommClass ℂ I
local instance LPSOriginalAffineKaehlerCompatibilityDictionary023 : IsScalarTower ℂ I K := .of_algebraMap_eq fun c =>
  (lpsOriginalInfinityConstant_value N hpos c).symm
local instance LPSOriginalAffineKaehlerCompatibilityDictionary024 : SMulCommClass ℂ I K where
  smul_comm c r k := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalAffineKaehlerCompatibilityDictionary025 : SMul I (KaehlerDifferential ℂ K) := instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalAffineKaehlerCompatibilityDictionary026 : Module I (KaehlerDifferential ℂ K) := instModuleKaehlerDifferentialOfSMulCommClass ℂ K


local notation "L" => LaurentPolynomial ℂ
local notation "T" => lpsOriginalComplexNormalLaurentChart N hpos
local instance LPSOriginalAffineKaehlerCompatibilityDictionary027 : Algebra L K := (lpsOriginalComplexLaurentBaseToGeneratedField N hpos).toAlgebra

/-- The structural Laurent-overlap complex constants have their unchanged values in the SAME original field. -/
lemma lpsOriginalLaurentConstant_value (c : ℂ) :
    (lpsOriginalComplexLaurentConstantRingHom N hpos c).val = algebraMap ℂ K c := by
  have hc := congrArg (fun t : T => t.val)
    (RingHom.congr_fun (lpsOriginalComplexZeroConstantOverlapRingHomDiagram N hpos) c)
  change (lpsOriginalComplexZeroConstantRingHom N hpos c).val =
    (lpsOriginalComplexLaurentConstantRingHom N hpos c).val at hc
  exact hc.symm.trans (lpsOriginalZeroConstant_value N hpos c)

local instance LPSOriginalAffineKaehlerCompatibilityDictionary028 : Algebra ℂ T := (lpsOriginalComplexLaurentConstantRingHom N hpos).toAlgebra
local instance LPSOriginalAffineKaehlerCompatibilityDictionary029 : SMul ℂ T := Algebra.toSMul
local instance LPSOriginalAffineKaehlerCompatibilityDictionary030 : Module ℂ T := Algebra.toModule
local instance LPSOriginalAffineKaehlerCompatibilityDictionary031 : SMulCommClass ℂ T T where
  smul_comm c a b := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalAffineKaehlerCompatibilityDictionary032 : SMul T (KaehlerDifferential ℂ T) := instSMulKaehlerDifferentialOfSMulCommClass ℂ T
local instance LPSOriginalAffineKaehlerCompatibilityDictionary033 : Module T (KaehlerDifferential ℂ T) := instModuleKaehlerDifferentialOfSMulCommClass ℂ T
local instance LPSOriginalAffineKaehlerCompatibilityDictionary034 : IsScalarTower ℂ T K := .of_algebraMap_eq fun c =>
  (lpsOriginalLaurentConstant_value N hpos c).symm
local instance LPSOriginalAffineKaehlerCompatibilityDictionary035 : SMulCommClass ℂ T K where
  smul_comm c r k := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalAffineKaehlerCompatibilityDictionary036 : SMul T (KaehlerDifferential ℂ K) := instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalAffineKaehlerCompatibilityDictionary037 : Module T (KaehlerDifferential ℂ K) := instModuleKaehlerDifferentialOfSMulCommClass ℂ K

local instance LPSOriginalAffineKaehlerCompatibilityDictionary038 : Algebra R T := (lpsOriginalComplexNormalZeroToLaurent N hpos).toAlgebra
local instance LPSOriginalAffineKaehlerCompatibilityDictionary039 : SMul R T := Algebra.toSMul
local instance LPSOriginalAffineKaehlerCompatibilityDictionary040 : Module R T := Algebra.toModule
local instance LPSOriginalAffineKaehlerCompatibilityDictionary041 : IsScalarTower R T K := .of_algebraMap_eq fun r => by rfl
local instance LPSOriginalAffineKaehlerCompatibilityDictionary042 : IsScalarTower ℂ R T := .of_algebraMap_eq fun c =>
  (RingHom.congr_fun (lpsOriginalComplexZeroConstantOverlapRingHomDiagram N hpos) c).symm
local instance LPSOriginalAffineKaehlerCompatibilityDictionary043 : SMulCommClass ℂ R T where
  smul_comm c r t := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalAffineKaehlerCompatibilityDictionary044 : SMul R (KaehlerDifferential ℂ T) := instSMulKaehlerDifferentialOfSMulCommClass ℂ T
local instance LPSOriginalAffineKaehlerCompatibilityDictionary045 : Module R (KaehlerDifferential ℂ T) := instModuleKaehlerDifferentialOfSMulCommClass ℂ T
local instance LPSOriginalAffineKaehlerCompatibilityDictionary046 : IsLocalization.Away (algebraMap P R Polynomial.X) T :=
  lpsOriginalComplexNormalLaurent_localization N hpos

local instance LPSOriginalAffineKaehlerCompatibilityDictionary047 : Algebra I T := (lpsOriginalComplexNormalInfinityToLaurent N hpos).toAlgebra
local instance LPSOriginalAffineKaehlerCompatibilityDictionary048 : SMul I T := Algebra.toSMul
local instance LPSOriginalAffineKaehlerCompatibilityDictionary049 : Module I T := Algebra.toModule
local instance LPSOriginalAffineKaehlerCompatibilityDictionary050 : IsScalarTower I T K := .of_algebraMap_eq fun r => by rfl
local instance LPSOriginalAffineKaehlerCompatibilityDictionary051 : IsScalarTower ℂ I T := .of_algebraMap_eq fun c =>
  (RingHom.congr_fun (lpsOriginalComplexInfinityConstantOverlapRingHomDiagram N hpos) c).symm
local instance LPSOriginalAffineKaehlerCompatibilityDictionary052 : SMulCommClass ℂ I T where
  smul_comm c r t := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalAffineKaehlerCompatibilityDictionary053 : SMul I (KaehlerDifferential ℂ T) := instSMulKaehlerDifferentialOfSMulCommClass ℂ T
local instance LPSOriginalAffineKaehlerCompatibilityDictionary054 : Module I (KaehlerDifferential ℂ T) := instModuleKaehlerDifferentialOfSMulCommClass ℂ T

include hN in
/-- Genuine zero-to-Laurent localization proves the actual overlap differential map injective. -/
lemma lpsOriginalLaurentKaehler_map_injective :
    Function.Injective (KaehlerDifferential.map ℂ ℂ T K) :=
  kaehler_field_map_injective_localization ℂ R T K (Submonoid.powers (algebraMap P R Polynomial.X))
    (lpsOriginalZeroAffineKaehler_map_injective N hpos hN)

include hN in
/-- Two actual affine differentials with equal original field images have equal restrictions in the actual Laurent differential module. -/
lemma lpsOriginalAffineKaehler_overlap_compatible
    (tau : KaehlerDifferential ℂ R) (eta : KaehlerDifferential ℂ I)
    (he : KaehlerDifferential.map ℂ ℂ R K tau = KaehlerDifferential.map ℂ ℂ I K eta) :
    KaehlerDifferential.map ℂ ℂ R T tau = KaehlerDifferential.map ℂ ℂ I T eta := by
  apply lpsOriginalLaurentKaehler_map_injective N hpos hN
  rw [← kaehler_field_map_comp ℂ R T K, ← kaehler_field_map_comp ℂ I T K]
  exact he

/-- Construct the unique pair of actual affine preimages with equal Laurent restrictions from native no poles at every filled point. -/
lemma lpsOriginalNativeNoPole_existsUnique_compatibleAffineKaehlerPreimages
    (omega : KaehlerDifferential ℂ K)
    (h : ∀ x : LPSOriginalFilledCurve N, 0 ≤ meromorphicOrderValuation
      (lpsOriginalLocalChartCenter N hN x)
      (lpsOriginalNativeCovectorToLocal N hN x
        (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN omega))) :
    ∃! pair : KaehlerDifferential ℂ R × KaehlerDifferential ℂ I,
      KaehlerDifferential.map ℂ ℂ R K pair.1 = omega ∧
      KaehlerDifferential.map ℂ ℂ I K pair.2 = omega ∧
      KaehlerDifferential.map ℂ ℂ R T pair.1 = KaehlerDifferential.map ℂ ℂ I T pair.2 := by
  obtain ⟨tau,eta,ht,he⟩ := lpsOriginalNativeNoPole_exists_twoAffineKaehlerPreimages N hpos hN omega h
  refine ⟨(tau,eta),⟨ht,he,lpsOriginalAffineKaehler_overlap_compatible N hpos hN tau eta (ht.trans he.symm)⟩,?_⟩
  intro pair hp
  apply Prod.ext
  · exact lpsOriginalZeroAffineKaehler_map_injective N hpos hN (hp.1.trans ht.symm)
  · exact lpsOriginalInfinityAffineKaehler_map_injective N hpos hN (hp.2.1.trans he.symm)
end
end QEC.Coding.TannerLiftedProduct
