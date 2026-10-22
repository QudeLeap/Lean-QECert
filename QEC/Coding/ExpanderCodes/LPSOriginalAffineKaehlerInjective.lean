import QEC.Coding.ExpanderCodes.LPSOriginalLocalKaehlerInjective
import QEC.Coding.AlgebraicGeometry.Differentials.AffineKaehlerInjective
import QEC.Coding.ExpanderCodes.LPSOriginalZeroAffineDifferentials
import QEC.Coding.ExpanderCodes.LPSOriginalInfinityAffineDifferentials

/-!
# Injective original affine differentials

Use actual arbitrary-maximal-point coverage and the proved point-local injection to clear kernel elements outside every maximal ideal. The real clearing ideal proves both affine differential maps injective.

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
local instance LPSOriginalAffineKaehlerInjectiveDictionary001 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => lpsOriginalComplexNormalZeroChart N hpos
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
local instance LPSOriginalAffineKaehlerInjectiveDictionary002 : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance LPSOriginalAffineKaehlerInjectiveDictionary003 : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance LPSOriginalAffineKaehlerInjectiveDictionary004 : IsScalarTower ℂ P K := .of_algebraMap_eq' rfl
local instance LPSOriginalAffineKaehlerInjectiveDictionary005 : Algebra ℂ R := (lpsOriginalComplexZeroConstantRingHom N hpos).toAlgebra
local instance LPSOriginalAffineKaehlerInjectiveDictionary006 : SMul ℂ R := Algebra.toSMul
local instance LPSOriginalAffineKaehlerInjectiveDictionary007 : Module ℂ R := Algebra.toModule
local instance LPSOriginalAffineKaehlerInjectiveDictionary008 : SMulCommClass ℂ R R where
  smul_comm c a b := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalAffineKaehlerInjectiveDictionary009 : SMul R (KaehlerDifferential ℂ R) := instSMulKaehlerDifferentialOfSMulCommClass ℂ R
local instance LPSOriginalAffineKaehlerInjectiveDictionary010 : Module R (KaehlerDifferential ℂ R) := instModuleKaehlerDifferentialOfSMulCommClass ℂ R
local instance LPSOriginalAffineKaehlerInjectiveDictionary011 : IsScalarTower ℂ R K := .of_algebraMap_eq fun c =>
  (lpsOriginalZeroConstant_value N hpos c).symm
local instance LPSOriginalAffineKaehlerInjectiveDictionary012 : SMulCommClass ℂ R K where
  smul_comm c r k := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalAffineKaehlerInjectiveDictionary013 : SMul R (KaehlerDifferential ℂ K) := instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalAffineKaehlerInjectiveDictionary014 : Module R (KaehlerDifferential ℂ K) := instModuleKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalAffineKaehlerInjectiveDictionary015 : IsDedekindDomain R := lpsOriginalZeroChart_isDedekindDomain N hpos
local instance LPSOriginalAffineKaehlerInjectiveDictionary016 : IsFractionRing R K := lpsOriginalZeroChart_isFractionRing N hpos

section localPoint
variable (x : LPSOriginalFilledCurve N)
local notation "V" => Valuation.valuationSubring
  (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x))
local instance LPSOriginalAffineKaehlerInjectiveDictionary017 : Algebra V K := (ValuationSubring.subtype V).toAlgebra
local instance LPSOriginalAffineKaehlerInjectiveDictionary018 : SMul V K := Algebra.toSMul
local instance LPSOriginalAffineKaehlerInjectiveDictionary019 : Module V K := Algebra.toModule
local instance LPSOriginalAffineKaehlerInjectiveDictionary020 : SMulCommClass ℂ V K where
  smul_comm c f g := by
    change algebraMap ℂ K c * (f.val * g) = f.val * (algebraMap ℂ K c * g)
    ring
local instance LPSOriginalAffineKaehlerInjectiveDictionary021 : SMul V (KaehlerDifferential ℂ K) := instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalAffineKaehlerInjectiveDictionary022 : Module V (KaehlerDifferential ℂ K) := instModuleKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalAffineKaehlerInjectiveDictionary023 : Algebra ℂ V :=
  (lpsOriginalComplexConstantsToMeromorphicValuationRing N hpos hN x).toAlgebra
local instance LPSOriginalAffineKaehlerInjectiveDictionary024 : IsScalarTower ℂ V K := .of_algebraMap_eq fun c => by rfl

/-- An actual zero-affine kernel element has a zero-clearing scalar outside the real point evaluation kernel. -/
lemma lpsOriginalZeroAffineKaehler_kernel_clear
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X))
    (tau : KaehlerDifferential ℂ R) (hzero : KaehlerDifferential.map ℂ ℂ R K tau = 0) :
    ∃ s : R, s ∉ RingHom.ker (lpsOriginalZeroNormalChartEvaluation N hpos hN x hj) ∧
      s • tau = 0 := by
  exact kaehler_field_map_zero_heightOne_clear ℂ R K
    (lpsOriginalZeroHeightOneCentre N hpos hN x hj) V
    (lpsOriginalZeroHeightOneCentre_valuationRing N hpos hN x hj) (fun _ => rfl)
    (lpsOriginalLocalKaehler_map_injective N hpos hN x) tau hzero
end localPoint

include hN in
/-- Actual maximal-point coverage and local kernel clearing prove the zero-affine differential map injective. -/
lemma lpsOriginalZeroAffineKaehler_map_injective :
    Function.Injective (KaehlerDifferential.map ℂ ℂ R K) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro tau htau
  apply submodule_mem_of_forall_maximal_clear R (KaehlerDifferential ℂ R) ⊥ tau
  intro M hM
  obtain ⟨x,hx⟩ := lpsOriginalZeroNormalChart_allMaximalPoints N hpos hN M
  obtain ⟨s,hs,hs0⟩ := lpsOriginalZeroAffineKaehler_kernel_clear N hpos hN (Sum.inl x)
    (lpsOriginalFieldJ_interior_order_nonnegative N hpos hN x) tau htau
  exact ⟨s,by rwa [hx],hs0⟩
end
end QEC.Coding.TannerLiftedProduct


namespace QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance LPSOriginalAffineKaehlerInjectiveDictionary025 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => lpsOriginalComplexNormalInfinityChart N hpos
local notation "S" => lpsOriginalInfinityRegularPoints N hpos hN
local instance LPSOriginalAffineKaehlerInjectiveDictionary026 : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance LPSOriginalAffineKaehlerInjectiveDictionary027 : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance LPSOriginalAffineKaehlerInjectiveDictionary028 : IsScalarTower ℂ P K := .of_algebraMap_eq' rfl
local instance LPSOriginalAffineKaehlerInjectiveDictionary029 : Algebra ℂ R := (lpsOriginalComplexInfinityConstantRingHom N hpos).toAlgebra
local instance LPSOriginalAffineKaehlerInjectiveDictionary030 : SMul ℂ R := Algebra.toSMul
local instance LPSOriginalAffineKaehlerInjectiveDictionary031 : Module ℂ R := Algebra.toModule
local instance LPSOriginalAffineKaehlerInjectiveDictionary032 : SMulCommClass ℂ R R where
  smul_comm c a b := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalAffineKaehlerInjectiveDictionary033 : SMul R (KaehlerDifferential ℂ R) := instSMulKaehlerDifferentialOfSMulCommClass ℂ R
local instance LPSOriginalAffineKaehlerInjectiveDictionary034 : Module R (KaehlerDifferential ℂ R) := instModuleKaehlerDifferentialOfSMulCommClass ℂ R
local instance LPSOriginalAffineKaehlerInjectiveDictionary035 : IsScalarTower ℂ R K := .of_algebraMap_eq fun c =>
  (lpsOriginalInfinityConstant_value N hpos c).symm
local instance LPSOriginalAffineKaehlerInjectiveDictionary036 : SMulCommClass ℂ R K where
  smul_comm c r k := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalAffineKaehlerInjectiveDictionary037 : SMul R (KaehlerDifferential ℂ K) := instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalAffineKaehlerInjectiveDictionary038 : Module R (KaehlerDifferential ℂ K) := instModuleKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalAffineKaehlerInjectiveDictionary039 : IsDedekindDomain R := lpsOriginalInfinityChart_isDedekindDomain N hpos
local instance LPSOriginalAffineKaehlerInjectiveDictionary040 : IsFractionRing R K := lpsOriginalInfinityChart_isFractionRing N hpos

section localPoint
variable (x : LPSOriginalFilledCurve N)
local notation "V" => Valuation.valuationSubring
  (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x))
local instance LPSOriginalAffineKaehlerInjectiveDictionary041 : Algebra V K := (ValuationSubring.subtype V).toAlgebra
local instance LPSOriginalAffineKaehlerInjectiveDictionary042 : SMul V K := Algebra.toSMul
local instance LPSOriginalAffineKaehlerInjectiveDictionary043 : Module V K := Algebra.toModule
local instance LPSOriginalAffineKaehlerInjectiveDictionary044 : SMulCommClass ℂ V K where
  smul_comm c f g := by
    change algebraMap ℂ K c * (f.val * g) = f.val * (algebraMap ℂ K c * g)
    ring
local instance LPSOriginalAffineKaehlerInjectiveDictionary045 : SMul V (KaehlerDifferential ℂ K) := instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalAffineKaehlerInjectiveDictionary046 : Module V (KaehlerDifferential ℂ K) := instModuleKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalAffineKaehlerInjectiveDictionary047 : Algebra ℂ V :=
  (lpsOriginalComplexConstantsToMeromorphicValuationRing N hpos hN x).toAlgebra
local instance LPSOriginalAffineKaehlerInjectiveDictionary048 : IsScalarTower ℂ V K := .of_algebraMap_eq fun c => by rfl

/-- An actual reciprocal-affine kernel element has a zero-clearing scalar outside the real point evaluation kernel. -/
lemma lpsOriginalInfinityAffineKaehler_kernel_clear
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹)
    (tau : KaehlerDifferential ℂ R) (hzero : KaehlerDifferential.map ℂ ℂ R K tau = 0) :
    ∃ s : R, s ∉ RingHom.ker (lpsOriginalInfinityNormalChartEvaluation N hpos hN x hj) ∧
      s • tau = 0 := by
  exact kaehler_field_map_zero_heightOne_clear ℂ R K
    (lpsOriginalInfinityHeightOneCentre N hpos hN x hj) V
    (lpsOriginalInfinityHeightOneCentre_valuationRing N hpos hN x hj) (fun _ => rfl)
    (lpsOriginalLocalKaehler_map_injective N hpos hN x) tau hzero
end localPoint

include hN in
/-- Actual reciprocal maximal-point coverage and local kernel clearing prove the reciprocal-affine differential map injective. -/
lemma lpsOriginalInfinityAffineKaehler_map_injective :
    Function.Injective (KaehlerDifferential.map ℂ ℂ R K) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro tau htau
  apply submodule_mem_of_forall_maximal_clear R (KaehlerDifferential ℂ R) ⊥ tau
  intro M hM
  obtain ⟨x,hx⟩ := lpsOriginalInfinityNormalChart_allMaximalPoints N hpos hN M
  obtain ⟨s,hs,hs0⟩ := lpsOriginalInfinityAffineKaehler_kernel_clear N hpos hN
    x.val x.property tau htau
  exact ⟨s,by rwa [hx],hs0⟩
end
end QEC.Coding.TannerLiftedProduct
