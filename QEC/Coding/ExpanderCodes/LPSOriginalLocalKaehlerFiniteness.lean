import QEC.Coding.AlgebraicGeometry.Differentials.AffineKaehlerInjective
import QEC.Coding.ExpanderCodes.LPSOriginalZeroAffineDifferentials
import QEC.Coding.ExpanderCodes.LPSOriginalInfinityAffineDifferentials

/-!
# Essential finiteness of original local rings

Prove both actual complex affine normalizations finite type with literal constants and their true polynomial fraction embeddings. Derive essential finite type for each original point valuation ring by genuine height-one localization.

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
local instance LPSOriginalLocalKaehlerFinitenessDictionary001 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => lpsOriginalComplexNormalZeroChart N hpos
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
local instance LPSOriginalLocalKaehlerFinitenessDictionary002 : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance LPSOriginalLocalKaehlerFinitenessDictionary003 : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance LPSOriginalLocalKaehlerFinitenessDictionary004 : IsScalarTower ℂ P K := .of_algebraMap_eq' rfl
local instance LPSOriginalLocalKaehlerFinitenessDictionary005 : Algebra ℂ R := (lpsOriginalComplexZeroConstantRingHom N hpos).toAlgebra
local instance LPSOriginalLocalKaehlerFinitenessDictionary006 : SMul ℂ R := Algebra.toSMul
local instance LPSOriginalLocalKaehlerFinitenessDictionary007 : Module ℂ R := Algebra.toModule
local instance LPSOriginalLocalKaehlerFinitenessDictionary008 : SMulCommClass ℂ R R where
  smul_comm c a b := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalLocalKaehlerFinitenessDictionary009 : SMul R (KaehlerDifferential ℂ R) := instSMulKaehlerDifferentialOfSMulCommClass ℂ R
local instance LPSOriginalLocalKaehlerFinitenessDictionary010 : Module R (KaehlerDifferential ℂ R) := instModuleKaehlerDifferentialOfSMulCommClass ℂ R
local instance LPSOriginalLocalKaehlerFinitenessDictionary011 : IsScalarTower ℂ R K := .of_algebraMap_eq fun c =>
  (lpsOriginalZeroConstant_value N hpos c).symm
local instance LPSOriginalLocalKaehlerFinitenessDictionary012 : SMulCommClass ℂ R K where
  smul_comm c r k := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalLocalKaehlerFinitenessDictionary013 : SMul R (KaehlerDifferential ℂ K) := instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalLocalKaehlerFinitenessDictionary014 : Module R (KaehlerDifferential ℂ K) := instModuleKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalLocalKaehlerFinitenessDictionary015 : IsDedekindDomain R := lpsOriginalZeroChart_isDedekindDomain N hpos
local instance LPSOriginalLocalKaehlerFinitenessDictionary016 : IsFractionRing R K := lpsOriginalZeroChart_isFractionRing N hpos

local instance LPSOriginalLocalKaehlerFinitenessDictionary017 : IsScalarTower P J K := .of_algebraMap_eq' rfl
local instance LPSOriginalLocalKaehlerFinitenessDictionary018 : FiniteDimensional J K := lpsOriginalGeneratedFunctionField_finiteDimensional N hpos

/-- The actual zero normalization is a finite-type complex algebra, using its finite separable function-field extension and literal constants. -/
lemma lpsOriginalZeroChart_finiteType : Algebra.FiniteType ℂ R := by
  let : Module.Finite P R := IsIntegralClosure.finite (A := P) («K» := J) (L := K) R
  let : IsScalarTower ℂ P R := .of_algebraMap_eq fun c => by
    apply IsFractionRing.injective R K
    rw [← IsScalarTower.algebraMap_apply ℂ R K,
      ← IsScalarTower.algebraMap_apply P R K,
      ← IsScalarTower.algebraMap_apply ℂ P K]
  exact Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType ℂ P)
    (inferInstance : Algebra.FiniteType P R)

section localPoint
variable (x : LPSOriginalFilledCurve N)
local notation "V" => Valuation.valuationSubring
  (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x))
local instance LPSOriginalLocalKaehlerFinitenessDictionary019 : Algebra V K := (ValuationSubring.subtype V).toAlgebra
local instance LPSOriginalLocalKaehlerFinitenessDictionary020 : SMul V K := Algebra.toSMul
local instance LPSOriginalLocalKaehlerFinitenessDictionary021 : Module V K := Algebra.toModule
local instance LPSOriginalLocalKaehlerFinitenessDictionary022 : SMulCommClass ℂ V K where
  smul_comm c f g := by
    change algebraMap ℂ K c * (f.val * g) = f.val * (algebraMap ℂ K c * g)
    ring
local instance LPSOriginalLocalKaehlerFinitenessDictionary023 : SMul V (KaehlerDifferential ℂ K) := instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalLocalKaehlerFinitenessDictionary024 : Module V (KaehlerDifferential ℂ K) := instModuleKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalLocalKaehlerFinitenessDictionary025 : Algebra ℂ V :=
  (lpsOriginalComplexConstantsToMeromorphicValuationRing N hpos hN x).toAlgebra
local instance LPSOriginalLocalKaehlerFinitenessDictionary026 : IsScalarTower ℂ V K := .of_algebraMap_eq fun c => by rfl

/-- The actual zero-chart point valuation ring is essentially finite type by genuine height-one localization. -/
lemma lpsOriginalZeroValuation_essFiniteType
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)) :
    Algebra.EssFiniteType ℂ V := by
  let : Algebra.FiniteType ℂ R := lpsOriginalZeroChart_finiteType N hpos
  exact heightOne_valuation_essFiniteType ℂ R K
    (lpsOriginalZeroHeightOneCentre N hpos hN x hj) V
    (lpsOriginalZeroHeightOneCentre_valuationRing N hpos hN x hj) (fun _ => rfl)
end localPoint
end
end QEC.Coding.TannerLiftedProduct


namespace QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance LPSOriginalLocalKaehlerFinitenessDictionary027 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => lpsOriginalComplexNormalInfinityChart N hpos
local notation "S" => lpsOriginalInfinityRegularPoints N hpos hN
local instance LPSOriginalLocalKaehlerFinitenessDictionary028 : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance LPSOriginalLocalKaehlerFinitenessDictionary029 : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance LPSOriginalLocalKaehlerFinitenessDictionary030 : IsScalarTower ℂ P K := .of_algebraMap_eq' rfl
local instance LPSOriginalLocalKaehlerFinitenessDictionary031 : Algebra ℂ R := (lpsOriginalComplexInfinityConstantRingHom N hpos).toAlgebra
local instance LPSOriginalLocalKaehlerFinitenessDictionary032 : SMul ℂ R := Algebra.toSMul
local instance LPSOriginalLocalKaehlerFinitenessDictionary033 : Module ℂ R := Algebra.toModule
local instance LPSOriginalLocalKaehlerFinitenessDictionary034 : SMulCommClass ℂ R R where
  smul_comm c a b := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalLocalKaehlerFinitenessDictionary035 : SMul R (KaehlerDifferential ℂ R) := instSMulKaehlerDifferentialOfSMulCommClass ℂ R
local instance LPSOriginalLocalKaehlerFinitenessDictionary036 : Module R (KaehlerDifferential ℂ R) := instModuleKaehlerDifferentialOfSMulCommClass ℂ R
local instance LPSOriginalLocalKaehlerFinitenessDictionary037 : IsScalarTower ℂ R K := .of_algebraMap_eq fun c =>
  (lpsOriginalInfinityConstant_value N hpos c).symm
local instance LPSOriginalLocalKaehlerFinitenessDictionary038 : SMulCommClass ℂ R K where
  smul_comm c r k := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalLocalKaehlerFinitenessDictionary039 : SMul R (KaehlerDifferential ℂ K) := instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalLocalKaehlerFinitenessDictionary040 : Module R (KaehlerDifferential ℂ K) := instModuleKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalLocalKaehlerFinitenessDictionary041 : IsDedekindDomain R := lpsOriginalInfinityChart_isDedekindDomain N hpos
local instance LPSOriginalLocalKaehlerFinitenessDictionary042 : IsFractionRing R K := lpsOriginalInfinityChart_isFractionRing N hpos

local instance LPSOriginalLocalKaehlerFinitenessDictionary043 : FiniteDimensional J K := lpsOriginalGeneratedFunctionField_finiteDimensional N hpos

/-- The actual reciprocal normalization is finite type over literal complex constants, with the true reciprocal polynomial fraction embedding. -/
lemma lpsOriginalInfinityChart_finiteType : Algebra.FiniteType ℂ R := by
  let : Algebra P J := lpsOriginalReciprocalBaseCAlgebra
  let : SMul P J := Algebra.toSMul
  let : Module P J := Algebra.toModule
  let : IsFractionRing P J := lpsOriginalReciprocalBaseC_isFractionRing
  let : Algebra P K := (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos).toAlgebra
  let : SMul P K := Algebra.toSMul
  let : Module P K := Algebra.toModule
  let : IsScalarTower P J K := .of_algebraMap_eq' rfl
  let : IsScalarTower ℂ P K := .of_algebraMap_eq fun c => by
    change algebraMap J K (algebraMap ℂ J c) =
      algebraMap J K (lpsOriginalComplexJFractionInversion (algebraMap ℂ J c))
    rw [lpsOriginalComplexJFractionInversion_constant]
  let : Module.Finite P R := IsIntegralClosure.finite (A := P) («K» := J) (L := K) R
  let : IsScalarTower ℂ P R := .of_algebraMap_eq fun c => by
    apply IsFractionRing.injective R K
    rw [← IsScalarTower.algebraMap_apply ℂ R K,
      ← IsScalarTower.algebraMap_apply P R K,
      ← IsScalarTower.algebraMap_apply ℂ P K]
  exact Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType ℂ P)
    (inferInstance : Algebra.FiniteType P R)

section localPoint
variable (x : LPSOriginalFilledCurve N)
local notation "V" => Valuation.valuationSubring
  (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x))
local instance LPSOriginalLocalKaehlerFinitenessDictionary044 : Algebra V K := (ValuationSubring.subtype V).toAlgebra
local instance LPSOriginalLocalKaehlerFinitenessDictionary045 : SMul V K := Algebra.toSMul
local instance LPSOriginalLocalKaehlerFinitenessDictionary046 : Module V K := Algebra.toModule
local instance LPSOriginalLocalKaehlerFinitenessDictionary047 : SMulCommClass ℂ V K where
  smul_comm c f g := by
    change algebraMap ℂ K c * (f.val * g) = f.val * (algebraMap ℂ K c * g)
    ring
local instance LPSOriginalLocalKaehlerFinitenessDictionary048 : SMul V (KaehlerDifferential ℂ K) := instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalLocalKaehlerFinitenessDictionary049 : Module V (KaehlerDifferential ℂ K) := instModuleKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalLocalKaehlerFinitenessDictionary050 : Algebra ℂ V :=
  (lpsOriginalComplexConstantsToMeromorphicValuationRing N hpos hN x).toAlgebra
local instance LPSOriginalLocalKaehlerFinitenessDictionary051 : IsScalarTower ℂ V K := .of_algebraMap_eq fun c => by rfl

/-- The actual reciprocal-chart point valuation ring is essentially finite type by genuine height-one localization. -/
lemma lpsOriginalInfinityValuation_essFiniteType
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹) :
    Algebra.EssFiniteType ℂ V := by
  let : Algebra.FiniteType ℂ R := lpsOriginalInfinityChart_finiteType N hpos
  exact heightOne_valuation_essFiniteType ℂ R K
    (lpsOriginalInfinityHeightOneCentre N hpos hN x hj) V
    (lpsOriginalInfinityHeightOneCentre_valuationRing N hpos hN x hj) (fun _ => rfl)
end localPoint
end
end QEC.Coding.TannerLiftedProduct
