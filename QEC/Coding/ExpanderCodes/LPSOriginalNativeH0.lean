import QEC.Coding.ExpanderCodes.LPSOriginalNativeGlobalRegularity

/-!
# Complex-linear native H0 comparison on the original curve

The actual restriction maps preserve complex constants. Their generic field
map is injective and its image is precisely the intersection of both affine
Kähler images, equivalently native no poles at every filled point. This yields
a constructed complex-linear equivalence of genuine global differential
sections with that regular submodule. Properness/GAGA, reduction and arithmetic
spectral estimates require further mathematical results.
-/
namespace QEC.Coding.TannerLiftedProduct
open CategoryTheory _root_.AlgebraicGeometry Opposite QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped _root_.AlgebraicGeometry MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local notation "R" => lpsOriginalComplexNormalZeroChart N hpos
local notation "I" => lpsOriginalComplexNormalInfinityChart N hpos
local notation "T" => lpsOriginalComplexNormalLaurentChart N hpos
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "X" => lpsOriginalComplexNormalGluedScheme N hpos
local notation "c" => lpsOriginalComplexNormalGlobalConstantMap N hpos
local notation "Omega" => lpsOriginalComplexNormalDifferentialSheaf N hpos
local notation "f0" => lpsOriginalComplexNormalGluedChartMap N hpos false
attribute [local instance] lpsOriginalZeroChartDifferentialAlgebra
  lpsOriginalInfinityChartDifferentialAlgebra lpsOriginalZeroChartDifferentialSMul
  lpsOriginalZeroChartDifferentialModule lpsOriginalZeroChartDifferentialSMulComm
  lpsOriginalZeroChartOmegaSMul lpsOriginalZeroChartOmegaModule
  lpsOriginalInfinityChartDifferentialSMul lpsOriginalInfinityChartDifferentialModule
  lpsOriginalInfinityChartDifferentialSMulComm lpsOriginalInfinityChartOmegaSMul
  lpsOriginalInfinityChartOmegaModule
  LPSOriginalAffineKaehlerCompatibilityDictionary028
  LPSOriginalAffineKaehlerCompatibilityDictionary029
  LPSOriginalAffineKaehlerCompatibilityDictionary030
  LPSOriginalAffineKaehlerCompatibilityDictionary031
  LPSOriginalAffineKaehlerCompatibilityDictionary032
  LPSOriginalAffineKaehlerCompatibilityDictionary033
  LPSOriginalAffineKaehlerCompatibilityDictionary038
  LPSOriginalAffineKaehlerCompatibilityDictionary039
  LPSOriginalAffineKaehlerCompatibilityDictionary040
  LPSOriginalAffineKaehlerCompatibilityDictionary042
  LPSOriginalAffineKaehlerCompatibilityDictionary043
  LPSOriginalAffineKaehlerCompatibilityDictionary044
  LPSOriginalAffineKaehlerCompatibilityDictionary045
  LPSOriginalAffineKaehlerCompatibilityDictionary047
  LPSOriginalAffineKaehlerCompatibilityDictionary048
  LPSOriginalAffineKaehlerCompatibilityDictionary049
  LPSOriginalAffineKaehlerCompatibilityDictionary051
  LPSOriginalAffineKaehlerCompatibilityDictionary052
  LPSOriginalAffineKaehlerCompatibilityDictionary053
  LPSOriginalAffineKaehlerCompatibilityDictionary054

attribute [local instance] originalNativeGlobalZeroOpen originalNativeGlobalInfinityOpen
attribute [local instance]
  LPSOriginalAffineKaehlerCompatibilityDictionary001
  LPSOriginalAffineKaehlerCompatibilityDictionary002
  LPSOriginalAffineKaehlerCompatibilityDictionary003
  LPSOriginalAffineKaehlerCompatibilityDictionary004
  LPSOriginalAffineKaehlerCompatibilityDictionary011
  LPSOriginalAffineKaehlerCompatibilityDictionary012
  LPSOriginalAffineKaehlerCompatibilityDictionary013
  LPSOriginalAffineKaehlerCompatibilityDictionary014
  LPSOriginalAffineKaehlerCompatibilityDictionary023
  LPSOriginalAffineKaehlerCompatibilityDictionary024
  LPSOriginalAffineKaehlerCompatibilityDictionary025
  LPSOriginalAffineKaehlerCompatibilityDictionary026

attribute [local instance] LPSOriginalAffineKaehlerCompatibilityDictionary027
  LPSOriginalAffineKaehlerCompatibilityDictionary034
  LPSOriginalAffineKaehlerCompatibilityDictionary035
  LPSOriginalAffineKaehlerCompatibilityDictionary036
  LPSOriginalAffineKaehlerCompatibilityDictionary037
  LPSOriginalAffineKaehlerCompatibilityDictionary041
  LPSOriginalAffineKaehlerCompatibilityDictionary050

local instance originalNativeGlobalComplexModule : Module ℂ Γ(Omega, ⊤) :=
  schemeDifferentialGlobalConstantModule ℂ X c

local notation "U" => Functor.obj (Scheme.Hom.opensFunctor (f0)) ⊤

def lpsOriginalNativeGlobalGenericDifferentialAddHom : Γ(Omega, ⊤) →+ KaehlerDifferential ℂ K :=
  (KaehlerDifferential.map ℂ ℂ R K).toAddMonoidHom.comp
    ((lpsOriginalZeroImageFromKaehler N hpos).inv.hom.comp
      ((Omega).presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom)

lemma lpsOriginalNativeGlobalZeroProjection_eq_restriction (z : Γ(Omega, ⊤)) :
    (lpsOriginalNativeGlobalAffinePair N hpos z).1 =
      @affineDifferentialGlobalRestrictionToKaehler ℂ inferInstance X c
        (CommRingCat.of R) inferInstance (f0) (originalNativeGlobalZeroOpen N hpos)
        (lpsOriginalComplexNormalGlobalConstantMap_zero_affine N hpos) z :=
  @affineDifferentialChartImageKaehlerIso_inv_global ℂ inferInstance X c
    (CommRingCat.of R) inferInstance (f0) (originalNativeGlobalZeroOpen N hpos)
    (lpsOriginalComplexNormalGlobalConstantMap_zero_affine N hpos) z

lemma lpsOriginalNativeGlobalZeroProjection_smul (r : ℂ) (z : Γ(Omega, ⊤)) :
    (lpsOriginalNativeGlobalAffinePair N hpos (r • z)).1 =
      r • (lpsOriginalNativeGlobalAffinePair N hpos z).1 := by
  have h0 := lpsOriginalNativeGlobalZeroProjection_eq_restriction N hpos (r • z)
  have h1 := @affineDifferentialGlobalRestrictionToKaehler_smul ℂ inferInstance X c
    (CommRingCat.of R) inferInstance (f0) (originalNativeGlobalZeroOpen N hpos)
    (lpsOriginalComplexNormalGlobalConstantMap_zero_affine N hpos) r z
  have h2 := congrArg (fun t : KaehlerDifferential ℂ R => r • t)
    (lpsOriginalNativeGlobalZeroProjection_eq_restriction N hpos z).symm
  exact h0.trans (h1.trans h2)

lemma lpsOriginalNativeGlobalGenericDifferential_smul (r : ℂ) (z : Γ(Omega, ⊤)) :
    lpsOriginalNativeGlobalGenericDifferential N hpos (r • z) =
      r • lpsOriginalNativeGlobalGenericDifferential N hpos z :=
  (congrArg (KaehlerDifferential.map ℂ ℂ R K)
    (lpsOriginalNativeGlobalZeroProjection_smul N hpos r z)).trans
      ((KaehlerDifferential.map ℂ ℂ R K).map_smul_of_tower r
        (lpsOriginalNativeGlobalAffinePair N hpos z).1)

def lpsOriginalNativeGlobalGenericDifferentialLinearMap :
    Γ(Omega, ⊤) →ₗ[ℂ] KaehlerDifferential ℂ K where
  __ := lpsOriginalNativeGlobalGenericDifferentialAddHom N hpos
  map_smul' r z := lpsOriginalNativeGlobalGenericDifferential_smul N hpos r z

def lpsOriginalNativeRegularKaehlerSubmodule : Submodule ℂ (KaehlerDifferential ℂ K) :=
  (KaehlerDifferential.map ℂ ℂ R K).range.restrictScalars ℂ ⊓
    (KaehlerDifferential.map ℂ ℂ I K).range.restrictScalars ℂ

lemma lpsOriginalNativeRegularKaehlerSubmodule_mem_iff (omega : KaehlerDifferential ℂ K) :
    omega ∈ lpsOriginalNativeRegularKaehlerSubmodule N hpos ↔
    ∀ x : LPSOriginalFilledCurve N, 0 ≤ meromorphicOrderValuation
      (lpsOriginalLocalChartCenter N hN x)
      (lpsOriginalNativeCovectorToLocal N hN x
        (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN omega)) :=
  lpsOriginalTwoAffineKaehlerRanges_iff_allNativeNoPole N hpos hN omega

include hN in
lemma lpsOriginalNativeGlobalGenericDifferentialLinearMap_mem
    (z : Γ(Omega, ⊤)) :
    lpsOriginalNativeGlobalGenericDifferentialLinearMap N hpos z ∈
      lpsOriginalNativeRegularKaehlerSubmodule N hpos := by
  apply (lpsOriginalNativeRegularKaehlerSubmodule_mem_iff N hpos hN _).mpr
  exact lpsOriginalNativeGlobalGenericDifferential_noPole N hpos hN z

def lpsOriginalNativeH0ToRegularCovectorLinearMap :
    Γ(Omega, ⊤) →ₗ[ℂ] lpsOriginalNativeRegularKaehlerSubmodule N hpos :=
  (lpsOriginalNativeGlobalGenericDifferentialLinearMap N hpos).codRestrict
    (lpsOriginalNativeRegularKaehlerSubmodule N hpos)
    (lpsOriginalNativeGlobalGenericDifferentialLinearMap_mem N hpos hN)

include hN in
lemma lpsOriginalNativeH0ToRegularCovectorLinearMap_bijective :
    Function.Bijective (lpsOriginalNativeH0ToRegularCovectorLinearMap N hpos hN) := by
  constructor
  · intro z z' h
    exact lpsOriginalNativeGlobalGenericDifferential_injective N hpos hN
      (congrArg Subtype.val h)
  · intro omega
    have h := (lpsOriginalNativeRegularKaehlerSubmodule_mem_iff N hpos hN omega.val).mp omega.property
    obtain ⟨z, hz, _⟩ := lpsOriginalNativeNoPole_existsUnique_globalDifferentialSection
      N hpos hN omega.val h
    exact ⟨z, Subtype.ext hz.1⟩

def lpsOriginalNativeH0RegularCovectorLinearEquiv :
    Γ(Omega, ⊤) ≃ₗ[ℂ] lpsOriginalNativeRegularKaehlerSubmodule N hpos :=
  LinearEquiv.ofBijective (lpsOriginalNativeH0ToRegularCovectorLinearMap N hpos hN)
    (lpsOriginalNativeH0ToRegularCovectorLinearMap_bijective N hpos hN)
end
end QEC.Coding.TannerLiftedProduct
