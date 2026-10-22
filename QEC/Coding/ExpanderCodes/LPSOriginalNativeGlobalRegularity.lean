import QEC.Coding.ExpanderCodes.LPSOriginalNativeGlobalDifferentials

/-!
# Native regularity of original global differentials

Global sections have equal Laurent and original field images. Their generic
covectors have no poles at every original filled point. Conversely, native
all-point regularity gives a unique genuine global section, using the proved
affine preimages and actual original sheaf gluing.
-/
namespace QEC.Coding.TannerLiftedProduct
open CategoryTheory _root_.AlgebraicGeometry Opposite QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped _root_.AlgebraicGeometry MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local notation "R" => lpsOriginalComplexNormalZeroChart N hpos
local notation "I" => lpsOriginalComplexNormalInfinityChart N hpos
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "Omega" => lpsOriginalComplexNormalDifferentialSheaf N hpos
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

lemma lpsOriginalNativeNoPole_existsUnique_globalDifferentialSection
    (omega : KaehlerDifferential ℂ K)
    (h : ∀ x : LPSOriginalFilledCurve N, 0 ≤ meromorphicOrderValuation
      (lpsOriginalLocalChartCenter N hN x)
      (lpsOriginalNativeCovectorToLocal N hN x
        (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN omega))) :
    ∃! z : Γ(Omega, ⊤),
      KaehlerDifferential.map ℂ ℂ R K (lpsOriginalNativeGlobalAffinePair N hpos z).1 = omega ∧
      KaehlerDifferential.map ℂ ℂ I K (lpsOriginalNativeGlobalAffinePair N hpos z).2 = omega := by
  obtain ⟨p, hp, _⟩ := lpsOriginalNativeNoPole_existsUnique_compatibleAffineKaehlerPreimages
    N hpos hN omega h
  obtain ⟨z, hz, _⟩ := lpsOriginalCompatibleAffine_existsUnique_globalPair N hpos p.1 p.2 hp.2.2
  have h0 := (congrArg (fun t : KaehlerDifferential ℂ R × KaehlerDifferential ℂ I =>
    KaehlerDifferential.map ℂ ℂ R K t.1) hz).trans hp.1
  have h1 := (congrArg (fun t : KaehlerDifferential ℂ R × KaehlerDifferential ℂ I =>
    KaehlerDifferential.map ℂ ℂ I K t.2) hz).trans hp.2.1
  refine ⟨z, ⟨h0, h1⟩, ?_⟩
  intro z' hz'
  apply lpsOriginalNativeGlobalAffinePair_injective N hpos
  apply Prod.ext
  · exact lpsOriginalZeroAffineKaehler_map_injective N hpos hN (hz'.1.trans h0.symm)
  · exact lpsOriginalInfinityAffineKaehler_map_injective N hpos hN (hz'.2.trans h1.symm)
end
end QEC.Coding.TannerLiftedProduct

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
local notation "Omega" => lpsOriginalComplexNormalDifferentialSheaf N hpos
local notation "X" => lpsOriginalComplexNormalGluedScheme N hpos
local notation "c" => lpsOriginalComplexNormalGlobalConstantMap N hpos
local notation "f0" => lpsOriginalComplexNormalGluedChartMap N hpos false
local notation "f1" => lpsOriginalComplexNormalGluedChartMap N hpos true
local notation "q0" => CommRingCat.ofHom (lpsOriginalComplexNormalZeroToLaurent N hpos)
local notation "q1" => CommRingCat.ofHom (lpsOriginalComplexNormalInfinityToLaurent N hpos)
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

lemma lpsOriginalNativeGlobalAffinePair_LaurentCompatible (z : Γ(Omega, ⊤)) :
    KaehlerDifferential.map ℂ ℂ R T (lpsOriginalNativeGlobalAffinePair N hpos z).1 =
      KaehlerDifferential.map ℂ ℂ I T (lpsOriginalNativeGlobalAffinePair N hpos z).2 := by
  have hp := (lpsOriginalNativeGlobalAffinePair_eq_iff N hpos z
    (lpsOriginalNativeGlobalAffinePair N hpos z).1
    (lpsOriginalNativeGlobalAffinePair N hpos z).2).mp rfl
  exact @affineDifferentialChartPair_globalCompatibility ℂ
    (CommRingCat.of R) (CommRingCat.of I) (CommRingCat.of T)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance (q0) (q1) (fun _ => rfl) (fun _ => rfl)
    (lpsOriginalZeroLaurentAffineCoefficientSquare N hpos)
    (lpsOriginalInfinityLaurentAffineCoefficientSquare N hpos)
    X (f0) (f1) (originalZeroLaurentRestrictionOpen N hpos)
    (originalInfinityLaurentRestrictionOpen N hpos)
    (originalNativeGlobalZeroOpen N hpos) (originalNativeGlobalInfinityOpen N hpos) c
    (lpsOriginalComplexNormalGlobalConstantMap_zero_affine N hpos)
    (lpsOriginalComplexNormalGlobalConstantMap_infinity_affine N hpos)
    (lpsOriginalComplexNormalGluedOverlap_agreement N hpos) z
    (lpsOriginalNativeGlobalAffinePair N hpos z).1
    (lpsOriginalNativeGlobalAffinePair N hpos z).2 hp.1 hp.2

lemma lpsOriginalNativeGlobalAffinePair_fieldCompatible (z : Γ(Omega, ⊤)) :
    KaehlerDifferential.map ℂ ℂ R K (lpsOriginalNativeGlobalAffinePair N hpos z).1 =
      KaehlerDifferential.map ℂ ℂ I K (lpsOriginalNativeGlobalAffinePair N hpos z).2 := by
  have h := congrArg (KaehlerDifferential.map ℂ ℂ T K)
    (lpsOriginalNativeGlobalAffinePair_LaurentCompatible N hpos z)
  rw [← kaehler_field_map_comp ℂ R T K, ← kaehler_field_map_comp ℂ I T K] at h
  exact h

def lpsOriginalNativeGlobalGenericDifferential (z : Γ(Omega, ⊤)) : KaehlerDifferential ℂ K :=
  KaehlerDifferential.map ℂ ℂ R K (lpsOriginalNativeGlobalAffinePair N hpos z).1

lemma lpsOriginalNativeGlobalGenericDifferential_noPole (z : Γ(Omega, ⊤)) :
    ∀ x : LPSOriginalFilledCurve N, 0 ≤ meromorphicOrderValuation
      (lpsOriginalLocalChartCenter N hN x)
      (lpsOriginalNativeCovectorToLocal N hN x
        (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN
          (lpsOriginalNativeGlobalGenericDifferential N hpos z))) := by
  apply (lpsOriginalTwoAffineKaehlerRanges_iff_allNativeNoPole N hpos hN _).mp
  exact ⟨⟨(lpsOriginalNativeGlobalAffinePair N hpos z).1, rfl⟩,
    ⟨(lpsOriginalNativeGlobalAffinePair N hpos z).2,
      (lpsOriginalNativeGlobalAffinePair_fieldCompatible N hpos z).symm⟩⟩
end
end QEC.Coding.TannerLiftedProduct

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
local notation "Omega" => lpsOriginalComplexNormalDifferentialSheaf N hpos
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

include hN in
lemma lpsOriginalNativeGlobalGenericDifferential_injective :
    Function.Injective (lpsOriginalNativeGlobalGenericDifferential N hpos) := by
  intro z z' h
  apply lpsOriginalNativeGlobalAffinePair_injective N hpos
  apply Prod.ext
  · exact lpsOriginalZeroAffineKaehler_map_injective N hpos hN h
  · exact lpsOriginalInfinityAffineKaehler_map_injective N hpos hN
      ((lpsOriginalNativeGlobalAffinePair_fieldCompatible N hpos z).symm.trans
        (h.trans (lpsOriginalNativeGlobalAffinePair_fieldCompatible N hpos z')))

end
end QEC.Coding.TannerLiftedProduct
