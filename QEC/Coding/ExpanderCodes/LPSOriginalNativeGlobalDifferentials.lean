import QEC.Coding.AlgebraicGeometry.Differentials.AffineChartDescent
import QEC.Coding.ExpanderCodes.LPSOriginalDifferentialImages
import QEC.Coding.ExpanderCodes.LPSOriginalDifferentialSheaf
import QEC.Coding.ExpanderCodes.LPSOriginalAffineKaehlerCompatibility

/-!
# Actual original global differential descent

The literal zero and infinity chart images cover the original normalization,
and their intersection is the actual Laurent image. Canonical differential
restrictions and genuine sheaf gluing construct a unique global differential
section from each compatible pair of affine Kähler covectors.
-/
namespace QEC.Coding.TannerLiftedProduct
open CategoryTheory _root_.AlgebraicGeometry Opposite QEC.Coding.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N)
local notation "R" => lpsOriginalComplexNormalZeroChart N hpos
local notation "I" => lpsOriginalComplexNormalInfinityChart N hpos
local notation "T" => lpsOriginalComplexNormalLaurentChart N hpos
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

local instance originalZeroLaurentRestrictionOpen :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (lpsOriginalComplexNormalZeroToLaurent N hpos))) :=
  lpsOriginalComplexNormalZeroToLaurent_openImmersion N hpos
local instance originalInfinityLaurentRestrictionOpen :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (lpsOriginalComplexNormalInfinityToLaurent N hpos))) :=
  lpsOriginalComplexNormalInfinityToLaurent_openImmersion N hpos

lemma lpsOriginalZeroLaurentAffineCoefficientSquare :
    (CommRingCat.ofHom (algebraMap ℂ R) : CommRingCat.of ℂ ⟶ CommRingCat.of R) ≫
      CommRingCat.ofHom (lpsOriginalComplexNormalZeroToLaurent N hpos) =
        CommRingCat.ofHom (algebraMap ℂ T) := by
  apply CommRingCat.hom_ext
  exact lpsOriginalComplexZeroConstantOverlapRingHomDiagram N hpos

lemma lpsOriginalInfinityLaurentAffineCoefficientSquare :
    (CommRingCat.ofHom (algebraMap ℂ I) : CommRingCat.of ℂ ⟶ CommRingCat.of I) ≫
      CommRingCat.ofHom (lpsOriginalComplexNormalInfinityToLaurent N hpos) =
        CommRingCat.ofHom (algebraMap ℂ T) := by
  apply CommRingCat.hom_ext
  exact lpsOriginalComplexInfinityConstantOverlapRingHomDiagram N hpos

end
end QEC.Coding.TannerLiftedProduct

namespace QEC.Coding.TannerLiftedProduct
open CategoryTheory _root_.AlgebraicGeometry Opposite QEC.Coding.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N)
local notation "R" => lpsOriginalComplexNormalZeroChart N hpos
local notation "I" => lpsOriginalComplexNormalInfinityChart N hpos
local notation "T" => lpsOriginalComplexNormalLaurentChart N hpos
local notation "X" => lpsOriginalComplexNormalGluedScheme N hpos
local notation "c" => lpsOriginalComplexNormalGlobalConstantMap N hpos
local notation "Omega" => lpsOriginalComplexNormalDifferentialSheaf N hpos
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

attribute [local instance] originalZeroLaurentRestrictionOpen originalInfinityLaurentRestrictionOpen
omit [NeZero N] in
local instance originalNativeGlobalZeroOpen :
    IsOpenImmersion (f0 : Spec (CommRingCat.of R) ⟶ X) :=
  lpsOriginalComplexNormalGluedChartMap_openImmersion N hpos false
omit [NeZero N] in
local instance originalNativeGlobalInfinityOpen :
    IsOpenImmersion (f1 : Spec (CommRingCat.of I) ⟶ X) :=
  lpsOriginalComplexNormalGluedChartMap_openImmersion N hpos true

omit [NeZero N] in
local instance originalNativeGlobalLaurentCompositeOpen :
    IsOpenImmersion (Spec.map (q0) ≫ (f0) : Spec (CommRingCat.of T) ⟶ X) :=
  @IsOpenImmersion.comp _ _ _ (Spec.map (q0)) (f0)
    (lpsOriginalComplexNormalZeroToLaurent_openImmersion N hpos)
    (originalNativeGlobalZeroOpen N hpos)

local notation "U" => Functor.obj (Scheme.Hom.opensFunctor (f0)) ⊤
local notation "V" => Functor.obj (Scheme.Hom.opensFunctor (f1)) ⊤
local notation "W" => Functor.obj (Scheme.Hom.opensFunctor (Spec.map (q0) ≫ (f0))) ⊤

def lpsOriginalZeroImageFromKaehler :
    AddCommGrpCat.of (KaehlerDifferential ℂ R) ≅ Γ(Omega, U) :=
  @affineDifferentialChartImageKaehlerIso ℂ (CommRingCat.of R) inferInstance inferInstance X
    (f0) (originalNativeGlobalZeroOpen N hpos) c
    (lpsOriginalComplexNormalGlobalConstantMap_zero_affine N hpos)

def lpsOriginalInfinityImageFromKaehler :
    AddCommGrpCat.of (KaehlerDifferential ℂ I) ≅ Γ(Omega, V) :=
  @affineDifferentialChartImageKaehlerIso ℂ (CommRingCat.of I) inferInstance inferInstance X
    (f1) (originalNativeGlobalInfinityOpen N hpos) c
    (lpsOriginalComplexNormalGlobalConstantMap_infinity_affine N hpos)

omit [NeZero N] in
lemma lpsOriginalNativeGlobalChartImage_cover : U ⊔ V = ⊤ := by
  simpa only [Scheme.Hom.image_top_eq_opensRange, lpsOriginalComplexNormalChartImage] using
    lpsOriginalComplexNormalChartImage_cover N hpos

omit [NeZero N] in
lemma lpsOriginalNativeGlobalLaurentImage_intersection : W = U ⊓ V := by
  have h := lpsOriginalComplexNormalLaurentImage_intersection N hpos
  change (Spec.map (q0) ≫ (f0)).opensRange = (f0).opensRange ⊓ (f1).opensRange at h
  simpa only [Scheme.Hom.image_top_eq_opensRange] using h

lemma lpsOriginalCompatibleAffine_existsUnique_globalSection
    (a : KaehlerDifferential ℂ R) (b : KaehlerDifferential ℂ I)
    (hcompat : KaehlerDifferential.map ℂ ℂ R T a = KaehlerDifferential.map ℂ ℂ I T b) :
    ∃! z : Γ(Omega, ⊤),
      (Omega).presheaf.map (homOfLE le_top : U ⟶ ⊤).op z =
        (lpsOriginalZeroImageFromKaehler N hpos).hom a ∧
      (Omega).presheaf.map (homOfLE le_top : V ⟶ ⊤).op z =
        (lpsOriginalInfinityImageFromKaehler N hpos).hom b :=
  @affineDifferentialChartPair_existsUnique_global ℂ
    (CommRingCat.of R) (CommRingCat.of I) (CommRingCat.of T)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance (q0) (q1)
    (fun _ => rfl) (fun _ => rfl)
    (lpsOriginalZeroLaurentAffineCoefficientSquare N hpos)
    (lpsOriginalInfinityLaurentAffineCoefficientSquare N hpos)
    X (f0) (f1) (originalZeroLaurentRestrictionOpen N hpos)
    (originalInfinityLaurentRestrictionOpen N hpos)
    (originalNativeGlobalZeroOpen N hpos) (originalNativeGlobalInfinityOpen N hpos) c
    (lpsOriginalComplexNormalGlobalConstantMap_zero_affine N hpos)
    (lpsOriginalComplexNormalGlobalConstantMap_infinity_affine N hpos)
    (lpsOriginalComplexNormalGluedOverlap_agreement N hpos)
    (lpsOriginalNativeGlobalChartImage_cover N hpos)
    (lpsOriginalNativeGlobalLaurentImage_intersection N hpos) a b hcompat
end
end QEC.Coding.TannerLiftedProduct

namespace QEC.Coding.TannerLiftedProduct
open CategoryTheory _root_.AlgebraicGeometry Opposite QEC.Coding.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N)
local notation "R" => lpsOriginalComplexNormalZeroChart N hpos
local notation "I" => lpsOriginalComplexNormalInfinityChart N hpos
local notation "T" => lpsOriginalComplexNormalLaurentChart N hpos
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
local notation "U" => Functor.obj (Scheme.Hom.opensFunctor
  (lpsOriginalComplexNormalGluedChartMap N hpos false)) ⊤
local notation "V" => Functor.obj (Scheme.Hom.opensFunctor
  (lpsOriginalComplexNormalGluedChartMap N hpos true)) ⊤

def lpsOriginalNativeGlobalAffinePair :
    Γ(Omega, ⊤) → KaehlerDifferential ℂ R × KaehlerDifferential ℂ I :=
  schemeModuleGlobalIsoPair Omega U V
    (lpsOriginalZeroImageFromKaehler N hpos).symm
    (lpsOriginalInfinityImageFromKaehler N hpos).symm

lemma lpsOriginalNativeGlobalAffinePair_injective :
    Function.Injective (lpsOriginalNativeGlobalAffinePair N hpos) :=
  schemeModuleGlobalIsoPair_injective Omega U V
    (lpsOriginalZeroImageFromKaehler N hpos).symm
    (lpsOriginalInfinityImageFromKaehler N hpos).symm
    (lpsOriginalNativeGlobalChartImage_cover N hpos)

lemma lpsOriginalNativeGlobalAffinePair_eq_iff (z : Γ(Omega, ⊤))
    (a : KaehlerDifferential ℂ R) (b : KaehlerDifferential ℂ I) :
    lpsOriginalNativeGlobalAffinePair N hpos z = (a, b) ↔
    (Omega).presheaf.map (homOfLE le_top : U ⟶ ⊤).op z =
      (lpsOriginalZeroImageFromKaehler N hpos).hom a ∧
    (Omega).presheaf.map (homOfLE le_top : V ⟶ ⊤).op z =
      (lpsOriginalInfinityImageFromKaehler N hpos).hom b :=
  schemeModuleGlobalIsoPair_eq_iff Omega U V
    (lpsOriginalZeroImageFromKaehler N hpos).symm
    (lpsOriginalInfinityImageFromKaehler N hpos).symm z a b

lemma lpsOriginalCompatibleAffine_existsUnique_globalPair
    (a : KaehlerDifferential ℂ R) (b : KaehlerDifferential ℂ I)
    (hcompat : KaehlerDifferential.map ℂ ℂ R T a = KaehlerDifferential.map ℂ ℂ I T b) :
    ∃! z : Γ(Omega, ⊤), lpsOriginalNativeGlobalAffinePair N hpos z = (a, b) := by
  obtain ⟨z, hz, huniq⟩ := lpsOriginalCompatibleAffine_existsUnique_globalSection N hpos a b hcompat
  refine ⟨z, (lpsOriginalNativeGlobalAffinePair_eq_iff N hpos z a b).mpr hz, ?_⟩
  intro z' hz'
  exact huniq z' ((lpsOriginalNativeGlobalAffinePair_eq_iff N hpos z' a b).mp hz')
end
end QEC.Coding.TannerLiftedProduct
