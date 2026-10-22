import QEC.Coding.AlgebraicGeometry.Differentials.SchemeRestriction
import QEC.Coding.ExpanderCodes.LPSOriginalDifferentialSheaf

/-!
# Global differential restrictions on the original normalization charts

Both literal chart inclusions restrict the same genuine global differential
sheaf. The proved open-immersion comparison, actual constant diagrams and
affine comparison identify those restrictions with the corresponding tilde
Kähler modules. Native global-section descent and the subsequent original
curve arithmetic and spectral estimates require further proofs.
-/
namespace QEC.Coding.TannerLiftedProduct
open CategoryTheory _root_.AlgebraicGeometry QEC.Coding.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N)
local notation "X" => lpsOriginalComplexNormalGluedScheme N hpos
local notation "Z" => lpsOriginalComplexNormalZeroChart N hpos
local notation "I" => lpsOriginalComplexNormalInfinityChart N hpos
local notation "c" => lpsOriginalComplexNormalGlobalConstantMap N hpos
local instance lpsOriginalChartDifferentialRestrictionOpenImmersion (b : Bool) :
    IsOpenImmersion (lpsOriginalComplexNormalGluedChartMap N hpos b) :=
  lpsOriginalComplexNormalGluedChartMap_openImmersion N hpos b

attribute [local instance] lpsOriginalZeroChartDifferentialAlgebra
  lpsOriginalInfinityChartDifferentialAlgebra lpsOriginalZeroChartDifferentialSMul
  lpsOriginalZeroChartDifferentialModule lpsOriginalZeroChartDifferentialSMulComm
  lpsOriginalZeroChartOmegaSMul lpsOriginalZeroChartOmegaModule
  lpsOriginalInfinityChartDifferentialSMul lpsOriginalInfinityChartDifferentialModule
  lpsOriginalInfinityChartDifferentialSMulComm lpsOriginalInfinityChartOmegaSMul
  lpsOriginalInfinityChartOmegaModule

def lpsOriginalComplexNormalChartDifferentialRestrictionIso (b : Bool) :
    schemeDifferentialSheaf (lpsOriginalComplexNormalSchemeChart N hpos b) (CommRingCat.of ℂ)
      (c ≫ (lpsOriginalComplexNormalGluedChartMap N hpos b).appTop) ≅
    (Scheme.Modules.restrictFunctor (lpsOriginalComplexNormalGluedChartMap N hpos b)).obj
      (lpsOriginalComplexNormalDifferentialSheaf N hpos) :=
  schemeDifferentialRestrictionIso (lpsOriginalComplexNormalGluedChartMap N hpos b)
    (CommRingCat.of ℂ) c

lemma lpsOriginalComplexNormalChartDifferentialRestrictionIso_derivation (b : Bool) :
    (schemeDifferentialSheafDerivation (lpsOriginalComplexNormalSchemeChart N hpos b)
      (CommRingCat.of ℂ) (c ≫ (lpsOriginalComplexNormalGluedChartMap N hpos b).appTop)).postcomp
      ((Scheme.Modules.toPresheafOfModules (lpsOriginalComplexNormalSchemeChart N hpos b)).map
        (lpsOriginalComplexNormalChartDifferentialRestrictionIso N hpos b).hom) =
    schemeRestrictedDifferentialSheafDerivation (lpsOriginalComplexNormalGluedChartMap N hpos b)
      (CommRingCat.of ℂ) c :=
  schemeDifferentialRestrictionIso_derivation (lpsOriginalComplexNormalGluedChartMap N hpos b)
    (CommRingCat.of ℂ) c

def lpsOriginalZeroChartGlobalDifferentialRestrictionIso :
    (Scheme.Modules.restrictFunctor (lpsOriginalComplexNormalGluedChartMap N hpos false)).obj
      (lpsOriginalComplexNormalDifferentialSheaf N hpos) ≅
    tilde (R := CommRingCat.of Z) (ModuleCat.of Z (KaehlerDifferential ℂ Z)) := by
  have h : (c ≫ (lpsOriginalComplexNormalGluedChartMap N hpos false).appTop :
      CommRingCat.of ℂ ⟶ Γ(Spec (CommRingCat.of Z), ⊤)) =
      affineDifferentialGlobalConstantMap ℂ (CommRingCat.of Z) :=
    lpsOriginalComplexNormalGlobalConstantMap_zero_affine N hpos
  exact (lpsOriginalComplexNormalChartDifferentialRestrictionIso N hpos false).symm ≪≫
    eqToIso (congrArg (fun c' : CommRingCat.of ℂ ⟶ Γ(Spec (CommRingCat.of Z), ⊤) =>
      schemeDifferentialSheaf (Spec (CommRingCat.of Z)) (CommRingCat.of ℂ) c') h) ≪≫
    lpsOriginalZeroChartDifferentialSheafIso N hpos

def lpsOriginalInfinityChartGlobalDifferentialRestrictionIso :
    (Scheme.Modules.restrictFunctor (lpsOriginalComplexNormalGluedChartMap N hpos true)).obj
      (lpsOriginalComplexNormalDifferentialSheaf N hpos) ≅
    tilde (R := CommRingCat.of I) (ModuleCat.of I (KaehlerDifferential ℂ I)) := by
  have h : (c ≫ (lpsOriginalComplexNormalGluedChartMap N hpos true).appTop :
      CommRingCat.of ℂ ⟶ Γ(Spec (CommRingCat.of I), ⊤)) =
      affineDifferentialGlobalConstantMap ℂ (CommRingCat.of I) :=
    lpsOriginalComplexNormalGlobalConstantMap_infinity_affine N hpos
  exact (lpsOriginalComplexNormalChartDifferentialRestrictionIso N hpos true).symm ≪≫
    eqToIso (congrArg (fun c' : CommRingCat.of ℂ ⟶ Γ(Spec (CommRingCat.of I), ⊤) =>
      schemeDifferentialSheaf (Spec (CommRingCat.of I)) (CommRingCat.of ℂ) c') h) ≪≫
    lpsOriginalInfinityChartDifferentialSheafIso N hpos
end
end QEC.Coding.TannerLiftedProduct
