import QEC.Coding.AlgebraicGeometry.Differentials.AffineDifferentials
import QEC.Coding.ExpanderCodes.LPSOriginalComplexNormalCharts

/-!
# The original normalization differential sheaf and its affine charts

The actual structure map to `Spec ℂ` supplies the global constants and the
universal differential module sheaf. Its literal zero and reciprocal constant
diagrams are proved, and both chart differential sheaves are identified with
the corresponding tilde Kähler modules. This is an internal step in the PK22 proof
(original LPS route, registered PK22 `main.tex`, `ex:Xpq`, lines 484–486).
Restriction of the global curve sheaf to these charts, native global sections,
and the spectral estimates remain further proof obligations.
-/
namespace QEC.Coding.TannerLiftedProduct
open CategoryTheory _root_.AlgebraicGeometry QEC.Coding.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N)
local notation "X" => lpsOriginalComplexNormalGluedScheme N hpos

def lpsOriginalComplexNormalGlobalConstantMap : CommRingCat.of ℂ ⟶ Γ(X, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫
    (lpsOriginalComplexNormalGluedToSpecC N hpos).appTop

lemma lpsOriginalComplexNormalGlobalConstantMap_chart (b : Bool) :
    lpsOriginalComplexNormalGlobalConstantMap N hpos ≫
      (lpsOriginalComplexNormalGluedChartMap N hpos b).appTop =
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫
      (lpsOriginalComplexChartToSpecC N hpos b).appTop := by
  unfold lpsOriginalComplexNormalGlobalConstantMap
  rw [Category.assoc, ← Scheme.Hom.comp_appTop,
    lpsOriginalComplexNormalGluedToSpecC_chart]

lemma lpsOriginalComplexNormalGlobalConstantMap_zero :
    lpsOriginalComplexNormalGlobalConstantMap N hpos ≫
      (lpsOriginalComplexNormalGluedChartMap N hpos false).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of (lpsOriginalComplexNormalZeroChart N hpos))).hom =
    CommRingCat.ofHom (lpsOriginalComplexZeroConstantRingHom N hpos) := by
  have h := congrArg
    (fun t : CommRingCat.of ℂ ⟶
        Γ(Spec (CommRingCat.of (lpsOriginalComplexNormalZeroChart N hpos)), ⊤) =>
      t ≫ (Scheme.ΓSpecIso
        (CommRingCat.of (lpsOriginalComplexNormalZeroChart N hpos))).hom)
    (lpsOriginalComplexNormalGlobalConstantMap_chart N hpos false)
  trans ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫
    (lpsOriginalComplexChartToSpecC N hpos false).appTop) ≫
      (Scheme.ΓSpecIso
        (CommRingCat.of (lpsOriginalComplexNormalZeroChart N hpos))).hom
  · exact (Category.assoc _ _ _).symm.trans h
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫
    (Spec.map (CommRingCat.ofHom (lpsOriginalComplexZeroConstantRingHom N hpos))).appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of (lpsOriginalComplexNormalZeroChart N hpos))).hom = _
  rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

lemma lpsOriginalComplexNormalGlobalConstantMap_infinity :
    lpsOriginalComplexNormalGlobalConstantMap N hpos ≫
      (lpsOriginalComplexNormalGluedChartMap N hpos true).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of (lpsOriginalComplexNormalInfinityChart N hpos))).hom =
    CommRingCat.ofHom (lpsOriginalComplexInfinityConstantRingHom N hpos) := by
  have h := congrArg
    (fun t : CommRingCat.of ℂ ⟶
        Γ(Spec (CommRingCat.of (lpsOriginalComplexNormalInfinityChart N hpos)), ⊤) =>
      t ≫ (Scheme.ΓSpecIso
        (CommRingCat.of (lpsOriginalComplexNormalInfinityChart N hpos))).hom)
    (lpsOriginalComplexNormalGlobalConstantMap_chart N hpos true)
  trans ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫
    (lpsOriginalComplexChartToSpecC N hpos true).appTop) ≫
      (Scheme.ΓSpecIso
        (CommRingCat.of (lpsOriginalComplexNormalInfinityChart N hpos))).hom
  · exact (Category.assoc _ _ _).symm.trans h
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫
    (Spec.map (CommRingCat.ofHom (lpsOriginalComplexInfinityConstantRingHom N hpos))).appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of (lpsOriginalComplexNormalInfinityChart N hpos))).hom = _
  rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

def lpsOriginalComplexNormalDifferentialSheaf : Scheme.Modules X :=
  schemeDifferentialSheaf X (CommRingCat.of ℂ)
    (lpsOriginalComplexNormalGlobalConstantMap N hpos)

/-- The actual universal derivation into the original curve's differential module sheaf. -/
def lpsOriginalComplexNormalDifferentialSheafDerivation :
    ((Scheme.Modules.toPresheafOfModules X).obj
      (lpsOriginalComplexNormalDifferentialSheaf N hpos)).Derivation'
        (schemeConstantPresheafMap X (CommRingCat.of ℂ)
          (lpsOriginalComplexNormalGlobalConstantMap N hpos)) :=
  schemeDifferentialSheafDerivation X (CommRingCat.of ℂ)
    (lpsOriginalComplexNormalGlobalConstantMap N hpos)

lemma lpsOriginalComplexNormalDifferentialSheaf_existsUnique (M : Scheme.Modules X)
    (d : ((Scheme.Modules.toPresheafOfModules X).obj M).Derivation'
      (schemeConstantPresheafMap X (CommRingCat.of ℂ)
        (lpsOriginalComplexNormalGlobalConstantMap N hpos))) :
    ∃! f : lpsOriginalComplexNormalDifferentialSheaf N hpos ⟶ M,
      (lpsOriginalComplexNormalDifferentialSheafDerivation N hpos).postcomp
        ((Scheme.Modules.toPresheafOfModules X).map f) = d :=
  schemeDifferentialSheafDerivation_existsUnique X (CommRingCat.of ℂ)
    (lpsOriginalComplexNormalGlobalConstantMap N hpos) M d
local notation "Z" => lpsOriginalComplexNormalZeroChart N hpos
local notation "I" => lpsOriginalComplexNormalInfinityChart N hpos
local instance lpsOriginalZeroChartDifferentialAlgebra : Algebra ℂ Z :=
  (lpsOriginalComplexZeroConstantRingHom N hpos).toAlgebra
local instance lpsOriginalInfinityChartDifferentialAlgebra : Algebra ℂ I :=
  (lpsOriginalComplexInfinityConstantRingHom N hpos).toAlgebra

local instance lpsOriginalZeroChartDifferentialSMul : SMul ℂ Z := Algebra.toSMul
local instance lpsOriginalZeroChartDifferentialModule : Module ℂ Z := Algebra.toModule
local instance lpsOriginalZeroChartDifferentialSMulComm : SMulCommClass ℂ Z Z where
  smul_comm c a b := by simp only [Algebra.smul_def]; ring
local instance lpsOriginalZeroChartOmegaSMul : SMul Z (KaehlerDifferential ℂ Z) :=
  instSMulKaehlerDifferentialOfSMulCommClass ℂ Z
local instance lpsOriginalZeroChartOmegaModule : Module Z (KaehlerDifferential ℂ Z) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℂ Z
local instance lpsOriginalInfinityChartDifferentialSMul : SMul ℂ I := Algebra.toSMul
local instance lpsOriginalInfinityChartDifferentialModule : Module ℂ I := Algebra.toModule
local instance lpsOriginalInfinityChartDifferentialSMulComm : SMulCommClass ℂ I I where
  smul_comm c a b := by simp only [Algebra.smul_def]; ring
local instance lpsOriginalInfinityChartOmegaSMul : SMul I (KaehlerDifferential ℂ I) :=
  instSMulKaehlerDifferentialOfSMulCommClass ℂ I
local instance lpsOriginalInfinityChartOmegaModule : Module I (KaehlerDifferential ℂ I) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℂ I

lemma lpsOriginalComplexNormalGlobalConstantMap_zero_affine :
    lpsOriginalComplexNormalGlobalConstantMap N hpos ≫
      (lpsOriginalComplexNormalGluedChartMap N hpos false).appTop =
    affineDifferentialGlobalConstantMap ℂ (CommRingCat.of Z) := by
  apply (cancel_mono (Scheme.ΓSpecIso (CommRingCat.of Z)).hom).mp
  change _ = (CommRingCat.ofHom (lpsOriginalComplexZeroConstantRingHom N hpos) ≫
    (Scheme.ΓSpecIso (CommRingCat.of Z)).inv) ≫ (Scheme.ΓSpecIso (CommRingCat.of Z)).hom
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact lpsOriginalComplexNormalGlobalConstantMap_zero N hpos

lemma lpsOriginalComplexNormalGlobalConstantMap_infinity_affine :
    lpsOriginalComplexNormalGlobalConstantMap N hpos ≫
      (lpsOriginalComplexNormalGluedChartMap N hpos true).appTop =
    affineDifferentialGlobalConstantMap ℂ (CommRingCat.of I) := by
  apply (cancel_mono (Scheme.ΓSpecIso (CommRingCat.of I)).hom).mp
  change _ = (CommRingCat.ofHom (lpsOriginalComplexInfinityConstantRingHom N hpos) ≫
    (Scheme.ΓSpecIso (CommRingCat.of I)).inv) ≫ (Scheme.ΓSpecIso (CommRingCat.of I)).hom
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact lpsOriginalComplexNormalGlobalConstantMap_infinity N hpos

/-- Genuine differential sheaf comparison on the literal zero normalization chart. -/
def lpsOriginalZeroChartDifferentialSheafIso :
    schemeDifferentialSheaf (Spec (CommRingCat.of Z)) (CommRingCat.of ℂ)
      (affineDifferentialGlobalConstantMap ℂ (CommRingCat.of Z)) ≅
    tilde (R := CommRingCat.of Z) (ModuleCat.of Z (KaehlerDifferential ℂ Z)) :=
  affineDifferentialSheafIso ℂ (CommRingCat.of Z)

/-- Genuine differential sheaf comparison on the literal reciprocal normalization chart. -/
def lpsOriginalInfinityChartDifferentialSheafIso :
    schemeDifferentialSheaf (Spec (CommRingCat.of I)) (CommRingCat.of ℂ)
      (affineDifferentialGlobalConstantMap ℂ (CommRingCat.of I)) ≅
    tilde (R := CommRingCat.of I) (ModuleCat.of I (KaehlerDifferential ℂ I)) :=
  affineDifferentialSheafIso ℂ (CommRingCat.of I)

end
end QEC.Coding.TannerLiftedProduct
