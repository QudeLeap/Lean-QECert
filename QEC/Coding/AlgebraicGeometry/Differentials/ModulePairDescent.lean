import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Two-open descent for genuine scheme module sheaves

The actual sheaf condition glues compatible local sections uniquely. Genuine
section isomorphisms then identify global sections with their affine pairs.
-/
namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {X : Scheme.{u}} (M : X.Modules) (U V : X.Opens)

def schemeModuleAbelianSheaf : TopCat.Sheaf AddCommGrpCat X :=
  ⟨M.presheaf, Scheme.Modules.isSheaf M⟩

def schemeModulePairOpens : Bool → X.Opens
  | false => U
  | true => V

def schemeModulePairSections (s : Γ(M, U)) (t : Γ(M, V)) :
    (b : Bool) → M.presheaf.obj (op (schemeModulePairOpens U V b))
  | false => s
  | true => t

lemma schemeModulePairSections_compatible (s : Γ(M, U)) (t : Γ(M, V))
    (h : M.presheaf.map (TopologicalSpace.Opens.infLELeft U V).op s =
      M.presheaf.map (TopologicalSpace.Opens.infLERight U V).op t) :
    TopCat.Presheaf.IsCompatible M.presheaf (schemeModulePairOpens U V)
      (schemeModulePairSections M U V s t) := by
  intro b d
  cases b <;> cases d
  · rfl
  · exact h
  · let i : V ⊓ U ⟶ U ⊓ V := eqToHom (inf_comm V U)
    have hr := congrArg (fun z => M.presheaf.map i.op z) h
    have hs : M.presheaf.map i.op
        (M.presheaf.map (TopologicalSpace.Opens.infLELeft U V).op s) =
        M.presheaf.map (TopologicalSpace.Opens.infLERight V U).op s := by
      rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp]
      rfl
    have ht : M.presheaf.map i.op
        (M.presheaf.map (TopologicalSpace.Opens.infLERight U V).op t) =
        M.presheaf.map (TopologicalSpace.Opens.infLELeft V U).op t := by
      rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp]
      rfl
    exact (ht.symm.trans hr.symm).trans hs
  · rfl

lemma schemeModulePairOpens_cover (hcover : U ⊔ V = ⊤) :
    (⊤ : X.Opens) ≤ iSup (schemeModulePairOpens U V) := by
  rw [← hcover]
  exact sup_le (le_iSup (schemeModulePairOpens U V) false)
    (le_iSup (schemeModulePairOpens U V) true)

lemma schemeModulePair_existsUnique_global (hcover : U ⊔ V = ⊤)
    (s : Γ(M, U)) (t : Γ(M, V))
    (h : M.presheaf.map (TopologicalSpace.Opens.infLELeft U V).op s =
      M.presheaf.map (TopologicalSpace.Opens.infLERight U V).op t) :
    ∃! z : Γ(M, ⊤), M.presheaf.map (homOfLE le_top).op z = s ∧
      M.presheaf.map (homOfLE le_top).op z = t := by
  obtain ⟨z, hz, huniq⟩ := (schemeModuleAbelianSheaf M).existsUnique_gluing'
    (schemeModulePairOpens U V) ⊤ (fun _ => homOfLE le_top)
    (schemeModulePairOpens_cover U V hcover) (schemeModulePairSections M U V s t)
    (schemeModulePairSections_compatible M U V s t h)
  refine ⟨z, ⟨hz false, hz true⟩, ?_⟩
  intro z' hz'
  apply huniq z'
  intro b
  cases b
  · exact hz'.1
  · exact hz'.2

lemma schemeModulePair_restrictions_injective (hcover : U ⊔ V = ⊤) :
    Function.Injective (fun z : Γ(M, ⊤) =>
      ((M.presheaf.map (homOfLE le_top).op z,
       M.presheaf.map (homOfLE le_top).op z) : Γ(M,U) × Γ(M,V))) := by
  intro s t h
  exact (schemeModuleAbelianSheaf M).eq_of_locally_eq₂
    (homOfLE le_top) (homOfLE le_top) (by rw [hcover]) s t
    (congrArg Prod.fst h) (congrArg Prod.snd h)

end
end QEC.Coding.AlgebraicGeometry

namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {X : Scheme.{u}} (M : X.Modules) (U V : X.Opens)
variable {A B : AddCommGrpCat.{u}} (e : Γ(M, U) ≅ A) (f : Γ(M, V) ≅ B)

def schemeModuleGlobalIsoPair (z : Γ(M, ⊤)) : A × B :=
  (e.hom (M.presheaf.map (homOfLE le_top).op z),
    f.hom (M.presheaf.map (homOfLE le_top).op z))

lemma schemeModuleGlobalIsoPair_injective (hcover : U ⊔ V = ⊤) :
    Function.Injective (schemeModuleGlobalIsoPair M U V e f) := by
  intro s t h
  apply schemeModulePair_restrictions_injective M U V hcover
  apply Prod.ext
  · have hh := congrArg (fun a : A => e.inv a) (congrArg Prod.fst h)
    exact (Iso.hom_inv_id_apply e _).symm.trans (hh.trans (Iso.hom_inv_id_apply e _))
  · have hh := congrArg (fun b : B => f.inv b) (congrArg Prod.snd h)
    exact (Iso.hom_inv_id_apply f _).symm.trans (hh.trans (Iso.hom_inv_id_apply f _))
end
end QEC.Coding.AlgebraicGeometry

namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {X : Scheme.{u}} (M : X.Modules) (U V : X.Opens)
variable {A B : AddCommGrpCat.{u}} (e : Γ(M, U) ≅ A) (f : Γ(M, V) ≅ B)

lemma schemeModuleGlobalIsoPair_eq_iff (z : Γ(M, ⊤)) (a : A) (b : B) :
    schemeModuleGlobalIsoPair M U V e f z = (a, b) ↔
    M.presheaf.map (homOfLE le_top : U ⟶ ⊤).op z = e.inv a ∧
      M.presheaf.map (homOfLE le_top : V ⟶ ⊤).op z = f.inv b := by
  constructor
  · intro h
    have he := congrArg (fun t : A × B => e.inv t.1) h
    have hf := congrArg (fun t : A × B => f.inv t.2) h
    exact ⟨(Iso.hom_inv_id_apply e _).symm.trans he,
      (Iso.hom_inv_id_apply f _).symm.trans hf⟩
  · rintro ⟨he, hf⟩
    apply Prod.ext
    · exact (congrArg e.hom he).trans (Iso.inv_hom_id_apply e a)
    · exact (congrArg f.hom hf).trans (Iso.inv_hom_id_apply f b)
end
end QEC.Coding.AlgebraicGeometry
