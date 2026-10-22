import QEC.Coding.AlgebraicGeometry.Differentials.SchemeRestriction

/-!
# Restricting actual global differential sections

The proved open-immersion isomorphism induces image-section isomorphisms and
global restriction maps. These preserve universal derivatives and scalars;
proved structural coefficient equalities transport the same actual maps.
-/
namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {Y X : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
variable (k : CommRingCat.{u}) (c : k ⟶ Γ(X, ⊤))
local notation "OmegaX" => schemeDifferentialSheaf X k c
local notation "OmegaY" => schemeDifferentialSheaf Y k (schemeRestrictionConstantMap f k c)

lemma additiveSectionIso_hom_injective {A B : AddCommGrpCat.{u}} (e : A ≅ B) :
    Function.Injective e.hom := by
  intro a b h
  have hh := congrArg (fun x : B => e.inv x) h
  exact (Iso.hom_inv_id_apply e a).symm.trans (hh.trans (Iso.hom_inv_id_apply e b))

def schemeDifferentialRestrictionImageSectionIso (U : Y.Opens) :
    Γ(OmegaY, U) ≅ Γ(OmegaX, f ''ᵁ U) :=
  ((Scheme.Modules.toPresheaf Y).mapIso (schemeDifferentialRestrictionIso f k c)).app (op U) ≪≫
    (OmegaX).restrictAppIso f U

lemma schemeDifferentialRestrictionImageSectionIso_D (U : Y.Opens) (a : Γ(Y, U)) :
    (schemeDifferentialRestrictionImageSectionIso f k c U).hom
      ((schemeDifferentialSheafDerivation Y k (schemeRestrictionConstantMap f k c)).d
        (X := op U) a) =
    (schemeDifferentialSheafDerivation X k c).d (X := op (f ''ᵁ U))
      ((f.appIso U).inv a) := by
  exact PresheafOfModules.Derivation.congr_d
    (schemeDifferentialRestrictionIso_derivation f k c) (X := op U) a

lemma schemeDifferentialRestrictionImageSectionIso_smul (U : Y.Opens)
    (a : Γ(Y, U)) (s : Γ(OmegaY, U)) :
    (schemeDifferentialRestrictionImageSectionIso f k c U).hom (a • s) =
      (f.appIso U).inv a • (schemeDifferentialRestrictionImageSectionIso f k c U).hom s := by
  exact Scheme.Modules.Hom.app_smul (schemeDifferentialRestrictionIso f k c).hom a s

lemma schemeRestrictionGlobal_appIso_inv_appTop (a : Γ(X, ⊤)) :
    (f.appIso ⊤).inv (f.appTop a) =
      X.presheaf.map (homOfLE le_top : f ''ᵁ ⊤ ⟶ ⊤).op a := by
  have htop : f.appLE ⊤ ⊤ (by simp) = f.appTop := f.appLE_eq_app
  have h := f.appLE_appIso_inv (U := ⊤) (V := ⊤) (by simp)
  rw [htop] at h
  exact congrArg (fun t => t a) h

def schemeDifferentialGlobalRestriction : Γ(OmegaX, ⊤) ⟶ Γ(OmegaY, ⊤) :=
  (OmegaX).presheaf.map (homOfLE le_top : f ''ᵁ ⊤ ⟶ ⊤).op ≫
    (schemeDifferentialRestrictionImageSectionIso f k c ⊤).inv

lemma schemeDifferentialGlobalRestriction_smul (a : Γ(X, ⊤)) (s : Γ(OmegaX, ⊤)) :
    schemeDifferentialGlobalRestriction f k c (a • s) =
      f.appTop a • schemeDifferentialGlobalRestriction f k c s := by
  let e := schemeDifferentialRestrictionImageSectionIso f k c ⊤
  let i : f ''ᵁ ⊤ ⟶ (⊤ : X.Opens) := homOfLE le_top
  let r := (OmegaX).presheaf.map i.op
  apply additiveSectionIso_hom_injective e
  change e.hom (e.inv (r (a • s))) = e.hom (f.appTop a • e.inv (r s))
  have h1 : e.hom (e.inv (r (a • s))) = r (a • s) := Iso.inv_hom_id_apply e _
  have h2 : r (a • s) = X.presheaf.map i.op a • r s :=
    Scheme.Modules.map_smul («M» := OmegaX) i a s
  have h3 : X.presheaf.map i.op a • r s = (f.appIso ⊤).inv (f.appTop a) • r s :=
    congrArg (fun b => b • r s) (schemeRestrictionGlobal_appIso_inv_appTop f a).symm
  have h4 : (f.appIso ⊤).inv (f.appTop a) • r s =
      (f.appIso ⊤).inv (f.appTop a) • e.hom (e.inv (r s)) :=
    congrArg (fun z => (f.appIso ⊤).inv (f.appTop a) • z) (Iso.inv_hom_id_apply e (r s)).symm
  have h5 : (f.appIso ⊤).inv (f.appTop a) • e.hom (e.inv (r s)) =
      e.hom (f.appTop a • e.inv (r s)) :=
    (schemeDifferentialRestrictionImageSectionIso_smul f k c ⊤ (f.appTop a) (e.inv (r s))).symm
  exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

lemma schemeDifferentialGlobalRestriction_D (a : Γ(X, ⊤)) :
    schemeDifferentialGlobalRestriction f k c
      ((schemeDifferentialSheafDerivation X k c).d (X := op ⊤) a) =
    (schemeDifferentialSheafDerivation Y k (schemeRestrictionConstantMap f k c)).d
      (X := op ⊤) (f.appTop a) := by
  let e := schemeDifferentialRestrictionImageSectionIso f k c ⊤
  let r := (OmegaX).presheaf.map (homOfLE le_top : f ''ᵁ ⊤ ⟶ ⊤).op
  apply additiveSectionIso_hom_injective e
  have he : e.hom (e.inv (r ((schemeDifferentialSheafDerivation X k c).d a))) =
      r ((schemeDifferentialSheafDerivation X k c).d a) := by
    exact Iso.inv_hom_id_apply e _
  change e.hom (e.inv (r ((schemeDifferentialSheafDerivation X k c).d a))) =
    e.hom ((schemeDifferentialSheafDerivation Y k (schemeRestrictionConstantMap f k c)).d
      (f.appTop a))
  rw [he]
  have hr : (f.appIso ⊤).inv (f.appTop a) =
      X.presheaf.map (homOfLE le_top : f ''ᵁ ⊤ ⟶ ⊤).op a := by
    have htop : f.appLE ⊤ ⊤ (by simp) = f.appTop := f.appLE_eq_app
    have h := f.appLE_appIso_inv (U := ⊤) (V := ⊤) (by simp)
    rw [htop] at h
    exact congrArg (fun t => t a) h
  have hd := (schemeDifferentialSheafDerivation X k c).d_map
    (homOfLE le_top : f ''ᵁ ⊤ ⟶ ⊤).op a
  exact hd.symm.trans ((congrArg
    (fun z => (schemeDifferentialSheafDerivation X k c).d (X := op (f ''ᵁ ⊤)) z)
      hr.symm).trans (schemeDifferentialRestrictionImageSectionIso_D f k c ⊤
        (f.appTop a)).symm)
end
end QEC.Coding.AlgebraicGeometry

namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {Y X : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
variable (k : CommRingCat.{u}) (c : k ⟶ Γ(X, ⊤)) (d : k ⟶ Γ(Y, ⊤))
variable (h : schemeRestrictionConstantMap f k c = d)
local notation "OmegaX" => schemeDifferentialSheaf X k c
local notation "OmegaY" => schemeDifferentialSheaf Y k d

def schemeDifferentialGlobalRestrictionTo : Γ(OmegaX, ⊤) ⟶ Γ(OmegaY, ⊤) := by
  subst d
  exact schemeDifferentialGlobalRestriction f k c

lemma schemeDifferentialGlobalRestrictionTo_D (a : Γ(X, ⊤)) :
    schemeDifferentialGlobalRestrictionTo f k c d h
      ((schemeDifferentialSheafDerivation X k c).d (X := op ⊤) a) =
      (schemeDifferentialSheafDerivation Y k d).d (X := op ⊤) (f.appTop a) := by
  subst d
  exact schemeDifferentialGlobalRestriction_D f k c a

lemma schemeDifferentialGlobalRestrictionTo_smul (a : Γ(X, ⊤)) (s : Γ(OmegaX, ⊤)) :
    schemeDifferentialGlobalRestrictionTo f k c d h (a • s) =
      f.appTop a • schemeDifferentialGlobalRestrictionTo f k c d h s := by
  subst d
  exact schemeDifferentialGlobalRestriction_smul f k c a s
end
end QEC.Coding.AlgebraicGeometry

namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {Y X : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
variable (k : CommRingCat.{u}) (c : k ⟶ Γ(X, ⊤)) (d : k ⟶ Γ(Y, ⊤))
variable (h : schemeRestrictionConstantMap f k c = d)

def schemeDifferentialRestrictionImageSectionIsoTo (U : Y.Opens) :
    Γ(schemeDifferentialSheaf Y k d, U) ≅ Γ(schemeDifferentialSheaf X k c, f ''ᵁ U) := by
  subst d
  exact schemeDifferentialRestrictionImageSectionIso f k c U

end
end QEC.Coding.AlgebraicGeometry
