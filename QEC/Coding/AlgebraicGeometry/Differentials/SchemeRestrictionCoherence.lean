import QEC.Coding.AlgebraicGeometry.Differentials.SchemeSectionRestriction

/-!
# Compositional differential restriction and actual image sections

Universal derivations prove coherence of the sheaf comparisons. Their actual
section maps commute with nested image restrictions and with the genuine
coefficient identifications. Equal immersions give equal image comparisons.
-/
namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {Y X Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
variable [IsOpenImmersion f] [IsOpenImmersion g]
variable (k : CommRingCat.{u}) (c : k ⟶ Γ(X, ⊤))
local notation "cY" => schemeRestrictionConstantMap f k c
local notation "cZ" => schemeRestrictionConstantMap g k cY
local notation "OmegaX" => schemeDifferentialSheaf X k c
local notation "OmegaY" => schemeDifferentialSheaf Y k cY
local notation "OmegaZ" => schemeDifferentialSheaf Z k cZ

def schemeDifferentialRestrictionComparisonTo
    {W V : Scheme.{u}} (i : W ⟶ V) [IsOpenImmersion i]
    (b : CommRingCat.{u}) (a : b ⟶ Γ(V, ⊤)) (d : b ⟶ Γ(W, ⊤))
    (h : schemeRestrictionConstantMap i b a = d) :
    schemeDifferentialSheaf W b d ⟶
      (Scheme.Modules.restrictFunctor i).obj (schemeDifferentialSheaf V b a) := by
  subst d
  exact schemeDifferentialRestrictionComparison i b a

lemma schemeDifferentialRestrictionComparisonTo_D
    {W V : Scheme.{u}} (i : W ⟶ V) [IsOpenImmersion i]
    (b : CommRingCat.{u}) (a : b ⟶ Γ(V, ⊤)) (d : b ⟶ Γ(W, ⊤))
    (h : schemeRestrictionConstantMap i b a = d) (U : W.Opens) (x : Γ(W, U)) :
    (schemeDifferentialRestrictionComparisonTo i b a d h).app U
      ((schemeDifferentialSheafDerivation W b d).d (X := op U) x) =
    (schemeDifferentialSheafDerivation V b a).d (X := op (i ''ᵁ U))
      ((i.appIso U).inv x) := by
  subst d
  exact PresheafOfModules.Derivation.congr_d
    (schemeDifferentialRestrictionIso_derivation i b a) (X := op U) x

omit [IsOpenImmersion f] [IsOpenImmersion g] in
lemma schemeRestrictionConstantMap_comp :
    schemeRestrictionConstantMap (g ≫ f) k c = cZ :=
  (Category.assoc c f.appTop g.appTop).symm

def schemeDifferentialRestrictionComparisonComposite :
    OmegaZ ⟶ (Scheme.Modules.restrictFunctor (g ≫ f)).obj OmegaX :=
  schemeDifferentialRestrictionComparison g k cY ≫
    (Scheme.Modules.restrictFunctor g).map (schemeDifferentialRestrictionComparison f k c) ≫
    (Scheme.Modules.restrictFunctorComp g f).inv.app OmegaX

lemma schemeDifferentialRestrictionComparison_comp :
    schemeDifferentialRestrictionComparisonTo (g ≫ f) k c cZ
      (schemeRestrictionConstantMap_comp f g k c) =
    schemeDifferentialRestrictionComparisonComposite f g k c := by
  apply (schemeDifferentialSheafHomEquiv Z k cZ
    ((Scheme.Modules.restrictFunctor (g ≫ f)).obj OmegaX)).injective
  rw [← schemeDifferentialSheafDerivation_postcomp,
    ← schemeDifferentialSheafDerivation_postcomp]
  ext U a
  change (schemeDifferentialRestrictionComparisonTo (g ≫ f) k c cZ
      (schemeRestrictionConstantMap_comp f g k c)).app U.unop
        ((schemeDifferentialSheafDerivation Z k cZ).d a) =
    (schemeDifferentialRestrictionComparisonComposite f g k c).app U.unop
      ((schemeDifferentialSheafDerivation Z k cZ).d a)
  have hdirect := schemeDifferentialRestrictionComparisonTo_D (g ≫ f) k c cZ
    (schemeRestrictionConstantMap_comp f g k c) U.unop a
  refine hdirect.trans ?_
  change (schemeDifferentialSheafDerivation X k c).d
      (((g ≫ f).appIso U.unop).inv a) =
    ((Scheme.Modules.restrictFunctorComp g f).inv.app OmegaX).app U.unop
      ((schemeDifferentialRestrictionComparison f k c).app (g ''ᵁ U.unop)
        ((schemeDifferentialRestrictionComparison g k cY).app U.unop
          ((schemeDifferentialSheafDerivation Z k cZ).d a)))
  have hg := PresheafOfModules.Derivation.congr_d
    (schemeDifferentialRestrictionIso_derivation g k cY) (X := U) a
  have hgf := congrArg (fun z : Γ(OmegaY, g ''ᵁ U.unop) =>
    (schemeDifferentialRestrictionComparison f k c).app (g ''ᵁ U.unop) z) hg
  have hf := PresheafOfModules.Derivation.congr_d
    (schemeDifferentialRestrictionIso_derivation f k c) (X := op (g ''ᵁ U.unop))
      ((g.appIso U.unop).inv a)
  have hright := congrArg (fun z : Γ(OmegaX, f ''ᵁ (g ''ᵁ U.unop)) =>
    ((Scheme.Modules.restrictFunctorComp g f).inv.app OmegaX).app U.unop z) (hgf.trans hf)
  refine (Eq.trans ?_ hright.symm)
  rw [Scheme.Modules.restrictFunctorComp_inv_app_app]
  have hr := congrArg (fun e : Γ(X, (g ≫ f) ''ᵁ U.unop) ≅ Γ(Z, U.unop) => e.inv a)
    (Scheme.Hom.comp_appIso g f U.unop)
  have hd := (schemeDifferentialSheafDerivation X k c).d_map
    (eqToHom (Scheme.Hom.comp_image g f U.unop)).op
      ((f.appIso (g ''ᵁ U.unop)).inv ((g.appIso U.unop).inv a))
  exact (congrArg (fun z : Γ(X, (g ≫ f) ''ᵁ U.unop) =>
    (schemeDifferentialSheafDerivation X k c).d (X := op ((g ≫ f) ''ᵁ U.unop)) z) hr).trans hd
end
end QEC.Coding.AlgebraicGeometry

namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {Y X Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
variable [IsOpenImmersion f] [IsOpenImmersion g]
variable (k : CommRingCat.{u}) (c : k ⟶ Γ(X, ⊤))
local notation "cY" => schemeRestrictionConstantMap f k c
local notation "cZ" => schemeRestrictionConstantMap g k cY
local notation "OmegaX" => schemeDifferentialSheaf X k c
local notation "OmegaY" => schemeDifferentialSheaf Y k cY
local notation "OmegaZ" => schemeDifferentialSheaf Z k cZ

lemma schemeDifferentialRestrictionImageSectionIso_comp (U : Z.Opens) (s : Γ(OmegaZ, U)) :
    (schemeDifferentialRestrictionImageSectionIsoTo (g ≫ f) k c cZ
      (schemeRestrictionConstantMap_comp f g k c) U).hom s =
    (OmegaX).presheaf.map (eqToHom (Scheme.Hom.comp_image g f U)).op
      ((schemeDifferentialRestrictionImageSectionIso f k c (g ''ᵁ U)).hom
        ((schemeDifferentialRestrictionImageSectionIso g k cY U).hom s)) := by
  have hc := congrArg (fun t : OmegaZ ⟶
      (Scheme.Modules.restrictFunctor (g ≫ f)).obj OmegaX => t.app U s)
    (schemeDifferentialRestrictionComparison_comp f g k c)
  exact hc

lemma schemeDifferentialRestrictionImageSectionIso_naturality
    {U V : Y.Opens} (i : U ⟶ V) (s : Γ(OmegaY, V)) :
    (schemeDifferentialRestrictionImageSectionIso f k c U).hom
      ((OmegaY).presheaf.map i.op s) =
    (OmegaX).presheaf.map (f.opensFunctor.map i).op
      ((schemeDifferentialRestrictionImageSectionIso f k c V).hom s) :=
  congrArg (fun t => t s)
    (((Scheme.Modules.toPresheaf Y).map (schemeDifferentialRestrictionIso f k c).hom).naturality
      i.op)

lemma schemeDifferentialRestrictionImageSectionIso_globalRestriction
    (s : Γ(OmegaY, ⊤)) :
    (schemeDifferentialRestrictionImageSectionIsoTo (g ≫ f) k c cZ
      (schemeRestrictionConstantMap_comp f g k c) ⊤).hom
        (schemeDifferentialGlobalRestriction g k cY s) =
    (OmegaX).presheaf.map (eqToHom (Scheme.Hom.comp_image g f ⊤)).op
      ((OmegaX).presheaf.map
        (f.opensFunctor.map (homOfLE le_top : g ''ᵁ ⊤ ⟶ ⊤)).op
          ((schemeDifferentialRestrictionImageSectionIso f k c ⊤).hom s)) := by
  have hc := schemeDifferentialRestrictionImageSectionIso_comp f g k c ⊤
    (schemeDifferentialGlobalRestriction g k cY s)
  have hi : (schemeDifferentialRestrictionImageSectionIso g k cY ⊤).hom
      (schemeDifferentialGlobalRestriction g k cY s) =
    (OmegaY).presheaf.map (homOfLE le_top : g ''ᵁ ⊤ ⟶ ⊤).op s :=
    Iso.inv_hom_id_apply (schemeDifferentialRestrictionImageSectionIso g k cY ⊤) _
  have hn := schemeDifferentialRestrictionImageSectionIso_naturality f k c
    (homOfLE le_top : g ''ᵁ ⊤ ⟶ ⊤) s
  exact hc.trans (congrArg (fun z : Γ(OmegaX, f ''ᵁ (g ''ᵁ ⊤)) =>
    (OmegaX).presheaf.map (eqToHom (Scheme.Hom.comp_image g f ⊤)).op z)
      ((congrArg (fun z : Γ(OmegaY, g ''ᵁ ⊤) =>
        (schemeDifferentialRestrictionImageSectionIso f k c (g ''ᵁ ⊤)).hom z) hi).trans hn))
variable (d : k ⟶ Γ(Y, ⊤)) (e : k ⟶ Γ(Z, ⊤))
variable (hf : schemeRestrictionConstantMap f k c = d)
variable (hg : schemeRestrictionConstantMap g k d = e)

include hf hg in
omit [IsOpenImmersion f] [IsOpenImmersion g] in
lemma schemeRestrictionConstantMap_comp_to :
    schemeRestrictionConstantMap (g ≫ f) k c = e := by
  change c ≫ (f.appTop ≫ g.appTop) = e
  exact (Category.assoc c f.appTop g.appTop).symm.trans
    ((congrArg (fun a : k ⟶ Γ(Y, ⊤) => a ≫ g.appTop) hf).trans hg)

lemma schemeDifferentialRestrictionImageSectionIsoTo_globalRestriction
    (s : Γ(schemeDifferentialSheaf Y k d, ⊤)) :
    (schemeDifferentialRestrictionImageSectionIsoTo (g ≫ f) k c e
      (schemeRestrictionConstantMap_comp_to f g k c d e hf hg) ⊤).hom
        (schemeDifferentialGlobalRestrictionTo g k d e hg s) =
    (OmegaX).presheaf.map (eqToHom (Scheme.Hom.comp_image g f ⊤)).op
      ((OmegaX).presheaf.map
        (f.opensFunctor.map (homOfLE le_top : g ''ᵁ ⊤ ⟶ ⊤)).op
          ((schemeDifferentialRestrictionImageSectionIsoTo f k c d hf ⊤).hom s)) := by
  subst d
  subst e
  exact schemeDifferentialRestrictionImageSectionIso_globalRestriction f g k c s

end
end QEC.Coding.AlgebraicGeometry

namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {Y X : Scheme.{u}} (i j : Y ⟶ X)
variable [IsOpenImmersion i] [IsOpenImmersion j]
variable (k : CommRingCat.{u}) (c : k ⟶ Γ(X, ⊤)) (d : k ⟶ Γ(Y, ⊤))
variable (hi : schemeRestrictionConstantMap i k c = d)
variable (hj : schemeRestrictionConstantMap j k c = d)
local notation "OmegaX" => schemeDifferentialSheaf X k c

lemma schemeOpenImmersionImage_congr (h : i = j) (U : Y.Opens) : i ''ᵁ U = j ''ᵁ U := by
  subst j
  rfl

lemma schemeDifferentialRestrictionImageSectionIsoTo_congr
    (h : i = j) (U : Y.Opens) (s : Γ(schemeDifferentialSheaf Y k d, U)) :
    (schemeDifferentialRestrictionImageSectionIsoTo i k c d hi U).hom s =
    (OmegaX).presheaf.map (eqToHom (schemeOpenImmersionImage_congr i j h U)).op
      ((schemeDifferentialRestrictionImageSectionIsoTo j k c d hj U).hom s) := by
  subst j
  change (schemeDifferentialRestrictionImageSectionIsoTo i k c d hi U).hom s =
    (OmegaX).presheaf.map (𝟙 (op (i ''ᵁ U)))
      ((schemeDifferentialRestrictionImageSectionIsoTo i k c d hi U).hom s)
  exact (congrArg (fun t : Γ(OmegaX, i ''ᵁ U) ⟶ Γ(OmegaX, i ''ᵁ U) =>
    t ((schemeDifferentialRestrictionImageSectionIsoTo i k c d hi U).hom s))
      ((OmegaX).presheaf.map_id (op (i ''ᵁ U)))).symm
end
end QEC.Coding.AlgebraicGeometry

namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
variable [IsOpenImmersion f] [IsOpenImmersion g]

lemma schemeNestedImage_le : (g ≫ f) ''ᵁ ⊤ ≤ f ''ᵁ ⊤ := by
  rw [Scheme.Hom.comp_image]
  exact f.image_mono le_top

lemma schemeModuleNestedImageRestriction (M : X.Modules) (s : Γ(M, f ''ᵁ ⊤)) :
    M.presheaf.map (eqToHom (Scheme.Hom.comp_image g f ⊤)).op
      (M.presheaf.map (f.opensFunctor.map (homOfLE le_top : g ''ᵁ ⊤ ⟶ ⊤)).op s) =
    M.presheaf.map (homOfLE (schemeNestedImage_le f g)).op s := by
  rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp]
  rfl

lemma schemeModuleRestriction_cast (M : X.Modules) {W V U : X.Opens}
    (e : W = V) (h : V ≤ U) (s : Γ(M, U)) :
    M.presheaf.map (eqToHom e).op (M.presheaf.map (homOfLE h).op s) =
      M.presheaf.map (homOfLE (e.le.trans h)).op s := by
  rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp]
  rfl
end
end QEC.Coding.AlgebraicGeometry
