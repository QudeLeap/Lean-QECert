import QEC.Coding.AlgebraicGeometry.Differentials.SchemeRestrictionCoherence
import QEC.Coding.AlgebraicGeometry.Differentials.AffineDifferentials

/-!
# Affine differential restriction and Kähler naturality

The genuine section restriction preserves universal derivative generators and
scalar multiplication, hence equals the actual algebraic Kähler map on every
covector. Affine image-section isomorphisms commute with these restrictions
and preserve scalars from the global coefficient ring.
-/
namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
noncomputable section
universe u
lemma affineCoefficientRestrictionSquare (C A B : CommRingCat.{u})
    (phi : C ⟶ A) (psi : C ⟶ B) (q : A ⟶ B) (h : phi ≫ q = psi) :
    (phi ≫ (Scheme.ΓSpecIso A).inv) ≫ (Spec.map q).appTop =
      psi ≫ (Scheme.ΓSpecIso B).inv := by
  have hn : (Scheme.ΓSpecIso A).inv ≫ (Spec.map q).appTop =
      q ≫ (Scheme.ΓSpecIso B).inv := (Scheme.ΓSpecIso_inv_naturality q).symm
  have h1 := Category.assoc phi (Scheme.ΓSpecIso A).inv (Spec.map q).appTop
  have h2 := congrArg (fun t : A ⟶ Γ(Spec B, ⊤) => phi ≫ t) hn
  have h3 := (Category.assoc phi q (Scheme.ΓSpecIso B).inv).symm
  have h4 := congrArg (fun t : C ⟶ B => t ≫ (Scheme.ΓSpecIso B).inv) h
  exact h1.trans (h2.trans (h3.trans h4))
end
end QEC.Coding.AlgebraicGeometry

namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable (k : Type u) (A B : CommRingCat.{u}) [CommRing k]
variable [Algebra k A] [Algebra k B]
variable (q : A ⟶ B)
variable (hcoeff : (CommRingCat.ofHom (algebraMap k A) : CommRingCat.of k ⟶ A) ≫ q =
  (CommRingCat.ofHom (algebraMap k B) : CommRingCat.of k ⟶ B))
local notation "f" => Spec.map q
local notation "cA" => affineDifferentialGlobalConstantMap k A
local notation "cB" => affineDifferentialGlobalConstantMap k B
local notation "OmegaA" => schemeDifferentialSheaf (Spec A) (CommRingCat.of k) cA
local notation "OmegaB" => schemeDifferentialSheaf (Spec B) (CommRingCat.of k) cB


include hcoeff

lemma affineDifferentialRestrictionConstantMap :
    schemeRestrictionConstantMap (f) (CommRingCat.of k) cA = cB :=
  affineCoefficientRestrictionSquare (CommRingCat.of k) A B
    (CommRingCat.ofHom (algebraMap k A)) (CommRingCat.ofHom (algebraMap k B)) q hcoeff


variable [hopen : IsOpenImmersion (Spec.map q)]

def affineDifferentialGlobalRestriction : Γ(OmegaA, ⊤) ⟶ Γ(OmegaB, ⊤) :=
  schemeDifferentialGlobalRestrictionTo (f) (CommRingCat.of k) cA cB
    (affineDifferentialRestrictionConstantMap k A B q hcoeff)


lemma affineDifferentialGlobalRestriction_smul (a : A) (s : Γ(OmegaA, ⊤)) :
    affineDifferentialGlobalRestriction k A B q hcoeff (a • s) =
      q a • affineDifferentialGlobalRestriction k A B q hcoeff s := by
  have ha : a • s = (Scheme.ΓSpecIso A).inv a • s := by
    rw [Scheme.Modules.smul_Spec_def]
    simp only [show (⊤ : (Spec A).Opens).leTop = 𝟙 _ from rfl,
      op_id]
    exact congrArg (fun t : Γ(Spec A, ⊤) ⟶ Γ(Spec A, ⊤) =>
      t ((Scheme.ΓSpecIso A).inv a) • s) ((Spec A).presheaf.map_id _)
  have hb : q a • affineDifferentialGlobalRestriction k A B q hcoeff s =
      (Scheme.ΓSpecIso B).inv (q a) •
        affineDifferentialGlobalRestriction k A B q hcoeff s := by
    rw [Scheme.Modules.smul_Spec_def]
    simp only [show (⊤ : (Spec B).Opens).leTop = 𝟙 _ from rfl,
      op_id]
    exact congrArg (fun t : Γ(Spec B, ⊤) ⟶ Γ(Spec B, ⊤) =>
      t ((Scheme.ΓSpecIso B).inv (q a)) • affineDifferentialGlobalRestriction k A B q hcoeff s) ((Spec B).presheaf.map_id _)
  have hr := (congrArg (fun t : A ⟶ Γ(Spec B, ⊤) => t a)
    (Scheme.ΓSpecIso_inv_naturality q)).symm
  rw [ha]
  exact (schemeDifferentialGlobalRestrictionTo_smul (f) (CommRingCat.of k) cA cB
    (affineDifferentialRestrictionConstantMap k A B q hcoeff)
    ((Scheme.ΓSpecIso A).inv a) s).trans
      ((congrArg (fun b : Γ(Spec B, ⊤) =>
        b • affineDifferentialGlobalRestriction k A B q hcoeff s) hr).trans hb.symm)

lemma affineDifferentialGlobalRestriction_D (a : A) :
    affineDifferentialGlobalRestriction k A B q hcoeff
      ((schemeDifferentialSheafDerivation (Spec A) (CommRingCat.of k) cA).d
        (X := op ⊤) ((Scheme.ΓSpecIso A).inv a)) =
    (schemeDifferentialSheafDerivation (Spec B) (CommRingCat.of k) cB).d
      (X := op ⊤) ((Scheme.ΓSpecIso B).inv (q a)) := by
  have h1 := schemeDifferentialGlobalRestrictionTo_D (f) (CommRingCat.of k) cA cB
    (affineDifferentialRestrictionConstantMap k A B q hcoeff) ((Scheme.ΓSpecIso A).inv a)
  have hr := (congrArg (fun t : A ⟶ Γ(Spec B, ⊤) => t a)
    (Scheme.ΓSpecIso_inv_naturality q)).symm
  have h2 := congrArg (fun b : Γ(Spec B, ⊤) =>
    (schemeDifferentialSheafDerivation (Spec B) (CommRingCat.of k) cB).d (X := op ⊤) b) hr
  exact h1.trans h2

def affineDifferentialGlobalRestrictionKaehler :
    KaehlerDifferential k A →+ KaehlerDifferential k B :=
  (affineDifferentialGlobalSectionsEquiv k B).toAddEquiv.toAddMonoidHom.comp
    ((affineDifferentialGlobalRestriction k A B q hcoeff).hom.comp
      (affineDifferentialGlobalSectionsEquiv k A).symm.toAddEquiv.toAddMonoidHom)


lemma affineDifferentialGlobalRestrictionKaehler_D (a : A) :
    affineDifferentialGlobalRestrictionKaehler k A B q hcoeff (KaehlerDifferential.D k A a) =
      KaehlerDifferential.D k B (q a) := by
  have h : (affineDifferentialGlobalSectionsEquiv k A).symm (KaehlerDifferential.D k A a) =
      (schemeDifferentialSheafDerivation (Spec A) (CommRingCat.of k) cA).d
        ((Scheme.ΓSpecIso A).inv a) :=
    (affineDifferentialGlobalSectionsEquiv k A).symm_apply_eq.mpr
      (affineDifferentialGlobalSectionsEquiv_D k A a).symm
  change affineDifferentialGlobalSectionsEquiv k B
    (affineDifferentialGlobalRestriction k A B q hcoeff
      ((affineDifferentialGlobalSectionsEquiv k A).symm (KaehlerDifferential.D k A a))) = _
  have h1 := congrArg (fun z : Γ(OmegaA, ⊤) =>
    affineDifferentialGlobalSectionsEquiv k B (affineDifferentialGlobalRestriction k A B q hcoeff z)) h
  have h2 := congrArg (fun z : Γ(OmegaB, ⊤) => affineDifferentialGlobalSectionsEquiv k B z)
    (affineDifferentialGlobalRestriction_D k A B q hcoeff a)
  exact h1.trans (h2.trans (affineDifferentialGlobalSectionsEquiv_D k B (q a)))
lemma affineDifferentialGlobalRestrictionKaehler_smul
    (a : A) (s : KaehlerDifferential k A) :
    affineDifferentialGlobalRestrictionKaehler k A B q hcoeff (a • s) =
      q a • affineDifferentialGlobalRestrictionKaehler k A B q hcoeff s := by
  change affineDifferentialGlobalSectionsEquiv k B
    (affineDifferentialGlobalRestriction k A B q hcoeff
      ((affineDifferentialGlobalSectionsEquiv k A).symm (a • s))) = _
  rw [LinearEquiv.map_smul]
  have h := affineDifferentialGlobalRestriction_smul k A B q hcoeff a
    ((affineDifferentialGlobalSectionsEquiv k A).symm s)
  exact (congrArg (affineDifferentialGlobalSectionsEquiv k B) h).trans
    ((affineDifferentialGlobalSectionsEquiv k B).map_smul (q a) _)

end
end QEC.Coding.AlgebraicGeometry

namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable (k : Type u) (A B : CommRingCat.{u}) [CommRing k]
variable [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
variable (q : A ⟶ B)
variable (hcoeff : (CommRingCat.ofHom (algebraMap k A) : CommRingCat.of k ⟶ A) ≫ q =
  (CommRingCat.ofHom (algebraMap k B) : CommRingCat.of k ⟶ B))
variable [IsOpenImmersion (Spec.map q)]
variable (hq : ∀ a : A, q a = algebraMap A B a)

def affineDifferentialGlobalRestrictionKaehlerLinear :
    KaehlerDifferential k A →ₗ[A] KaehlerDifferential k B where
  __ := affineDifferentialGlobalRestrictionKaehler k A B q hcoeff
  map_smul' a s :=
    (affineDifferentialGlobalRestrictionKaehler_smul k A B q hcoeff a s).trans
      ((congrArg (fun b : B => b • affineDifferentialGlobalRestrictionKaehler k A B q hcoeff s)
        (hq a)).trans (IsScalarTower.algebraMap_smul B a _))

lemma affineDifferentialGlobalRestrictionKaehlerLinear_eq :
    affineDifferentialGlobalRestrictionKaehlerLinear k A B q hcoeff hq =
      KaehlerDifferential.map k k A B := by
  apply LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation k A)
  intro a
  change affineDifferentialGlobalRestrictionKaehler k A B q hcoeff (KaehlerDifferential.D k A a) =
    KaehlerDifferential.map k k A B (KaehlerDifferential.D k A a)
  exact (affineDifferentialGlobalRestrictionKaehler_D k A B q hcoeff a).trans
    ((congrArg (KaehlerDifferential.D k B) (hq a)).trans (KaehlerDifferential.map_D k k A B a).symm)

include hq in
lemma affineDifferentialGlobalRestrictionKaehler_eq_map (s : KaehlerDifferential k A) :
    affineDifferentialGlobalRestrictionKaehler k A B q hcoeff s =
      KaehlerDifferential.map k k A B s :=
  LinearMap.congr_fun
    (affineDifferentialGlobalRestrictionKaehlerLinear_eq k A B q hcoeff hq) s
end
end QEC.Coding.AlgebraicGeometry

namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable (k : Type u) (A B : CommRingCat.{u}) [CommRing k]
variable [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
variable (q : A ⟶ B)
variable (hcoeff : (CommRingCat.ofHom (algebraMap k A) : CommRingCat.of k ⟶ A) ≫ q =
  (CommRingCat.ofHom (algebraMap k B) : CommRingCat.of k ⟶ B))
variable [IsOpenImmersion (Spec.map q)]
variable (hq : ∀ a : A, q a = algebraMap A B a)
variable {X : Scheme.{u}} (f : Spec A ⟶ X) [IsOpenImmersion f]
variable (c : CommRingCat.of k ⟶ Γ(X, ⊤))
variable (hf : schemeRestrictionConstantMap f (CommRingCat.of k) c =
  affineDifferentialGlobalConstantMap k A)
local notation "OmegaX" => schemeDifferentialSheaf X (CommRingCat.of k) c
local notation "OmegaA" => schemeDifferentialSheaf (Spec A) (CommRingCat.of k)
  (affineDifferentialGlobalConstantMap k A)
local notation "OmegaB" => schemeDifferentialSheaf (Spec B) (CommRingCat.of k)
  (affineDifferentialGlobalConstantMap k B)

def affineDifferentialChartImageKaehlerIso :
    AddCommGrpCat.of (KaehlerDifferential k A) ≅ Γ(OmegaX, f ''ᵁ ⊤) :=
  (affineDifferentialGlobalSectionsEquiv k A).symm.toAddEquiv.toAddCommGrpIso ≪≫
    schemeDifferentialRestrictionImageSectionIsoTo f (CommRingCat.of k) c
      (affineDifferentialGlobalConstantMap k A) hf ⊤

include hq in
lemma affineDifferentialGlobalRestriction_inverseEquiv (s : KaehlerDifferential k A) :
    affineDifferentialGlobalRestriction k A B q hcoeff
      ((affineDifferentialGlobalSectionsEquiv k A).symm s) =
    (affineDifferentialGlobalSectionsEquiv k B).symm
      (KaehlerDifferential.map k k A B s) := by
  apply (affineDifferentialGlobalSectionsEquiv k B).injective
  exact (affineDifferentialGlobalRestrictionKaehler_eq_map k A B q hcoeff hq s).trans
    ((affineDifferentialGlobalSectionsEquiv k B).apply_symm_apply _).symm

include hq in
lemma affineDifferentialChartImageKaehlerIso_restrict (s : KaehlerDifferential k A) :
    (OmegaX).presheaf.map (eqToHom (Scheme.Hom.comp_image (Spec.map q) f ⊤)).op
      ((OmegaX).presheaf.map
        (f.opensFunctor.map (homOfLE le_top : Spec.map q ''ᵁ ⊤ ⟶ ⊤)).op
          ((affineDifferentialChartImageKaehlerIso k A f c hf).hom s)) =
    (schemeDifferentialRestrictionImageSectionIsoTo (Spec.map q ≫ f) (CommRingCat.of k) c
      (affineDifferentialGlobalConstantMap k B)
      (schemeRestrictionConstantMap_comp_to f (Spec.map q) (CommRingCat.of k) c
        (affineDifferentialGlobalConstantMap k A) (affineDifferentialGlobalConstantMap k B)
        hf (affineDifferentialRestrictionConstantMap k A B q hcoeff)) ⊤).hom
          ((affineDifferentialGlobalSectionsEquiv k B).symm
            (KaehlerDifferential.map k k A B s)) := by
  have hn := (schemeDifferentialRestrictionImageSectionIsoTo_globalRestriction
    f (Spec.map q) (CommRingCat.of k) c
      (affineDifferentialGlobalConstantMap k A) (affineDifferentialGlobalConstantMap k B)
      hf (affineDifferentialRestrictionConstantMap k A B q hcoeff)
      ((affineDifferentialGlobalSectionsEquiv k A).symm s)).symm
  exact hn.trans (congrArg (fun z : Γ(OmegaB, ⊤) =>
    (schemeDifferentialRestrictionImageSectionIsoTo (Spec.map q ≫ f) (CommRingCat.of k) c
      (affineDifferentialGlobalConstantMap k B)
      (schemeRestrictionConstantMap_comp_to f (Spec.map q) (CommRingCat.of k) c
        (affineDifferentialGlobalConstantMap k A) (affineDifferentialGlobalConstantMap k B)
        hf (affineDifferentialRestrictionConstantMap k A B q hcoeff)) ⊤).hom z)
    (affineDifferentialGlobalRestriction_inverseEquiv k A B q hcoeff hq s))
end
end QEC.Coding.AlgebraicGeometry

namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u

lemma schemeDifferentialImageSectionIsoTo_inv_global
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (k : CommRingCat.{u}) (c : k ⟶ Γ(X, ⊤)) (d : k ⟶ Γ(Y, ⊤))
    (h : schemeRestrictionConstantMap f k c = d)
    (s : Γ(schemeDifferentialSheaf X k c, ⊤)) :
    (schemeDifferentialRestrictionImageSectionIsoTo f k c d h ⊤).inv
      ((schemeDifferentialSheaf X k c).presheaf.map
        (homOfLE le_top : f ''ᵁ ⊤ ⟶ ⊤).op s) =
    schemeDifferentialGlobalRestrictionTo f k c d h s := by
  subst d
  rfl

lemma schemeModuleSpecTop_smul (A : CommRingCat.{u}) (M : (Spec A).Modules)
    (a : A) (s : Γ(M, ⊤)) : a • s = (Scheme.ΓSpecIso A).inv a • s := by
  rw [Scheme.Modules.smul_Spec_def]
  simp only [show (⊤ : (Spec A).Opens).leTop = 𝟙 _ from rfl, op_id]
  exact congrArg (fun t : Γ(Spec A, ⊤) ⟶ Γ(Spec A, ⊤) => t ((Scheme.ΓSpecIso A).inv a) • s)
    ((Spec A).presheaf.map_id _)

variable (k : Type u) [CommRing k] (X : Scheme.{u})
variable (c : CommRingCat.of k ⟶ Γ(X, ⊤))
local notation "OmegaX" => schemeDifferentialSheaf X (CommRingCat.of k) c

local instance schemeDifferentialGlobalConstantModule : Module k Γ(OmegaX, ⊤) :=
  Module.compHom Γ(OmegaX, ⊤) c.hom

variable (A : CommRingCat.{u}) [Algebra k A] (f : Spec A ⟶ X) [IsOpenImmersion f]
variable (hf : schemeRestrictionConstantMap f (CommRingCat.of k) c =
  affineDifferentialGlobalConstantMap k A)
local notation "OmegaA" => schemeDifferentialSheaf (Spec A) (CommRingCat.of k)
  (affineDifferentialGlobalConstantMap k A)
local notation "psi" => schemeDifferentialGlobalRestrictionTo f (CommRingCat.of k) c
  (affineDifferentialGlobalConstantMap k A) hf

def affineDifferentialGlobalRestrictionToKaehler : Γ(OmegaX, ⊤) →+ KaehlerDifferential k A :=
  (affineDifferentialGlobalSectionsEquiv k A).toAddEquiv.toAddMonoidHom.comp (psi).hom

lemma affineDifferentialGlobalRestrictionToKaehler_smul (r : k) (s : Γ(OmegaX, ⊤)) :
    affineDifferentialGlobalRestrictionToKaehler k X c A f hf (r • s) =
      r • affineDifferentialGlobalRestrictionToKaehler k X c A f hf s := by
  change (affineDifferentialGlobalSectionsEquiv k A) ((psi) (c r • s)) =
    r • (affineDifferentialGlobalSectionsEquiv k A) ((psi) s)
  have hp := schemeDifferentialGlobalRestrictionTo_smul f (CommRingCat.of k) c
    (affineDifferentialGlobalConstantMap k A) hf (c r) s
  have hc : f.appTop (c r) = (Scheme.ΓSpecIso A).inv (algebraMap k A r) :=
    congrArg (fun t : CommRingCat.of k ⟶ Γ(Spec A, ⊤) => t r) hf
  have h1 := congrArg (affineDifferentialGlobalSectionsEquiv k A) hp
  have h2 := congrArg (fun b : Γ(Spec A, ⊤) =>
    (affineDifferentialGlobalSectionsEquiv k A) (b • (psi) s)) hc
  have h3 := congrArg (affineDifferentialGlobalSectionsEquiv k A)
    (schemeModuleSpecTop_smul A OmegaA (algebraMap k A r) ((psi) s)).symm
  have h4 := (affineDifferentialGlobalSectionsEquiv k A).map_smul (algebraMap k A r) ((psi) s)
  have h5 := IsScalarTower.algebraMap_smul A r
    ((affineDifferentialGlobalSectionsEquiv k A) ((psi) s))
  exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

lemma affineDifferentialChartImageKaehlerIso_inv_global (s : Γ(OmegaX, ⊤)) :
    (affineDifferentialChartImageKaehlerIso k A f c hf).inv
      ((OmegaX).presheaf.map (homOfLE le_top : f ''ᵁ ⊤ ⟶ ⊤).op s) =
    affineDifferentialGlobalRestrictionToKaehler k X c A f hf s := by
  change (affineDifferentialGlobalSectionsEquiv k A)
    ((schemeDifferentialRestrictionImageSectionIsoTo f (CommRingCat.of k) c
      (affineDifferentialGlobalConstantMap k A) hf ⊤).inv
        ((OmegaX).presheaf.map (homOfLE le_top : f ''ᵁ ⊤ ⟶ ⊤).op s)) =
    (affineDifferentialGlobalSectionsEquiv k A) ((psi) s)
  exact congrArg (affineDifferentialGlobalSectionsEquiv k A)
    (schemeDifferentialImageSectionIsoTo_inv_global f (CommRingCat.of k) c
      (affineDifferentialGlobalConstantMap k A) hf s)
end
end QEC.Coding.AlgebraicGeometry
