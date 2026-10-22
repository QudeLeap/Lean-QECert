import QEC.Coding.AlgebraicGeometry.Differentials.AffineRestriction
import QEC.Coding.AlgebraicGeometry.Differentials.ModulePairDescent

/-!
# Genuine two-affine-chart differential descent

Actual coefficient and overlap diagrams turn equality of Kähler restrictions
into equality of sections on the real image intersection. The sheaf condition
then constructs a unique global differential. Conversely, global sections
force equality of the same actual Kähler restrictions.
-/
namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable (k : Type u) (A C B : CommRingCat.{u}) [CommRing k]
variable [Algebra k A] [Algebra k C] [Algebra k B]
variable [Algebra A B] [Algebra C B] [IsScalarTower k A B] [IsScalarTower k C B]
variable (q : A ⟶ B) (r : C ⟶ B)
variable (hq : ∀ a : A, q a = algebraMap A B a)
variable (hr : ∀ a : C, r a = algebraMap C B a)
variable (hqa : (CommRingCat.ofHom (algebraMap k A) : CommRingCat.of k ⟶ A) ≫ q =
  CommRingCat.ofHom (algebraMap k B))
variable (hra : (CommRingCat.ofHom (algebraMap k C) : CommRingCat.of k ⟶ C) ≫ r =
  CommRingCat.ofHom (algebraMap k B))
variable {X : Scheme.{u}} (f : Spec A ⟶ X) (g : Spec C ⟶ X)
variable [IsOpenImmersion (Spec.map q)] [IsOpenImmersion (Spec.map r)]
variable [IsOpenImmersion f] [IsOpenImmersion g]
variable (c : CommRingCat.of k ⟶ Γ(X, ⊤))
variable (hf : schemeRestrictionConstantMap f (CommRingCat.of k) c =
  affineDifferentialGlobalConstantMap k A)
variable (hg : schemeRestrictionConstantMap g (CommRingCat.of k) c =
  affineDifferentialGlobalConstantMap k C)
variable (he : Spec.map q ≫ f = Spec.map r ≫ g)
local notation "Omega" => schemeDifferentialSheaf X (CommRingCat.of k) c
local notation "U" => Functor.obj (Scheme.Hom.opensFunctor f) ⊤
local notation "V" => Functor.obj (Scheme.Hom.opensFunctor g) ⊤
local notation "W" => Functor.obj (Scheme.Hom.opensFunctor (Spec.map q ≫ f)) ⊤
local notation "W1" => Functor.obj (Scheme.Hom.opensFunctor (Spec.map r ≫ g)) ⊤
local notation "E0" => affineDifferentialChartImageKaehlerIso k A f c hf
local notation "E1" => affineDifferentialChartImageKaehlerIso k C g c hg
local notation "eW" => schemeOpenImmersionImage_congr
  (Spec.map q ≫ f) (Spec.map r ≫ g) he ⊤
local notation "hc0" => schemeRestrictionConstantMap_comp_to f (Spec.map q) (CommRingCat.of k) c
  (affineDifferentialGlobalConstantMap k A) (affineDifferentialGlobalConstantMap k B)
  hf (affineDifferentialRestrictionConstantMap k A B q hqa)
local notation "hc1" => schemeRestrictionConstantMap_comp_to g (Spec.map r) (CommRingCat.of k) c
  (affineDifferentialGlobalConstantMap k C) (affineDifferentialGlobalConstantMap k B)
  hg (affineDifferentialRestrictionConstantMap k C B r hra)
local notation "F0" => schemeDifferentialRestrictionImageSectionIsoTo (Spec.map q ≫ f)
  (CommRingCat.of k) c (affineDifferentialGlobalConstantMap k B) hc0 ⊤
local notation "F1" => schemeDifferentialRestrictionImageSectionIsoTo (Spec.map r ≫ g)
  (CommRingCat.of k) c (affineDifferentialGlobalConstantMap k B) hc1 ⊤
local notation "EB" => affineDifferentialGlobalSectionsEquiv k B

include hq hr hqa hra he in
lemma affineDifferentialChartPair_imageCompatibility
    (a : KaehlerDifferential k A) (b : KaehlerDifferential k C)
    (hcompat : KaehlerDifferential.map k k A B a = KaehlerDifferential.map k k C B b) :
    (Omega).presheaf.map (homOfLE (schemeNestedImage_le f (Spec.map q))).op ((E0).hom a) =
    (Omega).presheaf.map
      (homOfLE ((eW).le.trans (schemeNestedImage_le g (Spec.map r)))).op ((E1).hom b) := by
  have h0 := affineDifferentialChartImageKaehlerIso_restrict k A B q hqa hq f c hf a
  have h1 := affineDifferentialChartImageKaehlerIso_restrict k C B r hra hr g c hg b
  have hn0 : (Omega).presheaf.map (homOfLE (schemeNestedImage_le f (Spec.map q))).op
      ((E0).hom a) = (F0).hom ((EB).symm (KaehlerDifferential.map k k A B a)) :=
    (schemeModuleNestedImageRestriction f (Spec.map q) Omega ((E0).hom a)).symm.trans h0
  have hn1 : (Omega).presheaf.map (homOfLE (schemeNestedImage_le g (Spec.map r))).op
      ((E1).hom b) = (F1).hom ((EB).symm (KaehlerDifferential.map k k C B b)) :=
    (schemeModuleNestedImageRestriction g (Spec.map r) Omega ((E1).hom b)).symm.trans h1
  have hs := schemeDifferentialRestrictionImageSectionIsoTo_congr
    (Spec.map q ≫ f) (Spec.map r ≫ g) (CommRingCat.of k) c
    (affineDifferentialGlobalConstantMap k B) hc0 hc1 he ⊤
      ((EB).symm (KaehlerDifferential.map k k A B a))
  have hb := congrArg (fun z : KaehlerDifferential k B =>
    (Omega).presheaf.map (eqToHom eW).op ((F1).hom ((EB).symm z))) hcompat
  have hn1' := congrArg (fun z : Γ(Omega, W1) =>
    (Omega).presheaf.map (eqToHom eW).op z) hn1.symm
  exact hn0.trans (hs.trans (hb.trans (hn1'.trans
    (schemeModuleRestriction_cast Omega eW (schemeNestedImage_le g (Spec.map r)) ((E1).hom b)))))

include hq hr hqa hra he in
lemma affineDifferentialChartPair_compatible
    (hW : W = U ⊓ V)
    (a : KaehlerDifferential k A) (b : KaehlerDifferential k C)
    (hcompat : KaehlerDifferential.map k k A B a = KaehlerDifferential.map k k C B b) :
    (Omega).presheaf.map (TopologicalSpace.Opens.infLELeft U V).op ((E0).hom a) =
      (Omega).presheaf.map (TopologicalSpace.Opens.infLERight U V).op ((E1).hom b) := by
  have hp := affineDifferentialChartPair_imageCompatibility k A C B q r hq hr hqa hra
    f g c hf hg he a b hcompat
  have hc := congrArg (fun z : Γ(Omega, W) =>
    (Omega).presheaf.map (eqToHom hW.symm).op z) hp
  have h0 := schemeModuleRestriction_cast Omega hW.symm
    (schemeNestedImage_le f (Spec.map q)) ((E0).hom a)
  have h1 := schemeModuleRestriction_cast Omega hW.symm
    ((eW).le.trans (schemeNestedImage_le g (Spec.map r))) ((E1).hom b)
  exact h0.symm.trans (hc.trans h1)

include hq hr hqa hra he in
lemma affineDifferentialChartPair_existsUnique_global
    (hcover : U ⊔ V = ⊤) (hW : W = U ⊓ V)
    (a : KaehlerDifferential k A) (b : KaehlerDifferential k C)
    (hcompat : KaehlerDifferential.map k k A B a = KaehlerDifferential.map k k C B b) :
    ∃! z : Γ(Omega, ⊤),
      (Omega).presheaf.map (homOfLE le_top : U ⟶ ⊤).op z = (E0).hom a ∧
      (Omega).presheaf.map (homOfLE le_top : V ⟶ ⊤).op z = (E1).hom b :=
  schemeModulePair_existsUnique_global Omega U V hcover ((E0).hom a) ((E1).hom b)
    (affineDifferentialChartPair_compatible k A C B q r hq hr hqa hra f g c hf hg he hW a b hcompat)
end
end QEC.Coding.AlgebraicGeometry

namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable (k : Type u) (A C B : CommRingCat.{u}) [CommRing k]
variable [Algebra k A] [Algebra k C] [Algebra k B]
variable [Algebra A B] [Algebra C B] [IsScalarTower k A B] [IsScalarTower k C B]
variable (q : A ⟶ B) (r : C ⟶ B)
variable (hq : ∀ a : A, q a = algebraMap A B a)
variable (hr : ∀ a : C, r a = algebraMap C B a)
variable (hqa : (CommRingCat.ofHom (algebraMap k A) : CommRingCat.of k ⟶ A) ≫ q =
  CommRingCat.ofHom (algebraMap k B))
variable (hra : (CommRingCat.ofHom (algebraMap k C) : CommRingCat.of k ⟶ C) ≫ r =
  CommRingCat.ofHom (algebraMap k B))
variable {X : Scheme.{u}} (f : Spec A ⟶ X) (g : Spec C ⟶ X)
variable [IsOpenImmersion (Spec.map q)] [IsOpenImmersion (Spec.map r)]
variable [IsOpenImmersion f] [IsOpenImmersion g]
variable (c : CommRingCat.of k ⟶ Γ(X, ⊤))
variable (hf : schemeRestrictionConstantMap f (CommRingCat.of k) c =
  affineDifferentialGlobalConstantMap k A)
variable (hg : schemeRestrictionConstantMap g (CommRingCat.of k) c =
  affineDifferentialGlobalConstantMap k C)
variable (he : Spec.map q ≫ f = Spec.map r ≫ g)
local notation "Omega" => schemeDifferentialSheaf X (CommRingCat.of k) c
local notation "U" => Functor.obj (Scheme.Hom.opensFunctor f) ⊤
local notation "V" => Functor.obj (Scheme.Hom.opensFunctor g) ⊤
local notation "W" => Functor.obj (Scheme.Hom.opensFunctor (Spec.map q ≫ f)) ⊤
local notation "W1" => Functor.obj (Scheme.Hom.opensFunctor (Spec.map r ≫ g)) ⊤
local notation "E0" => affineDifferentialChartImageKaehlerIso k A f c hf
local notation "E1" => affineDifferentialChartImageKaehlerIso k C g c hg
local notation "eW" => schemeOpenImmersionImage_congr
  (Spec.map q ≫ f) (Spec.map r ≫ g) he ⊤
local notation "hc0" => schemeRestrictionConstantMap_comp_to f (Spec.map q) (CommRingCat.of k) c
  (affineDifferentialGlobalConstantMap k A) (affineDifferentialGlobalConstantMap k B)
  hf (affineDifferentialRestrictionConstantMap k A B q hqa)
local notation "hc1" => schemeRestrictionConstantMap_comp_to g (Spec.map r) (CommRingCat.of k) c
  (affineDifferentialGlobalConstantMap k C) (affineDifferentialGlobalConstantMap k B)
  hg (affineDifferentialRestrictionConstantMap k C B r hra)
local notation "F0" => schemeDifferentialRestrictionImageSectionIsoTo (Spec.map q ≫ f)
  (CommRingCat.of k) c (affineDifferentialGlobalConstantMap k B) hc0 ⊤
local notation "F1" => schemeDifferentialRestrictionImageSectionIsoTo (Spec.map r ≫ g)
  (CommRingCat.of k) c (affineDifferentialGlobalConstantMap k B) hc1 ⊤
local notation "EB" => affineDifferentialGlobalSectionsEquiv k B

include hq hr hqa hra he in
lemma affineDifferentialChartPair_of_imageCompatibility
    (a : KaehlerDifferential k A) (b : KaehlerDifferential k C)
    (hcompat : (Omega).presheaf.map
        (homOfLE (schemeNestedImage_le f (Spec.map q))).op ((E0).hom a) =
      (Omega).presheaf.map
        (homOfLE ((eW).le.trans (schemeNestedImage_le g (Spec.map r)))).op ((E1).hom b)) :
    KaehlerDifferential.map k k A B a = KaehlerDifferential.map k k C B b := by
  have h0 := affineDifferentialChartImageKaehlerIso_restrict k A B q hqa hq f c hf a
  have h1 := affineDifferentialChartImageKaehlerIso_restrict k C B r hra hr g c hg b
  have hn0 : (Omega).presheaf.map (homOfLE (schemeNestedImage_le f (Spec.map q))).op
      ((E0).hom a) = (F0).hom ((EB).symm (KaehlerDifferential.map k k A B a)) :=
    (schemeModuleNestedImageRestriction f (Spec.map q) Omega ((E0).hom a)).symm.trans h0
  have hn1 : (Omega).presheaf.map (homOfLE (schemeNestedImage_le g (Spec.map r))).op
      ((E1).hom b) = (F1).hom ((EB).symm (KaehlerDifferential.map k k C B b)) :=
    (schemeModuleNestedImageRestriction g (Spec.map r) Omega ((E1).hom b)).symm.trans h1
  have hs := schemeDifferentialRestrictionImageSectionIsoTo_congr
    (Spec.map q ≫ f) (Spec.map r ≫ g) (CommRingCat.of k) c
    (affineDifferentialGlobalConstantMap k B) hc0 hc1 he ⊤
      ((EB).symm (KaehlerDifferential.map k k C B b))
  have hcast := schemeModuleRestriction_cast Omega eW
    (schemeNestedImage_le g (Spec.map r)) ((E1).hom b)
  have hn1' := congrArg (fun z : Γ(Omega, W1) =>
    (Omega).presheaf.map (eqToHom eW).op z) hn1
  have hE : (F0).hom ((EB).symm (KaehlerDifferential.map k k A B a)) =
      (F0).hom ((EB).symm (KaehlerDifferential.map k k C B b)) :=
    hn0.symm.trans (hcompat.trans (hcast.symm.trans (hn1'.trans hs.symm)))
  exact (EB).symm.injective (additiveSectionIso_hom_injective F0 hE)

include hq hr hqa hra he in
lemma affineDifferentialChartPair_globalCompatibility
    (z : Γ(Omega, ⊤)) (a : KaehlerDifferential k A) (b : KaehlerDifferential k C)
    (ha : (Omega).presheaf.map (homOfLE le_top : U ⟶ ⊤).op z = (E0).hom a)
    (hb : (Omega).presheaf.map (homOfLE le_top : V ⟶ ⊤).op z = (E1).hom b) :
    KaehlerDifferential.map k k A B a = KaehlerDifferential.map k k C B b := by
  apply affineDifferentialChartPair_of_imageCompatibility k A C B q r hq hr hqa hra
    f g c hf hg he a b
  have h0 : (Omega).presheaf.map
        (homOfLE (schemeNestedImage_le f (Spec.map q))).op ((E0).hom a) =
      (Omega).presheaf.map (homOfLE le_top : W ⟶ ⊤).op z := by
    have hr := congrArg (fun t : Γ(Omega, U) =>
      (Omega).presheaf.map (homOfLE (schemeNestedImage_le f (Spec.map q))).op t) ha.symm
    refine hr.trans ?_
    rw [← ConcreteCategory.comp_apply, ← (Omega).presheaf.map_comp]
    rfl
  have h1 : (Omega).presheaf.map
        (homOfLE ((eW).le.trans (schemeNestedImage_le g (Spec.map r)))).op ((E1).hom b) =
      (Omega).presheaf.map (homOfLE le_top : W ⟶ ⊤).op z := by
    have hr := congrArg (fun t : Γ(Omega, V) =>
      (Omega).presheaf.map
        (homOfLE ((eW).le.trans (schemeNestedImage_le g (Spec.map r)))).op t) hb.symm
    refine hr.trans ?_
    rw [← ConcreteCategory.comp_apply, ← (Omega).presheaf.map_comp]
    rfl
  exact h0.trans h1.symm
end
end QEC.Coding.AlgebraicGeometry
