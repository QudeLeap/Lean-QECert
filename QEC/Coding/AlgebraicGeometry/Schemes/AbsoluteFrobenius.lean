import QEC.Coding.AlgebraicGeometry.Schemes.PrimeAlgebraFrobenius
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Geometry.RingedSpace.Stalks

/-!
# Absolute Frobenius over a prime field

The structure morphism supplies every open section ring with its actual
prime-field map, including the trivial ring of the empty open. P-power
components commute with restrictions. Genuine germs compute the induced
stalk map, and positive powers reflect units, yielding a scheme morphism.
For a locally finite-type structure morphism the constructed Frobenius is
finite. The morphism is natural and preserves the prime-field structure.
No Frobenius, locality, finiteness or inverse is supplied by the caller.
-/

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace QEC.Coding.AlgebraicGeometry.SchemeFrobenius
noncomputable section
open QEC.Coding.AlgebraicGeometry.PrimeFrobenius
variable (p : ℕ) [Fact p.Prime] (X : Scheme) (f : X ⟶ Spec (.of (ZMod p)))

def sectionBase (U : X.Opens) : ZMod p →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (.of (ZMod p))).inv ≫ f.appTop ≫
    X.presheaf.map (homOfLE le_top).op).hom

def sectionPower (U : X.Opens) : Γ(X, U) →+* Γ(X, U) :=
  letI : Algebra (ZMod p) Γ(X, U) := (sectionBase p X f U).toAlgebra
  primeAlgebraFrobenius p Γ(X, U)

lemma sectionPower_apply (U : X.Opens) (s : Γ(X, U)) :
    sectionPower p X f U s = s^p := rfl

abbrev powerPresheafHom : X.toPresheafedSpace ⟶ X.toPresheafedSpace where
  base := 𝟙 X.toTopCat
  c := {
    app := fun U => CommRingCat.ofHom (sectionPower p X f U.unop)
    naturality := by
      intro U V i
      ext s
      change (X.presheaf.map i s)^p = X.presheaf.map i (s^p)
      exact ((X.presheaf.map i).hom.map_pow s p).symm
  }

lemma powerPresheafHom_stalk_apply (x : X) (s : X.presheaf.stalk x) :
    (powerPresheafHom p X f).stalkMap x s = s^p := by
  obtain ⟨U, hx, a, rfl⟩ := X.presheaf.exists_germ_eq s
  have hg := PresheafedSpace.stalkMap_germ_apply (powerPresheafHom p X f) U x hx a
  change (powerPresheafHom p X f).stalkMap x (X.presheaf.germ U x hx a) =
    X.presheaf.germ U x hx (a^p) at hg
  exact hg.trans ((X.presheaf.germ U x hx).hom.map_pow a p)

def absoluteFrobenius : X ⟶ X := Scheme.Hom.mk {
  toHom := powerPresheafHom p X f
  prop := by
    intro x
    constructor
    intro a ha
    have hpow := powerPresheafHom_stalk_apply p X f x a
    change ((powerPresheafHom p X f).stalkMap x).hom a = a^p at hpow
    rw [hpow] at ha
    exact (isUnit_pow_iff (Fact.out : p.Prime).ne_zero).mp ha
}

lemma absoluteFrobenius_apply (x : X) : absoluteFrobenius p X f x = x := rfl

lemma absoluteFrobenius_app_apply (U : X.Opens) (s : Γ(X, U)) :
    (absoluteFrobenius p X f).app U s = s^p := sectionPower_apply p X f U s

lemma absoluteFrobenius_stalk_apply (x : X) (s : X.presheaf.stalk x) :
    (absoluteFrobenius p X f).toLRSHom.stalkMap x s = s^p :=
  powerPresheafHom_stalk_apply p X f x s


lemma absoluteFrobenius_natural {Y : Scheme} (g : X ⟶ Y)
    (h : Y ⟶ Spec (.of (ZMod p))) :
    absoluteFrobenius p X f ≫ g = g ≫ absoluteFrobenius p Y h := by
  have hb : (absoluteFrobenius p X f ≫ g).base = (g ≫ absoluteFrobenius p Y h).base := by
    exact (Category.id_comp g.base).trans (Category.comp_id g.base).symm
  apply Scheme.Hom.ext hb
  intro U
  have hi : (eqToHom (congrArg (fun b => (Opens.map b).obj U) hb.symm)).op =
      𝟙 (op (g ⁻¹ᵁ U)) := Subsingleton.elim _ _
  have hm : X.presheaf.map (eqToHom (congrArg (fun b => (Opens.map b).obj U) hb.symm)).op =
      𝟙 Γ(X, g ⁻¹ᵁ U) :=
    (congrArg (fun i => X.presheaf.map i) hi).trans (X.presheaf.map_id (op (g ⁻¹ᵁ U)))
  have hp2 : g.app U ≫ (absoluteFrobenius p X f).app (g ⁻¹ᵁ U) =
      (absoluteFrobenius p Y h).app U ≫ g.app U := by
    ext s
    change (g.app U s)^p = g.app U (s^p)
    exact ((g.app U).hom.map_pow s p).symm
  have hp : (absoluteFrobenius p X f ≫ g).app U = (g ≫ absoluteFrobenius p Y h).app U :=
    (Scheme.Hom.comp_app (absoluteFrobenius p X f) g U).trans
      (hp2.trans (Scheme.Hom.comp_app g (absoluteFrobenius p Y h) U).symm)
  exact (congrArg (fun r => (absoluteFrobenius p X f ≫ g).app U ≫ r) hm).trans
    ((Category.comp_id _).trans hp)

lemma absoluteFrobenius_primeSpec_id :
    absoluteFrobenius p (Spec (.of (ZMod p))) (𝟙 _) = 𝟙 _ := by
  apply ext_of_isAffine
  ext s
  change s^p = s
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (ZMod p))).hom).injective
  exact ((Scheme.ΓSpecIso (.of (ZMod p))).hom.hom.map_pow s p).trans (ZMod.pow_card _)

lemma absoluteFrobenius_overPrimeField : absoluteFrobenius p X f ≫ f = f :=
  (absoluteFrobenius_natural p X f f (𝟙 _)).trans
    ((congrArg (fun r => f ≫ r) (absoluteFrobenius_primeSpec_id p)).trans (Category.comp_id f))

lemma sectionBase_finiteType [LocallyOfFiniteType f]
    (U : X.Opens) (hU : IsAffineOpen U) : (sectionBase p X f U).FiniteType := by
  have hbase := f.finiteType_appLE (isAffineOpen_top _) hU (show U ≤ f ⁻¹ᵁ ⊤ from le_top)
  have hiso : (Scheme.ΓSpecIso (.of (ZMod p))).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (ZMod p))).inv).surjective
  exact hbase.comp hiso

lemma absoluteFrobenius_finite [LocallyOfFiniteType f] :
    IsFinite (absoluteFrobenius p X f) := by
  refine { isAffine_preimage := ?_, finite_app := ?_ }
  · intro U hU
    exact hU
  · intro U hU
    let : Algebra (ZMod p) Γ(X, U) := (sectionBase p X f U).toAlgebra
    let : Algebra.FiniteType (ZMod p) Γ(X, U) := sectionBase_finiteType p X f U hU
    exact primeAlgebraFrobenius_finite p Γ(X, U)

end
end QEC.Coding.AlgebraicGeometry.SchemeFrobenius
