import Mathlib.AlgebraicGeometry.Spec
import Mathlib.AlgebraicGeometry.Scheme

/-!
# Structural scalars in scheme stalks

The actual structural morphism to Spec R supplies scalar germs. Prove naturality
through scheme maps, affine-chart evaluation and compatibility with genuine
dependent stalk transport. No scalar algebra is transported from a desired target.
-/

namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
noncomputable section

/-- Scalar germ supplied by the actual structural morphism to Spec R. -/
def schemeStalkScalar (R : CommRingCat) (X : Scheme)
    (f : X ⟶ Spec R) (x : X) : R →+* X.presheaf.stalk x :=
  (f.stalkMap x).hom.comp (StructureSheaf.toStalk R (f x)).hom

/-- Pullback of scalar germs through an actual scheme morphism. -/
lemma schemeStalkScalar_comp (R : CommRingCat) (X Y : Scheme)
    (g : X ⟶ Y) (f : Y ⟶ Spec R) (x : X) (r : R) :
    (g.stalkMap x) (schemeStalkScalar R Y f (g x) r) =
      schemeStalkScalar R X (g ≫ f) x r := by
  unfold schemeStalkScalar
  rw [Scheme.Hom.stalkMap_comp]
  rfl

/-- On an actual affine chart the structural scalar germ is the literal scalar's stalk image. -/
lemma schemeStalkScalar_SpecMap (R S : CommRingCat) (f : R ⟶ S)
    (x : PrimeSpectrum S) (r : R) :
    schemeStalkScalar R (Spec S) (Spec.map f) x r =
      (StructureSheaf.toStalk S x) (f r) := by
  exact stalkMap_toStalk_apply f x r

/-- Structural scalar naturality evaluated on a genuine affine chart. -/
lemma schemeStalkScalar_chart (R S : CommRingCat) (Y : Scheme)
    (g : Spec S ⟶ Y) (f : Y ⟶ Spec R) (u : R ⟶ S)
    (h : g ≫ f = Spec.map u) (x : PrimeSpectrum S) (r : R) :
    (g.stalkMap x) (schemeStalkScalar R Y f (g x) r) =
      StructureSheaf.toStalk S x (u r) := by
  exact (schemeStalkScalar_comp R (Spec S) Y g f x r).trans
    ((congrArg (fun m => schemeStalkScalar R (Spec S) m x r) h).trans
      (schemeStalkScalar_SpecMap R S u x r))

/-- Genuine index transport does not change the scalar evaluated by a ring equivalence. -/
lemma scalarRingEquiv_transport (R B : CommRingCat) (T : Type*) (A : T → CommRingCat)
    (s : ∀ t, R →+* A t) {t t' : T} (h : t = t') (e : A t' ≃+* B) (r : R) :
    (Eq.mpr (congrArg (fun z => A z ≃+* B) h) e) (s t r) = e (s t' r) := by
  cases h
  rfl

end
end QEC.Coding.AlgebraicGeometry
