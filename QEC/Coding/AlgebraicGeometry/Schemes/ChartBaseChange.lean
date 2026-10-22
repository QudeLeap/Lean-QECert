import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Scalar extension of a chart intersection

A genuine chart-intersection pullback stays a pullback after base change:
`Over.pullback` is a right adjoint and `Over.forget` preserves connected limits.
The scalar-first maps have both canonical projections. No preservation of
arbitrary colimits is asserted.
-/

namespace QEC.Coding.AlgebraicGeometry.ChartBaseChange
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe v u
variable {C : Type u} [Category.{v} C]
variable {P U V X Z T : C}
variable (a : P ⟶ U) (b : P ⟶ V) (i : U ⟶ X) (j : V ⟶ X)
variable (x : X ⟶ Z) (t : T ⟶ Z)

def firstOverlapOver : Over.mk (a ≫ i ≫ x) ⟶ Over.mk (i ≫ x) :=
  Over.homMk a rfl

def secondOverlapOver (h : IsPullback a b i j) :
    Over.mk (a ≫ i ≫ x) ⟶ Over.mk (j ≫ x) :=
  Over.homMk b (by
    change b ≫ (j ≫ x) = a ≫ i ≫ x
    simpa only [Category.assoc] using congrArg (fun k => k ≫ x) h.w.symm)

def leftChartOver : Over.mk (i ≫ x) ⟶ Over.mk x := Over.homMk i rfl

def rightChartOver : Over.mk (j ≫ x) ⟶ Over.mk x := Over.homMk j rfl

lemma intersectionOver (h : IsPullback a b i j) :
    IsPullback (firstOverlapOver a i x) (secondOverlapOver a b i j x h)
      (leftChartOver i x) (rightChartOver j x) := by
  apply IsPullback.of_map (Over.forget Z)
  · ext
    exact h.w
  · exact h

variable [HasPullbacks C]

lemma intersectionBaseChangedOver (h : IsPullback a b i j) :
    IsPullback ((Over.pullback t).map (firstOverlapOver a i x))
      ((Over.pullback t).map (secondOverlapOver a b i j x h))
      ((Over.pullback t).map (leftChartOver i x))
      ((Over.pullback t).map (rightChartOver j x)) :=
  (intersectionOver a b i j x h).map (Over.pullback t)

lemma intersectionBaseChanged (h : IsPullback a b i j) :
    IsPullback (((Over.pullback t).map (firstOverlapOver a i x)).left)
      (((Over.pullback t).map (secondOverlapOver a b i j x h)).left)
      (((Over.pullback t).map (leftChartOver i x)).left)
      (((Over.pullback t).map (rightChartOver j x)).left) :=
  (intersectionBaseChangedOver a b i j x t h).map (Over.forget T)

/-- Base change with the new scalar scheme as the first pullback factor. -/
def scalarFirstBaseChangedMap {A B : C} (f : A ⟶ Z) (g : B ⟶ Z)
    (u : A ⟶ B) (hu : u ≫ g = f) : pullback t f ⟶ pullback t g :=
  (pullbackSymmetry t f).hom ≫
    ((Over.pullback t).map (Over.homMk u hu : Over.mk f ⟶ Over.mk g)).left ≫ (pullbackSymmetry t g).inv

lemma scalarFirstBaseChangedMap_scalarProjection {A B : C}
    (f : A ⟶ Z) (g : B ⟶ Z) (u : A ⟶ B) (hu : u ≫ g = f) :
    scalarFirstBaseChangedMap t f g u hu ≫ pullback.fst t g = pullback.fst t f := by
  simp only [scalarFirstBaseChangedMap, Category.assoc, pullbackSymmetry_inv_comp_fst,
    Over.pullback_map_left, Over.mk_hom, Over.homMk_left, pullback.lift_snd, pullbackSymmetry_hom_comp_snd]

lemma scalarFirstBaseChangedMap_chartProjection {A B : C}
    (f : A ⟶ Z) (g : B ⟶ Z) (u : A ⟶ B) (hu : u ≫ g = f) :
    scalarFirstBaseChangedMap t f g u hu ≫ pullback.snd t g = pullback.snd t f ≫ u := by
  simp only [scalarFirstBaseChangedMap, Category.assoc, pullbackSymmetry_inv_comp_snd,
    Over.pullback_map_left, Over.mk_hom, pullback.lift_fst, pullbackSymmetry_hom_comp_fst_assoc,
    Over.homMk_left]

lemma intersectionBaseChangedScalarFirst (h : IsPullback a b i j) :
    IsPullback
      (scalarFirstBaseChangedMap t (a ≫ i ≫ x) (i ≫ x) a rfl)
      (scalarFirstBaseChangedMap t (a ≫ i ≫ x) (j ≫ x) b
        (by simpa only [Category.assoc] using congrArg (fun k => k ≫ x) h.w.symm))
      (scalarFirstBaseChangedMap t (i ≫ x) x i rfl)
      (scalarFirstBaseChangedMap t (j ≫ x) x j rfl) := by
  apply (intersectionBaseChanged a b i j x t h).of_iso'
    (pullbackSymmetry t (a ≫ i ≫ x)) (pullbackSymmetry t (i ≫ x))
    (pullbackSymmetry t (j ≫ x)) (pullbackSymmetry t x)
  · simp [scalarFirstBaseChangedMap, firstOverlapOver, Category.assoc]
  · simp [scalarFirstBaseChangedMap, secondOverlapOver, Category.assoc]
  · simp [scalarFirstBaseChangedMap, leftChartOver, Category.assoc]
  · simp [scalarFirstBaseChangedMap, rightChartOver, Category.assoc]

end
end QEC.Coding.AlgebraicGeometry.ChartBaseChange
namespace QEC.Coding.AlgebraicGeometry.ChartBaseChange
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe v u
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {A B Z T : C} (t : T ⟶ Z)
lemma scalarFirstBaseChangedMap_eq_pullbackMap
    (f : A ⟶ Z) (g : B ⟶ Z) (u : A ⟶ B) (hu : u ≫ g = f) :
    scalarFirstBaseChangedMap t f g u hu =
      pullback.map t f t g (𝟙 T) u (𝟙 Z) (by simp)
        (by simpa only [Category.comp_id] using hu.symm) := by
  apply pullback.hom_ext
  · simp only [scalarFirstBaseChangedMap_scalarProjection, pullback.map, pullback.lift_fst,
      Category.comp_id]
  · simp only [scalarFirstBaseChangedMap_chartProjection, pullback.map, pullback.lift_snd]
end
end QEC.Coding.AlgebraicGeometry.ChartBaseChange
