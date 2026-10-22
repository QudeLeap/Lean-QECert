import Mathlib.AlgebraicGeometry.Gluing

/-!
# Overlap images in genuine scheme gluing

The actual relation defining scheme gluing identifies the image of a chart
overlap with the intersection of the two chart images.
-/
namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
local instance schemeGlueOverlapOpenImmersion (D : Scheme.GlueData.{u}) (i j : D.J) :
    IsOpenImmersion (D.f i j) := D.f_open i j

lemma schemeGlueOverlap_image_intersection (D : Scheme.GlueData.{u}) (i j : D.J) :
    (D.f i j ≫ D.ι i).opensRange = (D.ι i).opensRange ⊓ (D.ι j).opensRange := by
  apply TopologicalSpace.Opens.ext
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    constructor
    · exact ⟨D.f i j z, (Scheme.Hom.comp_apply _ _ z).symm⟩
    · refine ⟨(D.t i j ≫ D.f j i) z, ?_⟩
      have h := congrArg (fun f => f z) (D.glue_condition i j)
      simpa only [Scheme.Hom.comp_apply] using h
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    obtain ⟨z, hz, _⟩ := (D.ι_eq_iff i j a b).mp (ha.trans hb.symm)
    refine ⟨z, ?_⟩
    exact (Scheme.Hom.comp_apply _ _ z).trans ((congrArg (D.ι i) hz).trans ha)
end
end QEC.Coding.AlgebraicGeometry
