import QEC.Coding.AlgebraicGeometry.SchemeOverlapImages
import QEC.Coding.ExpanderCodes.LPSOriginalComplexNormalCharts

/-!
# Actual original normalization chart and Laurent images

The two literal chart images cover the original normalization scheme. The
literal Laurent inclusion has exactly their intersection as its image.
-/

namespace QEC.Coding.TannerLiftedProduct
open CategoryTheory _root_.AlgebraicGeometry QEC.Coding.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
variable (N : ℕ) (hpos : 0 < N)
local instance originalOverlapImageOpenImmersion (b : Bool) :
    IsOpenImmersion (lpsOriginalComplexNormalSchemeOverlapMap N hpos b) :=
  lpsOriginalComplexNormalSchemeOverlapMap_openImmersion N hpos b
local instance originalChartImageOpenImmersion (b : Bool) :
    IsOpenImmersion (lpsOriginalComplexNormalGluedChartMap N hpos b) :=
  lpsOriginalComplexNormalGluedChartMap_openImmersion N hpos b

def lpsOriginalComplexNormalChartImage (b : Bool) :
    (lpsOriginalComplexNormalGluedScheme N hpos).Opens :=
  (lpsOriginalComplexNormalGluedChartMap N hpos b).opensRange

lemma lpsOriginalComplexNormalChartImage_cover :
    lpsOriginalComplexNormalChartImage N hpos false ⊔
      lpsOriginalComplexNormalChartImage N hpos true = ⊤ := by
  apply le_antisymm le_top
  intro x _
  obtain ⟨b, y, hy⟩ := lpsOriginalComplexNormalGluedChartMap_cover N hpos x
  cases b
  · exact Or.inl ⟨y, hy⟩
  · exact Or.inr ⟨y, hy⟩

lemma lpsOriginalComplexNormalLaurentImage_intersection :
    (lpsOriginalComplexNormalSchemeOverlapMap N hpos false ≫
      lpsOriginalComplexNormalGluedChartMap N hpos false).opensRange =
      lpsOriginalComplexNormalChartImage N hpos false ⊓
        lpsOriginalComplexNormalChartImage N hpos true := by
  let D := lpsOriginalComplexNormalSchemeGlueData N hpos
  have e : D.V (false, true) =
      Spec (.of (lpsOriginalComplexNormalLaurentChart N hpos)) := by
    simp [D, lpsOriginalComplexNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData', lpsOriginalComplexNormalSchemeGlueDataPrime]
  have hf : D.f false true = eqToHom e ≫
      lpsOriginalComplexNormalSchemeOverlapMap N hpos false := by
    simp [D, lpsOriginalComplexNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f',
      lpsOriginalComplexNormalSchemeGlueDataPrime]
  have h := schemeGlueOverlap_image_intersection D false true
  have he : D.f false true ≫ D.ι false = eqToHom e ≫
      (lpsOriginalComplexNormalSchemeOverlapMap N hpos false ≫
        lpsOriginalComplexNormalGluedChartMap N hpos false) := by
    have hcomp := congrArg (fun a : D.V (false, true) ⟶
      lpsOriginalComplexNormalSchemeChart N hpos false =>
        a ≫ lpsOriginalComplexNormalGluedChartMap N hpos false) hf
    exact hcomp.trans (Category.assoc (eqToHom e)
      (lpsOriginalComplexNormalSchemeOverlapMap N hpos false)
      (lpsOriginalComplexNormalGluedChartMap N hpos false))
  have hi : IsOpenImmersion (D.f false true) := D.f_open false true
  have hj : IsOpenImmersion (D.ι false) := Scheme.GlueData.ι_isOpenImmersion D false
  let hc : IsOpenImmersion (D.f false true ≫ D.ι false) :=
    @IsOpenImmersion.comp _ _ _ (D.f false true) (D.ι false) hi hj
  have hr : (D.f false true ≫ D.ι false).opensRange =
      (lpsOriginalComplexNormalSchemeOverlapMap N hpos false ≫
        lpsOriginalComplexNormalGluedChartMap N hpos false).opensRange := by
    apply TopologicalSpace.Opens.ext
    change Set.range (D.f false true ≫ D.ι false) = Set.range
      (lpsOriginalComplexNormalSchemeOverlapMap N hpos false ≫
        lpsOriginalComplexNormalGluedChartMap N hpos false)
    rw [he]
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨(eqToHom e) z, (Scheme.Hom.comp_apply _ _ z).symm⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨z, hz⟩ := (eqToHom e).homeomorph.surjective y
      refine ⟨z, ?_⟩
      exact (Scheme.Hom.comp_apply _ _ z).trans
        (congrArg (lpsOriginalComplexNormalSchemeOverlapMap N hpos false ≫
          lpsOriginalComplexNormalGluedChartMap N hpos false) hz)
  exact hr.symm.trans h
end
end QEC.Coding.TannerLiftedProduct
