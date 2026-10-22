import QEC.Coding.ExpanderCodes.LPSOriginalNormalizationBaseChange

/-!
# Original normalization comparison

Internal proof closure for the original generated modular-equation fields and
actual j and reciprocal-j charts. The PK22 source graph route is ex:Xpq
(main.tex, lines 484–486); this normalization comparison is derived internal
mathematics, not the public asymptotically good qLDPC theorem.

The maps, overlaps, inverses, and both projection identities are constructed.
No global comparison or overlap conclusion is supplied as a hypothesis.
-/

namespace QEC.Coding.TannerLiftedProduct
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open QEC.Coding.AlgebraicGeometry.ChartBaseChange
noncomputable section

set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerNormalComplexBaseChangedOverlapMap_complexProjection
    (N : ℕ) (hN : 0 < N) (b : Bool) :
    lpsOriginalIntegerNormalComplexBaseChangedOverlapMap N hN b ≫ pullback.fst _ _ =
      pullback.fst _ _ := by
  cases b <;> exact scalarFirstBaseChangedMap_scalarProjection _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerNormalComplexBaseChangedOverlapMap_integerProjection
    (N : ℕ) (hN : 0 < N) (b : Bool) :
    lpsOriginalIntegerNormalComplexBaseChangedOverlapMap N hN b ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ lpsOriginalIntegerNormalSchemeOverlapMap N hN b := by
  cases b <;> exact scalarFirstBaseChangedMap_chartProjection _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalComplexNormalLaurentBaseChangeIso_overlap
    (N : ℕ) [NeZero N] (hN : 0 < N) (b : Bool) :
    (lpsOriginalComplexNormalLaurentBaseChangeIso N hN).hom ≫
      lpsOriginalIntegerNormalComplexBaseChangedOverlapMap N hN b =
    lpsOriginalComplexNormalSchemeOverlapMap N hN b ≫
      (lpsOriginalComplexNormalChartBaseChangeIso N hN b).hom := by
  apply pullback.hom_ext
  · simp only [Category.assoc, lpsOriginalIntegerNormalComplexBaseChangedOverlapMap_complexProjection,
      lpsOriginalComplexNormalChartBaseChangeIso_complexProjection]
    rw [lpsOriginalComplexNormalLaurentBaseChangeIso_complexProjection]
    exact (lpsOriginalComplexChartToSpecC_overlap N hN b).symm
  · simp only [Category.assoc, lpsOriginalIntegerNormalComplexBaseChangedOverlapMap_integerProjection,
      lpsOriginalComplexNormalChartBaseChangeIso_integerProjection]
    rw [← Category.assoc, lpsOriginalComplexNormalLaurentBaseChangeIso_integerProjection]
    exact (lpsOriginalComplexToIntegerChartMap_overlap N hN b).symm

set_option backward.isDefEq.respectTransparency false in
def lpsOriginalComplexNormalBaseChangeOverlapIso (N : ℕ) [NeZero N] (hN : 0 < N) :
    Spec (.of (lpsOriginalComplexNormalLaurentChart N hN)) ≅
      pullback ((lpsOriginalIntegerNormalComplexBaseChangeOpenCover N hN).f false)
        ((lpsOriginalIntegerNormalComplexBaseChangeOpenCover N hN).f true) :=
  lpsOriginalComplexNormalLaurentBaseChangeIso N hN ≪≫
    (lpsOriginalIntegerNormalComplexBaseChangedCharts_pullback N hN).isoPullback

set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalComplexNormalBaseChangeOverlapIso_zeroProjection
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    (lpsOriginalComplexNormalBaseChangeOverlapIso N hN).hom ≫ pullback.fst _ _ =
      lpsOriginalComplexNormalSchemeOverlapMap N hN false ≫
        (lpsOriginalComplexNormalChartBaseChangeIso N hN false).hom := by
  rw [lpsOriginalComplexNormalBaseChangeOverlapIso, Iso.trans_hom, Category.assoc,
    IsPullback.isoPullback_hom_fst]
  exact lpsOriginalComplexNormalLaurentBaseChangeIso_overlap N hN false

set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalComplexNormalBaseChangeOverlapIso_infinityProjection
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    (lpsOriginalComplexNormalBaseChangeOverlapIso N hN).hom ≫ pullback.snd _ _ =
      lpsOriginalComplexNormalSchemeOverlapMap N hN true ≫
        (lpsOriginalComplexNormalChartBaseChangeIso N hN true).hom := by
  rw [lpsOriginalComplexNormalBaseChangeOverlapIso, Iso.trans_hom, Category.assoc,
    IsPullback.isoPullback_hom_snd]
  exact lpsOriginalComplexNormalLaurentBaseChangeIso_overlap N hN true

end
end QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
noncomputable section

set_option backward.isDefEq.respectTransparency false in
def lpsOriginalIntegerBaseChangeToComplexNormalChart (N : ℕ) [NeZero N] (hN : 0 < N) (b : Bool) :
    (lpsOriginalIntegerNormalComplexBaseChangeOpenCover N hN).X b ⟶
      lpsOriginalComplexNormalGluedScheme N hN :=
  (lpsOriginalComplexNormalChartBaseChangeIso N hN b).inv ≫
    lpsOriginalComplexNormalGluedChartMap N hN b

set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerBaseChangeToComplexNormalChart_zeroInfinity
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    pullback.fst ((lpsOriginalIntegerNormalComplexBaseChangeOpenCover N hN).f false)
        ((lpsOriginalIntegerNormalComplexBaseChangeOpenCover N hN).f true) ≫
      lpsOriginalIntegerBaseChangeToComplexNormalChart N hN false =
    pullback.snd _ _ ≫ lpsOriginalIntegerBaseChangeToComplexNormalChart N hN true := by
  apply (cancel_epi (lpsOriginalComplexNormalBaseChangeOverlapIso N hN).hom).mp
  simp only [lpsOriginalIntegerBaseChangeToComplexNormalChart, ← Category.assoc]
  rw [lpsOriginalComplexNormalBaseChangeOverlapIso_zeroProjection,
    lpsOriginalComplexNormalBaseChangeOverlapIso_infinityProjection]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact lpsOriginalComplexNormalGluedOverlap_agreement N hN

set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerBaseChangeToComplexNormalChart_compatible
    (N : ℕ) [NeZero N] (hN : 0 < N) (b c : Bool) :
    pullback.fst ((lpsOriginalIntegerNormalComplexBaseChangeOpenCover N hN).f b)
        ((lpsOriginalIntegerNormalComplexBaseChangeOpenCover N hN).f c) ≫
      lpsOriginalIntegerBaseChangeToComplexNormalChart N hN b =
    pullback.snd _ _ ≫ lpsOriginalIntegerBaseChangeToComplexNormalChart N hN c := by
  cases b <;> cases c
  · rw [fst_eq_snd_of_mono_eq]
  · exact lpsOriginalIntegerBaseChangeToComplexNormalChart_zeroInfinity N hN
  · apply (cancel_epi (pullbackSymmetry
        ((lpsOriginalIntegerNormalComplexBaseChangeOpenCover N hN).f false)
        ((lpsOriginalIntegerNormalComplexBaseChangeOpenCover N hN).f true)).hom).mp
    simpa only [← Category.assoc, pullbackSymmetry_hom_comp_fst,
      pullbackSymmetry_hom_comp_snd] using
        (lpsOriginalIntegerBaseChangeToComplexNormalChart_zeroInfinity N hN).symm
  · rw [fst_eq_snd_of_mono_eq]

set_option backward.isDefEq.respectTransparency false in
def lpsOriginalIntegerBaseChangeToComplexNormal (N : ℕ) [NeZero N] (hN : 0 < N) :
    lpsOriginalIntegerNormalComplexBaseChange N hN ⟶
      lpsOriginalComplexNormalGluedScheme N hN :=
  (lpsOriginalIntegerNormalComplexBaseChangeOpenCover N hN).glueMorphisms
    (lpsOriginalIntegerBaseChangeToComplexNormalChart N hN)
    (lpsOriginalIntegerBaseChangeToComplexNormalChart_compatible N hN)

set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerBaseChangeToComplexNormal_chart
    (N : ℕ) [NeZero N] (hN : 0 < N) (b : Bool) :
    (lpsOriginalIntegerNormalComplexBaseChangeOpenCover N hN).f b ≫
      lpsOriginalIntegerBaseChangeToComplexNormal N hN =
      lpsOriginalIntegerBaseChangeToComplexNormalChart N hN b :=
  Scheme.Cover.ι_glueMorphisms (lpsOriginalIntegerNormalComplexBaseChangeOpenCover N hN)
    (lpsOriginalIntegerBaseChangeToComplexNormalChart N hN)
    (lpsOriginalIntegerBaseChangeToComplexNormalChart_compatible N hN) b

set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalComplexNormalToIntegerBaseChange_hom_inv
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    lpsOriginalComplexNormalToIntegerBaseChange N hN ≫
      lpsOriginalIntegerBaseChangeToComplexNormal N hN =
      𝟙 (lpsOriginalComplexNormalGluedScheme N hN) := by
  apply (lpsOriginalComplexNormalSchemeGlueData N hN).openCover.hom_ext
  intro b
  change lpsOriginalComplexNormalGluedChartMap N hN b ≫
    (lpsOriginalComplexNormalToIntegerBaseChange N hN ≫
      lpsOriginalIntegerBaseChangeToComplexNormal N hN) =
    lpsOriginalComplexNormalGluedChartMap N hN b ≫ 𝟙 _
  rw [← Category.assoc, lpsOriginalComplexNormalToIntegerBaseChange_chart,
    Category.assoc, lpsOriginalIntegerBaseChangeToComplexNormal_chart]
  simp only [lpsOriginalIntegerBaseChangeToComplexNormalChart, Iso.hom_inv_id_assoc,
    Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalComplexNormalToIntegerBaseChange_inv_hom
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    lpsOriginalIntegerBaseChangeToComplexNormal N hN ≫
      lpsOriginalComplexNormalToIntegerBaseChange N hN =
      𝟙 (lpsOriginalIntegerNormalComplexBaseChange N hN) := by
  apply (lpsOriginalIntegerNormalComplexBaseChangeOpenCover N hN).hom_ext
  intro b
  rw [← Category.assoc, lpsOriginalIntegerBaseChangeToComplexNormal_chart]
  simp only [lpsOriginalIntegerBaseChangeToComplexNormalChart, Category.assoc,
    lpsOriginalComplexNormalToIntegerBaseChange_chart, Iso.inv_hom_id_assoc, Category.comp_id]

/-- The actual original complex normalization is the complex fiber of the
original proper integer normalization. Both maps and inverse laws are constructed. -/
def lpsOriginalComplexNormalGluedIntegerBaseChangeIso
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    lpsOriginalComplexNormalGluedScheme N hN ≅ lpsOriginalIntegerNormalComplexBaseChange N hN where
  hom := lpsOriginalComplexNormalToIntegerBaseChange N hN
  inv := lpsOriginalIntegerBaseChangeToComplexNormal N hN
  hom_inv_id := lpsOriginalComplexNormalToIntegerBaseChange_hom_inv N hN
  inv_hom_id := lpsOriginalComplexNormalToIntegerBaseChange_inv_hom N hN

end
end QEC.Coding.TannerLiftedProduct
