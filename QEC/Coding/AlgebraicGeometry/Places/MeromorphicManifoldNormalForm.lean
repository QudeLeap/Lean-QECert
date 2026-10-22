import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Genuine meromorphic normal forms on complex manifolds

Normal-form values are natural under analytic local coordinate changes that
preserve punctured neighborhoods. Normalize the actual chart representatives
of a meromorphic function, prove coordinate independence, unchanged orders
and genuine global codiscrete equality, and obtain analyticity from nonnegative
orders without imposing a representative value at a removable singularity.
-/

namespace QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
noncomputable section

lemma normalizedGermValue_comp (f g : ℂ → ℂ) (x : ℂ)
    (hf : MeromorphicAt f (g x)) (hg : AnalyticAt ℂ g x)
    (ht : Tendsto g (𝓝[≠] x) (𝓝[≠] (g x))) :
    toMeromorphicNFAt (f ∘ g) x x = toMeromorphicNFAt f (g x) (g x) := by
  have hcomp := hf.comp_analyticAt hg
  have hn₁ : MeromorphicNFAt (toMeromorphicNFAt (f ∘ g) x) x :=
    meromorphicNFAt_toMeromorphicNFAt
  have hn₂ : MeromorphicNFAt (toMeromorphicNFAt f (g x) ∘ g) x :=
    (meromorphicNFAt_toMeromorphicNFAt (f := f) (x := g x)).comp_analyticAt hg
  have he : (f ∘ g) =ᶠ[𝓝[≠] x] (toMeromorphicNFAt f (g x) ∘ g) :=
    ht.eventually hf.eq_nhdsNE_toMeromorphicNFAt
  exact ((hn₁.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hn₂).mp
    (hcomp.eq_nhdsNE_toMeromorphicNFAt.symm.trans he)).eq_of_nhds

lemma normalizedGermValue_eventuallyEq (f g : ℂ → ℂ) (x : ℂ)
    (h : f =ᶠ[𝓝[≠] x] g) :
    toMeromorphicNFAt f x x = toMeromorphicNFAt g x x :=
  (toMeromorphicNFAt_eventuallyEq_nhds_congr h).eq_of_nhds

lemma normalizedGermValue_on (f : ℂ → ℂ) (U : Set ℂ) (x : ℂ)
    (hf : MeromorphicOn f U) (hx : x ∈ U) :
    toMeromorphicNFOn f U x = toMeromorphicNFAt f x x :=
  toMeromorphicNFOn_eq_toMeromorphicNFAt hf hx

end
end QEC.Coding.AlgebraicGeometry.MeromorphicGerms

namespace QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) ω M]

def chartNormalizedMeromorphicFunction (F : M → ℂ) (x : M) : ℂ :=
  toMeromorphicNFAt (F ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) (chartAt ℂ x x)

lemma chartNormalizedMeromorphicFunction_chart
    (F : M → ℂ) (hF : ∀ x : M, MeromorphicOn (F ∘ (chartAt ℂ x).symm) (chartAt ℂ x).target)
    (x : M) (z : ℂ) (hz : z ∈ (chartAt ℂ x).target) :
    chartNormalizedMeromorphicFunction F ((chartAt ℂ x).symm z) =
      toMeromorphicNFOn (F ∘ (chartAt ℂ x).symm) (chartAt ℂ x).target z := by
  let e := chartAt ℂ x
  let y := e.symm z
  let d := chartAt ℂ y
  let w := d y
  let g := d.symm.trans e
  have hys : y ∈ e.source := e.map_target hz
  have hyd : y ∈ d.source := mem_chart_source ℂ y
  have hw : w ∈ g.source := by
    change w ∈ d.target ∧ d.symm w ∈ e.source
    constructor
    · exact d.map_source hyd
    · change d.symm (d y) ∈ e.source
      rw [d.left_inv hyd]
      exact hys
  have hgz : g w = z := by
    change e (d.symm (d y)) = z
    rw [d.left_inv hyd]
    exact e.right_inv hz
  have ht : Tendsto g (𝓝[≠] w) (𝓝[≠] (g w)) :=
    tendsto_nhdsWithin_iff.mpr ⟨(g.continuousAt hw).tendsto.mono_left nhdsWithin_le_nhds,
      g.eventually_ne_nhdsWithin hw⟩
  have hc : ContDiffOn ℂ ω (e ∘ d.symm) g.source := by
    simpa only [extChartAt_coe,extChartAt_coe_symm,ext_coord_change_source,
      modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,Set.image_id,Function.id_comp,Function.comp_id] using (contDiffOn_ext_coord_change (I := 𝓘(ℂ)) x y)
  have hg : AnalyticAt ℂ (e ∘ d.symm) w :=
    (hc.contDiffAt (g.open_source.mem_nhds hw)).analyticAt
  have he : (F ∘ d.symm) =ᶠ[𝓝[≠] w] ((F ∘ e.symm) ∘ (e ∘ d.symm)) := by
    have hh : ∀ᶠ u in 𝓝[≠] w, u ∈ g.source := nhdsWithin_le_nhds (g.open_source.mem_nhds hw)
    filter_upwards [hh] with u hu
    have hu' : d.symm u ∈ e.source := hu.2
    simp only [Function.comp_def]
    rw [e.left_inv hu']
  change toMeromorphicNFAt (F ∘ d.symm) w w = _
  rw [normalizedGermValue_eventuallyEq _ _ w he]
  have hf : MeromorphicAt (F ∘ e.symm) ((e ∘ d.symm) w) := by
    change MeromorphicAt (F ∘ e.symm) (g w)
    rw [hgz]
    exact hF x z hz
  rw [normalizedGermValue_comp _ _ w hf hg ht]
  change toMeromorphicNFAt (F ∘ e.symm) (g w) (g w) = _
  rw [hgz]
  exact (normalizedGermValue_on _ _ z (hF x) hz).symm

lemma chartNormalizedMeromorphicFunction_chart_eventually
    (F : M → ℂ) (hF : ∀ x : M, MeromorphicOn (F ∘ (chartAt ℂ x).symm) (chartAt ℂ x).target)
    (x : M) (z : ℂ) (hz : z ∈ (chartAt ℂ x).target) :
    (chartNormalizedMeromorphicFunction F ∘ (chartAt ℂ x).symm) =ᶠ[𝓝 z]
      toMeromorphicNFOn (F ∘ (chartAt ℂ x).symm) (chartAt ℂ x).target := by
  filter_upwards [(chartAt ℂ x).open_target.mem_nhds hz] with u hu
  exact chartNormalizedMeromorphicFunction_chart F hF x u hu

lemma chartNormalizedMeromorphicFunction_meromorphic
    (F : M → ℂ) (hF : ∀ x : M, MeromorphicOn (F ∘ (chartAt ℂ x).symm) (chartAt ℂ x).target)
    (x : M) :
    MeromorphicOn (chartNormalizedMeromorphicFunction F ∘ (chartAt ℂ x).symm) (chartAt ℂ x).target := by
  intro z hz
  exact (meromorphicNFOn_toMeromorphicNFOn _ _ hz).meromorphicAt.congr
    ((chartNormalizedMeromorphicFunction_chart_eventually F hF x z hz).symm.filter_mono nhdsWithin_le_nhds)

lemma chartNormalizedMeromorphicFunction_order
    (F : M → ℂ) (hF : ∀ x : M, MeromorphicOn (F ∘ (chartAt ℂ x).symm) (chartAt ℂ x).target)
    (x : M) (z : ℂ) (hz : z ∈ (chartAt ℂ x).target) :
    meromorphicOrderAt (chartNormalizedMeromorphicFunction F ∘ (chartAt ℂ x).symm) z =
      meromorphicOrderAt (F ∘ (chartAt ℂ x).symm) z := by
  rw [meromorphicOrderAt_congr ((chartNormalizedMeromorphicFunction_chart_eventually F hF x z hz).filter_mono nhdsWithin_le_nhds)]
  exact meromorphicOrderAt_toMeromorphicNFOn (hF x) hz

lemma chartNormalizedMeromorphicFunction_codiscrete
    (F : M → ℂ) (hF : ∀ x : M, MeromorphicOn (F ∘ (chartAt ℂ x).symm) (chartAt ℂ x).target) :
    F =ᶠ[Filter.codiscrete M] chartNormalizedMeromorphicFunction F := by
  change {y | F y = chartNormalizedMeromorphicFunction F y} ∈ Filter.codiscreteWithin (Set.univ : Set M)
  rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  intro x hx
  simp only [Set.compl_univ,Set.union_empty]
  let e := chartAt ℂ x
  have hs : x ∈ e.source := mem_chart_source ℂ x
  have ht : Tendsto e (𝓝[≠] x) (𝓝[≠] (e x)) :=
    tendsto_nhdsWithin_iff.mpr ⟨(e.continuousAt hs).tendsto.mono_left nhdsWithin_le_nhds,
      e.eventually_ne_nhdsWithin hs⟩
  have hh := ht.eventually ((hF x).toMeromorphicNFOn_eq_self_on_nhdsNE (e.map_source hs))
  have hsrc : ∀ᶠ y in 𝓝[≠] x, y ∈ e.source := nhdsWithin_le_nhds (e.open_source.mem_nhds hs)
  filter_upwards [hh,hsrc] with y hy hys
  have hc := chartNormalizedMeromorphicFunction_chart F hF x (e y) (e.map_source hys)
  rw [e.left_inv hys] at hc
  change toMeromorphicNFOn (F ∘ e.symm) e.target (e y) = F (e.symm (e y)) at hy
  rw [e.left_inv hys] at hy
  exact hy.symm.trans hc.symm

lemma chartNormalizedMeromorphicFunction_analyticAt
    (F : M → ℂ) (hF : ∀ x : M, MeromorphicOn (F ∘ (chartAt ℂ x).symm) (chartAt ℂ x).target)
    (x : M) (z : ℂ) (hz : z ∈ (chartAt ℂ x).target)
    (ho : 0 ≤ meromorphicOrderAt (F ∘ (chartAt ℂ x).symm) z) :
    AnalyticAt ℂ (chartNormalizedMeromorphicFunction F ∘ (chartAt ℂ x).symm) z := by
  have ha := ((hF x z hz).meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt).mp ho
  have he := (chartNormalizedMeromorphicFunction_chart_eventually F hF x z hz).trans
    (toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds (hF x) hz)
  exact ha.congr he.symm

end
end QEC.Coding.AlgebraicGeometry.MeromorphicGerms
