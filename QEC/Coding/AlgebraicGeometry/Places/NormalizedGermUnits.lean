import QEC.Coding.AlgebraicGeometry.Places.MeromorphicManifoldNormalForm

/-!
# NormalizedGermUnits

Normal-form values under analytic units and genuine complex chart transitions.
-/

namespace QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
open scoped Manifold ContDiff
noncomputable section

/-- Normal-form value commutes with multiplication by a genuine analytic unit. -/
lemma normalizedGermValue_mul_analyticUnit
    (f u : ℂ → ℂ) (x : ℂ) (hf : MeromorphicAt f x)
    (hu : AnalyticAt ℂ u x) (hunit : u x ≠ 0) :
    toMeromorphicNFAt (f * u) x x = toMeromorphicNFAt f x x * u x := by
  have hn : MeromorphicNFAt (toMeromorphicNFAt f x * u) x :=
    (meromorphicNFAt_mul_iff_left hu hunit).mpr meromorphicNFAt_toMeromorphicNFAt
  have he : (f * u) =ᶠ[𝓝[≠] x] (toMeromorphicNFAt f x * u) := by
    filter_upwards [hf.eq_nhdsNE_toMeromorphicNFAt] with z hz
    exact congrArg (fun t : ℂ => t * u z) hz
  have hv := normalizedGermValue_eventuallyEq (f * u) (toMeromorphicNFAt f x * u) x he
  rw [toMeromorphicNFAt_eq_self.mpr hn] at hv
  exact hv

/-- Normal-form value commutes with analytic reparametrization and an analytic unit. -/
lemma normalizedGermValue_comp_mul_analyticUnit
    (f g u : ℂ → ℂ) (x : ℂ) (hf : MeromorphicAt f (g x))
    (hg : AnalyticAt ℂ g x) (hu : AnalyticAt ℂ u x) (hunit : u x ≠ 0)
    (ht : Tendsto g (𝓝[≠] x) (𝓝[≠] (g x))) :
    toMeromorphicNFAt ((f ∘ g) * u) x x =
      toMeromorphicNFAt f (g x) (g x) * u x := by
  rw [normalizedGermValue_mul_analyticUnit (f ∘ g) u x
    (hf.comp_analyticAt hg) hu hunit,
    normalizedGermValue_comp f g x hf hg ht]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) ω M]

/-- Actual complex analytic chart transitions have analytic, nonvanishing derivative. -/
lemma complexChartTransition_analytic_unit
    (x y : M) (z : ℂ)
    (hz : z ∈ ((chartAt ℂ x).symm.trans (chartAt ℂ y)).source) :
    let g := (chartAt ℂ x).symm.trans (chartAt ℂ y)
    AnalyticAt ℂ g z ∧ deriv g z ≠ 0 := by
  let e := chartAt ℂ x
  let d := chartAt ℂ y
  let g := e.symm.trans d
  have hc : ContDiffOn ℂ ω g g.source := by
    simpa only [g, e, d, OpenPartialHomeomorph.coe_trans,
      OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.symm_target,
      OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.trans_target, extChartAt_coe, extChartAt_coe_symm, ext_coord_change_source,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.image_id,
      Function.id_comp, Function.comp_id] using
      (contDiffOn_ext_coord_change (I := 𝓘(ℂ)) y x)
  have hg : AnalyticAt ℂ g z :=
    (hc.contDiffAt (g.open_source.mem_nhds hz)).analyticAt
  have hi : ContDiffOn ℂ ω g.symm g.target := by
    simpa only [g, e, d, OpenPartialHomeomorph.coe_trans,
      OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.symm_target,
      OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.trans_target, extChartAt_coe, extChartAt_coe_symm, ext_coord_change_source,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.image_id,
      Function.id_comp, Function.comp_id] using
      (contDiffOn_ext_coord_change (I := 𝓘(ℂ)) x y)
  have hgi : AnalyticAt ℂ g.symm (g z) :=
    (hi.contDiffAt (g.open_target.mem_nhds (g.map_source hz))).analyticAt
  have he : (g.symm ∘ g) =ᶠ[𝓝 z] (fun t : ℂ => t) := by
    filter_upwards [g.open_source.mem_nhds hz] with t ht
    exact g.left_inv ht
  have hidentity : deriv (g.symm ∘ g) z = (1 : ℂ) := by
    rw [he.deriv_eq]
    exact deriv_id z
  have hchain := deriv_comp z hgi.differentiableAt hg.differentiableAt
  refine ⟨hg, ?_⟩
  intro hzero
  rw [hchain, hzero, mul_zero] at hidentity
  exact zero_ne_one hidentity

end
end QEC.Coding.AlgebraicGeometry.MeromorphicGerms
