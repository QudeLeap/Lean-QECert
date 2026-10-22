import QEC.Coding.ExpanderCodes.LPSOriginalNativeCovectorNormalForm

/-!
# LPSOriginalNativeHolomorphicExtension

Analytic extension of actual no-pole representatives and preservation of their quotient class.
This is a derived internal proof step on the existing original curve. The analytic/cusp interpretation
follows the Milne references in `LPSOriginalHolomorphicDifferentialComparison`. This package does not
prove good reduction, Frobenius/Weil, LPS spectral estimates or the arbitrary-field PK22 code family.
-/

namespace QEC.Coding.TannerLiftedProduct
open Filter Topology QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped Manifold ContDiff
noncomputable section
variable (N : ℕ) [NeZero N] (hN : 4 ∣ N)

/-- Repair preserves the independently defined all-chart meromorphy condition. -/
lemma lpsOriginalNormalizedFilledCovector_meromorphic
    (sigma : LPSOriginalFilledCovectorRepresentatives N hN)
    (hmer : lpsOriginalFilledCovectorChartMeromorphic N hN sigma) :
    lpsOriginalFilledCovectorChartMeromorphic N hN
      (lpsOriginalNormalizedFilledCovector N hN sigma) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  intro x z hz
  have he : lpsOriginalFilledCovectorChartCoefficient N hN
      (lpsOriginalNormalizedFilledCovector N hN sigma) x =ᶠ[𝓝 z]
      toMeromorphicNFOn (lpsOriginalFilledCovectorChartCoefficient N hN sigma x)
        (chartAt ℂ x).target := by
    filter_upwards [(chartAt ℂ x).open_target.mem_nhds hz] with w hw
    exact lpsOriginalNormalizedFilledCovector_chart N hN sigma hmer x w hw
  exact (meromorphicNFOn_toMeromorphicNFOn _ _ hz).meromorphicAt.congr
    (he.symm.filter_mono nhdsWithin_le_nhds)

/-- Actual no-pole orders at every own-chart center make the repaired Hom-bundle section analytic. -/
lemma lpsOriginalNormalizedFilledCovector_contMDiff
    (sigma : LPSOriginalFilledCovectorRepresentatives N hN)
    (hmer : lpsOriginalFilledCovectorChartMeromorphic N hN sigma)
    (horder : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      ∀ x : LPSOriginalFilledCurve N,
        0 ≤ meromorphicOrderAt (lpsOriginalFilledCovectorChartCoefficient N hN sigma x)
          (chartAt ℂ x x)) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun x : LPSOriginalFilledCurve N => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ)
        (E := fun y : LPSOriginalFilledCurve N =>
          TangentSpace 𝓘(ℂ) y →L[ℂ] Bundle.Trivial (LPSOriginalFilledCurve N) ℂ y)
        x (lpsOriginalNormalizedFilledCovector N hN sigma x)) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  intro x
  apply (contMDiffAt_hom_bundle _).mpr
  refine ⟨contMDiffAt_id, ?_⟩
  let e := chartAt ℂ x
  let f := lpsOriginalFilledCovectorChartCoefficient N hN sigma x
  have hx : e x ∈ e.target := e.map_source (mem_chart_source ℂ x)
  have ha : AnalyticAt ℂ (toMeromorphicNFAt f (e x)) (e x) :=
    ((hmer x (e x) hx).meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt).mp
      (horder x)
  have hc : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω e x :=
    contMDiffAt_extChartAt (I := 𝓘(ℂ))
  have hg : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
      (fun y => toMeromorphicNFAt f (e x) (e y)) x :=
    ha.contDiffAt.contMDiffAt.comp x hc
  have hm := (ContinuousLinearMap.mul ℂ ℂ).contMDiffAt (n := ω) |>.comp x hg
  apply hm.congr_of_eventuallyEq
  have hf : toMeromorphicNFOn f e.target =ᶠ[𝓝 (e x)] toMeromorphicNFAt f (e x) :=
    toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds (hmer x) hx
  have hfixed := hc.continuousAt.tendsto.eventually hf
  filter_upwards [e.open_source.mem_nhds (mem_chart_source ℂ x), hfixed] with y hy hfy
  rw [lpsOriginalNormalizedFilledCovector_inCoordinates N hN sigma hmer x y hy]
  have hnorm := normalizedGermValue_on f e.target (e y) (hmer x) (e.map_source hy)
  rw [← hnorm, hfy]
  rfl

/-- Repair preserves the representative away from a discrete set, in the actual codiscrete filter. -/
lemma lpsOriginalNormalizedFilledCovector_codiscrete
    (sigma : LPSOriginalFilledCovectorRepresentatives N hN)
    (hmer : lpsOriginalFilledCovectorChartMeromorphic N hN sigma) :
    letI := lpsOriginalFilledTopology N
    ∀ᶠ y in Filter.codiscrete (LPSOriginalFilledCurve N),
      sigma y = lpsOriginalNormalizedFilledCovector N hN sigma y := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  change {y | sigma y = lpsOriginalNormalizedFilledCovector N hN sigma y} ∈
    Filter.codiscreteWithin (Set.univ : Set (LPSOriginalFilledCurve N))
  rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  intro x hx
  simp only [Set.compl_univ, Set.union_empty]
  let e := chartAt ℂ x
  let f := lpsOriginalFilledCovectorChartCoefficient N hN sigma x
  have hs : x ∈ e.source := mem_chart_source ℂ x
  have ht : Tendsto e (𝓝[≠] x) (𝓝[≠] (e x)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨(e.continuousAt hs).tendsto.mono_left nhdsWithin_le_nhds,
        e.eventually_ne_nhdsWithin hs⟩
  have hf := ht.eventually ((hmer x).toMeromorphicNFOn_eq_self_on_nhdsNE
    (e.map_source hs))
  filter_upwards [hf, nhdsWithin_le_nhds (e.open_source.mem_nhds hs)] with y hy hys
  have hc := lpsOriginalNormalizedFilledCovector_chart N hN sigma hmer x (e y)
    (e.map_source hys)
  change lpsOriginalFilledCovectorChartCoefficient N hN
    (lpsOriginalNormalizedFilledCovector N hN sigma) x (e y) =
      toMeromorphicNFOn f e.target (e y) at hc
  change toMeromorphicNFOn f e.target (e y) = f (e y) at hy
  have heq : lpsOriginalFilledCovectorChartCoefficient N hN
      (lpsOriginalNormalizedFilledCovector N hN sigma) x (e y) = f (e y) := hc.trans hy
  apply ContinuousLinearMap.ext
  intro v
  rw [lpsOriginalFilledCovectorChart_evaluate N hN sigma x y v hys,
    lpsOriginalFilledCovectorChart_evaluate N hN
      (lpsOriginalNormalizedFilledCovector N hN sigma) x y v hys, heq]

/-- The repaired representative belongs to the genuine all-chart meromorphic subtype. -/
def lpsOriginalNormalizedMeromorphicCovectorRepresentative
    (sigma : LPSOriginalFilledMeromorphicCovectorRepresentatives N hN) :
    LPSOriginalFilledMeromorphicCovectorRepresentatives N hN :=
  ⟨lpsOriginalNormalizedFilledCovector N hN sigma.val,
    lpsOriginalNormalizedFilledCovector_meromorphic N hN sigma.val sigma.property⟩

/-- Repair preserves the genuine meromorphic quotient class, without asserting pointwise equality. -/
lemma lpsOriginalNormalizedMeromorphicCovector_class
    (sigma : LPSOriginalFilledMeromorphicCovectorRepresentatives N hN) :
    lpsOriginalCompactMeromorphicCovectorClass N hN sigma =
      lpsOriginalCompactMeromorphicCovectorClass N hN
        (lpsOriginalNormalizedMeromorphicCovectorRepresentative N hN sigma) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let : AddCommGroup (LPSOriginalFilledMeromorphicCovectorRepresentatives N hN) :=
    (lpsOriginalFilledMeromorphicCovectorSubmodule N hN).addCommGroup
  change Submodule.Quotient.mk sigma =
    Submodule.Quotient.mk (lpsOriginalNormalizedMeromorphicCovectorRepresentative N hN sigma)
  apply (Submodule.Quotient.eq (lpsOriginalFilledMeromorphicCovectorZeroSubmodule N hN)).mpr
  change ∀ᶠ y in Filter.codiscrete (LPSOriginalFilledCurve N),
    sigma.val y - lpsOriginalNormalizedFilledCovector N hN sigma.val y = 0
  filter_upwards [lpsOriginalNormalizedFilledCovector_codiscrete N hN sigma.val sigma.property]
    with y hy
  exact sub_eq_zero.mpr hy

end
end QEC.Coding.TannerLiftedProduct
