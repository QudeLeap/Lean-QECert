import QEC.Coding.ExpanderCodes.LPSOriginalNativeCovectorCoordinates

/-!
# LPSOriginalNativeCovectorNormalForm

Coordinate-independent normal-form filling of original cotangent representatives.
This is a derived internal proof step on the existing original curve. The analytic/cusp interpretation
follows the Milne references in `LPSOriginalHolomorphicDifferentialComparison`. This package does not
prove good reduction, Frobenius/Weil, LPS spectral estimates or the arbitrary-field PK22 code family.
-/

namespace QEC.Coding.TannerLiftedProduct
open Filter Topology QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped Manifold ContDiff
noncomputable section
variable (N : ℕ) [NeZero N] (hN : 4 ∣ N)

/-- Actual normalized coefficient values obey the derivative-weighted chart cocycle. -/
lemma lpsOriginalNormalizedCovectorCoefficient_cocycle
    (sigma : LPSOriginalFilledCovectorRepresentatives N hN)
    (hmer : lpsOriginalFilledCovectorChartMeromorphic N hN sigma)
    (x y : LPSOriginalFilledCurve N) (z : ℂ)
    (hz : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      z ∈ ((chartAt ℂ x).symm.trans (chartAt ℂ y)).source) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    let g := (chartAt ℂ x).symm.trans (chartAt ℂ y)
    toMeromorphicNFAt (lpsOriginalFilledCovectorChartCoefficient N hN sigma x) z z =
      toMeromorphicNFAt (lpsOriginalFilledCovectorChartCoefficient N hN sigma y)
        (g z) (g z) * deriv g z := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let g := (chartAt ℂ x).symm.trans (chartAt ℂ y)
  let fx := lpsOriginalFilledCovectorChartCoefficient N hN sigma x
  let fy := lpsOriginalFilledCovectorChartCoefficient N hN sigma y
  have ha := complexChartTransition_analytic_unit x y z hz
  have hf : MeromorphicAt fy (g z) := hmer y (g z) ((g.map_source hz).1)
  have ht : Tendsto g (𝓝[≠] z) (𝓝[≠] (g z)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨(g.continuousAt hz).tendsto.mono_left nhdsWithin_le_nhds,
        g.eventually_ne_nhdsWithin hz⟩
  have he : fx =ᶠ[𝓝[≠] z] ((fy ∘ g) * deriv g) := by
    filter_upwards [nhdsWithin_le_nhds (g.open_source.mem_nhds hz)] with w hw
    exact lpsOriginalFilledCovectorChartCoefficient_cocycle N hN sigma x y w hw
  change toMeromorphicNFAt fx z z = toMeromorphicNFAt fy (g z) (g z) * deriv g z
  rw [normalizedGermValue_eventuallyEq fx ((fy ∘ g) * deriv g) z he]
  exact normalizedGermValue_comp_mul_analyticUnit fy g (deriv g) z hf
    ha.1 ha.1.deriv ha.2 ht

/-- Fill each actual cotangent representative using its own-chart normal-form value. This operation on arbitrary meromorphic representatives is not asserted linear. -/
def lpsOriginalNormalizedFilledCovector
    (sigma : LPSOriginalFilledCovectorRepresentatives N hN) :
    LPSOriginalFilledCovectorRepresentatives N hN := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  exact fun x => ContinuousLinearMap.mul ℂ ℂ
    (toMeromorphicNFAt (lpsOriginalFilledCovectorChartCoefficient N hN sigma x)
      (chartAt ℂ x x) (chartAt ℂ x x))

/-- The whole repaired covector in any chart is multiplication by its normalized coefficient. -/
lemma lpsOriginalNormalizedFilledCovector_inCoordinates
    (sigma : LPSOriginalFilledCovectorRepresentatives N hN)
    (hmer : lpsOriginalFilledCovectorChartMeromorphic N hN sigma)
    (x y : LPSOriginalFilledCurve N)
    (hy : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      y ∈ (chartAt ℂ x).source) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ)) ℂ
      (Bundle.Trivial (LPSOriginalFilledCurve N) ℂ) x y x y
      (lpsOriginalNormalizedFilledCovector N hN sigma y) =
      ContinuousLinearMap.mul ℂ ℂ
        (toMeromorphicNFAt (lpsOriginalFilledCovectorChartCoefficient N hN sigma x)
          (chartAt ℂ x y) (chartAt ℂ x y)) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  have hz : chartAt ℂ x y ∈ ((chartAt ℂ x).symm.trans (chartAt ℂ y)).source := by
    change chartAt ℂ x y ∈ (chartAt ℂ x).target ∧
      (chartAt ℂ x).symm (chartAt ℂ x y) ∈ (chartAt ℂ y).source
    exact ⟨(chartAt ℂ x).map_source hy,
      by rw [(chartAt ℂ x).left_inv hy]; exact mem_chart_source ℂ y⟩
  have hk := lpsOriginalNormalizedCovectorCoefficient_cocycle N hN sigma hmer x y
    (chartAt ℂ x y) hz
  have he : ((chartAt ℂ x).symm.trans (chartAt ℂ y)) (chartAt ℂ x y) =
      chartAt ℂ y y := by
    rw [OpenPartialHomeomorph.trans_apply, (chartAt ℂ x).left_inv hy]
  dsimp only at hk
  rw [he] at hk
  have ht : (trivializationAt ℂ (Bundle.Trivial (LPSOriginalFilledCurve N) ℂ) x).continuousLinearMapAt ℂ y = ContinuousLinearMap.id ℂ ℂ :=
    Bundle.Trivial.continuousLinearMapAt_trivialization ℂ _ ℂ y
  rw [ContinuousLinearMap.inCoordinates, ht, ContinuousLinearMap.id_comp,
    TangentBundle.symmL_trivializationAt_eq_core hy, tangentBundleCore_coordChange_achart]
  have heq : extChartAt 𝓘(ℂ) y ∘ (extChartAt 𝓘(ℂ) x).symm =
      (((chartAt ℂ x).symm.trans (chartAt ℂ y)) : ℂ → ℂ) := rfl
  rw [heq]
  simp only [modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ]
  change (ContinuousLinearMap.mul ℂ ℂ
    (toMeromorphicNFAt (lpsOriginalFilledCovectorChartCoefficient N hN sigma y)
      (chartAt ℂ y y) (chartAt ℂ y y))).comp
        (fderiv ℂ (((chartAt ℂ x).symm.trans (chartAt ℂ y)) : ℂ → ℂ)
          (chartAt ℂ x y)) = _
  apply ContinuousLinearMap.ext
  intro v
  change toMeromorphicNFAt (lpsOriginalFilledCovectorChartCoefficient N hN sigma y)
    (chartAt ℂ y y) (chartAt ℂ y y) *
      (fderiv ℂ (((chartAt ℂ x).symm.trans (chartAt ℂ y)) : ℂ → ℂ)
        (chartAt ℂ x y)) v =
      toMeromorphicNFAt (lpsOriginalFilledCovectorChartCoefficient N hN sigma x)
        (chartAt ℂ x y) (chartAt ℂ x y) * v
  rw [fderiv_eq_deriv_mul, ← mul_assoc, ← hk]

/-- The genuine repaired chart coefficient equals the chartwise meromorphic normal form. -/
lemma lpsOriginalNormalizedFilledCovector_chart
    (sigma : LPSOriginalFilledCovectorRepresentatives N hN)
    (hmer : lpsOriginalFilledCovectorChartMeromorphic N hN sigma)
    (x : LPSOriginalFilledCurve N) (z : ℂ)
    (hz : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      z ∈ (chartAt ℂ x).target) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    lpsOriginalFilledCovectorChartCoefficient N hN (lpsOriginalNormalizedFilledCovector N hN sigma)
      x z = toMeromorphicNFOn (lpsOriginalFilledCovectorChartCoefficient N hN sigma x)
        (chartAt ℂ x).target z := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  unfold lpsOriginalFilledCovectorChartCoefficient
  rw [lpsOriginalNormalizedFilledCovector_inCoordinates N hN sigma hmer x
    ((chartAt ℂ x).symm z) ((chartAt ℂ x).map_target hz),
    (chartAt ℂ x).right_inv hz]
  change toMeromorphicNFAt (lpsOriginalFilledCovectorChartCoefficient N hN sigma x) z z * 1 = _
  rw [mul_one]
  exact (normalizedGermValue_on _ _ z (hmer x) hz).symm

end
end QEC.Coding.TannerLiftedProduct
