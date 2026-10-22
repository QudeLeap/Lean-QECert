import QEC.Coding.ExpanderCodes.LPSOriginalNativeCovectorCoordinates

/-!
# LPSOriginalHolomorphicNativeCovectors

Every actual analytic section embeds linearly and injectively in the native meromorphic quotient.
This is a derived internal proof step on the existing original curve. The analytic/cusp interpretation
follows the Milne references in `LPSOriginalHolomorphicDifferentialComparison`. This package does not
prove good reduction, Frobenius/Weil, LPS spectral estimates or the arbitrary-field PK22 code family.
-/

namespace QEC.Coding.TannerLiftedProduct
open Filter Topology QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped Manifold ContDiff
noncomputable section
variable (N : ℕ) [NeZero N] (hN : 4 ∣ N)

/-- Every analytic cotangent section has analytic coefficients everywhere in every chart. -/
lemma lpsOriginalHolomorphicCovector_allChart_analytic
    (sigma : LPSOriginalHolomorphicCovectorSections N hN)
    (x : LPSOriginalFilledCurve N) (z : ℂ)
    (hz : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      z ∈ (chartAt ℂ x).target) :
    AnalyticAt ℂ (lpsOriginalFilledCovectorChartCoefficient N hN (fun y => sigma y) x) z := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let e := chartAt ℂ x
  let y := e.symm z
  let d := chartAt ℂ y
  let g := e.symm.trans d
  have hy : y ∈ e.source := e.map_target hz
  have hsrc : z ∈ g.source := ⟨hz, mem_chart_source ℂ y⟩
  have hvalue : g z = d y := rfl
  have ha := complexChartTransition_analytic_unit x y z hsrc
  have hc : AnalyticAt ℂ
      (lpsOriginalFilledCovectorChartCoefficient N hN (fun t => sigma t) y) (g z) := by
    change AnalyticAt ℂ (lpsOriginalHolomorphicCovectorChartCoefficient N hN sigma y) (g z)
    rw [hvalue]
    exact lpsOriginalHolomorphicCovectorChartCoefficient_analytic N hN sigma y
  have he : lpsOriginalFilledCovectorChartCoefficient N hN (fun t => sigma t) x =ᶠ[𝓝 z]
      ((lpsOriginalFilledCovectorChartCoefficient N hN (fun t => sigma t) y ∘ g) * deriv g) := by
    filter_upwards [g.open_source.mem_nhds hsrc] with w hw
    exact lpsOriginalFilledCovectorChartCoefficient_cocycle N hN (fun t => sigma t) x y w hw
  exact ((hc.comp ha.1).mul ha.1.deriv).congr he.symm

/-- Include all analytic sections into the genuine meromorphic representative module. -/
def lpsOriginalHolomorphicCovectorToMeromorphicLinearMap :
    LPSOriginalHolomorphicCovectorSections N hN →ₗ[ℂ]
      LPSOriginalFilledMeromorphicCovectorRepresentatives N hN := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  exact
    { toFun := fun sigma => ⟨fun y => sigma y, fun x z hz =>
        (lpsOriginalHolomorphicCovector_allChart_analytic N hN sigma x z hz).meromorphicAt⟩
      map_add' := fun _ _ => Subtype.ext rfl
      map_smul' := fun _ _ => Subtype.ext rfl }

/-- The actual complex-linear native quotient map on all analytic sections. -/
def lpsOriginalHolomorphicCovectorToClassLinearMap :
    LPSOriginalHolomorphicCovectorSections N hN →ₗ[ℂ]
      LPSOriginalCompactMeromorphicCovectorGerms N hN :=
  (lpsOriginalCompactMeromorphicCovectorClass N hN).comp
    (lpsOriginalHolomorphicCovectorToMeromorphicLinearMap N hN)

/-- Actual local germ equality determines an analytic section, so the native quotient map is injective. -/
lemma lpsOriginalHolomorphicCovectorToClass_injective :
    Function.Injective (lpsOriginalHolomorphicCovectorToClassLinearMap N hN) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  intro sigma tau he
  apply ContMDiffSection.ext
  intro x
  have hg := congrArg (lpsOriginalNativeCovectorToLocal N hN x) he
  change lpsOriginalCovectorRepresentativeToLocal N hN x
      (lpsOriginalHolomorphicCovectorToMeromorphicLinearMap N hN sigma) =
      lpsOriginalCovectorRepresentativeToLocal N hN x
        (lpsOriginalHolomorphicCovectorToMeromorphicLinearMap N hN tau) at hg
  have hpunctured := Filter.Germ.coe_eq.mp (congrArg Subtype.val hg)
  have hvalues := analytic_value_eq_of_punctured_germ
    (lpsOriginalHolomorphicCovectorChartCoefficient_analytic N hN sigma x)
    (lpsOriginalHolomorphicCovectorChartCoefficient_analytic N hN tau x) hpunctured
  apply ContinuousLinearMap.ext
  intro v
  rw [lpsOriginalHolomorphicCovectorChart_evaluate N hN sigma x x v (mem_chart_source ℂ x),
    lpsOriginalHolomorphicCovectorChart_evaluate N hN tau x x v (mem_chart_source ℂ x), hvalues]

end
end QEC.Coding.TannerLiftedProduct
