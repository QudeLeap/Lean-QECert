import QEC.Coding.AlgebraicGeometry.Places.MeromorphicManifoldNormalForm
import QEC.Coding.ExpanderCodes.LPSOriginalHolomorphicIntegral
import QEC.Coding.ExpanderCodes.LPSOriginalCompactMeromorphicDifferentialComparison

/-!
# Normalize original no-pole functions before proving integrality

Construct a genuine global representative in meromorphic normal form. Preserve
its actual chart meromorphy and SAME upstairs restriction class. Nonnegative
interior germ orders make this representative genuinely holomorphic upstairs,
so the proved monic equation implies actual C[j] integrality. The raw function
may assign arbitrary values at removable singularities; no analyticity of
those assigned values is assumed.

Derived original PK22 ex:Xpq closure for parent #449. Global algebraic point
coverage, reciprocal-chart comparison and the public theorem remain further
mathematical obligations.
-/

namespace QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section

def lpsOriginalNormalizedFilledFunction (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ) : LPSOriginalFilledCurve N → ℂ :=
  letI := lpsOriginalFilledTopology N
  letI := lpsOriginalFilledChartedSpace N hN
  chartNormalizedMeromorphicFunction F

lemma lpsOriginalNormalizedFilledFunction_meromorphic
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    lpsOriginalFilledChartMeromorphic N hN (lpsOriginalNormalizedFilledFunction N hN F) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  exact chartNormalizedMeromorphicFunction_meromorphic F hF

lemma lpsOriginalNormalizedFilledFunction_restriction
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    lpsOriginalFilledMeromorphicRestriction N hN (lpsOriginalNormalizedFilledFunction N hN F)
      (lpsOriginalNormalizedFilledFunction_meromorphic N hN F hF) =
    lpsOriginalFilledMeromorphicRestriction N hN F hF := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  apply Subtype.ext
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  have he : F =ᶠ[Filter.codiscrete (LPSOriginalFilledCurve N)] lpsOriginalNormalizedFilledFunction N hN F :=
    chartNormalizedMeromorphicFunction_codiscrete F hF
  have hh : (fun z : ℂ => F (lpsOriginalHolomorphicCovectorProjection N (UpperHalfPlane.ofComplex z)))
      =ᶠ[Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet]
      (fun z : ℂ => lpsOriginalNormalizedFilledFunction N hN F
        (lpsOriginalHolomorphicCovectorProjection N (UpperHalfPlane.ofComplex z))) :=
    (lpsOriginalFilledProjection_tendsto_codiscrete N hN).eventually he
  exact hh.symm

lemma lpsOriginalNormalizedFilledFunction_upstairs_holomorphic
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F)
    (hno : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      ∀ x : MulAction.orbitRel.Quotient
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ,
      0 ≤ meromorphicOrderAt (F ∘ (chartAt ℂ (Sum.inl x : LPSOriginalFilledCurve N)).symm)
        (chartAt ℂ (Sum.inl x : LPSOriginalFilledCurve N) (Sum.inl x))) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun τ : ℍ => lpsOriginalNormalizedFilledFunction N hN F (Sum.inl ⟦τ⟧)) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  intro τ
  let π := lpsOriginalHolomorphicCovectorProjection N
  have hg : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (lpsOriginalNormalizedFilledFunction N hN F) (π τ) := by
    apply contMDiffAt_iff_source.mpr
    rw [contMDiffWithinAt_iff_contDiffWithinAt]
    have ha := chartNormalizedMeromorphicFunction_analyticAt F hF (π τ)
      (chartAt ℂ (π τ) (π τ)) (mem_chart_target ℂ (π τ)) (hno ⟦τ⟧)
    simpa only [extChartAt_coe_symm,extChartAt_coe,modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm,Set.range_id,Function.comp_def,id_eq,
      lpsOriginalNormalizedFilledFunction] using ha.contDiffAt.contDiffWithinAt
  exact (hg.comp τ (lpsOriginalHolomorphicCovectorProjection_contMDiff N hN τ)).mdifferentiableAt (by decide)

lemma lpsOriginalFilledNoInteriorPole_integral
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F)
    (hno : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      ∀ x : MulAction.orbitRel.Quotient
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ,
      0 ≤ meromorphicOrderAt (F ∘ (chartAt ℂ (Sum.inl x : LPSOriginalFilledCurve N)).symm)
        (chartAt ℂ (Sum.inl x : LPSOriginalFilledCurve N) (Sum.inl x))) :
    letI := ((lpsOriginalFullMeromorphicJFractionEmbedding N hN).comp
      (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))).toAlgebra
    IsIntegral (Polynomial ℂ) (lpsOriginalFilledMeromorphicRestriction N hN F hF) := by
  have hi := lpsOriginalFilledHolomorphic_integral N hN
    (lpsOriginalNormalizedFilledFunction N hN F)
    (lpsOriginalNormalizedFilledFunction_meromorphic N hN F hF)
    (lpsOriginalNormalizedFilledFunction_upstairs_holomorphic N hN F hF hno)
  rwa [lpsOriginalNormalizedFilledFunction_restriction] at hi

end
end QEC.Coding.TannerLiftedProduct
