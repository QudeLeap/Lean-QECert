import QEC.Coding.ExpanderCodes.LPSOriginalFilledCharts
import QEC.Coding.ExpanderCodes.LPSOriginalCuspAnalytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
# LPSOriginalFilledAnalytic

Prove the actual filled original curve is a complex analytic manifold: original transitions are inherited, mixed transitions use the genuine Mobius/q formula and inverse theorem, and true cusp transitions are disjoint or identity. The original inclusion and projection remain analytic at every nonzero level divisible by four. Differential gluing, original arithmetic model, good reduction, Hecke/Frobenius/Jacobian/Rosati magnitude and PK22 main remain unproved.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

-- This general theorem proves the reverse analytic direction from ACTUAL inverse laws.
/-- A true complex partial homeomorphism with analytic nonzero derivative has an analytic inverse by its actual inverse laws. -/
lemma lpsOpenPartialHomeomorph_inverse_analytic
    (e : OpenPartialHomeomorph ℂ ℂ) (z : ℂ) (hz : z∈e.source)
    (ha : AnalyticAt ℂ e z) (hd : deriv e z≠0) :
    AnalyticAt ℂ e.symm (e z) := by
  apply (analyticAt_comp_iff_of_deriv_ne_zero ha hd).mp
  apply analyticAt_id.congr
  have hn : ∀ᶠ z' in 𝓝 z, z'∈e.source := e.open_source.mem_nhds hz
  filter_upwards [hn] with z' hz'
  exact (e.left_inv hz').symm

/-- The real interior-to-cusp transition has the genuine analytic Mobius/q formula and nonzero derivative. -/
lemma lpsOriginalFilled_interior_cusp_analytic (N : ℕ) [NeZero N] (hN : 4∣N)
    (x : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (z : ℂ) (hz : letI := lpsOriginalFilledTopology N
      z∈((lpsOriginalFilledInteriorChart N hN x).symm.trans
      (lpsOriginalFilledCuspChart N c)).source) :
    letI := lpsOriginalFilledTopology N
    let e := (lpsOriginalFilledInteriorChart N hN x).symm.trans
      (lpsOriginalFilledCuspChart N c)
    AnalyticAt ℂ e z ∧ deriv e z≠0 := by
  let := lpsOriginalFilledTopology N
  change z∈(lpsOriginalFilledInteriorChart N hN x).target ∧
    (lpsOriginalFilledInteriorChart N hN x).symm z∈
      (lpsOriginalFilledCuspChart N c).source at hz
  have hpos := lpsOriginalFilledInteriorChart_target_pos N hN x z hz.1
  let τ : ℍ := ⟨z,hpos⟩
  have hx := hz.2
  rw [lpsOriginalFilledInteriorChart_symm] at hx
  rw [lpsOriginalFilledCuspChart_source,UpperHalfPlane.ofComplex_apply_of_im_pos hpos] at hx
  have ha := lpsOriginalCuspCoordinate_analytic_deriv N
    (lpsOriginalCuspRepresentative N c) τ hx
  have he : (((lpsOriginalFilledInteriorChart N hN x).symm.trans
      (lpsOriginalFilledCuspChart N c)) : ℂ → ℂ)=
      (fun w : ℂ => lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)
        (Sum.inl (Quotient.mk (MulAction.orbitRel
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
          (UpperHalfPlane.ofComplex w)))) := by
    funext w
    rw [OpenPartialHomeomorph.trans_apply,lpsOriginalFilledInteriorChart_symm]
    rfl
  dsimp only
  rw [he]
  exact ha

/-- The real reverse mixed transition is analytic by the actual inverse-function theorem and chart inverse laws. -/
lemma lpsOriginalFilled_cusp_interior_analytic (N : ℕ) [NeZero N] (hN : 4∣N)
    (x : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (z : ℂ) (hz : letI := lpsOriginalFilledTopology N
      z∈((lpsOriginalFilledCuspChart N c).symm.trans
        (lpsOriginalFilledInteriorChart N hN x)).source) :
    letI := lpsOriginalFilledTopology N
    AnalyticAt ℂ ((lpsOriginalFilledCuspChart N c).symm.trans
      (lpsOriginalFilledInteriorChart N hN x)) z := by
  let := lpsOriginalFilledTopology N
  let e := (lpsOriginalFilledCuspChart N c).symm.trans
    (lpsOriginalFilledInteriorChart N hN x)
  have hf := lpsOriginalFilled_interior_cusp_analytic N hN x c (e z)
    (e.map_source hz)
  have hi := lpsOpenPartialHomeomorph_inverse_analytic e.symm (e z)
    (e.map_source hz) hf.1 hf.2
  simpa only [OpenPartialHomeomorph.symm_symm,e.left_inv hz] using hi

/-- Distinct actual cusp chart sources are disjoint; the same selected cusp gives a locally identity analytic transition. -/
lemma lpsOriginalFilled_cusp_cusp_analytic (N : ℕ) [NeZero N]
    (c d : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (z : ℂ) (hz : letI := lpsOriginalFilledTopology N
      z∈((lpsOriginalFilledCuspChart N c).symm.trans
        (lpsOriginalFilledCuspChart N d)).source) :
    letI := lpsOriginalFilledTopology N
    AnalyticAt ℂ ((lpsOriginalFilledCuspChart N c).symm.trans
      (lpsOriginalFilledCuspChart N d)) z := by
  let := lpsOriginalFilledTopology N
  by_cases hcd : c=d
  · subst d
    apply analyticAt_id.congr
    have hn : ∀ᶠ w in 𝓝 z, w∈(lpsOriginalFilledCuspChart N c).target :=
      (lpsOriginalFilledCuspChart N c).open_target.mem_nhds hz.1
    filter_upwards [hn] with w hw
    exact ((lpsOriginalFilledCuspChart N c).right_inv hw).symm
  · have hd := lpsOriginalFilledCuspPartialEquiv_sources_disjoint N
      (lpsOriginalCuspRepresentative N c) (lpsOriginalCuspRepresentative N d)
      (by simpa only [lpsOriginalCuspRepresentative_orbit] using hcd)
    exact False.elim (Set.disjoint_left.mp hd
      ((lpsOriginalFilledCuspChart N c).map_target hz.1) hz.2)

/-- The same original filled topology and explicitly constructed atlas form a complex analytic manifold for nonzero levels divisible by four. -/
lemma lpsOriginalFilled_isManifold (N : ℕ) [NeZero N] (hN : 4∣N) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    IsManifold 𝓘(ℂ) ω (LPSOriginalFilledCurve N) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  apply isManifold_of_contDiffOn 𝓘(ℂ) ω (LPSOriginalFilledCurve N)
  intro a b ha hb
  change a∈Set.range (lpsOriginalFilledInteriorChart N hN) ∪
    Set.range (lpsOriginalFilledCuspChart N) at ha
  change b∈Set.range (lpsOriginalFilledInteriorChart N hN) ∪
    Set.range (lpsOriginalFilledCuspChart N) at hb
  rcases ha with ⟨x,rfl⟩|⟨c,rfl⟩ <;> rcases hb with ⟨y,rfl⟩|⟨d,rfl⟩
  · let := lpsGamma0QuotientChartedSpace N hN
    let := lpsGamma0Quotient_isManifold N hN
    have hc := IsManifold.compatible_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I:=𝓘(ℂ)) (n:=ω) x)
      (IsManifold.chart_mem_maximalAtlas (I:=𝓘(ℂ)) (n:=ω) y)
    have hf := (mem_groupoid_of_pregroupoid.mpr hc).1
    simpa only [lpsOriginalFilledInteriorChart,
      OpenPartialHomeomorph.lift_openEmbedding_trans,contDiffPregroupoid] using hf
  · intro z hz
    have ht := (lpsOriginalFilled_interior_cusp_analytic N hN x d z hz.1).1
    simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
      Function.comp_def,id_eq] using ht.contDiffAt (n:=ω) |>.contDiffWithinAt
  · intro z hz
    have ht := lpsOriginalFilled_cusp_interior_analytic N hN y c z hz.1
    simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
      Function.comp_def,id_eq] using ht.contDiffAt (n:=ω) |>.contDiffWithinAt
  · intro z hz
    have ht := lpsOriginalFilled_cusp_cusp_analytic N c d z hz.1
    simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
      Function.comp_def,id_eq] using ht.contDiffAt (n:=ω) |>.contDiffWithinAt

/-- The actual original interior inclusion remains complex analytic in the preserved lifted charts. -/
lemma lpsOriginalFilled_interior_contMDiff (N : ℕ) [NeZero N] (hN : 4∣N) :
    letI := lpsOriginalFilledTopology N
    letI := lpsGamma0QuotientChartedSpace N hN
    letI := lpsOriginalFilledChartedSpace N hN
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (Sum.inl : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ → LPSOriginalFilledCurve N) := by
  let := lpsOriginalFilledTopology N
  let := lpsGamma0QuotientChartedSpace N hN
  let := lpsOriginalFilledChartedSpace N hN
  intro x
  apply contMDiffAt_iff.mpr
  refine ⟨(lpsOriginalFilledTopology_interior_continuous N).continuousAt,?_⟩
  have hid := (contMDiffAt_iff.mp (contMDiff_id (I:=𝓘(ℂ)) (n:=ω) x)).2
  have hc : chartAt ℂ (Sum.inl x : LPSOriginalFilledCurve N)=
      (chartAt ℂ x).lift_openEmbedding (lpsOriginalFilledTopology_interior_openEmbedding N) := rfl
  simpa only [extChartAt_coe,extChartAt_coe_symm,modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm,hc,Function.comp_def,id_eq,
    OpenPartialHomeomorph.lift_openEmbedding_apply] using hid

/-- The original upper-half-plane orbit projection into the same filled curve is complex analytic. -/
lemma lpsOriginalFilled_projection_contMDiff (N : ℕ) [NeZero N] (hN : 4∣N) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun τ : ℍ => (Sum.inl (Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) τ) : LPSOriginalFilledCurve N)) := by
  let := lpsOriginalFilledTopology N
  let := lpsGamma0QuotientChartedSpace N hN
  let := lpsOriginalFilledChartedSpace N hN
  exact (lpsOriginalFilled_interior_contMDiff N hN).comp
    (lpsGamma0Quotient_projection_contMDiff N hN)

/-- Every nonzero original theta level has the genuine filled complex analytic structure, without a spectral or arithmetic magnitude assumption. -/
lemma lpsOriginalThetaLevel_filled_isManifold (q : ℕ) (hq : q≠0) :
    let : NeZero ((4*q)^2) := ⟨by positivity⟩
    letI := lpsOriginalFilledTopology ((4*q)^2)
    letI := lpsOriginalFilledChartedSpace ((4*q)^2)
      (dvd_pow (dvd_mul_right 4 q) (by decide))
    IsManifold 𝓘(ℂ) ω (LPSOriginalFilledCurve ((4*q)^2)) := by
  let : NeZero ((4*q)^2) := ⟨by positivity⟩
  exact lpsOriginalFilled_isManifold ((4*q)^2)
    (dvd_pow (dvd_mul_right 4 q) (by decide))


end
end QEC.Coding.TannerLiftedProduct
