import QEC.Coding.ExpanderCodes.LPSOriginalFilledCusps
import QEC.Coding.ExpanderCodes.LPSCuspDifferentialCharts
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

/-!
# LPSOriginalCuspAnalytic

A genuine original cusp-source point supplies one original Gamma0 witness. Its fixed determinant-one Mobius change gives the actual minimum-width q coordinate locally. Exponential and Mobius calculus prove analyticity and nonzero derivative; neither a chart transition law nor a magnitude law is assumed.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

-- Ordinary calculus closure needed by the genuine mixed transitions; no target atlas laws.
/-- The genuine q exponential composed with a positive-determinant Mobius action is complex analytic. -/
lemma lpsQParam_smul_analytic (h : ℝ) (g : GL (Fin 2) ℝ)
    (hg : 0<g.val.det) (τ : ℍ) :
    AnalyticAt ℂ (fun z : ℂ => Function.Periodic.qParam h ((g • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) τ := by
  let f : ℂ → ℂ := fun z => (g • UpperHalfPlane.ofComplex z : ℍ)
  have ha : AnalyticAt ℂ (Function.Periodic.qParam h) (f (τ:ℂ)) :=
    (Function.Periodic.contDiff_qParam (h:=h) ω).contDiffAt.analyticAt
  simpa only [Function.comp_def,UpperHalfPlane.ofComplex_apply] using
    ha.comp (f:=f) (UpperHalfPlane.analyticAt_smul hg τ)

/-- At nonzero width, the actual q and Mobius derivative formulas give a nonzero composed derivative. -/
lemma lpsQParam_smul_deriv_ne_zero (h : ℝ) (hh : h≠0) (g : GL (Fin 2) ℝ)
    (hg : 0<g.val.det) (τ : ℍ) :
    deriv (fun z : ℂ => Function.Periodic.qParam h ((g • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) τ≠0 := by
  let f : ℂ → ℂ := fun z => (g • UpperHalfPlane.ofComplex z : ℍ)
  have hf := UpperHalfPlane.hasStrictDerivAt_smul hg τ |>.hasDerivAt
  have hq := (Function.Periodic.differentiable_qParam (h:=h)).differentiableAt (x:=f τ)
  change deriv (Function.Periodic.qParam h ∘ f) (τ:ℂ)≠0
  rw [deriv_comp (τ:ℂ) hq hf.differentiableAt,lpsQParam_deriv]
  apply mul_ne_zero
  · exact mul_ne_zero
      (div_ne_zero Complex.two_pi_I_ne_zero (Complex.ofReal_ne_zero.mpr hh))
      (Function.Periodic.qParam_ne_zero (f τ))
  · exact UpperHalfPlane.deriv_smul_ne_zero hg τ

-- A point in the genuine cusp source supplies ONE actual Gamma0 witness.
-- The same fixed Mobius change stays high near the point and gives the actual q formula.
/-- True cusp-source membership supplies a fixed actual original-group Mobius change giving the q-coordinate nearby. -/
lemma lpsOriginalCuspCoordinate_eventually_mobius (N : ℕ) [NeZero N]
    (ρ : SL(2,ℤ)) (τ : ℍ)
    (hx : Sum.inl (Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) τ) ∈
        lpsOriginalFilledCuspSource N ρ) :
    ∃ g : GL (Fin 2) ℝ, g.val.det=1 ∧
      (fun z : ℂ => lpsOriginalFilledCuspPartialEquiv N ρ
        (Sum.inl (Quotient.mk (MulAction.orbitRel
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
          (UpperHalfPlane.ofComplex z)))) =ᶠ[𝓝 (τ:ℂ)]
      (fun z : ℂ => Function.Periodic.qParam (lpsOriginalCuspGroup N ρ).strictWidthInfty
        ((g • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) := by
  let π : ℍ → MulAction.orbitRel.Quotient
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ := Quotient.mk _
  change π τ∈Set.range (lpsOriginalCuspProjection N ρ) at hx
  obtain ⟨σ,hσ⟩ := hx
  have ho := Quotient.eq.mp hσ
  rw [MulAction.orbitRel_apply,MulAction.mem_orbit_iff] at ho
  obtain ⟨γ,hγ⟩ := ho
  let r := Matrix.SpecialLinearGroup.mapGL ℝ ρ
  let g := r⁻¹*γ.val
  have hστ : g • τ=σ.val := by
    dsimp only [g]
    rw [mul_smul]
    change γ.val • τ=r • σ.val at hγ
    rw [hγ]
    exact inv_smul_smul r σ.val
  have hγd : γ.val.val.det=1 := by
    obtain ⟨δ,hδ,he⟩ := γ.property
    rw [←he]
    simp only [←Matrix.GeneralLinearGroup.val_det_apply, Matrix.SpecialLinearGroup.det_mapGL, Units.val_one]
  have hd : g.val.det=1 := by
    change ((r⁻¹*γ.val).val).det=1
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, Matrix.GeneralLinearGroup.coe_inv, Matrix.det_nonsing_inv]
    have hr : r.val.det=1 := by
      simp only [r,←Matrix.GeneralLinearGroup.val_det_apply,Matrix.SpecialLinearGroup.det_mapGL,Units.val_one]
    simp only [hr,hγd,Ring.inverse_one,mul_one]
  have hu : ContinuousAt (fun z : ℂ => g • UpperHalfPlane.ofComplex z) (τ:ℂ) :=
    (continuous_const_smul g).continuousAt.comp
      (UpperHalfPlane.contMDiffAt_ofComplex (n:=ω) τ.im_pos).continuousAt
  have hnear : ∀ᶠ z in 𝓝 (τ:ℂ), 1<(g • UpperHalfPlane.ofComplex z).im := by
    apply (UpperHalfPlane.continuous_im.continuousAt.comp hu)
    change Set.Ioi 1∈𝓝 ((g • UpperHalfPlane.ofComplex (τ:ℂ)).im)
    rw [UpperHalfPlane.ofComplex_apply,hστ]
    exact isOpen_Ioi.mem_nhds σ.property
  refine ⟨g,hd,?_⟩
  filter_upwards [hnear] with z hz
  let σz : {σ : ℍ // 1<σ.im} := ⟨g • UpperHalfPlane.ofComplex z,hz⟩
  have hp : lpsOriginalCuspProjection N ρ σz=π (UpperHalfPlane.ofComplex z) := by
    change π (r • (g • UpperHalfPlane.ofComplex z))=π (UpperHalfPlane.ofComplex z)
    have hr : r*g=γ.val := by dsimp only [g];group
    rw [←mul_smul,hr]
    apply Quotient.sound
    exact ⟨γ,rfl⟩
  have hf := lpsOriginalFilledCuspPartialEquiv_projection N ρ σz
  rw [hp] at hf
  exact hf

/-- The actual original minimal-width cusp coordinate is locally analytic with a proved nonzero derivative. -/
lemma lpsOriginalCuspCoordinate_analytic_deriv (N : ℕ) [NeZero N]
    (ρ : SL(2,ℤ)) (τ : ℍ)
    (hx : Sum.inl (Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) τ) ∈
        lpsOriginalFilledCuspSource N ρ) :
    let f : ℂ → ℂ := fun z => lpsOriginalFilledCuspPartialEquiv N ρ
        (Sum.inl (Quotient.mk (MulAction.orbitRel
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
          (UpperHalfPlane.ofComplex z)))
    AnalyticAt ℂ f (τ:ℂ) ∧ deriv f (τ:ℂ)≠0 := by
  obtain ⟨g,hd,he⟩ := lpsOriginalCuspCoordinate_eventually_mobius N ρ τ hx
  have hg : 0<g.val.det := by rw [hd];norm_num
  constructor
  · exact (lpsQParam_smul_analytic _ g hg τ).congr he.symm
  · rw [he.deriv_eq]
    exact lpsQParam_smul_deriv_ne_zero _
      (lpsOriginalCuspGroup_width_positive N ρ).ne' g hg τ


end
end QEC.Coding.TannerLiftedProduct
