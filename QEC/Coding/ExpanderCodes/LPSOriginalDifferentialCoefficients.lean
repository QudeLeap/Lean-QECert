import QEC.Coding.ExpanderCodes.LPSOriginalFilledAnalytic
import QEC.Coding.ExpanderCodes.LPSOriginalCuspQDifferential

/-!
# LPSOriginalDifferentialCoefficients

Original coefficient calculus and actual Gamma0 lift witnesses prove the minimal-width differential pullback and its analytic and complex-linear cusp behavior.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section

/-- The derivative of the actual inverse chart cancels the forward derivative. -/
lemma lpsOpenPartialHomeomorph_inverse_deriv
    (e : OpenPartialHomeomorph ℂ ℂ) (z : ℂ) (hz : z∈e.source)
    (ha : AnalyticAt ℂ e z) (hd : deriv e z≠0) :
    deriv e.symm (e z) * deriv e z = 1 := by
  have hi := lpsOpenPartialHomeomorph_inverse_analytic e z hz ha hd
  have he : (e.symm∘e) =ᶠ[𝓝 z] id := by
    have hn : ∀ᶠ w in 𝓝 z, w∈e.source := e.open_source.mem_nhds hz
    filter_upwards [hn] with w hw
    exact e.left_inv hw
  calc
    deriv e.symm (e z) * deriv e z = deriv (e.symm∘e) z :=
      (deriv_comp z hi.differentiableAt ha.differentiableAt).symm
    _ = deriv id z := he.deriv_eq
    _ = 1 := deriv_id z

/-- A genuine original Gamma0 group witness gives the local minimal-width Mobius/q formula. -/
lemma lpsOriginalCuspCoordinate_eventually_original_mobius (N : ℕ) [NeZero N]
    (ρ : SL(2,ℤ)) (τ : ℍ)
    (hx : Sum.inl (Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) τ) ∈
        lpsOriginalFilledCuspSource N ρ) :
    ∃ g : GL (Fin 2) ℝ, g.val.det=1 ∧
      (Matrix.SpecialLinearGroup.mapGL ℝ ρ)*g∈
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ∧
      (fun z : ℂ => lpsOriginalFilledCuspPartialEquiv N ρ
        (Sum.inl (Quotient.mk (MulAction.orbitRel
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
          (UpperHalfPlane.ofComplex z)))) =ᶠ[𝓝 (τ:ℂ)]
      (fun z : ℂ => Function.Periodic.qParam (lpsOriginalCuspGroup N ρ).strictWidthInfty
        ((g • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) := by
  let proj : ℍ → MulAction.orbitRel.Quotient
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ := Quotient.mk _
  change proj τ∈Set.range (lpsOriginalCuspProjection N ρ) at hx
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
  have hr : r*g=γ.val := by dsimp only [g];group
  refine ⟨g,hd,?_,?_⟩
  · change r*g∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
    rw [hr]
    exact γ.property
  · filter_upwards [hnear] with z hz
    let σz : {σ : ℍ // 1<σ.im} := ⟨g • UpperHalfPlane.ofComplex z,hz⟩
    have hp : lpsOriginalCuspProjection N ρ σz=proj (UpperHalfPlane.ofComplex z) := by
      change proj (r • (g • UpperHalfPlane.ofComplex z))=proj (UpperHalfPlane.ofComplex z)
      rw [←mul_smul,hr]
      apply Quotient.sound
      exact ⟨γ,rfl⟩
    have hf := lpsOriginalFilledCuspPartialEquiv_projection N ρ σz
    rw [hp] at hf
    exact hf

/-- The derivative of a positive-determinant Mobius product satisfies the actual chain rule. -/
lemma lpsMobius_deriv_mul (r g : GL (Fin 2) ℝ)
    (hr : 0<r.val.det) (hg : 0<g.val.det) (τ : ℍ) :
    deriv (fun z : ℂ => ((r*g) • UpperHalfPlane.ofComplex z : ℍ) : ℂ→ℂ) τ=
      deriv (fun z : ℂ => (r • UpperHalfPlane.ofComplex z : ℍ) : ℂ→ℂ) (g • τ : ℍ) *
      deriv (fun z : ℂ => (g • UpperHalfPlane.ofComplex z : ℍ) : ℂ→ℂ) τ := by
  let a : ℂ→ℂ := fun z => (r • UpperHalfPlane.ofComplex z : ℍ)
  let b : ℂ→ℂ := fun z => (g • UpperHalfPlane.ofComplex z : ℍ)
  have he : (fun z : ℂ => ((r*g) • UpperHalfPlane.ofComplex z : ℍ) : ℂ→ℂ)=a∘b := by
    funext z
    simp only [a,b,Function.comp_def,UpperHalfPlane.ofComplex_apply,mul_smul]
  rw [he]
  have ha : DifferentiableAt ℂ a (b (τ:ℂ)) := by
    simpa only [b,UpperHalfPlane.ofComplex_apply] using
      (UpperHalfPlane.hasStrictDerivAt_smul hr (g • τ)).hasDerivAt.differentiableAt
  have hb : DifferentiableAt ℂ b (τ:ℂ) :=
    (UpperHalfPlane.hasStrictDerivAt_smul hg τ).hasDerivAt.differentiableAt
  simpa only [a,b,UpperHalfPlane.ofComplex_apply] using deriv_comp (τ:ℂ) ha hb

/-- The original removable cusp differential coefficient is analytic on the entire unit disc. -/
lemma lpsOriginalCuspQCoefficient_analytic (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (ρ : SL(2,ℤ)) (q : ℂ) (hq : ‖q‖<1) :
    AnalyticAt ℂ (lpsOriginalCuspQCoefficient N f ρ) q := by
  by_cases hzero : q=0
  · subst q
    exact lpsOriginalCuspQCoefficient_analyticAt_zero N f ρ
  let h := (lpsOriginalCuspGroup N ρ).strictWidthInfty
  let ft := CuspForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ ρ)
  let F := UpperHalfPlane.cuspFunction h ft
  have hh : 0<h := lpsOriginalCuspGroup_width_positive N ρ
  have hp := Subgroup.strictWidthInfty_mem_strictPeriods (lpsOriginalCuspGroup N ρ)
  have hbounded := OnePoint.isBoundedAt_infty_iff.mp
    (ModularFormClass.bdd_at_cusps ft (Subgroup.strictWidthInfty_pos_iff.mp hh))
  have hF : AnalyticAt ℂ F q :=
    (UpperHalfPlane.differentiableOn_cuspFunction_ball hh
      (SlashInvariantFormClass.periodic_comp_ofComplex ft hp)
      (ModularFormClass.holo ft) hbounded).analyticAt
      (Metric.isOpen_ball.mem_nhds (by simpa only [Metric.mem_ball,dist_zero_right] using hq))
  have he : dslope F 0 =ᶠ[𝓝 q] (fun z => (F z-F 0)/z) := by
    have hn : ∀ᶠ z in 𝓝 q, z≠0 := isOpen_compl_singleton.mem_nhds hzero
    filter_upwards [hn] with z hz
    simp only [dslope_of_ne _ hz,slope,vsub_eq_sub,sub_zero,smul_eq_mul,div_eq_mul_inv]
    ring
  have hd : AnalyticAt ℂ (dslope F 0) q :=
    ((hF.sub analyticAt_const).div analyticAt_id hzero).congr he.symm
  exact analyticAt_const.mul hd


/-- The actual cusp coordinate pulls its minimal-width differential back to the original form. -/
lemma lpsOriginalCuspCoordinate_differential_pullback (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (ρ : SL(2,ℤ)) (τ : ℍ)
    (hx : Sum.inl (Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) τ) ∈
        lpsOriginalFilledCuspSource N ρ) :
    let Φ : ℂ→ℂ := fun z => lpsOriginalFilledCuspPartialEquiv N ρ
      (Sum.inl (Quotient.mk (MulAction.orbitRel
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
          (UpperHalfPlane.ofComplex z)))
    lpsOriginalCuspQCoefficient N f ρ (Φ τ) * deriv Φ τ = f τ := by
  obtain ⟨g,hd,hΓ,he⟩ :=
    lpsOriginalCuspCoordinate_eventually_original_mobius N ρ τ hx
  let r := Matrix.SpecialLinearGroup.mapGL ℝ ρ
  let h := (lpsOriginalCuspGroup N ρ).strictWidthInfty
  let b : ℂ→ℂ := fun z => (g • UpperHalfPlane.ofComplex z : ℍ)
  have hg : 0<g.val.det := by rw [hd];norm_num
  have hr : 0<r.val.det := by
    simp only [r,←Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.SpecialLinearGroup.det_mapGL,Units.val_one,zero_lt_one]
  have hc := deriv_comp (τ:ℂ)
    ((Function.Periodic.differentiable_qParam (h:=h)).differentiableAt (x:=b τ))
    ((UpperHalfPlane.hasStrictDerivAt_smul hg τ).hasDerivAt.differentiableAt)
  dsimp only
  rw [he.eq_of_nhds,he.deriv_eq]
  simp only [UpperHalfPlane.ofComplex_apply]
  change lpsOriginalCuspQCoefficient N f ρ (Function.Periodic.qParam h ((g • τ : ℍ) : ℂ)) *
    deriv (Function.Periodic.qParam h ∘ b) τ = _
  rw [hc]
  simp only [b,UpperHalfPlane.ofComplex_apply]
  rw [lpsOriginalCuspQCoefficient_pullback,
    lpsWeightTwo_slash_deriv f r hr]
  rw [mul_assoc,←lpsMobius_deriv_mul r g hr hg τ,←mul_smul]
  have ht := lpsCuspDifferential_Gamma0 N f (r*g) hΓ τ 1
  simpa only [lpsCuspDifferential_apply,mul_one] using ht

/-- The original cusp form is complex analytic in each upper-half-plane coordinate. -/
lemma lpsOriginalCuspForm_ofComplex_analytic (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (τ : ℍ) :
    AnalyticAt ℂ ((f : ℍ→ℂ)∘UpperHalfPlane.ofComplex) (τ:ℂ) := by
  let U : Set ℂ := {z | 0<z.im}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hf : DifferentiableOn ℂ ((f : ℍ→ℂ)∘UpperHalfPlane.ofComplex) U := by
    intro z hz
    exact (UpperHalfPlane.mdifferentiableAt_iff.mp (ModularFormClass.holo f ⟨z,hz⟩)).differentiableWithinAt
  exact hf.analyticAt (hU.mem_nhds τ.im_pos)


/-- The true original quotient local inverse preserves the weight-two differential. -/
lemma lpsGamma0_localInverse_differential_pullback (N : ℕ) [NeZero N] (hN : 4∣N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (σ τ : ℍ)
    (hs : Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) τ∈
      ((lpsGamma0_quotient_localHomeomorph N hN).localInverseAt σ).source) :
    let e := (lpsGamma0_quotient_localHomeomorph N hN).localInverseAt σ
    let proj := Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
    f (e (proj τ)) * deriv (fun z : ℂ => (e (proj (UpperHalfPlane.ofComplex z)) : ℂ)) τ =
      f τ := by
  let hf := lpsGamma0_quotient_localHomeomorph N hN
  let e := hf.localInverseAt σ
  let proj := Quotient.mk (MulAction.orbitRel
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
  let u : ℂ→ℍ := UpperHalfPlane.ofComplex
  let v : ℂ→ℍ := fun z => e (proj (u z))
  have hu : ContinuousAt u (τ:ℂ) :=
    (UpperHalfPlane.contMDiffAt_ofComplex (n:=ω) τ.im_pos).continuousAt
  have hproj : Continuous proj := continuous_quot_mk
  have ht : proj (u τ)=proj τ := by simp [u]
  have hv : ContinuousAt v (τ:ℂ) := by
    apply (e.continuousAt (by simpa only [ht] using hs)).comp
    exact hproj.continuousAt.comp hu
  have he : (fun z => proj (v z)) =ᶠ[𝓝 (τ:ℂ)] (fun z => proj (u z)) := by
    have hsrc : ∀ᶠ z in 𝓝 (τ:ℂ), proj (u z)∈e.source := by
      apply hproj.continuousAt.comp hu
      change e.source∈𝓝 (proj (u τ))
      exact e.open_source.mem_nhds (by simpa only [ht] using hs)
    filter_upwards [hsrc] with z hz
    exact hf.apply_localInverseAt_of_mem hz
  obtain ⟨γ,hγ⟩ := lpsGamma0_lifts_eventually_smul N hN u v τ hu hv he
  have hec : (fun z => (v z:ℂ)) =ᶠ[𝓝 (τ:ℂ)]
      (fun z => (γ.val • UpperHalfPlane.ofComplex z : ℍ)) := by
    filter_upwards [hγ] with z hz
    exact congrArg UpperHalfPlane.coe hz
  have hg := lpsCuspDifferential_Gamma0 N f γ.val γ.property τ 1
  have h0 : f (v (τ:ℂ)) * deriv (fun z => (v z:ℂ)) τ = f τ := by
    rw [hγ.eq_of_nhds,hec.deriv_eq]
    simp only [u,UpperHalfPlane.ofComplex_apply]
    simpa only [lpsCuspDifferential_apply,mul_one] using hg
  simpa only [v,u,UpperHalfPlane.ofComplex_apply] using h0


/-- The actual removable coefficient at a cusp is additive in the original form. -/
lemma lpsOriginalCuspQCoefficient_zero_add (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (ρ : SL(2,ℤ)) : lpsOriginalCuspQCoefficient N (f+g) ρ 0=
      lpsOriginalCuspQCoefficient N f ρ 0+lpsOriginalCuspQCoefficient N g ρ 0 := by
  let r := Matrix.SpecialLinearGroup.mapGL ℝ ρ
  let h := (lpsOriginalCuspGroup N ρ).strictWidthInfty
  let ft := CuspForm.translate f r
  let gt := CuspForm.translate g r
  have hh : 0<h := lpsOriginalCuspGroup_width_positive N ρ
  have hp := Subgroup.strictWidthInfty_mem_strictPeriods (lpsOriginalCuspGroup N ρ)
  have ha := ModularFormClass.analyticAt_cuspFunction_zero ft hh hp
  have hb := ModularFormClass.analyticAt_cuspFunction_zero gt hh hp
  have he : UpperHalfPlane.cuspFunction h (((f+g:_) : ℍ→ℂ) ∣[(2:ℤ)] r)=
      UpperHalfPlane.cuspFunction h ft + UpperHalfPlane.cuspFunction h gt := by
    rw [FunLike.coe_add,SlashAction.add_slash]
    exact ModularForm.cuspFunction_add hh hp ft gt
  simp only [lpsOriginalCuspQCoefficient,dslope_same]
  rw [he,deriv_add ha.differentiableAt hb.differentiableAt,mul_add]
  rfl

/-- The actual removable cusp coefficient is complex-linear under positive-determinant translation. -/
lemma lpsOriginalCuspQCoefficient_zero_smul (N : ℕ) [NeZero N]
    (c : ℂ) (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (ρ : SL(2,ℤ)) : lpsOriginalCuspQCoefficient N (c • f) ρ 0=
      c*lpsOriginalCuspQCoefficient N f ρ 0 := by
  let r := Matrix.SpecialLinearGroup.mapGL ℝ ρ
  let h := (lpsOriginalCuspGroup N ρ).strictWidthInfty
  let ft := CuspForm.translate f r
  have hh : 0<h := lpsOriginalCuspGroup_width_positive N ρ
  have hp := Subgroup.strictWidthInfty_mem_strictPeriods (lpsOriginalCuspGroup N ρ)
  have ha := ModularFormClass.analyticAt_cuspFunction_zero ft hh hp
  have hr : 0<r.val.det := by
    simp only [r,←Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.SpecialLinearGroup.det_mapGL,Units.val_one,zero_lt_one]
  have hσ : UpperHalfPlane.σ r c=c := by
    have hr' : 0<(Matrix.GeneralLinearGroup.det r : ℝ) := by
      simpa only [Matrix.GeneralLinearGroup.val_det_apply] using hr
    rw [UpperHalfPlane.σ,if_pos hr']
    rfl
  have he : UpperHalfPlane.cuspFunction h (((c • f:_) : ℍ→ℂ) ∣[(2:ℤ)] r)=
      c • UpperHalfPlane.cuspFunction h ft := by
    rw [FunLike.coe_smul,ModularForm.smul_slash]
    rw [hσ]
    exact ModularForm.cuspFunction_smul hh hp c ft
  simp only [lpsOriginalCuspQCoefficient,dslope_same]
  rw [he,deriv_const_smul c ha.differentiableAt]
  simp only [smul_eq_mul]
  change (h:ℂ)/((2:ℂ)*Real.pi*I)*(c*deriv (UpperHalfPlane.cuspFunction h ft) 0)=
    c*((h:ℂ)/((2:ℂ)*Real.pi*I)*deriv (UpperHalfPlane.cuspFunction h ft) 0)
  ring

end
end QEC.Coding.TannerLiftedProduct
