import QEC.Coding.ExpanderCodes.LPSOriginalMeromorphicPoleClearing

/-!
# True cusp clearing and actual same-weight modular ratios

This module belongs to the source-grounded original LPS analytic proof closure.
Milne, *Modular Functions and Modular Forms*, Theorem 6.1 (PDF85 / printed82)
and Propositions 1.16–1.18 motivate the genuine function-field degree argument.
The filled original Gamma0(N) manifold statements retain their proved scope
4 divides N, including the actual theta levels 16*q_graph^2.

The all-meromorphic objects use actual chartwise-meromorphic representatives
and genuine germ equality. They are never defined as the generated C(j,j_N).
The public arbitrary-field/all-rate PK22 theorem, arithmetic normalization,
uniform good reduction and geometric Weil estimate remain further proof work.
-/

namespace QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

/-- Real cusp translations multiply the genuine exponential coordinate by a fixed phase. -/
lemma lpsOriginalMeromorphicCusp_qParam_add (w : ℝ) (z u : ℂ) :
    Function.Periodic.qParam w (z+u) =
      Function.Periodic.qParam w u * Function.Periodic.qParam w z := by
  simp only [Function.Periodic.qParam,mul_add,add_div,Complex.exp_add]
  exact mul_comm _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual cusp representative changes give the SAME filled function a fixed nonzero phase. -/
lemma lpsOriginalFilledMeromorphic_cusp_phase
    (N : ℕ) [NeZero N] (ρ : SL(2,ℤ))
    (F : LPSOriginalFilledCurve N → ℂ) :
    letI := lpsOriginalFilledTopology N
    let c := lpsOriginalCuspOrbit N ρ
    let r := lpsOriginalCuspRepresentative N c
    let w := (lpsOriginalCuspGroup N r).strictWidthInfty
    ∃ α : ℂ, α ≠ 0 ∧ ∀ σ : {τ : ℍ // 1 < τ.im},
      F (Sum.inl (lpsOriginalCuspProjection N ρ σ)) =
        F ((lpsOriginalFilledCuspChart N c).symm
          (α * Function.Periodic.qParam w (σ.val : ℂ))) := by
  let := lpsOriginalFilledTopology N
  let c := lpsOriginalCuspOrbit N ρ
  let r := lpsOriginalCuspRepresentative N c
  let w := (lpsOriginalCuspGroup N r).strictWidthInfty
  obtain ⟨g,hg,x,hx⟩ := lpsOriginalCuspChange_translation N r ρ
    (lpsOriginalCuspRepresentative_orbit N c)
  let d := (Matrix.SpecialLinearGroup.mapGL ℝ r)⁻¹ * g *
    Matrix.SpecialLinearGroup.mapGL ℝ ρ
  let α := Function.Periodic.qParam w (x : ℂ)
  refine ⟨α,Function.Periodic.qParam_ne_zero _,?_⟩
  intro σ
  have hi : 1 < (d • σ.val).im := by
    rw [lpsSignedTranslation_im d x hx]
    exact σ.property
  let τ : {τ : ℍ // 1 < τ.im} := ⟨d • σ.val,hi⟩
  have hp : lpsOriginalCuspProjection N r τ =
      lpsOriginalCuspProjection N ρ σ := by
    apply Quotient.eq.mpr
    rw [MulAction.orbitRel_apply,MulAction.mem_orbit_iff]
    refine ⟨⟨g,hg⟩,?_⟩
    change g • (Matrix.SpecialLinearGroup.mapGL ℝ ρ • σ.val) =
      Matrix.SpecialLinearGroup.mapGL ℝ r • (d • σ.val)
    simp only [d,mul_smul,smul_inv_smul]
  have ht : (τ.val : ℂ) = (σ.val : ℂ)+(x : ℂ) := by
    change ((d • σ.val : ℍ) : ℂ) = _
    dsimp only [d]
    rcases hx with hplus | hminus
    · rw [hplus,lpsUpperRight_smul_coe]
    · rw [hminus,UpperHalfPlane.neg_smul,lpsUpperRight_smul_coe]
  let e := lpsOriginalFilledCuspChart N c
  have hs : Sum.inl (lpsOriginalCuspProjection N r τ) ∈ e.source := ⟨τ,rfl⟩
  have hq : e (Sum.inl (lpsOriginalCuspProjection N r τ)) =
      α * Function.Periodic.qParam w (σ.val : ℂ) := by
    change lpsOriginalFilledCuspPartialEquiv N r
      (Sum.inl (lpsOriginalCuspProjection N r τ)) = _
    rw [lpsOriginalFilledCuspPartialEquiv_projection,ht,
      lpsOriginalMeromorphicCusp_qParam_add]
  rw [←hp,← e.left_inv hs,hq]

/-- The actual analytic coefficient after removing the genuine Delta q-zero. -/
def lpsOriginalMeromorphicDeltaQCoefficient (q : ℂ) : ℂ :=
  dslope (UpperHalfPlane.cuspFunction 1 ModularForm.discriminant) 0 q

/-- The genuine Delta quotient by its q-zero is analytic at zero. -/
lemma lpsOriginalMeromorphicDeltaQCoefficient_analytic :
    AnalyticAt ℂ lpsOriginalMeromorphicDeltaQCoefficient 0 := by
  have hD := ModularFormClass.analyticAt_cuspFunction_zero CuspForm.discriminant
    one_pos one_mem_strictPeriods_SL
  obtain ⟨P,hP⟩ := hD
  exact ⟨P.fslope,hP.has_fpower_series_dslope_fslope⟩

/-- The genuine leading Delta q-coefficient equals one. -/
lemma lpsOriginalMeromorphicDeltaQCoefficient_zero :
    lpsOriginalMeromorphicDeltaQCoefficient 0 = 1 := by
  simpa [lpsOriginalMeromorphicDeltaQCoefficient,dslope_same,
    UpperHalfPlane.qExpansion_coeff,iteratedDeriv_one] using
    ModularForm.discriminant_qExpansion_coeff_one

/-- The SAME actual Delta equals its genuine q-zero times its analytic coefficient. -/
lemma lpsOriginalMeromorphicDeltaQCoefficient_nome (τ : ℍ) :
    ModularForm.discriminant τ = Function.Periodic.qParam 1 (τ : ℂ) *
      lpsOriginalMeromorphicDeltaQCoefficient (Function.Periodic.qParam 1 (τ : ℂ)) := by
  have hD0 := CuspFormClass.cuspFunction_apply_zero CuspForm.discriminant
    one_pos one_mem_strictPeriods_SL
  change UpperHalfPlane.cuspFunction 1 ModularForm.discriminant 0 = 0 at hD0
  have hD : UpperHalfPlane.cuspFunction 1 ModularForm.discriminant
      (Function.Periodic.qParam 1 (τ : ℂ)) = ModularForm.discriminant τ :=
    UpperHalfPlane.eq_cuspFunction τ one_ne_zero
      (SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant
        one_mem_strictPeriods_SL)
  have h := sub_smul_dslope (UpperHalfPlane.cuspFunction 1 ModularForm.discriminant)
    0 (Function.Periodic.qParam 1 (τ : ℂ))
  simpa only [sub_zero,smul_eq_mul,hD,hD0,lpsOriginalMeromorphicDeltaQCoefficient] using h.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual integer widths and local pole orders give an analytic Delta-cleared cusp coefficient. -/
lemma lpsOriginalMeromorphicDelta_cusp_coefficient
    (f : ℂ → ℂ) (n m k : ℕ) (hm : 0 < m) (hnk : n ≤ m*k)
    (hf : AnalyticAt ℂ (fun q => q^n * f q) 0)
    (α : ℂ) (hα : α ≠ 0) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧
      ∀ q : ℂ, H q = (q^m * lpsOriginalMeromorphicDeltaQCoefficient (q^m))^k * f (α*q) := by
  have hD : AnalyticAt ℂ
      (fun q : ℂ => lpsOriginalMeromorphicDeltaQCoefficient (q^m)) 0 :=
    lpsOriginalMeromorphicDeltaQCoefficient_analytic.fun_comp_of_eq
      (analyticAt_id.pow m) (zero_pow hm.ne')
  have hF : AnalyticAt ℂ (fun q : ℂ => (α*q)^n * f (α*q)) 0 :=
    hf.fun_comp_of_eq (analyticAt_const.mul analyticAt_id) (mul_zero α)
  let H : ℂ → ℂ := fun q => (α^n)⁻¹ * q^(m*k-n) *
    lpsOriginalMeromorphicDeltaQCoefficient (q^m)^k * ((α*q)^n * f (α*q))
  have hH : AnalyticAt ℂ H 0 :=
    (((analyticAt_const.mul (analyticAt_id.pow (m*k-n))).mul (hD.pow k)).mul hF)
  refine ⟨H,hH,?_⟩
  intro q
  calc
    H q = (α^n)⁻¹ * α^n * (q^(m*k-n)*q^n) *
        lpsOriginalMeromorphicDeltaQCoefficient (q^m)^k * f (α*q) := by
      dsimp only [H]
      rw [mul_pow]
      ring
    _ = q^(m*k) * lpsOriginalMeromorphicDeltaQCoefficient (q^m)^k * f (α*q) := by
      rw [inv_mul_cancel₀ (pow_ne_zero n hα),one_mul,←pow_add,Nat.sub_add_cancel hnk]
    _ = (q^m * lpsOriginalMeromorphicDeltaQCoefficient (q^m))^k * f (α*q) := by
      rw [mul_pow,pow_mul]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- True cusp phase, integer width and Delta zero make the cleared pullback bounded at infinity. -/
lemma lpsOriginalFilledMeromorphic_delta_cusp_bounded
    (N : ℕ) [NeZero N] (ρ : SL(2,ℤ))
    (F : LPSOriginalFilledCurve N → ℂ) (k : ℕ)
    (hf : letI := lpsOriginalFilledTopology N
      AnalyticAt ℂ (fun q : ℂ => q^k *
      F ((lpsOriginalFilledCuspChart N (lpsOriginalCuspOrbit N ρ)).symm q)) 0) :
    UpperHalfPlane.IsBoundedAtImInfty (fun τ : ℍ =>
      ModularForm.discriminant τ ^ k *
        F (Sum.inl ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧)) := by
  let := lpsOriginalFilledTopology N
  let c := lpsOriginalCuspOrbit N ρ
  let r := lpsOriginalCuspRepresentative N c
  let m := lpsOriginalCuspWidthNat N r
  let w := (lpsOriginalCuspGroup N r).strictWidthInfty
  have hm : 0 < m := lpsOriginalCuspWidthNat_positive N r
  have hw : 0 < w := lpsOriginalCuspGroup_width_positive N r
  obtain ⟨α,hα,hphase⟩ := lpsOriginalFilledMeromorphic_cusp_phase N ρ F
  obtain ⟨H,hH,hEq⟩ := lpsOriginalMeromorphicDelta_cusp_coefficient
    (fun q => F ((lpsOriginalFilledCuspChart N c).symm q)) k m k hm
    (by exact Nat.le_mul_of_pos_left k hm) hf α hα
  have hlim : Tendsto (fun τ : ℍ => H (Function.Periodic.qParam w (τ : ℂ)))
      UpperHalfPlane.atImInfty (𝓝 (H 0)) :=
    hH.continuousAt.tendsto.comp (UpperHalfPlane.qParam_tendsto_atImInfty hw)
  have hq (τ : ℍ) : Function.Periodic.qParam w (τ : ℂ)^m =
      Function.Periodic.qParam 1 (τ : ℂ) := by
    dsimp only [w]
    rw [lpsOriginalCuspWidthNat_cast]
    exact lpsOriginalQParam_width_pow m hm (τ : ℂ)
  have he : (fun τ : ℍ => H (Function.Periodic.qParam w (τ : ℂ))) =ᶠ[
      UpperHalfPlane.atImInfty] (fun τ : ℍ => ModularForm.discriminant τ ^ k *
        F (Sum.inl ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧)) := by
    filter_upwards [Filter.preimage_mem_comap (Filter.Ioi_mem_atTop (1 : ℝ))] with τ hτ
    rw [hEq,hq,←lpsOriginalMeromorphicDeltaQCoefficient_nome]
    rw [←hphase ⟨τ,hτ⟩]
    rfl
  exact (hlim.isBigO_one ℝ).congr' he (Filter.EventuallyEq.refl _ _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- One genuine Delta power makes an arbitrary original meromorphic function bounded at every cusp. -/
lemma lpsOriginalFilledMeromorphic_exists_delta_cusp_bounded
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    ∃ k : ℕ, ∀ ρ : SL(2,ℤ), UpperHalfPlane.IsBoundedAtImInfty
      (fun τ : ℍ => ModularForm.discriminant τ ^ k *
        F (Sum.inl ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧)) := by
  obtain ⟨k,hk⟩ := lpsOriginalFilledMeromorphic_uniform_cusp_pole_clearing N hN F hF
  exact ⟨k,fun ρ => lpsOriginalFilledMeromorphic_delta_cusp_bounded N ρ F k
    (hk (lpsOriginalCuspOrbit N ρ))⟩

/-- Any actual filled-curve function pulls back to a genuine weight-zero invariant. -/
def lpsOriginalFilledFunctionSlashInvariant
    (N : ℕ) (F : LPSOriginalFilledCurve N → ℂ) :
    SlashInvariantForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 0 where
  toFun τ := F (Sum.inl ⟦τ⟧)
  slash_action_eq' g hg := by
    funext τ
    have he : (⟦g • τ⟧ : MulAction.orbitRel.Quotient
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) = ⟦τ⟧ := by
      apply Quotient.sound
      change MulAction.orbitRel
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ (g • τ) τ
      rw [MulAction.orbitRel_apply,MulAction.mem_orbit_iff]
      exact ⟨⟨g,hg⟩,rfl⟩
    simp [ModularForm.slash_def,UpperHalfPlane.σ,
      Subgroup.HasDetOne.det_eq hg,he]

/-- Actual Delta transformation identifies the weight-12k slash with the original cusp pullback. -/
lemma lpsOriginalFilledFunction_delta_slash
    (N : ℕ) (F : LPSOriginalFilledCurve N → ℂ) (k : ℕ) (ρ : SL(2,ℤ)) :
    (fun τ : ℍ => ModularForm.discriminant τ ^ k * F (Sum.inl ⟦τ⟧))
      ∣[((k : ℤ)*12)] ρ =
      (fun τ : ℍ => ModularForm.discriminant τ ^ k *
        F (Sum.inl ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧)) := by
  let D := (CuspForm.discriminant : ModularForm 𝒮ℒ 12).pow k
  have hD : (D : ℍ → ℂ) ∣[(k : ℤ)*12] ρ = D :=
    SlashInvariantForm.slash_action_eqn D _ ⟨ρ,rfl⟩
  have hh := ModularForm.mul_slash_SL2 ((k : ℤ)*12) 0 ρ
    (D : ℍ → ℂ) (fun τ : ℍ => F (Sum.inl ⟦τ⟧))
  rw [add_zero,hD] at hh
  have hfun : (D : ℍ → ℂ) = (fun τ : ℍ => ModularForm.discriminant τ ^ k) := by
    rw [show D = (CuspForm.discriminant : ModularForm 𝒮ℒ 12).pow k from rfl,
      ModularForm.coe_pow]
    rfl
  rw [hfun] at hh
  refine hh.trans ?_
  funext τ
  simp only [Pi.mul_apply,ModularForm.SL_slash_apply,neg_zero,zpow_zero,mul_one]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Construct the actual Delta-cleared modular form from proved holomorphy and cusp boundedness. -/
def lpsOriginalFilledFunctionDeltaModularForm
    (N : ℕ) [NeZero N] (F : LPSOriginalFilledCurve N → ℂ) (k : ℕ)
    (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => F (Sum.inl ⟦τ⟧)))
    (hb : ∀ ρ : SL(2,ℤ), UpperHalfPlane.IsBoundedAtImInfty
      (fun τ : ℍ => ModularForm.discriminant τ ^ k *
        F (Sum.inl ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧))) :
    ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ((k : ℤ)*12) where
  toFun τ := ModularForm.discriminant τ ^ k * F (Sum.inl ⟦τ⟧)
  slash_action_eq' g hg := by
    let D := (CuspForm.discriminant : ModularForm 𝒮ℒ 12).pow k
    have hle : (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ := by
      intro g hg
      obtain ⟨γ,hγ,he⟩ := hg
      exact ⟨γ,he⟩
    have hD := SlashInvariantForm.slash_action_eqn D g (hle hg)
    have hZ := SlashInvariantForm.slash_action_eqn
      (lpsOriginalFilledFunctionSlashInvariant N F) g hg
    have hh := ModularForm.mul_slash ((k : ℤ)*12) 0 g
      (D : ℍ → ℂ) (lpsOriginalFilledFunctionSlashInvariant N F : ℍ → ℂ)
    rw [add_zero,hD,hZ] at hh
    have hd : |(g.det : ℝ)| = 1 := by
      simp [Subgroup.HasDetOne.det_eq hg]
    rw [hd,one_smul] at hh
    have hfun : (D : ℍ → ℂ) = (fun τ : ℍ => ModularForm.discriminant τ ^ k) := by
      rw [show D = (CuspForm.discriminant : ModularForm 𝒮ℒ 12).pow k from rfl,
        ModularForm.coe_pow]
      rfl
    rw [hfun] at hh
    exact hh
  holo' := (ModularFormClass.holo CuspForm.discriminant).pow k |>.mul hF
  bdd_at_cusps' {c} hc := by
    have hcSL := (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))).mp hc
    apply (OnePoint.isBoundedAt_iff_forall_SL2Z hcSL).mpr
    intro ρ hρ
    rw [lpsOriginalFilledFunction_delta_slash]
    exact hb ρ

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Any actual meromorphic function has a proved Delta/P(j)-cleared modular numerator. -/
lemma lpsOriginalFilledMeromorphic_exists_modular_numerator
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    ∃ (P : Polynomial ℂ) (k : ℕ)
      (A : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
        ((k : ℤ)*12)), P.Monic ∧ ∀ τ : ℍ,
      A τ = ModularForm.discriminant τ ^ k *
        P.eval (lpsOriginalJInvariant τ) * F (Sum.inl ⟦τ⟧) := by
  obtain ⟨P,hP,hhol⟩ :=
    lpsOriginalFilledMeromorphic_exists_holomorphic_pole_clearing N hN F hF
  let G : LPSOriginalFilledCurve N → ℂ := fun x =>
    P.eval (lpsOriginalFilledJ N x) * F x
  have hG : lpsOriginalFilledChartMeromorphic N hN G :=
    lpsOriginalFilledChartMeromorphic_mul N hN
      (lpsOriginalFilledChartMeromorphic_polynomial N hN
        (lpsOriginalFilledChartMeromorphic_j N hN) P) hF
  obtain ⟨k,hk⟩ := lpsOriginalFilledMeromorphic_exists_delta_cusp_bounded N hN G hG
  let A := lpsOriginalFilledFunctionDeltaModularForm N G k hhol hk
  refine ⟨P,k,A,hP,?_⟩
  intro τ
  change ModularForm.discriminant τ ^ k *
    (P.eval (lpsOriginalFilledJ N (Sum.inl ⟦τ⟧)) * F (Sum.inl ⟦τ⟧)) = _
  rw [lpsOriginalFilledJ_projection,mul_assoc]

/-- The SAME actual Delta power restricted to the original Gamma0 level. -/
def lpsOriginalMeromorphicDeltaPowerAtLevel
    (N : ℕ) (k : ℕ) :
    ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ((k : ℤ)*12) :=
  let D := (CuspForm.discriminant : ModularForm 𝒮ℒ 12).pow k
  let hle : (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ := by
    intro g hg
    obtain ⟨γ,hγ,he⟩ := hg
    exact ⟨γ,he⟩
  { toFun := D
    slash_action_eq' g hg := D.slash_action_eq' g (hle hg)
    holo' := D.holo'
    bdd_at_cusps' hc := D.bdd_at_cusps' (hc.mono hle) }

/-- The restricted modular form has the literal original Delta-power values. -/
lemma lpsOriginalMeromorphicDeltaPowerAtLevel_apply
    (N k : ℕ) (τ : ℍ) :
    lpsOriginalMeromorphicDeltaPowerAtLevel N k τ = ModularForm.discriminant τ ^ k := by
  change ((CuspForm.discriminant : ModularForm 𝒮ℒ 12).pow k) τ = _
  rw [ModularForm.coe_pow]
  rfl

/-- Faithful original j evaluation makes every nonzero polynomial nonzero somewhere upstairs. -/
lemma lpsOriginalJPolynomial_exists_nonzero
    (P : Polynomial ℂ) (hP : P ≠ 0) :
    ∃ τ : ℍ, P.eval (lpsOriginalJInvariant τ) ≠ 0 := by
  by_contra h
  have he : lpsOriginalJHolomorphicEval P = 0 := by
    apply Subtype.ext
    funext τ
    rw [lpsOriginalJHolomorphicEval_apply]
    exact not_not.mp ((not_exists.mp h) τ)
  apply hP
  apply lpsOriginalJHolomorphicEval_injective
  simpa only [map_zero] using he

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every actual meromorphic function is a ratio of actual same-weight forms with nonzero denominator. -/
lemma lpsOriginalFilledMeromorphic_exists_modular_ratio
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    ∃ (k : ℕ)
      (A B : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
        ((k : ℤ)*12)), B ≠ 0 ∧ ∀ τ : ℍ,
      A τ = B τ * F (Sum.inl ⟦τ⟧) := by
  obtain ⟨P,a,A,hP,hA⟩ :=
    lpsOriginalFilledMeromorphic_exists_modular_numerator N hN F hF
  let J : LPSOriginalFilledCurve N → ℂ := fun x => P.eval (lpsOriginalFilledJ N x)
  have hJ : lpsOriginalFilledChartMeromorphic N hN J :=
    lpsOriginalFilledChartMeromorphic_polynomial N hN
      (lpsOriginalFilledChartMeromorphic_j N hN) P
  obtain ⟨b,hb⟩ := lpsOriginalFilledMeromorphic_exists_delta_cusp_bounded N hN J hJ
  have hjhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => J (Sum.inl ⟦τ⟧)) := by
    have hh := (lpsOriginalJHolomorphicEval P).property
    have he : (lpsOriginalJHolomorphicEval P).val = (fun τ : ℍ => J (Sum.inl ⟦τ⟧)) := by
      funext τ
      exact lpsOriginalJHolomorphicEval_apply P τ
    rw [he] at hh
    exact hh
  let B := lpsOriginalFilledFunctionDeltaModularForm N J b hjhol hb
  let K := a+b
  have hwa : (a : ℤ)*12+(b : ℤ)*12=(K : ℤ)*12 := by
    simp only [K,Nat.cast_add,add_mul]
  have hwb : (b : ℤ)*12+(a : ℤ)*12=(K : ℤ)*12 := by
    simp only [K,Nat.cast_add,add_mul]
    ring
  let A' := (A.mul (lpsOriginalMeromorphicDeltaPowerAtLevel N b)).mcast hwa
  let B' := (B.mul (lpsOriginalMeromorphicDeltaPowerAtLevel N a)).mcast hwb
  have hAval (τ : ℍ) : A' τ = ModularForm.discriminant τ ^ K *
      P.eval (lpsOriginalJInvariant τ) * F (Sum.inl ⟦τ⟧) := by
    dsimp only [A']
    rw [ModularForm.mcast_apply,ModularForm.coe_mul,Pi.mul_apply,hA,
      lpsOriginalMeromorphicDeltaPowerAtLevel_apply]
    dsimp only [K]
    rw [pow_add]
    ring
  have hBval (τ : ℍ) : B' τ = ModularForm.discriminant τ ^ K *
      P.eval (lpsOriginalJInvariant τ) := by
    dsimp only [B']
    rw [ModularForm.mcast_apply,ModularForm.coe_mul,Pi.mul_apply,
      lpsOriginalMeromorphicDeltaPowerAtLevel_apply]
    change (ModularForm.discriminant τ ^ b * P.eval (lpsOriginalJInvariant τ)) *
      ModularForm.discriminant τ ^ a = _
    dsimp only [K]
    rw [pow_add]
    ring
  refine ⟨K,A',B',?_,?_⟩
  · obtain ⟨τ,hτ⟩ := lpsOriginalJPolynomial_exists_nonzero P hP.ne_zero
    intro hzero
    have hh := congrArg (fun f => f τ) hzero
    rw [hBval] at hh
    exact (mul_ne_zero (pow_ne_zero K (ModularForm.discriminant_ne_zero τ)) hτ) hh
  · intro τ
    rw [hAval,hBval]

end
end QEC.Coding.TannerLiftedProduct
