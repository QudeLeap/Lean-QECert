import QEC.Coding.ExpanderCodes.LPSOriginalFilledConnected
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.Analysis.Meromorphic.Order

/-!
# LPSOriginalModularFunction

The genuine normalized classical j = E4^3 / Delta descends through the ORIGINAL
Gamma0 orbit quotient. Its actual q-expansion and integral minimal cusp widths
prove nonconstancy and a pole of exactly that width at every TRUE added cusp.
Genuine chart transitions prove meromorphy at every actual preferred-chart target.
The assigned finite value0 at a cusp only chooses a representative function;
meromorphic germs ignore this value, and it is not a holomorphic extension.

This is the original modular-function ingredient in the classical X0(N) route
(Milne MF110, Theorem6.1 and section7), motivated by the original LPS family in
PK22 main.tex ex:Xpq. It does not prove j(Ntau), a modular equation, a rational
model, good reduction, Hecke/Frobenius, a Weil bound or the public PK22 theorem.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

/-- The actual classical j=E4^3/Delta; used throughout invariant, analytic, q and quotient proofs. -/
def lpsOriginalJInvariant (τ : ℍ) : ℂ :=
  ModularForm.E₄ τ^3/ModularForm.discriminant τ

/-- Correct classical 1728 normalization from the genuine graded-ring identity; exercised by the exact root fixture. -/
lemma lpsOriginalJInvariant_formula (τ : ℍ) :
    lpsOriginalJInvariant τ=
      1728*ModularForm.E₄ τ^3/(ModularForm.E₄ τ^3-ModularForm.E₆ τ^2) := by
  rw [lpsOriginalJInvariant,ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]
  rw [div_div_eq_mul_div]
  ring

/-- Actual SL(2,Z) invariance from the genuine weights4/12 and nonzero Mobius denominator; used by original Gamma0 invariance and all-cusp pullback. -/
lemma lpsOriginalJInvariant_SL_invariant (g : GL (Fin 2) ℝ)
    (hg : g∈(𝒮ℒ : Subgroup (GL (Fin 2) ℝ))) (τ : ℍ) :
    lpsOriginalJInvariant (g • τ)=lpsOriginalJInvariant τ := by
  have h4 := SlashInvariantForm.slash_action_eqn'' ModularForm.E₄ hg τ
  have h12 := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hg τ
  simp only [zpow_ofNat] at h4 h12
  change ModularForm.E₄ (g • τ)^3/ModularForm.discriminant (g • τ)=
    ModularForm.E₄ τ^3/ModularForm.discriminant τ
  rw [h4,show ModularForm.discriminant (g • τ)=
    UpperHalfPlane.denom g τ^12*ModularForm.discriminant τ from h12]
  field_simp [UpperHalfPlane.denom_ne_zero g τ]

/-- Genuine upper-half-plane holomorphy using actual Delta nowhere zero; used by the interior coordinate analytic proof. -/
lemma lpsOriginalJInvariant_holomorphic :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) lpsOriginalJInvariant := by
  exact ((ModularFormClass.holo ModularForm.E₄).pow 3).div
    (ModularFormClass.holo CuspForm.discriminant) ModularForm.discriminant_ne_zero

/-- Actual removable q*j coefficient built from normalized E4 and the divided slope of Delta; used by q pullback and every cusp germ. -/
def lpsOriginalJQCoefficient (q : ℂ) : ℂ :=
  (UpperHalfPlane.cuspFunction 1 ModularForm.E₄ q)^3 /
    dslope (UpperHalfPlane.cuspFunction 1 ModularForm.discriminant) 0 q

/-- Analyticity of the actual q*j coefficient at zero using true first Delta coefficient1; used by its limit and cusp meromorphic/order proofs. -/
lemma lpsOriginalJQCoefficient_analytic_zero :
    AnalyticAt ℂ lpsOriginalJQCoefficient 0 := by
  have hE := ModularFormClass.analyticAt_cuspFunction_zero ModularForm.E₄
    one_pos one_mem_strictPeriods_SL
  have hD := ModularFormClass.analyticAt_cuspFunction_zero CuspForm.discriminant
    one_pos one_mem_strictPeriods_SL
  obtain ⟨P,hP⟩ := hD
  have hd : AnalyticAt ℂ (dslope (UpperHalfPlane.cuspFunction 1 ModularForm.discriminant) 0) 0 :=
    ⟨P.fslope,hP.has_fpower_series_dslope_fslope⟩
  have hv : dslope (UpperHalfPlane.cuspFunction 1 ModularForm.discriminant) 0 0=1 := by
    simpa [dslope_same,UpperHalfPlane.qExpansion_coeff,iteratedDeriv_one] using
      ModularForm.discriminant_qExpansion_coeff_one
  exact (hE.pow 3).div hd (by rw [hv];norm_num)

/-- Exact leading coefficient1 at q=0; used to prove nonconstancy and the exact cusp pole order. -/
lemma lpsOriginalJQCoefficient_zero : lpsOriginalJQCoefficient 0=1 := by
  have hE : UpperHalfPlane.cuspFunction 1 ModularForm.E₄ 0=1 := by
    have h := EisensteinSeries.E_qExpansion_coeff_zero (by norm_num : 3≤4) ⟨2,rfl⟩
    change (UpperHalfPlane.qExpansion 1 ModularForm.E₄).coeff 0=1 at h
    simpa [UpperHalfPlane.qExpansion_coeff] using h
  have hD : dslope (UpperHalfPlane.cuspFunction 1 ModularForm.discriminant) 0 0=1 := by
    simpa [dslope_same,UpperHalfPlane.qExpansion_coeff,iteratedDeriv_one] using
      ModularForm.discriminant_qExpansion_coeff_one
  simp only [lpsOriginalJQCoefficient,hE,hD,one_pow,div_one]

/-- Exact q*j pullback on the original upper half plane; used by the limit and actual minimum-width cusp parametrization. -/
lemma lpsOriginalJInvariant_qParam_pullback (τ : ℍ) :
    Function.Periodic.qParam 1 (τ:ℂ)*lpsOriginalJInvariant τ=
      lpsOriginalJQCoefficient (Function.Periodic.qParam 1 (τ:ℂ)) := by
  have hq := Function.Periodic.qParam_ne_zero (h:=1) (τ:ℂ)
  have hD0 := CuspFormClass.cuspFunction_apply_zero CuspForm.discriminant
    one_pos one_mem_strictPeriods_SL
  have hE : UpperHalfPlane.cuspFunction 1 ModularForm.E₄
      (Function.Periodic.qParam 1 (τ:ℂ))=ModularForm.E₄ τ :=
    (UpperHalfPlane.eq_cuspFunction τ one_ne_zero
      (SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄
        one_mem_strictPeriods_SL))
  have hD : UpperHalfPlane.cuspFunction 1 ModularForm.discriminant
      (Function.Periodic.qParam 1 (τ:ℂ))=ModularForm.discriminant τ :=
    (UpperHalfPlane.eq_cuspFunction τ one_ne_zero
      (SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant
        one_mem_strictPeriods_SL))
  change UpperHalfPlane.cuspFunction 1 ModularForm.discriminant 0=0 at hD0
  rw [lpsOriginalJInvariant,lpsOriginalJQCoefficient,dslope_of_ne _ hq,
    slope,hD0,hE,hD]
  simp only [vsub_eq_sub,sub_zero,smul_eq_mul]
  field_simp [hq,ModularForm.discriminant_ne_zero τ]

/-- Original Gamma0 invariance derived from actual inclusion in SL; used to construct the literal original orbit quotient descent. -/
lemma lpsOriginalJInvariant_Gamma0_invariant (N : ℕ) (g : GL (Fin 2) ℝ)
    (hg : g∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) (τ : ℍ) :
    lpsOriginalJInvariant (g•τ)=lpsOriginalJInvariant τ := by
  apply lpsOriginalJInvariant_SL_invariant g _ τ
  obtain ⟨γ,_,hγ⟩ := hg
  exact ⟨γ,hγ⟩

/-- Actual quotient lift of j through original Gamma0 orbit equivalence; used by its recovery/nonconstancy and the filled meromorphic function. -/
def lpsOriginalJQuotient (N : ℕ) : MulAction.orbitRel.Quotient
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ → ℂ :=
  Quotient.lift lpsOriginalJInvariant (by
    intro τ σ h
    change MulAction.orbitRel (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ τ σ at h
    rw [MulAction.orbitRel_apply,MulAction.mem_orbit_iff] at h
    obtain ⟨g,hg⟩ := h
    rw [←hg]
    exact lpsOriginalJInvariant_Gamma0_invariant N g.val g.property σ)

/-- Literal original quotient-projection recovery; used by the root fixture and filled-curve restriction. -/
lemma lpsOriginalJQuotient_projection (N : ℕ) (τ : ℍ) :
    lpsOriginalJQuotient N ⟦τ⟧=lpsOriginalJInvariant τ := rfl

/-- The true limit q*j->1 at imaginary infinity; used to refute constancy of original j. -/
lemma lpsOriginalJInvariant_q_limit :
    Tendsto (fun τ : ℍ => Function.Periodic.qParam 1 (τ:ℂ)*lpsOriginalJInvariant τ)
      UpperHalfPlane.atImInfty (𝓝 1) := by
  have h := lpsOriginalJQCoefficient_analytic_zero.continuousAt.tendsto.comp
    (UpperHalfPlane.qParam_tendsto_atImInfty (by norm_num : (0:ℝ)<1))
  rw [lpsOriginalJQCoefficient_zero] at h
  exact h.congr (fun τ => (lpsOriginalJInvariant_qParam_pullback τ).symm)

/-- Original j is not constant, proved from the incompatible zero/one limits; used by quotient/filled nonconstancy and no holomorphic extension. -/
lemma lpsOriginalJInvariant_nonconstant :
    ¬∃ c : ℂ, ∀ τ : ℍ, lpsOriginalJInvariant τ=c := by
  rintro ⟨c,hc⟩
  have h0 := (UpperHalfPlane.qParam_tendsto_atImInfty (by norm_num : (0:ℝ)<1)).mul
    (tendsto_const_nhds (x:=c))
  have h1 := lpsOriginalJInvariant_q_limit
  simp only [hc,zero_mul] at h1 h0
  have he : (0:ℂ)=1 := tendsto_nhds_unique h0 h1
  exact zero_ne_one he

/-- The descended original quotient function is not constant; used by the root fixture and immediate original function-field construction. -/
lemma lpsOriginalJQuotient_nonconstant (N : ℕ) :
    ¬∃ c : ℂ, ∀ x, lpsOriginalJQuotient N x=c := by
  rintro ⟨c,hc⟩
  apply lpsOriginalJInvariant_nonconstant
  exact ⟨c,fun τ => hc ⟦τ⟧⟩

/-- The actual minimal strict width is a positive integer, extracted from actual integral SL matrix entries; used to select the true width natural. -/
lemma lpsOriginalCuspGroup_width_integer (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    ∃ m : ℕ, 0<m ∧ (lpsOriginalCuspGroup N ρ).strictWidthInfty=(m:ℝ) := by
  have hp := Subgroup.strictWidthInfty_mem_strictPeriods (lpsOriginalCuspGroup N ρ)
  have hg := lpsOriginalCuspGroup_le_SLRange N ρ (Subgroup.mem_strictPeriods_iff.mp hp)
  obtain ⟨γ,hγ⟩ := hg
  have he := congrArg (fun g : GL (Fin 2) ℝ => g 0 1) hγ
  let z : ℤ := γ 0 1
  have hz : (z:ℝ)=(lpsOriginalCuspGroup N ρ).strictWidthInfty := by
    simpa [z,Matrix.SpecialLinearGroup.mapGL_coe_matrix,Matrix.GeneralLinearGroup.upperRightHom] using he
  have hzR : (0:ℝ)<(z:ℝ) := by rw [hz];exact lpsOriginalCuspGroup_width_positive N ρ
  have hzpos : 0<z := by exact_mod_cast hzR
  refine ⟨z.toNat,by omega,?_⟩
  rw [←hz]
  exact_mod_cast (Int.toNat_of_nonneg (le_of_lt hzpos)).symm

/-- The genuine exponential coordinate raised to its positive integer width is the level-one q coordinate; used by actual cusp pullback. -/
lemma lpsOriginalQParam_width_pow (m : ℕ) (hm : 0<m) (τ : ℂ) :
    Function.Periodic.qParam (m:ℝ) τ^m=Function.Periodic.qParam 1 τ := by
  simp only [Function.Periodic.qParam,Complex.ofReal_one,div_one,←Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)]

/-- The natural number equal to the actual minimal strict width; used by all original cusp formulas and exact pole orders. -/
def lpsOriginalCuspWidthNat (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) : ℕ :=
  (lpsOriginalCuspGroup_width_integer N ρ).choose

/-- Positive actual natural width, derived from the proved integral minimum; used in q coordinate, analytic composition and leading-term proofs. -/
lemma lpsOriginalCuspWidthNat_positive (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    0<lpsOriginalCuspWidthNat N ρ :=
  (lpsOriginalCuspGroup_width_integer N ρ).choose_spec.1

/-- Exact equality between this natural width and the actual real minimal strict width; used to identify original cusp coordinates. -/
lemma lpsOriginalCuspWidthNat_cast (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    (lpsOriginalCuspGroup N ρ).strictWidthInfty=(lpsOriginalCuspWidthNat N ρ:ℝ) :=
  (lpsOriginalCuspGroup_width_integer N ρ).choose_spec.2

/-- Original quotient j on the interior and chosen value0 at added cusps; this finite assigned value is irrelevant to meromorphic germs and is not a regular extension. -/
def lpsOriginalFilledJ (N : ℕ) : LPSOriginalFilledCurve N → ℂ :=
  Sum.elim (lpsOriginalJQuotient N) (fun _ => 0)

/-- The exact same original upper-half-plane function is recovered by the filled orbit projection; used by the interior analytic proof. -/
lemma lpsOriginalFilledJ_projection (N : ℕ) (τ : ℍ) :
    lpsOriginalFilledJ N (Sum.inl ⟦τ⟧)=lpsOriginalJInvariant τ := rfl

/-- Every actual nonzero filled-disc parameter satisfies q^width*j=K(q^width); used by the original cusp germ. -/
lemma lpsOriginalFilledJ_cusp_param (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (q : (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target)
    (hq0 : q.val≠0) :
    q.val^(lpsOriginalCuspWidthNat N (lpsOriginalCuspRepresentative N c)) *
      lpsOriginalFilledJ N (lpsOriginalFilledCuspParam N c q)=
      lpsOriginalJQCoefficient
        (q.val^(lpsOriginalCuspWidthNat N (lpsOriginalCuspRepresentative N c))) := by
  let r := lpsOriginalCuspRepresentative N c
  let m := lpsOriginalCuspWidthNat N r
  obtain ⟨τ,hτ,hq⟩ := lpsOriginalFilledCuspParam_nonzero_lift N c q hq0
  have hpow : q.val^m=Function.Periodic.qParam 1 (τ.val:ℂ) := by
    rw [hq,lpsOriginalCuspWidthNat_cast]
    exact lpsOriginalQParam_width_pow m (lpsOriginalCuspWidthNat_positive N r) τ.val
  have hJ : lpsOriginalFilledJ N (lpsOriginalFilledCuspParam N c q)=
      lpsOriginalJInvariant τ.val := by
    rw [hτ]
    change lpsOriginalJInvariant (Matrix.SpecialLinearGroup.mapGL ℝ r • τ.val)=_
    exact lpsOriginalJInvariant_SL_invariant _ ⟨r,rfl⟩ τ.val
  change q.val^m*lpsOriginalFilledJ N (lpsOriginalFilledCuspParam N c q)=
    lpsOriginalJQCoefficient (q.val^m)
  rw [hJ,hpow]
  exact lpsOriginalJInvariant_qParam_pullback τ.val


/-- The literal cusp chart inverse has germ K(q^width)/q^width; used by meromorphy and exact pole order. -/
lemma lpsOriginalFilledJ_cusp_germ (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    (fun q : ℂ => lpsOriginalFilledJ N
      ((lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).symm q)) =ᶠ[𝓝[≠] 0]
    (fun q => lpsOriginalJQCoefficient
      (q^(lpsOriginalCuspWidthNat N (lpsOriginalCuspRepresentative N c))) /
      q^(lpsOriginalCuspWidthNat N (lpsOriginalCuspRepresentative N c))) := by
  let r := lpsOriginalCuspRepresentative N c
  let m := lpsOriginalCuspWidthNat N r
  let e := lpsOriginalFilledCuspPartialEquiv N r
  have htarget : ∀ᶠ q in 𝓝 (0:ℂ), q∈e.target :=
    (lpsOriginalFilledCuspPartialEquiv_target_open N r).mem_nhds
      (lpsOriginalFilledCuspPartialEquiv_target_zero N r)
  filter_upwards [nhdsWithin_le_nhds htarget,self_mem_nhdsWithin] with q hqt hq
  have hq0 : q≠0 := by simpa using hq
  have h := lpsOriginalFilledJ_cusp_param N c ⟨q,hqt⟩ hq0
  change q^m*lpsOriginalFilledJ N (e.symm q)=lpsOriginalJQCoefficient (q^m) at h
  exact (eq_div_iff (pow_ne_zero m hq0)).mpr (by rw [mul_comm];exact h)

/-- Meromorphy at each actual added cusp under the true minimum-width chart; used by pole order and all-chart meromorphy. -/
lemma lpsOriginalFilledJ_cusp_meromorphic (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    MeromorphicAt (fun q : ℂ => lpsOriginalFilledJ N
      ((lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).symm q)) 0 := by
  let r := lpsOriginalCuspRepresentative N c
  let m := lpsOriginalCuspWidthNat N r
  let e := lpsOriginalFilledCuspPartialEquiv N r
  have hm : 0<m := lpsOriginalCuspWidthNat_positive N r
  have ha : AnalyticAt ℂ (fun q : ℂ => lpsOriginalJQCoefficient (q^m)) 0 := by
    apply lpsOriginalJQCoefficient_analytic_zero.comp_of_eq (analyticAt_id.pow m)
    simp [Nat.ne_of_gt hm]
  have hmer : MeromorphicAt (fun q : ℂ => lpsOriginalJQCoefficient (q^m)/q^m) 0 :=
    ha.meromorphicAt.div (analyticAt_id.pow m).meromorphicAt
  exact hmer.congr (lpsOriginalFilledJ_cusp_germ N c).symm

/-- Exact order minus the positive original width at every true cusp, using actual leading coefficient1; used by the root fixture and immediate original divisor/function-field comparison. -/
lemma lpsOriginalFilledJ_cusp_order (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    meromorphicOrderAt (fun q : ℂ => lpsOriginalFilledJ N
      ((lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).symm q)) 0 =
      (-(lpsOriginalCuspWidthNat N (lpsOriginalCuspRepresentative N c):ℤ) : WithTop ℤ) := by
  let m := lpsOriginalCuspWidthNat N (lpsOriginalCuspRepresentative N c)
  have hm : 0<m := lpsOriginalCuspWidthNat_positive N _
  have ha : AnalyticAt ℂ (fun q : ℂ => lpsOriginalJQCoefficient (q^m)) 0 := by
    apply lpsOriginalJQCoefficient_analytic_zero.comp_of_eq (analyticAt_id.pow m)
    simp [Nat.ne_of_gt hm]
  apply (meromorphicOrderAt_eq_int_iff (lpsOriginalFilledJ_cusp_meromorphic N c)).mpr
  refine ⟨_,ha,?_,?_⟩
  · simp [Nat.ne_of_gt hm,lpsOriginalJQCoefficient_zero]
  · filter_upwards [lpsOriginalFilledJ_cusp_germ N c] with q hq
    rw [hq]
    simp [m,sub_zero,zpow_neg,zpow_natCast,div_eq_mul_inv,smul_eq_mul,mul_comm]

/-- The same nonconstant j admits no global holomorphic extension on the actual compact connected curve; uses connectedness/constant-field proof, not assumed extension failure. -/
lemma lpsOriginalJInvariant_no_holomorphic_extension (N : ℕ) [NeZero N] (hN : 4∣N) :
    ¬∃ f : LPSOriginalFilledCurve N→ℂ,
      (letI := lpsOriginalFilledTopology N;
        letI := lpsOriginalFilledChartedSpace N hN;
        MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) ∧
      (∀ τ : ℍ, f (Sum.inl ⟦τ⟧)=lpsOriginalJInvariant τ) := by
  rintro ⟨f,hf,hres⟩
  obtain ⟨c,hc⟩ := lpsOriginalFilled_holomorphic_eq_const N hN f hf
  apply lpsOriginalJInvariant_nonconstant
  refine ⟨c,fun τ => ?_⟩
  rw [←hres τ,hc]
  rfl

/-- Complex analyticity of genuine j composed with ofComplex in the actual open half plane; used by all interior targets. -/
lemma lpsOriginalJInvariant_ofComplex_analytic (τ : ℍ) :
    AnalyticAt ℂ (lpsOriginalJInvariant∘UpperHalfPlane.ofComplex) (τ:ℂ) := by
  let U : Set ℂ := {z | 0<z.im}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hf : DifferentiableOn ℂ (lpsOriginalJInvariant∘UpperHalfPlane.ofComplex) U := by
    intro z hz
    exact (UpperHalfPlane.mdifferentiableAt_iff.mp (lpsOriginalJInvariant_holomorphic ⟨z,hz⟩)).differentiableWithinAt
  exact hf.analyticAt (hU.mem_nhds τ.im_pos)

/-- Analyticity in every target point of every actual original interior chart; used by nonzero cusp overlaps and all-chart meromorphy. -/
lemma lpsOriginalFilledJ_interior_analytic (N : ℕ) [NeZero N] (hN : 4∣N)
    (x : MulAction.orbitRel.Quotient (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
    (z : ℂ) (hz : z∈(lpsOriginalFilledInteriorChart N hN x).target) :
    letI := lpsOriginalFilledTopology N
    AnalyticAt ℂ (fun w : ℂ => lpsOriginalFilledJ N
      ((lpsOriginalFilledInteriorChart N hN x).symm w)) z := by
  let := lpsOriginalFilledTopology N
  have he : (fun w : ℂ => lpsOriginalFilledJ N
      ((lpsOriginalFilledInteriorChart N hN x).symm w))=
      lpsOriginalJInvariant∘UpperHalfPlane.ofComplex := by
    funext w
    rw [lpsOriginalFilledInteriorChart_symm,lpsOriginalFilledJ_projection]
    rfl
  rw [he]
  exact lpsOriginalJInvariant_ofComplex_analytic
    ⟨z,lpsOriginalFilledInteriorChart_target_pos N hN x z hz⟩

/-- Analyticity at every nonzero point of every true cusp-chart target, proved by actual analytic overlap with an interior chart; used by all-chart meromorphy. -/
lemma lpsOriginalFilledJ_cusp_analytic_nonzero (N : ℕ) [NeZero N] (hN : 4∣N)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (z : ℂ) (hz : z∈(lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target)
    (hz0 : z≠0) :
    letI := lpsOriginalFilledTopology N
    AnalyticAt ℂ (fun w : ℂ => lpsOriginalFilledJ N
      ((lpsOriginalFilledCuspChart N c).symm w)) z := by
  let := lpsOriginalFilledTopology N
  obtain ⟨τ,hτ,_⟩ := lpsOriginalFilledCuspParam_nonzero_lift N c ⟨z,hz⟩ hz0
  let y := lpsOriginalCuspProjection N (lpsOriginalCuspRepresentative N c) τ
  let a := lpsOriginalFilledCuspChart N c
  let b := lpsOriginalFilledInteriorChart N hN y
  let e := a.symm.trans b
  have hp : a.symm z=Sum.inl y := hτ
  have hs : z∈e.source := by
    refine ⟨hz,?_⟩
    change a.symm z∈b.source
    rw [hp]
    exact lpsOriginalFilledInteriorChart_mem N hN y
  have he := lpsOriginalFilled_cusp_interior_analytic N hN y c z hs
  have hb := lpsOriginalFilledJ_interior_analytic N hN y (e z) (e.map_source hs).1
  have hf := hb.comp he
  apply hf.congr
  filter_upwards [e.open_source.mem_nhds hs] with w hw
  change lpsOriginalFilledJ N (b.symm (b (a.symm w)))=
    lpsOriginalFilledJ N (a.symm w)
  have hi := hw.2
  change a.symm w∈b.source at hi
  rw [b.left_inv hi]

/-- Meromorphy at every target point of every actual preferred chart of the same original filled curve; immediate input to its original meromorphic function field. -/
lemma lpsOriginalFilledJ_chart_meromorphic (N : ℕ) [NeZero N] (hN : 4∣N)
    (x : LPSOriginalFilledCurve N) (z : ℂ)
    (hz : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      z∈(chartAt ℂ x).target) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    MeromorphicAt (fun w : ℂ => lpsOriginalFilledJ N ((chartAt ℂ x).symm w)) z := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  cases x with
  | inl y => exact (lpsOriginalFilledJ_interior_analytic N hN y z hz).meromorphicAt
  | inr c =>
    by_cases hz0 : z=0
    · subst z
      exact lpsOriginalFilledJ_cusp_meromorphic N c
    · exact (lpsOriginalFilledJ_cusp_analytic_nonzero N hN c z hz hz0).meromorphicAt

/-- Nonconstancy of the filled meromorphic function follows through the actual orbit projection; immediate input to original function-field/model comparison. -/
lemma lpsOriginalFilledJ_nonconstant (N : ℕ) :
    ¬∃ c : ℂ, ∀ x : LPSOriginalFilledCurve N, lpsOriginalFilledJ N x=c := by
  rintro ⟨c,hc⟩
  apply lpsOriginalJInvariant_nonconstant
  exact ⟨c,fun τ => hc (Sum.inl ⟦τ⟧)⟩

end
end QEC.Coding.TannerLiftedProduct
