import QEC.Coding.ExpanderCodes.LPSOriginalLevelCuspArithmetic
import QEC.Coding.ExpanderCodes.LPSOriginalFilledAnalytic
import Mathlib.Topology.Maps.Proper.Basic
/-!
# LPSOriginalLevelMapGeometry

Prove actual cusp-representative width invariance and full preferred-coordinate power/phase
transport for the SAME original modular level map. The whole actual filled map is continuous
and proper at every nonzero level, and complex analytic when the lower level is divisible
by four. The positive local exponent is the true original cusp-width ratio.

This internal proof closure gives no global cover degree, second Hecke degeneracy map,
arithmetic normalization transport, uniform good reduction, Hecke/Frobenius/Weil bound,
LPS spectral estimate or PK22 main theorem. Parent #449 remains open and unproved.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

/-- A genuine signed cusp translation commutes with every strict-period translation. -/
lemma lpsSignedTranslation_commute_period (g : GL (Fin 2) ℝ) (x t : ℝ)
    (hg : g = Matrix.GeneralLinearGroup.upperRightHom x ∨
      g = -Matrix.GeneralLinearGroup.upperRightHom x) :
    g * Matrix.GeneralLinearGroup.upperRightHom t =
      Matrix.GeneralLinearGroup.upperRightHom t * g := by
  have hc : Matrix.GeneralLinearGroup.upperRightHom x * Matrix.GeneralLinearGroup.upperRightHom t =
      Matrix.GeneralLinearGroup.upperRightHom t * Matrix.GeneralLinearGroup.upperRightHom x := by
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_comm]
  rcases hg with rfl | rfl
  · exact hc
  · simpa only [neg_mul, mul_neg] using congrArg Neg.neg hc

/-- Conjugating a period by a genuine signed translation leaves that period unchanged. -/
lemma lpsSignedTranslation_conjugate_period (g : GL (Fin 2) ℝ) (x t : ℝ)
    (hg : g = Matrix.GeneralLinearGroup.upperRightHom x ∨
      g = -Matrix.GeneralLinearGroup.upperRightHom x) :
    g * Matrix.GeneralLinearGroup.upperRightHom t * g⁻¹ =
      Matrix.GeneralLinearGroup.upperRightHom t := by
  rw [lpsSignedTranslation_commute_period g x t hg, mul_assoc, mul_inv_cancel, mul_one]

/-- Actual orbit changes conjugate period membership within the SAME original Gamma0 group. -/
lemma lpsOriginalCuspGroup_periods_le_of_orbit_eq (N : ℕ) [NeZero N]
    (ρ ρ' : SL(2, ℤ)) (h : lpsOriginalCuspOrbit N ρ = lpsOriginalCuspOrbit N ρ') :
    (lpsOriginalCuspGroup N ρ').strictPeriods ≤ (lpsOriginalCuspGroup N ρ).strictPeriods := by
  obtain ⟨g, hg, x, hx⟩ := lpsOriginalCuspChange_translation N ρ ρ' h
  let r := Matrix.SpecialLinearGroup.mapGL ℝ ρ
  let e := Matrix.SpecialLinearGroup.mapGL ℝ ρ'
  let d := r⁻¹ * g * e
  intro t ht
  have hp := Subgroup.mem_strictPeriods_iff.mp ht
  apply Subgroup.mem_strictPeriods_iff.mpr
  rw [lpsOriginalCuspGroup, ConjAct.toConjAct_inv,
    Subgroup.mem_inv_pointwise_smul_iff, ConjAct.toConjAct_smul] at hp ⊢
  change e * Matrix.GeneralLinearGroup.upperRightHom t * e⁻¹ ∈
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) at hp
  change r * Matrix.GeneralLinearGroup.upperRightHom t * r⁻¹ ∈
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
  have he : r * Matrix.GeneralLinearGroup.upperRightHom t * r⁻¹ =
      g * (e * Matrix.GeneralLinearGroup.upperRightHom t * e⁻¹) * g⁻¹ := by
    calc
      _ = r * (d * Matrix.GeneralLinearGroup.upperRightHom t * d⁻¹) * r⁻¹ := by
        rw [lpsSignedTranslation_conjugate_period d x t hx]
      _ = _ := by
        dsimp only [d]
        simp only [mul_inv_rev,inv_inv,mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one]
  rw [he]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hp) (Subgroup.inv_mem _ hg)

/-- Actual period transport makes one genuine positive minimal cusp width divide the other. -/
lemma lpsOriginalCuspWidthNat_dvd_of_orbit_eq (N : ℕ) [NeZero N]
    (ρ ρ' : SL(2, ℤ)) (h : lpsOriginalCuspOrbit N ρ = lpsOriginalCuspOrbit N ρ') :
    lpsOriginalCuspWidthNat N ρ ∣ lpsOriginalCuspWidthNat N ρ' := by
  have hp := lpsOriginalCuspGroup_periods_le_of_orbit_eq N ρ ρ' h
    (Subgroup.strictWidthInfty_mem_strictPeriods (lpsOriginalCuspGroup N ρ'))
  rw [lpsOriginalCuspGroup_periods_generated] at hp
  obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp hp
  rw [lpsOriginalCuspWidthNat_cast, lpsOriginalCuspWidthNat_cast] at hz
  exact lpsOriginalCuspWidth_dvd_of_positive_zmultiple _ _
    (lpsOriginalCuspWidthNat_positive N ρ) (lpsOriginalCuspWidthNat_positive N ρ') z hz

/-- The true minimal natural cusp width is independent of the integral orbit representative. -/
lemma lpsOriginalCuspWidthNat_eq_of_orbit_eq (N : ℕ) [NeZero N]
    (ρ ρ' : SL(2, ℤ)) (h : lpsOriginalCuspOrbit N ρ = lpsOriginalCuspOrbit N ρ') :
    lpsOriginalCuspWidthNat N ρ = lpsOriginalCuspWidthNat N ρ' :=
  Nat.dvd_antisymm (lpsOriginalCuspWidthNat_dvd_of_orbit_eq N ρ ρ' h)
    (lpsOriginalCuspWidthNat_dvd_of_orbit_eq N ρ' ρ h.symm)

/-- Changing a genuine lower-level representative preserves actual higher-level width divisibility. -/
lemma lpsOriginalCuspWidthNat_dvd_of_level_orbit_eq (N M : ℕ) [NeZero N] [NeZero M]
    (hNM : N ∣ M) (ρ ρ' : SL(2, ℤ))
    (h : lpsOriginalCuspOrbit N ρ = lpsOriginalCuspOrbit N ρ') :
    lpsOriginalCuspWidthNat N ρ ∣ lpsOriginalCuspWidthNat M ρ' := by
  rw [lpsOriginalCuspWidthNat_eq_of_orbit_eq N ρ ρ' h]
  exact lpsOriginalCuspWidthNat_dvd_of_level_dvd N M hNM ρ'

/-- The SAME original level map preserves the whole represented cusp source, including the cusp. -/
lemma lpsOriginalFilledForgetLevel_cuspSource (N M : ℕ) [NeZero N] [NeZero M]
    (hNM : N ∣ M) (ρ : SL(2, ℤ)) (x : LPSOriginalFilledCurve M)
    (hx : x ∈ (lpsOriginalFilledCuspPartialEquiv M ρ).source) :
    lpsOriginalFilledForgetLevel N M hNM x ∈ (lpsOriginalFilledCuspPartialEquiv N ρ).source := by
  cases x with
  | inl y =>
    change y ∈ Set.range (lpsOriginalCuspProjection M ρ) at hx
    obtain ⟨σ, rfl⟩ := hx
    exact ⟨σ, rfl⟩
  | inr c =>
    change c = lpsOriginalCuspOrbit M ρ at hx
    subst c
    change lpsOriginalCuspForgetLevel N M hNM (lpsOriginalCuspOrbit M ρ) =
      lpsOriginalCuspOrbit N ρ
    exact lpsOriginalCuspForgetLevel_projection N M hNM ρ

/-- The actual coordinate on the entire cusp source is the genuine positive width-ratio power. -/
lemma lpsOriginalFilledForgetLevel_sameCuspCoordinate (N M : ℕ) [NeZero N] [NeZero M]
    (hNM : N ∣ M) (ρ : SL(2, ℤ)) (x : LPSOriginalFilledCurve M)
    (hx : x ∈ (lpsOriginalFilledCuspPartialEquiv M ρ).source) :
    lpsOriginalFilledCuspPartialEquiv N ρ (lpsOriginalFilledForgetLevel N M hNM x) =
      (lpsOriginalFilledCuspPartialEquiv M ρ x) ^ lpsOriginalCuspLevelDegree N M ρ := by
  cases x with
  | inl y =>
    change y ∈ Set.range (lpsOriginalCuspProjection M ρ) at hx
    obtain ⟨σ, rfl⟩ := hx
    change lpsOriginalFilledCuspPartialEquiv N ρ
      (Sum.inl (lpsOriginalCuspProjection N ρ σ)) = _
    rw [lpsOriginalFilledCuspPartialEquiv_projection,
      lpsOriginalFilledCuspPartialEquiv_projection]
    exact (lpsOriginalCuspLevelDegree_qParam N M hNM ρ σ.val).symm
  | inr c =>
    change c = lpsOriginalCuspOrbit M ρ at hx
    subst c
    rw [lpsOriginalFilledForgetLevel_cusp, lpsOriginalFilledCuspPartialEquiv_cusp,
      lpsOriginalFilledCuspPartialEquiv_cusp]
    exact (zero_pow (Nat.ne_of_gt (lpsOriginalCuspLevelDegree_positive N M hNM ρ))).symm

/-- Literal exponential algebra computes the constant phase of a translated cusp coordinate. -/
lemma lpsOriginalCuspCoordinate_qParam_add (w : ℝ) (z u : ℂ) :
    Function.Periodic.qParam w (z + u) =
      Function.Periodic.qParam w u * Function.Periodic.qParam w z := by
  simp only [Function.Periodic.qParam, mul_add, add_div, Complex.exp_add]
  exact mul_comm _ _

/-- The actual preferred chart differs by a proved unit-modulus phase on the full cusp source. -/
lemma lpsOriginalFilledCuspCoordinate_preferred_phase
    (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    letI := lpsOriginalFilledTopology N
    let c := lpsOriginalCuspOrbit N ρ
    ∃ α : ℂ, α ≠ 0 ∧ ‖α‖ = 1 ∧ ∀ y : LPSOriginalFilledCurve N,
      y ∈ (lpsOriginalFilledCuspPartialEquiv N ρ).source →
      y ∈ (lpsOriginalFilledCuspChart N c).source ∧
      lpsOriginalFilledCuspChart N c y =
        α * lpsOriginalFilledCuspPartialEquiv N ρ y := by
  let := lpsOriginalFilledTopology N
  let c := lpsOriginalCuspOrbit N ρ
  let r := lpsOriginalCuspRepresentative N c
  let w := (lpsOriginalCuspGroup N ρ).strictWidthInfty
  obtain ⟨g,hg,u,hu⟩ := lpsOriginalCuspChange_translation N r ρ
    (lpsOriginalCuspRepresentative_orbit N c)
  let d := (Matrix.SpecialLinearGroup.mapGL ℝ r)⁻¹ * g *
    Matrix.SpecialLinearGroup.mapGL ℝ ρ
  let α := Function.Periodic.qParam w (u : ℂ)
  have hw : (lpsOriginalCuspGroup N r).strictWidthInfty = w := by
    change (lpsOriginalCuspGroup N r).strictWidthInfty =
      (lpsOriginalCuspGroup N ρ).strictWidthInfty
    rw [lpsOriginalCuspWidthNat_cast, lpsOriginalCuspWidthNat_cast]
    exact congrArg (fun n : ℕ => (n : ℝ))
      (lpsOriginalCuspWidthNat_eq_of_orbit_eq N r ρ
        (lpsOriginalCuspRepresentative_orbit N c))
  refine ⟨α,Function.Periodic.qParam_ne_zero _,?_,?_⟩
  · simp [α,Function.Periodic.norm_qParam]
  · intro y hy
    have hs : y ∈ (lpsOriginalFilledCuspChart N c).source := by
      change y ∈ (lpsOriginalFilledCuspPartialEquiv N r).source
      cases y with
      | inl z =>
        change z ∈ Set.range (lpsOriginalCuspProjection N r)
        change z ∈ Set.range (lpsOriginalCuspProjection N ρ) at hy
        rw [lpsOriginalCuspRepresentative_range]
        exact hy
      | inr b =>
        change b = lpsOriginalCuspOrbit N r
        change b = c at hy
        rw [lpsOriginalCuspRepresentative_orbit]
        exact hy
    refine ⟨hs,?_⟩
    cases y with
    | inl z =>
      change z ∈ Set.range (lpsOriginalCuspProjection N ρ) at hy
      obtain ⟨σ,rfl⟩ := hy
      have hi : 1 < (d • σ.val).im := by
        rw [lpsSignedTranslation_im d u hu]
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
      have ht : (τ.val : ℂ) = (σ.val : ℂ)+(u : ℂ) := by
        change ((d • σ.val : ℍ) : ℂ) = _
        dsimp only [d]
        rcases hu with hplus | hminus
        · rw [hplus,lpsUpperRight_smul_coe]
        · rw [hminus,UpperHalfPlane.neg_smul,lpsUpperRight_smul_coe]
      change lpsOriginalFilledCuspPartialEquiv N r
        (Sum.inl (lpsOriginalCuspProjection N ρ σ)) =
          α * lpsOriginalFilledCuspPartialEquiv N ρ
            (Sum.inl (lpsOriginalCuspProjection N ρ σ))
      rw [←hp,lpsOriginalFilledCuspPartialEquiv_projection,ht,hw,
        lpsOriginalCuspCoordinate_qParam_add]
      rw [hp,lpsOriginalFilledCuspPartialEquiv_projection]
    | inr b =>
      change b = c at hy
      rw [hy,lpsOriginalFilledCuspChart_cusp]
      change 0 = α * 0
      exact (mul_zero α).symm

/-- Every full higher cusp coordinate maps into the actual lower chart with its genuine power and phase. -/
lemma lpsOriginalFilledForgetLevel_preferredCuspCoordinates
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ))) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledTopology M
    let ρ := lpsOriginalCuspRepresentative M c
    let d := lpsOriginalCuspForgetLevel N M hNM c
    ∃ α : ℂ, α ≠ 0 ∧ ‖α‖ = 1 ∧ ∀ q : ℂ,
      q ∈ (lpsOriginalFilledCuspChart M c).target →
      α * q ^ lpsOriginalCuspLevelDegree N M ρ ∈
        (lpsOriginalFilledCuspChart N d).target ∧
      lpsOriginalFilledForgetLevel N M hNM
        ((lpsOriginalFilledCuspChart M c).symm q) =
        (lpsOriginalFilledCuspChart N d).symm
          (α * q ^ lpsOriginalCuspLevelDegree N M ρ) ∧
      lpsOriginalFilledCuspChart N d
        (lpsOriginalFilledForgetLevel N M hNM
          ((lpsOriginalFilledCuspChart M c).symm q)) =
        α * q ^ lpsOriginalCuspLevelDegree N M ρ := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledTopology M
  let ρ := lpsOriginalCuspRepresentative M c
  let d := lpsOriginalCuspForgetLevel N M hNM c
  let eM := lpsOriginalFilledCuspChart M c
  let eN := lpsOriginalFilledCuspChart N d
  have hc : lpsOriginalCuspOrbit N ρ = d := by
    rw [← lpsOriginalCuspForgetLevel_projection N M hNM ρ]
    rw [lpsOriginalCuspRepresentative_orbit]
  obtain ⟨α,hα,hαnorm,hphase⟩ := lpsOriginalFilledCuspCoordinate_preferred_phase N ρ
  rw [hc] at hphase
  refine ⟨α,hα,hαnorm,?_⟩
  intro q hq
  have hx : eM.symm q ∈ (lpsOriginalFilledCuspPartialEquiv M ρ).source :=
    eM.map_target hq
  have hy := lpsOriginalFilledForgetLevel_cuspSource N M hNM ρ (eM.symm q) hx
  obtain ⟨hs,hcoord⟩ := hphase (lpsOriginalFilledForgetLevel N M hNM (eM.symm q)) hy
  have hqcoord : eN (lpsOriginalFilledForgetLevel N M hNM (eM.symm q)) =
      α * q ^ lpsOriginalCuspLevelDegree N M ρ := by
    rw [hcoord,lpsOriginalFilledForgetLevel_sameCuspCoordinate N M hNM ρ (eM.symm q) hx]
    change α * (eM (eM.symm q)) ^ lpsOriginalCuspLevelDegree N M ρ =
      α * q ^ lpsOriginalCuspLevelDegree N M ρ
    rw [eM.right_inv hq]
  refine ⟨?_,?_,hqcoord⟩
  · rw [← hqcoord]
    exact eN.map_source hs
  · rw [← hqcoord]
    exact (eN.left_inv hs).symm

/-- The canonical original level quotient map is continuous by actual quotient descent. -/
lemma lpsOriginalInteriorForgetLevel_continuous (N M : ℕ) (hNM : N ∣ M) :
    Continuous (lpsOriginalInteriorForgetLevel N M hNM) := by
  unfold lpsOriginalInteriorForgetLevel
  exact continuous_id.quotient_map' _

/-- The true preferred cusp parametrization followed by the level map is continuous on the full disc. -/
lemma lpsOriginalFilledForgetLevel_cuspChart_continuousOn
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ))) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledTopology M
    ContinuousOn
      (fun q : ℂ => lpsOriginalFilledForgetLevel N M hNM
        ((lpsOriginalFilledCuspChart M c).symm q))
      (lpsOriginalFilledCuspChart M c).target := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledTopology M
  let ρ := lpsOriginalCuspRepresentative M c
  let d := lpsOriginalCuspForgetLevel N M hNM c
  let e := lpsOriginalCuspLevelDegree N M ρ
  obtain ⟨α,hα,hαnorm,h⟩ := lpsOriginalFilledForgetLevel_preferredCuspCoordinates N M hNM c
  have hp : Continuous (fun q : ℂ => α * q ^ e) :=
    continuous_const.mul (continuous_id.pow e)
  have hc : ContinuousOn
      (fun q : ℂ => (lpsOriginalFilledCuspChart N d).symm (α * q ^ e))
      (lpsOriginalFilledCuspChart M c).target :=
    (lpsOriginalFilledCuspChart N d).continuousOn_invFun.comp hp.continuousOn
      (fun q hq => (h q hq).1)
  apply hc.congr
  intro q hq
  exact (h q hq).2.1

/-- The SAME whole original filled map is continuous by the actual cusp-gluing universal property. -/
lemma lpsOriginalFilledForgetLevel_continuous
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledTopology M
    Continuous (lpsOriginalFilledForgetLevel N M hNM) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledTopology M
  apply continuous_def.mpr
  intro s hs
  apply (lpsOriginalFilledTopology_isOpen_iff M
    ((lpsOriginalFilledForgetLevel N M hNM) ⁻¹' s)).mpr
  constructor
  · have hi : Continuous (fun y => Sum.inl (lpsOriginalInteriorForgetLevel N M hNM y)) :=
      (lpsOriginalFilledTopology_interior_continuous N).comp
        (lpsOriginalInteriorForgetLevel_continuous N M hNM)
    change IsOpen ((fun y => Sum.inl (lpsOriginalInteriorForgetLevel N M hNM y)) ⁻¹' s)
    exact hi.isOpen_preimage s hs
  · intro c
    have hc : Continuous (fun q : (lpsOriginalFilledCuspChart M c).target =>
      lpsOriginalFilledForgetLevel N M hNM ((lpsOriginalFilledCuspChart M c).symm q.val)) :=
      continuousOn_iff_continuous_domRestrict.mp
        (lpsOriginalFilledForgetLevel_cuspChart_continuousOn N M hNM c)
    change IsOpen ((fun q : (lpsOriginalFilledCuspChart M c).target =>
      lpsOriginalFilledForgetLevel N M hNM ((lpsOriginalFilledCuspChart M c).symm q.val)) ⁻¹' s)
    exact hc.isOpen_preimage s hs

/-- At levels divisible by four the SAME original filled map is complex analytic everywhere. -/
lemma lpsOriginalFilledForgetLevel_contMDiff
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (hN : 4 ∣ N) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledTopology M
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilledChartedSpace M (dvd_trans hN hNM)
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (lpsOriginalFilledForgetLevel N M hNM) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledTopology M
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilledChartedSpace M (dvd_trans hN hNM)
  intro x
  cases x with
  | inl y =>
    let eM := lpsOriginalFilledInteriorChart M (dvd_trans hN hNM) y
    let z := eM (Sum.inl y)
    have hz : 0 < z.im := lpsOriginalFilledInteriorChart_target_pos
      M (dvd_trans hN hNM) y z
      (eM.map_source (lpsOriginalFilledInteriorChart_mem M (dvd_trans hN hNM) y))
    have ha : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
        (fun z' : ℂ => (Sum.inl ⟦UpperHalfPlane.ofComplex z'⟧ : LPSOriginalFilledCurve N)) z :=
      (lpsOriginalFilled_projection_contMDiff N hN (UpperHalfPlane.ofComplex z)).comp z
        (UpperHalfPlane.contMDiffAt_ofComplex (n := ω) hz)
    apply contMDiffAt_iff_source.mpr
    have he : lpsOriginalFilledForgetLevel N M hNM ∘
        (extChartAt 𝓘(ℂ) (Sum.inl y : LPSOriginalFilledCurve M)).symm =
        (fun z' : ℂ => (Sum.inl ⟦UpperHalfPlane.ofComplex z'⟧ : LPSOriginalFilledCurve N)) := by
      funext z'
      change lpsOriginalFilledForgetLevel N M hNM
        ((lpsOriginalFilledInteriorChart M (dvd_trans hN hNM) y).symm z') = _
      rw [lpsOriginalFilledInteriorChart_symm,lpsOriginalFilledForgetLevel_projection]
    rw [he]
    convert ha.contMDiffWithinAt using 1
    simp only [extChartAt_coe,modelWithCornersSelf_coe]
    rfl
  | inr c =>
    let d := lpsOriginalCuspForgetLevel N M hNM c
    let eM := lpsOriginalFilledCuspChart M c
    let eN := lpsOriginalFilledCuspChart N d
    let e := lpsOriginalCuspLevelDegree N M (lpsOriginalCuspRepresentative M c)
    obtain ⟨α,hα,hαnorm,h⟩ := lpsOriginalFilledForgetLevel_preferredCuspCoordinates N M hNM c
    have he : (fun q : ℂ => eN (lpsOriginalFilledForgetLevel N M hNM (eM.symm q))) =ᶠ[𝓝 0]
        (fun q => α * q ^ e) := by
      have hz : (0 : ℂ) ∈ eM.target :=
        lpsOriginalFilledCuspPartialEquiv_target_zero M (lpsOriginalCuspRepresentative M c)
      filter_upwards [eM.open_target.mem_nhds hz] with q hq
      exact (h q hq).2.2
    have hp : ContDiff ℂ ω (fun q : ℂ => α * q ^ e) :=
      contDiff_const.mul (contDiff_id.pow e)
    have ha := hp.contDiffAt.congr_of_eventuallyEq he
    apply contMDiffAt_iff.mpr
    refine ⟨(lpsOriginalFilledForgetLevel_continuous N M hNM).continuousAt,?_⟩
    convert ha.contDiffWithinAt using 1
    · funext q
      change eN (lpsOriginalFilledForgetLevel N M hNM
        ((extChartAt 𝓘(ℂ) (Sum.inr c : LPSOriginalFilledCurve M)).symm q)) =
          eN (lpsOriginalFilledForgetLevel N M hNM (eM.symm q))
      apply congrArg (fun y => eN (lpsOriginalFilledForgetLevel N M hNM y))
      exact congrFun (extChartAt_coe_symm (I := 𝓘(ℂ))
        (Sum.inr c : LPSOriginalFilledCurve M)) q
    · exact (congrFun (extChartAt_coe (I := 𝓘(ℂ))
        (Sum.inr c : LPSOriginalFilledCurve M)) (Sum.inr c)).trans
          (lpsOriginalFilledCuspChart_cusp M c)


/-- The actual continuous level map is proper by genuine original compactness and Hausdorffness. -/
lemma lpsOriginalFilledForgetLevel_isProperMap
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledTopology M
    IsProperMap (lpsOriginalFilledForgetLevel N M hNM) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledTopology M
  let := lpsOriginalFilledTopology_compactSpace M
  let := lpsOriginalFilledTopology_t2Space N
  exact (lpsOriginalFilledForgetLevel_continuous N M hNM).isProperMap

end
end QEC.Coding.TannerLiftedProduct
