import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds

/-!
# LPSCuspHorocycle

The actual Fourier/Parseval closure at positive heights and the initial quadratic
coefficient-square bound for weight-two cusp forms. These internal analytic
lemmas do not give the near-square-root coefficient bound needed for PK22.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm

/-- The actual upper-half-plane point with real coordinate x and fixed positive height y. -/
noncomputable def lpsHorocyclePoint (y : ℝ) (hy : 0<y) (x : ℝ) : ℍ :=
  ⟨⟨x,y⟩,hy⟩

/-- The horizontal point has exactly the specified height. -/
@[simp] lemma lpsHorocyclePoint_im (y : ℝ) (hy : 0<y) (x : ℝ) :
    (lpsHorocyclePoint y hy x).im=y := rfl

/-- The actual horizontal parametrization is continuous. -/
lemma lpsHorocyclePoint_continuous (y : ℝ) (hy : 0<y) :
    Continuous (lpsHorocyclePoint y hy) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun x : ℝ => (⟨x,y⟩:ℂ))
  have he : (fun x : ℝ => (⟨x,y⟩:ℂ))=(fun x : ℝ => (x:ℂ)+Complex.I*(y:ℂ)) := by
    funext x
    apply Complex.ext <;> simp
  rw [he]
  fun_prop

/-- The true period-one q-parameter has its exact exponentially decaying norm. -/
lemma lpsHorocyclePoint_qParam_norm (y : ℝ) (hy : 0<y) (x : ℝ) :
    ‖Function.Periodic.qParam 1 (lpsHorocyclePoint y hy x:ℂ)‖=Real.exp (-2*Real.pi*y) := by
  rw [Function.Periodic.norm_qParam]
  simp

/-- The actual weight-two cusp form has its genuine q-expansion sum at every horizontal point. -/
lemma lpsWeightTwoCuspHorocycle_hasSum (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) (x : ℝ) :
    HasSum (fun n : ℕ => PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)*
      (Function.Periodic.qParam 1 (lpsHorocyclePoint y hy x:ℂ))^n)
      (f (lpsHorocyclePoint y hy x)) := by
  have hp : (1:ℝ)∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  let : Fact (IsCusp OnePoint.infty
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods (by norm_num) hp⟩
  exact ModularForm.hasSum_qExpansion f (by norm_num) hp _

/-- The norms of actual coefficients with the positive-height exponential weight are summable. -/
lemma lpsWeightTwoCuspHorocycle_coeff_norm_summable (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) :
    Summable (fun n : ℕ => ‖PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)‖*
      (Real.exp (-2*Real.pi*y))^n) := by
  have h := (lpsWeightTwoCuspHorocycle_hasSum N f y hy 0).summable.norm
  simpa only [norm_mul,norm_pow,lpsHorocyclePoint_qParam_norm] using h

/-- The actual q-parameter splits into the exact damping factor and period-one Fourier character. -/
lemma lpsHorocyclePoint_qParam (y : ℝ) (hy : 0<y) (x : ℝ) :
    Function.Periodic.qParam 1 (lpsHorocyclePoint y hy x:ℂ)=
      (Real.exp (-2*Real.pi*y):ℂ)*fourier (1:ℤ) (x:AddCircle (1:ℝ)) := by
  have hz : (lpsHorocyclePoint y hy x:ℂ)=(x:ℂ)+Complex.I*(y:ℂ) := by
    apply Complex.ext <;> simp [lpsHorocyclePoint]
  rw [Function.Periodic.qParam,hz,fourier_coe_apply]
  norm_num only [Complex.ofReal_one,Int.cast_one,mul_one,div_one]
  rw [mul_add,Complex.exp_add]
  have hi : 2*(Real.pi:ℂ)*Complex.I*(Complex.I*(y:ℂ))=
      Complex.ofReal (-2*Real.pi*y) := by
    calc
      _ = Complex.I^2*(2*(Real.pi:ℂ)*(y:ℂ)) := by ring
      _ = _ := by rw [Complex.I_sq];push_cast;ring
  rw [hi,←Complex.ofReal_exp,mul_comm]

/-- Natural powers of the first period-one Fourier character are the corresponding actual frequencies. -/
lemma lpsFourier_one_pow (n : ℕ) (x : ℝ) :
    (fourier (1:ℤ) (x:AddCircle (1:ℝ)))^n=fourier (n:ℤ) (x:AddCircle (1:ℝ)) := by
  rw [fourier_coe_apply,fourier_coe_apply,←Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The actual q-expansion coefficient at a positive height times its genuine Fourier character. -/
noncomputable def lpsCuspHorocycleTerm (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (n : ℕ) (x : AddCircle (1:ℝ)) : ℂ :=
  PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)*
    ((Real.exp (-2*Real.pi*y):ℂ)^n)*fourier (n:ℤ) x

/-- The sum of the actual exponentially weighted Fourier terms on the period-one circle. -/
noncomputable def lpsCuspHorocycleCircle (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (x : AddCircle (1:ℝ)) : ℂ := ∑' n : ℕ,lpsCuspHorocycleTerm N f y n x

/-- Every actual Fourier term has its exact coefficient norm and damping factor. -/
lemma lpsCuspHorocycleTerm_norm (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (n : ℕ) (x : AddCircle (1:ℝ)) :
    ‖lpsCuspHorocycleTerm N f y n x‖=
      ‖PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)‖*(Real.exp (-2*Real.pi*y))^n := by
  unfold lpsCuspHorocycleTerm
  rw [norm_mul,norm_mul,norm_pow,fourier_apply,Circle.norm_coe,mul_one,
    Complex.norm_real,Real.norm_eq_abs,Real.abs_exp]

/-- The norm-summable actual coefficient expansion defines a continuous circle function. -/
lemma lpsCuspHorocycleCircle_continuous (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) : Continuous (lpsCuspHorocycleCircle N f y) := by
  apply continuous_tsum (fun n => ?_) (lpsWeightTwoCuspHorocycle_coeff_norm_summable N f y hy)
    (fun n x => (lpsCuspHorocycleTerm_norm N f y n x).le)
  unfold lpsCuspHorocycleTerm
  exact continuous_const.mul (map_continuous (fourier (n:ℤ)))

/-- The actual circle expansion agrees with the original cusp form on the whole horizontal line. -/
lemma lpsCuspHorocycleCircle_coe (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) (x : ℝ) :
    lpsCuspHorocycleCircle N f y (x:AddCircle (1:ℝ))=f (lpsHorocyclePoint y hy x) := by
  have h := lpsWeightTwoCuspHorocycle_hasSum N f y hy x
  have he : (fun n : ℕ => PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)*
      (Function.Periodic.qParam 1 (lpsHorocyclePoint y hy x:ℂ))^n)=
      (fun n : ℕ => lpsCuspHorocycleTerm N f y n (x:AddCircle (1:ℝ))) := by
    funext n
    rw [lpsHorocyclePoint_qParam,mul_pow,lpsFourier_one_pow]
    unfold lpsCuspHorocycleTerm
    ring
  rw [he] at h
  exact h.tsum_eq

/-- The genuine horizontal Fourier series is summable at every circle point. -/
lemma lpsCuspHorocycleCircle_summable (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) (x : AddCircle (1:ℝ)) :
    Summable (fun n : ℕ => lpsCuspHorocycleTerm N f y n x) :=
  (lpsWeightTwoCuspHorocycle_coeff_norm_summable N f y hy).of_norm_bounded
    (fun n => (lpsCuspHorocycleTerm_norm N f y n x).le)

/-- Orthogonality gives the exact single-frequency Fourier coefficient of every true term. -/
lemma lpsCuspHorocycleTerm_fourierCoeff (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (n : ℕ) (k : ℤ) :
    fourierCoeff (lpsCuspHorocycleTerm N f y n) k=
      if (n:ℤ)=k then PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)*
        ((Real.exp (-2*Real.pi*y):ℂ)^n) else 0 := by
  unfold lpsCuspHorocycleTerm
  rw [fourierCoeff.const_mul,fourierCoeff_fourier]
  by_cases h : (n:ℤ)=k
  · subst k
    simp
  · have h' : k≠(n:ℤ) := fun he => h he.symm
    simp [h,h']

/-- Bochner integration of the actual norm-summable series gives the true sum of Fourier coefficients. -/
lemma lpsCuspHorocycleCircle_fourierCoeff_hasSum (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) (k : ℤ) :
    HasSum (fun n : ℕ => fourierCoeff (lpsCuspHorocycleTerm N f y n) k)
      (fourierCoeff (lpsCuspHorocycleCircle N f y) k) := by
  let F (n : ℕ) (x : AddCircle (1:ℝ)) : ℂ := fourier (-k) x*lpsCuspHorocycleTerm N f y n x
  have hnorm (n : ℕ) (x : AddCircle (1:ℝ)) : ‖F n x‖=
      ‖PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)‖*(Real.exp (-2*Real.pi*y))^n := by
    dsimp only [F]
    rw [norm_mul,fourier_apply,Circle.norm_coe,one_mul,lpsCuspHorocycleTerm_norm]
  have hcont (n : ℕ) : Continuous (F n) := by
    unfold F lpsCuspHorocycleTerm
    exact (map_continuous (fourier (-k))).mul
      (continuous_const.mul (map_continuous (fourier (n:ℤ))))
  have hi (n : ℕ) : Integrable (F n) (@AddCircle.haarAddCircle 1 ⟨by norm_num⟩) :=
    (hcont n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsum : Summable (fun n : ℕ => ∫ x : AddCircle (1:ℝ),‖F n x‖ ∂AddCircle.haarAddCircle) := by
    simp_rw [hnorm]
    simpa [integral_const] using
      lpsWeightTwoCuspHorocycle_coeff_norm_summable N f y hy
  have h := hasSum_integral_of_summable_integral_norm hi hsum
  have he (x : AddCircle (1:ℝ)) : (∑' n : ℕ,F n x)=
      fourier (-k) x*lpsCuspHorocycleCircle N f y x := by
    exact tsum_mul_left
  simp only [fourierCoeff,smul_eq_mul] at ⊢
  simpa only [F,he] using h

/-- Every nonnegative frequency has exactly the original q-coefficient times its damping factor. -/
lemma lpsCuspHorocycleCircle_fourierCoeff_nat (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) (n : ℕ) :
    fourierCoeff (lpsCuspHorocycleCircle N f y) (n:ℤ)=
      PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)*
        ((Real.exp (-2*Real.pi*y):ℂ)^n) := by
  have h := lpsCuspHorocycleCircle_fourierCoeff_hasSum N f y hy (n:ℤ)
  have he : (fun m : ℕ => fourierCoeff (lpsCuspHorocycleTerm N f y m) (n:ℤ))=
      (fun m : ℕ => if m=n then PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)*
        ((Real.exp (-2*Real.pi*y):ℂ)^n) else 0) := by
    funext m
    rw [lpsCuspHorocycleTerm_fourierCoeff]
    by_cases hm : m=n
    · subst m
      rw [if_pos rfl,if_pos rfl]
    · have hm' : (m:ℤ)≠(n:ℤ) := fun hc => hm (Int.ofNat_inj.mp hc)
      rw [if_neg hm',if_neg hm]
  rw [he] at h
  exact HasSum.unique h (hasSum_ite_eq n _)

/-- Every negative frequency of the actual holomorphic horizontal expansion vanishes. -/
lemma lpsCuspHorocycleCircle_fourierCoeff_neg (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) (k : ℤ) (hk : k<0) :
    fourierCoeff (lpsCuspHorocycleCircle N f y) k=0 := by
  have h := lpsCuspHorocycleCircle_fourierCoeff_hasSum N f y hy k
  have hn (n:ℕ) : (n:ℤ)≠k := by omega
  simp_rw [lpsCuspHorocycleTerm_fourierCoeff,if_neg (hn _)] at h
  exact h.unique hasSum_zero

/-- The actual continuous horizontal circle function is square integrable. -/
lemma lpsCuspHorocycleCircle_memLp (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) :
    MemLp (lpsCuspHorocycleCircle N f y) 2 (@AddCircle.haarAddCircle 1 ⟨by norm_num⟩) :=
  (lpsCuspHorocycleCircle_continuous N f y hy).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Actual Hilbert-space Parseval identifies the sum over all integer frequencies with its square integral. -/
lemma lpsCuspHorocycleCircle_parseval_int (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) :
    HasSum (fun k : ℤ => ‖fourierCoeff (lpsCuspHorocycleCircle N f y) k‖^2)
      (∫ x : AddCircle (1:ℝ), ‖lpsCuspHorocycleCircle N f y x‖^2 ∂AddCircle.haarAddCircle) := by
  have hm := lpsCuspHorocycleCircle_memLp N f y hy
  have h := hasSum_sq_fourierCoeff hm.toLp
  have he := fourierCoeff_congr_ae hm.coeFn_toLp
  simp_rw [he] at h
  convert h using 1
  apply integral_congr_ae
  filter_upwards [hm.coeFn_toLp] with x hx
  rw [hx]

/-- Vanishing negative frequencies gives the actual natural-indexed coefficient-square Parseval sum. -/
lemma lpsCuspHorocycleCircle_parseval_nat (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) :
    HasSum (fun n : ℕ => ‖PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)‖^2*
      (Real.exp (-2*Real.pi*y))^(2*n))
      (∫ x : AddCircle (1:ℝ), ‖lpsCuspHorocycleCircle N f y x‖^2 ∂AddCircle.haarAddCircle) := by
  have hneg (k : ℤ) (hk : k∉Set.range (fun n : ℕ => (n:ℤ))) :
      ‖fourierCoeff (lpsCuspHorocycleCircle N f y) k‖^2=0 := by
    have hk' : k<0 := by
      by_contra hc
      apply hk
      exact ⟨k.toNat,Int.toNat_of_nonneg (by omega)⟩
    rw [lpsCuspHorocycleCircle_fourierCoeff_neg N f y hy k hk',norm_zero,zero_pow (by norm_num)]
  have h := (Int.ofNat_injective.hasSum_iff hneg).mpr
    (lpsCuspHorocycleCircle_parseval_int N f y hy)
  apply h.congr_fun
  intro n
  change _=‖fourierCoeff (lpsCuspHorocycleCircle N f y) (n:ℤ)‖^2
  rw [lpsCuspHorocycleCircle_fourierCoeff_nat N f y hy,norm_mul,norm_pow,
    Complex.norm_real,Real.norm_eq_abs,Real.abs_exp,mul_pow,←pow_mul]
  congr 1
  congr 1
  omega

/-- The genuine weight-two cusp bound gives one constant for every positive-height circle. -/
lemma lpsCuspHorocycleCircle_norm_bound (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    ∃ C : ℝ, 0≤C ∧ ∀ (y : ℝ) (_hy : 0<y) (x : AddCircle (1:ℝ)),
      ‖lpsCuspHorocycleCircle N f y x‖≤C/y := by
  obtain ⟨C,hC⟩ := CuspFormClass.exists_bound f
  have hb (τ : ℍ) : ‖f τ‖≤C/τ.im := by simpa using hC τ
  have hC0 : 0≤C := by
    have h := hb (lpsHorocyclePoint 1 (by norm_num) 0)
    simp only [lpsHorocyclePoint_im,div_one] at h
    exact (norm_nonneg _).trans h
  refine ⟨C,hC0,fun y hy x => ?_⟩
  induction x using QuotientAddGroup.induction_on with | H x =>
    rw [lpsCuspHorocycleCircle_coe N f y hy]
    exact hb _

/-- The normalized Haar square integral is exactly the original horizontal interval integral. -/
lemma lpsCuspHorocycle_integral (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) :
    (∫ x : AddCircle (1:ℝ), ‖lpsCuspHorocycleCircle N f y x‖^2 ∂AddCircle.haarAddCircle)=
      ∫ x in (0:ℝ)..1, ‖f (lpsHorocyclePoint y hy x)‖^2 := by
  rw [AddCircle.integral_haarAddCircle]
  norm_num only [inv_one,one_smul]
  rw [←AddCircle.intervalIntegral_preimage 1 0]
  simp only [zero_add,lpsCuspHorocycleCircle_coe N f y hy]

/-- Actual Parseval identifies the exponentially weighted q-coefficient squares with the true interval integral. -/
lemma lpsCuspHorocycle_parseval (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) :
    HasSum (fun n : ℕ => ‖PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)‖^2*
      (Real.exp (-2*Real.pi*y))^(2*n))
      (∫ x in (0:ℝ)..1, ‖f (lpsHorocyclePoint y hy x)‖^2) := by
  rw [←lpsCuspHorocycle_integral N f y hy]
  exact lpsCuspHorocycleCircle_parseval_nat N f y hy

/-- A pointwise bound on the actual horizontal function bounds its true square integral. -/
lemma lpsCuspHorocycle_integral_bound_of_norm_bound (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (C y : ℝ) (hy : 0<y)
    (hb : ∀ x : AddCircle (1:ℝ), ‖lpsCuspHorocycleCircle N f y x‖≤C/y) :
    (∫ x : AddCircle (1:ℝ), ‖lpsCuspHorocycleCircle N f y x‖^2 ∂AddCircle.haarAddCircle)≤
      (C/y)^2 := by
  have hi : Integrable (fun x : AddCircle (1:ℝ) => ‖lpsCuspHorocycleCircle N f y x‖^2)
      AddCircle.haarAddCircle :=
    ((lpsCuspHorocycleCircle_continuous N f y hy).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h := integral_mono hi (integrable_const ((C/y)^2)) (fun x => ?_)
  · simpa using h
  · exact pow_le_pow_left₀ (norm_nonneg _) (hb x) 2

/-- The genuine cusp bound controls the sum of actual exponentially weighted coefficient squares. -/
lemma lpsCuspHorocycle_weighted_square_bound (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    ∃ C : ℝ, 0≤C ∧ ∀ (y : ℝ) (_hy : 0<y),
      (∑' n : ℕ, ‖PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)‖^2*
        (Real.exp (-2*Real.pi*y))^(2*n))≤(C/y)^2 := by
  obtain ⟨C,hC,hb⟩ := lpsCuspHorocycleCircle_norm_bound N f
  refine ⟨C,hC,fun y hy => ?_⟩
  rw [(lpsCuspHorocycleCircle_parseval_nat N f y hy).tsum_eq]
  exact lpsCuspHorocycle_integral_bound_of_norm_bound N f C y hy (hb y hy)

/-- The coefficient-square damping weight has exactly the four-pi exponential normalization. -/
lemma lpsCuspHorocycle_weight_exp (y : ℝ) (n : ℕ) :
    (Real.exp (-2*Real.pi*y))^(2*n)=Real.exp (-4*Real.pi*(n:ℝ)*y) := by
  rw [←Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The actual weight-two coefficients have one quadratic square-average bound for every finite initial range. -/
lemma lpsWeightTwoCusp_coeff_square_sum_bound (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    ∃ C : ℝ, 0≤C ∧ ∀ X : ℕ,
      (∑ n ∈ Finset.range X, ‖PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)‖^2)≤
        C*(X:ℝ)^2 := by
  obtain ⟨C,hC,hb⟩ := lpsCuspHorocycle_weighted_square_bound N f
  refine ⟨Real.exp (4*Real.pi)*C^2,by positivity,fun X => ?_⟩
  by_cases hx : X=0
  · subst X
    simp
  have hxR : 0<(X:ℝ) := by exact_mod_cast (by omega : 0<X)
  let y : ℝ := 1/(X:ℝ)
  have hy : 0<y := by dsimp [y];positivity
  have hw (n : ℕ) (hn : n∈Finset.range X) :
      Real.exp (-4*Real.pi)≤(Real.exp (-2*Real.pi*y))^(2*n) := by
    rw [lpsCuspHorocycle_weight_exp]
    apply Real.exp_le_exp.mpr
    dsimp [y]
    rw [mul_one_div]
    apply (le_div_iff₀ hxR).mpr
    have hnR : (n:ℝ)≤(X:ℝ) := by exact_mod_cast (Finset.mem_range.mp hn).le
    have h := mul_le_mul_of_nonneg_left hnR (by positivity : 0≤4*Real.pi)
    nlinarith
  have hs : Real.exp (-4*Real.pi)*
      (∑ n ∈ Finset.range X, ‖PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)‖^2)≤
      (C/y)^2 := by
    calc
      _ = ∑ n ∈ Finset.range X, Real.exp (-4*Real.pi)*
            ‖PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)‖^2 := Finset.mul_sum ..
      _ ≤ ∑ n ∈ Finset.range X, ‖PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)‖^2*
            (Real.exp (-2*Real.pi*y))^(2*n) := by
        apply Finset.sum_le_sum
        intro n hn
        rw [mul_comm (Real.exp _)]
        exact mul_le_mul_of_nonneg_left (hw n hn) (sq_nonneg _)
      _ ≤ ∑' n : ℕ, ‖PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)‖^2*
            (Real.exp (-2*Real.pi*y))^(2*n) :=
        sum_le_hasSum _ (fun n hn => by positivity)
          (lpsCuspHorocycleCircle_parseval_nat N f y hy).summable.hasSum
      _ ≤ _ := hb y hy
  have he : Real.exp (4*Real.pi)*Real.exp (-4*Real.pi)=1 := by
    rw [←Real.exp_add];simp
  have ht := mul_le_mul_of_nonneg_left hs (Real.exp_pos (4*Real.pi)).le
  rw [←mul_assoc,he,one_mul] at ht
  have hd : C/y=C*(X:ℝ) := by dsimp [y];field_simp
  rw [hd,mul_pow] at ht
  simpa only [mul_assoc] using ht

end QEC.Coding.TannerLiftedProduct
