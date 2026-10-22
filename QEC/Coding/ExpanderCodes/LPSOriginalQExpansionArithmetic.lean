import QEC.Coding.ExpanderCodes.LPSOriginalModularFunction
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# LPSOriginalQExpansionArithmetic

Connect the SAME original analytic q-times-j coefficient with a concrete
rational power series. Genuine analytic derivatives prove Taylor identities
for germs, products, constants, powers and divided slopes. The actual
normalized Eisenstein q-expansion coefficients give rational E4/E6 series;
the actual discriminant identity gives rational Delta. Its genuine divided
slope has constant one, so the formal-unit inverse is defined. Actual
analytic germ multiplication and formal cancellation identify the rational
q-times-j series with the Taylor series of lpsOriginalJQCoefficient.
Every actual coefficient of that SAME analytic function is a rational cast.

Rational Taylor coefficients do not assert integer coefficients, rational
or integral coefficients of a modular equation, exact minimal degree,
ALL compact meromorphic-function identification, an arithmetic normalization,
uniform good reduction, geometric Hecke/Frobenius/Weil or the public PK22
main theorem. The internal bridge is motivated by pinned PK22 main.tex
ex:Xpq/th:qLDPC and the audited original modular-curve route; no new public
source claim or alternate curve family is introduced.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology UpperHalfPlane ModularForm MatrixGroups
open scoped UpperHalfPlane ModularForm
noncomputable section

/-- Actual derivative-normalized Taylor series at zero of the given complex function. -/
def lpsOriginalTaylorSeries (f : ℂ→ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => (n.factorial:ℂ)⁻¹*iteratedDeriv n f 0

/-- Literal Taylor coefficient identity from the actual PowerSeries.mk construction. -/
lemma lpsOriginalTaylorSeries_coeff (f : ℂ→ℂ) (n : ℕ) :
    (lpsOriginalTaylorSeries f).coeff n=(n.factorial:ℂ)⁻¹*iteratedDeriv n f 0 := by
  simp only [lpsOriginalTaylorSeries,PowerSeries.coeff_mk]

/-- Actual neighborhood-germ equality gives identical Taylor coefficients by derivative locality. -/
lemma lpsOriginalTaylorSeries_congr {f g : ℂ→ℂ} (h : f=ᶠ[𝓝 0]g) :
    lpsOriginalTaylorSeries f=lpsOriginalTaylorSeries g := by
  ext n
  rw [lpsOriginalTaylorSeries_coeff,lpsOriginalTaylorSeries_coeff,
    Filter.EventuallyEq.iteratedDeriv_eq n h]

/-- Actual analytic product Taylor identity proved from iterated derivative multiplication and factorials. -/
lemma lpsOriginalTaylorSeries_mul {f g : ℂ→ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    lpsOriginalTaylorSeries (f*g)=
      lpsOriginalTaylorSeries f*lpsOriginalTaylorSeries g := by
  ext n
  simp only [lpsOriginalTaylorSeries_coeff,iteratedDeriv_mul hf.contDiffAt hg.contDiffAt,
    Finset.mul_sum,PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Nat.succ_eq_add_one]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Nat.cast_choose _ (by grind)]
  field_simp [Nat.factorial_ne_zero]

/-- Actual constant-one function has Taylor series one, including all positive derivatives. -/
lemma lpsOriginalTaylorSeries_one :
    lpsOriginalTaylorSeries (1 : ℂ→ℂ)=1 := by
  ext n
  cases n with
  | zero => simp [lpsOriginalTaylorSeries_coeff]
  | succ n =>
      rw [lpsOriginalTaylorSeries_coeff]
      change (Nat.factorial (n+1):ℂ)⁻¹*iteratedDeriv (n+1) (fun _ : ℂ => (1:ℂ)) 0=_
      simp [iteratedDeriv_const]

/-- Actual analytic power Taylor identity by genuine product closure and induction. -/
lemma lpsOriginalTaylorSeries_pow {f : ℂ→ℂ} (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    lpsOriginalTaylorSeries (f^n)=(lpsOriginalTaylorSeries f)^n := by
  induction n with
  | zero => simp only [pow_zero,lpsOriginalTaylorSeries_one]
  | succ n ih => rw [pow_succ,lpsOriginalTaylorSeries_mul (hf.pow n) hf,ih,pow_succ]

/-- Actual analytic divided slope shifts Taylor coefficients through power-series uniqueness. -/
lemma lpsOriginalTaylorSeries_dslope {f : ℂ→ℂ} (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    (lpsOriginalTaylorSeries (dslope f 0)).coeff n=
      (lpsOriginalTaylorSeries f).coeff (n+1) := by
  have hs := hf.hasFPowerSeriesAt.has_fpower_series_dslope_fslope
  have he := hs.eq_formalMultilinearSeries hs.analyticAt.hasFPowerSeriesAt
  have h := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) he
  simpa only [FormalMultilinearSeries.coeff_fslope,FormalMultilinearSeries.coeff_ofScalars,
    lpsOriginalTaylorSeries_coeff,div_eq_mul_inv,mul_comm] using h.symm

/-- Concrete rational Eisenstein series defined by actual Bernoulli numbers and divisor sums. -/
def lpsOriginalEisensteinQSeries (k : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => if n=0 then 1 else
    -(2*k/bernoulli k:ℚ)*(ArithmeticFunction.sigma (k-1) n)

/-- That concrete rational series maps to the SAME actual normalized Eisenstein q expansion. -/
lemma lpsOriginalEisensteinQSeries_map (k : ℕ) (hk : 3≤k) (hk2 : Even k) :
    PowerSeries.map (algebraMap ℚ ℂ) (lpsOriginalEisensteinQSeries k)=
      qExpansion 1 (ModularForm.E hk) := by
  ext n
  rw [PowerSeries.coeff_map,EisensteinSeries.E_qExpansion_coeff hk hk2]
  simp only [lpsOriginalEisensteinQSeries,PowerSeries.coeff_mk,eq_ratCast]
  split_ifs <;> push_cast <;> rfl

/-- The weight-four rational series maps to actual E4 q expansion. -/
lemma lpsOriginalE4QSeries_map :
    PowerSeries.map (algebraMap ℚ ℂ) (lpsOriginalEisensteinQSeries 4)=
      qExpansion 1 ModularForm.E₄ :=
  lpsOriginalEisensteinQSeries_map 4 (by decide) ⟨2,rfl⟩

/-- The weight-six rational series maps to actual E6 q expansion. -/
lemma lpsOriginalE6QSeries_map :
    PowerSeries.map (algebraMap ℚ ℂ) (lpsOriginalEisensteinQSeries 6)=
      qExpansion 1 ModularForm.E₆ :=
  lpsOriginalEisensteinQSeries_map 6 (by decide) ⟨3,rfl⟩

/-- Actual weight12 E4-cube minus E6-square form with genuine weight casts. -/
def lpsOriginalE4CubeSubE6SquareForm : ModularForm 𝒮ℒ 12 :=
  ModularForm.mcast (by decide) (ModularForm.E₄.pow 3)-
    ModularForm.mcast (by decide) (ModularForm.E₆.pow 2)

/-- Literal pointwise identity for that concrete modular form. -/
lemma lpsOriginalE4CubeSubE6SquareForm_apply (τ : ℍ) :
    lpsOriginalE4CubeSubE6SquareForm τ=ModularForm.E₄ τ^3-ModularForm.E₆ τ^2 := by
  simp only [lpsOriginalE4CubeSubE6SquareForm,ModularForm.coe_mcast,
    ModularForm.coe_pow,sub_apply,Pi.pow_apply]

/-- The actual q-expansion homomorphism evaluates that concrete form difference and powers. -/
lemma lpsOriginalE4CubeSubE6SquareForm_qExpansion :
    qExpansion 1 lpsOriginalE4CubeSubE6SquareForm=
      (qExpansion 1 ModularForm.E₄)^3-(qExpansion 1 ModularForm.E₆)^2 := by
  simp only [lpsOriginalE4CubeSubE6SquareForm,FunLike.coe_sub,ModularForm.coe_mcast,
    ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]

/-- The SAME actual Delta q expansion follows from the proved E4/E6 discriminant identity. -/
lemma lpsOriginalDiscriminant_qExpansion_formula :
    qExpansion 1 ModularForm.discriminant=(1728:ℂ)⁻¹ •
      ((qExpansion 1 ModularForm.E₄)^3-(qExpansion 1 ModularForm.E₆)^2) := by
  have he : (ModularForm.discriminant : ℍ→ℂ)=
      ((1728:ℂ)⁻¹ • lpsOriginalE4CubeSubE6SquareForm : ModularForm 𝒮ℒ 12) := by
    funext τ
    simp only [smul_apply,lpsOriginalE4CubeSubE6SquareForm_apply]
    simpa only [div_eq_mul_inv,mul_comm,smul_eq_mul] using ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq τ
  rw [he,FunLike.coe_smul,ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    lpsOriginalE4CubeSubE6SquareForm_qExpansion]

/-- Concrete rational Delta series given by the actual Eisenstein series and rational1728 inverse. -/
def lpsOriginalDeltaQSeries : PowerSeries ℚ :=
  PowerSeries.C (1728:ℚ)⁻¹*
    ((lpsOriginalEisensteinQSeries 4)^3-(lpsOriginalEisensteinQSeries 6)^2)

/-- Actual rational Delta series maps to SAME actual Delta q expansion. -/
lemma lpsOriginalDeltaQSeries_map :
    PowerSeries.map (algebraMap ℚ ℂ) lpsOriginalDeltaQSeries=
      qExpansion 1 ModularForm.discriminant := by
  simp only [lpsOriginalDeltaQSeries,map_mul,PowerSeries.map_C,map_sub,map_pow,
    lpsOriginalE4QSeries_map,lpsOriginalE6QSeries_map,
    lpsOriginalDiscriminant_qExpansion_formula,PowerSeries.smul_eq_C_mul]
  norm_num

/-- Concrete rational divided-slope series obtained by coefficient shift of actual Delta series. -/
def lpsOriginalDeltaSlopeQSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n => lpsOriginalDeltaQSeries.coeff (n+1)

/-- The actual rational shifted series maps to the genuine analytic divided-slope Taylor series. -/
lemma lpsOriginalDeltaSlopeQSeries_map :
    PowerSeries.map (algebraMap ℚ ℂ) lpsOriginalDeltaSlopeQSeries=
      lpsOriginalTaylorSeries (dslope (cuspFunction 1 ModularForm.discriminant) 0) := by
  ext n
  have ha : AnalyticAt ℂ (cuspFunction 1 ModularForm.discriminant) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero CuspForm.discriminant
      one_pos one_mem_strictPeriods_SL
  rw [PowerSeries.coeff_map,lpsOriginalTaylorSeries_dslope ha]
  have h := congrArg (fun S : PowerSeries ℂ => S.coeff (n+1)) lpsOriginalDeltaQSeries_map
  simpa only [lpsOriginalDeltaSlopeQSeries,PowerSeries.coeff_mk,
    PowerSeries.coeff_map,qExpansion,lpsOriginalTaylorSeries_coeff] using h

/-- The rational shifted series has constant1 from the proved SAME Delta first q coefficient. -/
lemma lpsOriginalDeltaSlopeQSeries_constant :
    PowerSeries.constantCoeff lpsOriginalDeltaSlopeQSeries=1 := by
  have h := congrArg (fun S : PowerSeries ℂ => S.coeff 1) lpsOriginalDeltaQSeries_map
  rw [PowerSeries.coeff_map,ModularForm.discriminant_qExpansion_coeff_one] at h
  change lpsOriginalDeltaQSeries.coeff 1=1
  rw [eq_ratCast] at h
  exact_mod_cast h

/-- Concrete rational q-times-j series using the proved constant-one denominator formal-unit inverse. -/
def lpsOriginalJQSeries : PowerSeries ℚ :=
  (lpsOriginalEisensteinQSeries 4)^3*
    PowerSeries.invOfUnit lpsOriginalDeltaSlopeQSeries 1

/-- Genuine divided-slope analyticity from the actual Delta analytic expansion. -/
lemma lpsOriginalDeltaSlope_analytic :
    AnalyticAt ℂ (dslope (cuspFunction 1 ModularForm.discriminant) 0) 0 := by
  have h := ModularFormClass.analyticAt_cuspFunction_zero CuspForm.discriminant
    one_pos one_mem_strictPeriods_SL
  exact h.hasFPowerSeriesAt.has_fpower_series_dslope_fslope.analyticAt

/-- Genuine divided-slope value1 at zero from the actual Delta first coefficient. -/
lemma lpsOriginalDeltaSlope_zero :
    dslope (cuspFunction 1 ModularForm.discriminant) 0 0=1 := by
  simpa [dslope_same,qExpansion_coeff,iteratedDeriv_one] using
    ModularForm.discriminant_qExpansion_coeff_one

/-- Actual rational q-times-j series maps to SAME original analytic K Taylor series by neighborhood multiplication and true formal-unit cancellation. -/
lemma lpsOriginalJQSeries_map :
    PowerSeries.map (algebraMap ℚ ℂ) lpsOriginalJQSeries=
      lpsOriginalTaylorSeries lpsOriginalJQCoefficient := by
  let D := lpsOriginalTaylorSeries (dslope (cuspFunction 1 ModularForm.discriminant) 0)
  have hD0 : D.coeff 0=1 := by
    simp only [D,lpsOriginalTaylorSeries_coeff,Nat.factorial_zero,
      Nat.cast_one,inv_one,one_mul,iteratedDeriv_zero]
    exact lpsOriginalDeltaSlope_zero
  have hDn : D≠0 := by
    intro h
    have := congrArg (fun S : PowerSeries ℂ => S.coeff 0) h
    rw [hD0,map_zero] at this
    exact one_ne_zero this
  apply mul_left_cancel₀ hDn
  have hL : D*PowerSeries.map (algebraMap ℚ ℂ) lpsOriginalJQSeries=
      (qExpansion 1 ModularForm.E₄)^3 := by
    change lpsOriginalTaylorSeries (dslope (cuspFunction 1 ModularForm.discriminant) 0)*_= _
    rw [←lpsOriginalDeltaSlopeQSeries_map,lpsOriginalJQSeries,←map_mul]
    have hm := PowerSeries.mul_invOfUnit lpsOriginalDeltaSlopeQSeries 1
      lpsOriginalDeltaSlopeQSeries_constant
    rw [mul_left_comm,hm,mul_one,map_pow,lpsOriginalE4QSeries_map]
  have hne : ∀ᶠ q in 𝓝 (0:ℂ), dslope (cuspFunction 1 ModularForm.discriminant) 0 q≠0 := by
    exact lpsOriginalDeltaSlope_analytic.continuousAt.eventually_ne
      (by rw [lpsOriginalDeltaSlope_zero];norm_num)
  have hg : (dslope (cuspFunction 1 ModularForm.discriminant) 0)*lpsOriginalJQCoefficient=ᶠ[𝓝 0]
      (cuspFunction 1 ModularForm.E₄)^3 := by
    filter_upwards [hne] with q hq
    change dslope (cuspFunction 1 ModularForm.discriminant) 0 q*
      ((cuspFunction 1 ModularForm.E₄ q)^3/dslope (cuspFunction 1 ModularForm.discriminant) 0 q)=_
    simp only [Pi.pow_apply]
    field_simp [hq]
  have hR := lpsOriginalTaylorSeries_congr hg
  rw [lpsOriginalTaylorSeries_mul lpsOriginalDeltaSlope_analytic
    lpsOriginalJQCoefficient_analytic_zero,lpsOriginalTaylorSeries_pow
      (ModularFormClass.analyticAt_cuspFunction_zero ModularForm.E₄
        one_pos one_mem_strictPeriods_SL) 3] at hR
  exact hL.trans hR.symm

/-- Every actual Taylor coefficient of SAME original q-times-j analytic coefficient is a rational cast. -/
lemma lpsOriginalJQCoefficient_rational (n : ℕ) :
    ∃ a : ℚ, (a:ℂ)=(n.factorial:ℂ)⁻¹*iteratedDeriv n lpsOriginalJQCoefficient 0 := by
  refine ⟨lpsOriginalJQSeries.coeff n,?_⟩
  have h := congrArg (fun S : PowerSeries ℂ => S.coeff n) lpsOriginalJQSeries_map
  simpa only [PowerSeries.coeff_map,lpsOriginalTaylorSeries_coeff,eq_ratCast] using h

end
end QEC.Coding.TannerLiftedProduct
