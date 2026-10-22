import QEC.Coding.ExpanderCodes.LPSAnalyticTheta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ModularForms.Identities

/-!
# Actual LPS theta S transformation and cusp constants

The existing analytic product has an exact S transformation derived from
Mathlib's Jacobi-theta identity. Positive-real scaling preserves the principal
square-root branch; collecting the four factors gives the weight-two multiplier
and the denominator `32 * q^3`.

The full imaginary-part filter gives uniform limits over the real coordinate.
The product has constant one at infinity and its S-slash has nonzero constant
`-1 / (32 * q^3)` at cusp zero. These are concrete inputs to the future
rational-cusp transformation and Eisenstein-correction proofs. This module
asserts neither a modular/cusp-form structure nor arithmetic coefficient growth.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm

/-- A positive real factor does not change the complex logarithm branch. -/
lemma cpow_pos_real_mul (r : ℝ) (hr : 0 < r) (z s : ℂ) (hz : z ≠ 0) :
    ((r : ℂ) * z) ^ s = (r : ℂ) ^ s * z ^ s := by
  have hn : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hn hz),
    Complex.cpow_def_of_ne_zero hn,Complex.cpow_def_of_ne_zero hz,
    Complex.log_ofReal_mul hr hz,add_mul,Complex.exp_add,Complex.ofReal_log hr.le]

/-- Apply the actual Jacobi S identity to a positively rescaled argument. -/
lemma theta_scaled_S (c : ℝ) (hc : 0 < c) (z : ℂ) (hz : 0 < z.im) :
    jacobiTheta ((c : ℂ) * (-1 / z)) =
      (-Complex.I * (z / (c : ℂ))) ^ (1 / 2 : ℂ) * jacobiTheta (z / (c : ℂ)) := by
  have hn : (c : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hc
  have zn : z ≠ 0 := by intro h; simp [h] at hz
  let τ : UpperHalfPlane := ⟨z / (c : ℂ), by simpa [Complex.div_ofReal_im] using div_pos hz hc⟩
  have h := jacobiTheta_S_smul τ
  simp only [UpperHalfPlane.modular_S_smul] at h
  dsimp [τ] at h
  convert h using 1
  congr 1
  field_simp

/-- Positive square scaling contributes its positive square root. -/
lemma scaled_half_factor (r : ℝ) (hr : 0 < r) (z : ℂ) (hz : z ≠ 0) :
    (((r : ℂ)^2) * z) ^ (1 / 2 : ℂ) = (r : ℂ) * z ^ (1 / 2 : ℂ) := by
  have hp : 0 < r^2 := sq_pos_of_pos hr
  have h := cpow_pos_real_mul (r^2) hp z (1/2) hz
  simp only [Complex.ofReal_pow] at h
  rw [h]
  have hh : ((r : ℂ)^2) ^ (1/2 : ℂ) = (r : ℂ) := by
    simpa only [one_div] using Complex.sq_cpow_two_inv (x := (r : ℂ)) (by simpa using hr)
  rw [hh]

/-- The existing named LPS product transforms to the dual scaled product. -/
theorem lpsStandardTheta_S_raw (q : ℕ) (hq : 0 < q) (z : ℂ) (hz : 0 < z.im) :
    lpsStandardTheta q (-1/z) = -(z^2 / (32*(q:ℂ)^3)) *
      jacobiTheta (z/2) * jacobiTheta (z/(8*(q:ℂ)^2))^3 := by
  have qn : (q : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hq
  have zn : z ≠ 0 := by intro h; simp [h] at hz
  have h8 : (0 : ℝ) < 8*(q:ℝ)^2 := mul_pos (by norm_num) (sq_pos_of_pos (by exact_mod_cast hq))
  have hs2 := theta_scaled_S 2 (by norm_num) z hz
  have hs8 := theta_scaled_S (8*(q:ℝ)^2) h8 z hz
  norm_num only [Complex.ofReal_ofNat,Complex.ofReal_mul,Complex.ofReal_pow,
    Complex.ofReal_natCast] at hs2 hs8
  have hz2 : -Complex.I * (z/2) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
    (div_ne_zero zn (by norm_num))
  have hf := scaled_half_factor (1/(2*(q:ℝ))) (by positivity) (-Complex.I*(z/2)) hz2
  have he : ((1/(2*(q:ℝ)) : ℝ):ℂ)^2 * (-Complex.I*(z/2)) =
      -Complex.I*(z/(8*(q:ℂ)^2)) := by
    push_cast
    field_simp
    ring
  rw [he] at hf
  unfold lpsStandardTheta lpsAnalyticThetaProduct
  have hh : (((2*q)^2 : ℕ):ℂ) * (2*(-1/z)) = (8*(q:ℂ)^2)*(-1/z) := by
    push_cast
    ring
  rw [hh,hs2,hs8,hf]
  have hfour : ((-Complex.I*(z/2))^(1/2 : ℂ))^4 = (-Complex.I*(z/2))^2 := by
    rw [show (4 : ℕ) = 2*2 by norm_num,pow_mul,show (1/2 : ℂ) = (2 : ℂ)⁻¹ by norm_num,Complex.cpow_ofNat_inv_pow]
  calc
    _ = (((-Complex.I*(z/2))^(1/2 : ℂ))^4) *
        (((1/(2*(q:ℝ)) : ℝ):ℂ)^3) * jacobiTheta (z/2) *
          jacobiTheta (z/(8*(q:ℂ)^2))^3 := by ring
    _ = _ := by
      rw [hfour]
      push_cast
      field_simp
      simp only [Complex.I_sq]
      ring

/-- Actual weight-two S-slash, with no modularity hypothesis. -/
theorem lpsStandardTheta_slash_S (q : ℕ) (hq : 0 < q) (z : UpperHalfPlane) :
    ((fun w : UpperHalfPlane => lpsStandardTheta q w) ∣[(2 : ℤ)] ModularGroup.S) z =
      -(32*(q:ℂ)^3)⁻¹ * jacobiTheta ((z:ℂ)/2) *
        jacobiTheta ((z:ℂ)/(8*(q:ℂ)^2))^3 := by
  have qn : (q:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hq
  have zn : (z:ℂ) ≠ 0 := z.ne_zero
  rw [SlashInvariantForm.slash_S_apply]
  simp only
  rw [show (-(z:ℂ))⁻¹ = -1/(z:ℂ) by field_simp,
    lpsStandardTheta_S_raw q hq (z:ℂ) z.im_pos]
  simp only [zpow_neg,zpow_ofNat]
  field_simp

/-- Uniform theta limit in the full imaginary-part filter, not just a vertical path. -/
theorem tendsto_jacobiTheta_im_infty :
    Tendsto jacobiTheta (comap Complex.im atTop) (𝓝 1) := by
  have him : Tendsto Complex.im (comap Complex.im atTop) atTop := tendsto_comap
  have hexp : Tendsto (fun z : ℂ => Real.exp (-Real.pi * z.im))
      (comap Complex.im atTop) (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (him.const_mul_atTop_of_neg (neg_lt_zero.mpr Real.pi_pos))
  have h := isBigO_at_im_infty_jacobiTheta_sub_one.trans_tendsto hexp
  simpa only [sub_add_cancel,zero_add] using h.add_const 1

/-- Positive rescaling preserves the full imaginary-part convergence filter. -/
theorem tendsto_jacobiTheta_div_im_infty (c : ℝ) (hc : 0 < c) :
    Tendsto (fun z : UpperHalfPlane => jacobiTheta ((z:ℂ)/(c:ℂ)))
      UpperHalfPlane.atImInfty (𝓝 1) := by
  apply tendsto_jacobiTheta_im_infty.comp
  rw [tendsto_comap_iff]
  have him : Tendsto UpperHalfPlane.im UpperHalfPlane.atImInfty atTop := tendsto_comap
  simpa only [Function.comp_def,Complex.div_ofReal_im,UpperHalfPlane.coe_im] using
    him.atTop_div_const hc


/-- Positive multiplication also preserves full imaginary-part convergence. -/
theorem tendsto_jacobiTheta_mul_im_infty (c : ℝ) (hc : 0 < c) :
    Tendsto (fun z : UpperHalfPlane => jacobiTheta ((c:ℂ)*(z:ℂ)))
      UpperHalfPlane.atImInfty (𝓝 1) := by
  have h := tendsto_jacobiTheta_div_im_infty (1/c) (by positivity)
  simpa only [one_div,Complex.ofReal_inv,div_eq_mul_inv,inv_inv,mul_one,mul_comm] using h

/-- The actual theta product has constant one at the infinity cusp. -/
theorem tendsto_lpsStandardTheta_im_infty (q : ℕ) (hq : 0 < q) :
    Tendsto (fun z : UpperHalfPlane => lpsStandardTheta q z)
      UpperHalfPlane.atImInfty (𝓝 1) := by
  have h2 := tendsto_jacobiTheta_mul_im_infty 2 (by norm_num)
  have h8 := tendsto_jacobiTheta_mul_im_infty (8*(q:ℝ)^2) (by positivity)
  have h := h2.mul (h8.pow 3)
  norm_num only [Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_pow,
    Complex.ofReal_natCast,one_pow,mul_one] at h
  apply h.congr
  intro z
  unfold lpsStandardTheta lpsAnalyticThetaProduct
  have he : (((2*q)^2 : ℕ):ℂ)*(2*(z:ℂ)) = 8*(q:ℂ)^2*(z:ℂ) := by
    push_cast
    ring
  rw [he]

/-- The actual S-slash has a nonzero constant at cusp zero. -/
theorem tendsto_lpsStandardTheta_slash_S (q : ℕ) (hq : 0 < q) :
    Tendsto ((fun w : UpperHalfPlane => lpsStandardTheta q w) ∣[(2 : ℤ)] ModularGroup.S)
      UpperHalfPlane.atImInfty (𝓝 (-(32*(q:ℂ)^3)⁻¹)) := by
  have h2 := tendsto_jacobiTheta_div_im_infty 2 (by norm_num)
  have h8 := tendsto_jacobiTheta_div_im_infty (8*(q:ℝ)^2) (by positivity)
  have hc : Tendsto (fun _ : UpperHalfPlane => -(32*(q:ℂ)^3)⁻¹)
      UpperHalfPlane.atImInfty (𝓝 (-(32*(q:ℂ)^3)⁻¹)) := tendsto_const_nhds
  have h := (hc.mul h2).mul (h8.pow 3)
  norm_num only [Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_pow,
    Complex.ofReal_natCast,one_pow,mul_one] at h
  exact h.congr (fun z => (lpsStandardTheta_slash_S q hq z).symm)

theorem lpsStandardTheta_slash_S_not_zero_at_infty (q : ℕ) (hq : 0 < q) :
    ¬ UpperHalfPlane.IsZeroAtImInfty
      ((fun w : UpperHalfPlane => lpsStandardTheta q w) ∣[(2 : ℤ)] ModularGroup.S) := by
  intro h
  have he := tendsto_nhds_unique (tendsto_lpsStandardTheta_slash_S q hq) h
  have qn : (q:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hq
  exact (neg_ne_zero.mpr (inv_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 qn)))) he

end QEC.Coding.TannerLiftedProduct
