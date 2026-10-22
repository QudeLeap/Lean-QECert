import QEC.Coding.ExpanderCodes.LPSThetaS
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Shifted theta series, residue transforms and Gauss limits

The shifted theta function is its actual absolutely summable integer series.
Reindexing integer residue classes derives the finite characteristic expansion
at every rational translate of S. Positive-real scaling preserves the principal
square-root branch. Real characteristics contribute unit-norm phases, so the
Gaussian tail bound is uniform over the real coordinate. Consequently the
finite characteristic sum converges to its actual quadratic Gauss sum along
the complete imaginary-part filter.

These are constructive analytic inputs to the actual LPS rational-cusp proof,
not assumptions of modularity, cusp boundedness or arithmetic coefficient growth.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Real Filter Topology

/-- Analytic shifted integer theta, represented through the actual two-variable Jacobi theta. -/
noncomputable def lpsShiftedTheta (a z : ℂ) : ℂ :=
  Complex.exp ((Real.pi:ℂ)*Complex.I*a^2*z) * jacobiTheta₂ (a*z) z

/-- Complete the square in the actual Jacobi series. -/
lemma lpsShiftedTheta_eq_tsum (a z : ℂ) : lpsShiftedTheta a z =
    ∑' n : ℤ, Complex.exp ((Real.pi:ℂ)*Complex.I*((n:ℂ)+a)^2*z) := by
  unfold lpsShiftedTheta jacobiTheta₂
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [jacobiTheta₂_term,← Complex.exp_add]
  congr 1
  ring

/-- Absolute summability is inherited from Jacobi theta on the upper half plane. -/
lemma summable_lpsShiftedTheta (a z : ℂ) (hz : 0<z.im) :
    Summable (fun n : ℤ => Complex.exp ((Real.pi:ℂ)*Complex.I*((n:ℂ)+a)^2*z)) := by
  have h := (hasSum_jacobiTheta₂_term (a*z) hz).summable.mul_left
    (Complex.exp ((Real.pi:ℂ)*Complex.I*a^2*z))
  apply h.congr
  intro n
  rw [jacobiTheta₂_term,← Complex.exp_add]
  congr 1
  ring

lemma lpsShiftedTheta_zero (z : ℂ) : lpsShiftedTheta 0 z=jacobiTheta z := by
  simp [lpsShiftedTheta,jacobiTheta_eq_jacobiTheta₂]

/-- Integer translation of the characteristic reindexes the whole integer series. -/
lemma lpsShiftedTheta_add_one (a z : ℂ) : lpsShiftedTheta (a+1) z=lpsShiftedTheta a z := by
  rw [lpsShiftedTheta_eq_tsum,lpsShiftedTheta_eq_tsum]
  conv_rhs => rw [← (Equiv.addRight (1:ℤ)).tsum_eq]
  apply tsum_congr
  intro n
  simp only [Equiv.coe_addRight,Int.cast_add,Int.cast_one]
  congr 1
  ring

/-- Actual two-variable Jacobi S identity with its exponential factor cancelled. -/
lemma lpsShiftedTheta_S (a z : ℂ) (hz : 0<z.im) :
    lpsShiftedTheta a (-1/z)=(-Complex.I*z)^(1/2:ℂ)*jacobiTheta₂ a z := by
  have hz0 : z≠0 := by intro he;subst z;simp at hz
  have hb : -Complex.I*z≠0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hz0
  have hp : (-Complex.I*z)^(1/2:ℂ)≠0 := (Complex.cpow_ne_zero_iff).mpr (Or.inl hb)
  have h := congrArg (fun w => (-Complex.I*z)^(1/2:ℂ)*w) (jacobiTheta₂_functional_equation a z)
  have he : lpsShiftedTheta a (-1/z)=
      Complex.exp (-(Real.pi:ℂ)*Complex.I*a^2/z)*jacobiTheta₂ (a/z) (-1/z) := by
    unfold lpsShiftedTheta
    have ha : a*(-1/z)=-(a/z) := by ring
    rw [ha,jacobiTheta₂_neg_left]
    congr 2
    ring
  rw [he]
  field_simp [hp] at h
  simpa only [neg_mul,neg_div,mul_comm Complex.I (Real.pi:ℂ)] using h.symm


/-- Actual residue-class quadratic exponential, not an assumed Gauss evaluation. -/
noncomputable def lpsQuadraticPhase (a : ℤ) (c : ℕ) (r : Fin c) : ℂ :=
  Complex.exp (2*(Real.pi:ℂ)*Complex.I*(a:ℂ)*(r.val:ℂ)^2/(c:ℂ))

/-- The integer quotient contributes an integral exponential period. -/
lemma lpsThetaResidue_term (a k : ℤ) (c : ℕ) [NeZero c] (r : Fin c) (z : ℂ) :
    Complex.exp ((Real.pi:ℂ)*Complex.I*((k:ℂ)*(c:ℂ)+(r.val:ℂ))^2*(z+2*(a:ℂ)/(c:ℂ))) =
      lpsQuadraticPhase a c r *
        Complex.exp ((Real.pi:ℂ)*Complex.I*((k:ℂ)+(r.val:ℂ)/(c:ℂ))^2*((c:ℂ)^2*z)) := by
  have hc : (c:ℂ)≠0 := by exact_mod_cast NeZero.ne c
  have he : (Real.pi:ℂ)*Complex.I*((k:ℂ)*(c:ℂ)+(r.val:ℂ))^2*(z+2*(a:ℂ)/(c:ℂ)) =
      2*(Real.pi:ℂ)*Complex.I*(a:ℂ)*(r.val:ℂ)^2/(c:ℂ) +
      (Real.pi:ℂ)*Complex.I*((k:ℂ)+(r.val:ℂ)/(c:ℂ))^2*((c:ℂ)^2*z) +
      ((a*(k^2*(c:ℤ)+2*k*(r.val:ℤ)) : ℤ):ℂ)*(2*(Real.pi:ℂ)*Complex.I) := by
    push_cast
    field_simp [hc]
    ring
  rw [he,Complex.exp_add,Complex.exp_int_mul_two_pi_mul_I,mul_one,Complex.exp_add]
  rfl

/-- Exact residue-class expansion of the actual Jacobi theta series. -/
lemma lpsTheta_residue_expansion (a : ℤ) (c : ℕ) [NeZero c] (z : ℂ) (hz : 0<z.im) :
    jacobiTheta (z+2*(a:ℂ)/(c:ℂ)) =
      ∑ r : Fin c, lpsQuadraticPhase a c r *
        lpsShiftedTheta ((r.val:ℂ)/(c:ℂ)) ((c:ℂ)^2*z) := by
  let τ := z+2*(a:ℂ)/(c:ℂ)
  have ht : 0<τ.im := by simpa [τ] using hz
  have hs : Summable (fun n : ℤ => Complex.exp ((Real.pi:ℂ)*Complex.I*(n:ℂ)^2*τ)) := by
    simpa only [jacobiTheta₂_term,mul_zero,zero_add] using (hasSum_jacobiTheta₂_term 0 ht).summable
  let e : Fin c × ℤ ≃ ℤ := ((Int.divModEquiv c).trans (Equiv.prodComm ℤ (Fin c))).symm
  have hse := hs.comp_injective e.injective
  dsimp only [Function.comp_def,τ] at hse
  rw [jacobiTheta,← e.tsum_eq,hse.tsum_prod,tsum_fintype]
  apply Finset.sum_congr rfl
  intro r hr
  rw [lpsShiftedTheta_eq_tsum,← tsum_mul_left]
  apply tsum_congr
  intro k
  change Complex.exp ((Real.pi:ℂ)*Complex.I*((k*(c:ℤ)+(r.val:ℤ):ℤ):ℂ)^2*τ)=_
  simp only [Int.cast_add,Int.cast_mul,Int.cast_natCast]
  exact lpsThetaResidue_term a k c r z


/-- Positive scaling fixes the square-root branch and contributes exactly 1/c. -/
lemma lpsShiftedTheta_scaled_S (a z : ℂ) (c : ℕ) [NeZero c] (hz : 0<z.im) :
    lpsShiftedTheta a ((c:ℂ)^2*(-1/z))=
      ((-Complex.I*z)^(1/2:ℂ)/(c:ℂ))*jacobiTheta₂ a (z/(c:ℂ)^2) := by
  have hcR : 0<(c:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne c)
  have hc : (c:ℂ)≠0 := by exact_mod_cast NeZero.ne c
  have hz0 : z≠0 := by intro he;subst z;simp at hz
  have hu : 0<(z/(c:ℂ)^2).im := by
    rw [← Complex.ofReal_natCast,← Complex.ofReal_pow,Complex.div_ofReal_im]
    exact div_pos hz (sq_pos_of_pos hcR)
  have h := lpsShiftedTheta_S a (z/(c:ℂ)^2) hu
  have ha : (c:ℂ)^2*(-1/z)=-1/(z/(c:ℂ)^2) := by field_simp
  rw [ha,h]
  have hb : -Complex.I*z≠0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hz0
  have hf := scaled_half_factor (1/(c:ℝ)) (by positivity) (-Complex.I*z) hb
  have he : ((1/(c:ℝ):ℝ):ℂ)^2*(-Complex.I*z)=-Complex.I*(z/(c:ℂ)^2) := by
    push_cast
    field_simp
  rw [he] at hf
  rw [hf]
  push_cast
  ring

/-- Exact finite characteristic/Gauss expansion at a rational translate of S. -/
lemma lpsTheta_rational_S (a : ℤ) (c : ℕ) [NeZero c] (z : ℂ) (hz : 0<z.im) :
    jacobiTheta (-1/z+2*(a:ℂ)/(c:ℂ))=
      ((-Complex.I*z)^(1/2:ℂ)/(c:ℂ)) *
        ∑ r : Fin c, lpsQuadraticPhase a c r * jacobiTheta₂ ((r.val:ℂ)/(c:ℂ)) (z/(c:ℂ)^2) := by
  have zn : z≠0 := by intro he;subst z;simp at hz
  have hi : 0<(-1/z).im := by
    simpa only [neg_div,one_div,Complex.neg_im,Complex.inv_im,neg_neg] using
      div_pos hz (Complex.normSq_pos.mpr zn)
  rw [lpsTheta_residue_expansion a c (-1/z) hi]
  simp_rw [lpsShiftedTheta_scaled_S _ z c hz]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  ring

/-- Real characteristic phases have norm one. -/
lemma jacobiTheta₂_term_norm_real_left (n : ℤ) (a : ℝ) (z : ℂ) :
    ‖jacobiTheta₂_term n (a:ℂ) z‖=‖Complex.exp ((Real.pi:ℂ)*Complex.I*(n:ℂ)^2*z)‖ := by
  rw [jacobiTheta₂_term,Complex.exp_add,norm_mul]
  have he : ‖Complex.exp (2*(Real.pi:ℂ)*Complex.I*(n:ℂ)*(a:ℂ))‖=1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re,Complex.mul_im]
  rw [he,one_mul]

/-- Pair the positive and negative terms after removing the constant term. -/
lemma hasSum_nat_jacobiTheta₂_real (a : ℝ) (z : ℂ) (hz : 0<z.im) :
    HasSum (fun n : ℕ => jacobiTheta₂_term (n+1) (a:ℂ) z +
      jacobiTheta₂_term (-(n+1)) (a:ℂ) z) (jacobiTheta₂ (a:ℂ) z-1) := by
  have h := (hasSum_jacobiTheta₂_term (a:ℂ) hz).nat_add_neg
  rw [← hasSum_nat_add_iff' 1] at h
  convert! h using 1
  simp [jacobiTheta₂_term,sub_eq_add_neg]

/-- Uniform Gaussian tail control for every real coordinate and real characteristic. -/
lemma norm_jacobiTheta₂_real_sub_one_le (a : ℝ) (z : ℂ) (hz : 0<z.im) :
    ‖jacobiTheta₂ (a:ℂ) z-1‖ ≤ 2/(1-Real.exp (-Real.pi*z.im))*Real.exp (-Real.pi*z.im) := by
  let y := Real.exp (-Real.pi*z.im)
  have hy : y<1 := Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr Real.pi_pos) hz)
  have hTerm : ∀ n : ℕ, ‖jacobiTheta₂_term (n+1) (a:ℂ) z +
      jacobiTheta₂_term (-(n+1)) (a:ℂ) z‖ ≤ 2*y^(n+1) := by
    intro n
    have hp := norm_exp_mul_sq_le hz (n+1)
    have hn := norm_exp_mul_sq_le hz (-(n+1))
    rw [← jacobiTheta₂_term_norm_real_left _ a] at hp hn
    have hh := (norm_add_le _ _).trans (add_le_add hp hn)
    have hAbs : ((n:ℤ)+1).natAbs=n+1 := by
      rw [← Int.natCast_one,← Int.natCast_add,Int.natAbs_natCast]
    simpa only [Int.natAbs_neg,hAbs,two_mul] using hh
  have hSum : HasSum (fun n : ℕ => 2*y^(n+1)) (2*(y/(1-y))) := by
    have hG := (hasSum_geometric_of_lt_one (Real.exp_pos _).le hy).mul_left (2*y)
    simpa only [pow_succ',div_eq_mul_inv,mul_assoc] using hG
  have hNorm : Summable (fun n : ℕ => ‖jacobiTheta₂_term (n+1) (a:ℂ) z +
      jacobiTheta₂_term (-(n+1)) (a:ℂ) z‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hTerm hSum.summable
  rw [← (hasSum_nat_jacobiTheta₂_real a z hz).tsum_eq]
  have h := (norm_tsum_le_tsum_norm hNorm).trans
    ((hNorm.tsum_mono hSum.summable hTerm).trans_eq hSum.tsum_eq)
  convert! h using 1
  ring


lemma isBigO_jacobiTheta₂_real_sub_one (a : ℝ) :
    (fun z : ℂ => jacobiTheta₂ (a:ℂ) z-1) =O[comap Complex.im atTop]
      fun z => Real.exp (-Real.pi*z.im) := by
  simp_rw [Asymptotics.IsBigO,Asymptotics.IsBigOWith,Filter.eventually_comap,Filter.eventually_atTop]
  refine ⟨2/(1-Real.exp (-(Real.pi*1))),1,fun y hy z hzy =>
    (norm_jacobiTheta₂_real_sub_one_le a z (hzy.symm ▸ zero_lt_one.trans_le hy)).trans ?_⟩
  rw [Real.norm_eq_abs,Real.abs_exp,hzy,neg_mul]
  gcongr
  simp [Real.pi_pos]

/-- Full imaginary-part-filter convergence; no restriction to a vertical path. -/
lemma tendsto_jacobiTheta₂_real_im_infty (a : ℝ) :
    Tendsto (fun z : ℂ => jacobiTheta₂ (a:ℂ) z) (comap Complex.im atTop) (𝓝 1) := by
  have him : Tendsto Complex.im (comap Complex.im atTop) atTop := tendsto_comap
  have he : Tendsto (fun z : ℂ => Real.exp (-Real.pi*z.im)) (comap Complex.im atTop) (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (him.const_mul_atTop_of_neg (neg_lt_zero.mpr Real.pi_pos))
  have h := (isBigO_jacobiTheta₂_real_sub_one a).trans_tendsto he
  simpa only [sub_add_cancel,zero_add] using h.add_const 1

lemma tendsto_jacobiTheta₂_real_affine (a t d : ℝ) (ht : 0<t) :
    Tendsto (fun z : UpperHalfPlane => jacobiTheta₂ (a:ℂ) (((z:ℂ)+(d:ℂ))/(t:ℂ)))
      UpperHalfPlane.atImInfty (𝓝 1) := by
  apply (tendsto_jacobiTheta₂_real_im_infty a).comp
  rw [tendsto_comap_iff]
  have him : Tendsto UpperHalfPlane.im UpperHalfPlane.atImInfty atTop := tendsto_comap
  simpa only [Function.comp_def,Complex.div_ofReal_im,Complex.add_im,Complex.ofReal_im,add_zero,
    UpperHalfPlane.coe_im] using him.atTop_div_const ht

/-- The genuine finite quadratic Gauss sum. -/
noncomputable def lpsUnaryQuadraticGauss (a : ℤ) (c : ℕ) : ℂ := ∑ r : Fin c, lpsQuadraticPhase a c r
/-- Finite characteristic transform of the genuine Jacobi theta. -/
noncomputable def lpsThetaGaussSum (a : ℤ) (c : ℕ) (z : ℂ) : ℂ :=
  ∑ r : Fin c, lpsQuadraticPhase a c r * jacobiTheta₂ ((r.val:ℂ)/(c:ℂ)) z

/-- The actual finite characteristic transform converges to its Gauss sum. -/
lemma tendsto_lpsThetaGaussSum_affine (a : ℤ) (c : ℕ) (t d : ℝ) (ht : 0<t) :
    Tendsto (fun z : UpperHalfPlane => lpsThetaGaussSum a c (((z:ℂ)+(d:ℂ))/(t:ℂ)))
      UpperHalfPlane.atImInfty (𝓝 (lpsUnaryQuadraticGauss a c)) := by
  unfold lpsThetaGaussSum lpsUnaryQuadraticGauss
  have h := tendsto_finsetSum Finset.univ (fun (r : Fin c) hr =>
    (tendsto_jacobiTheta₂_real_affine ((r.val:ℝ)/(c:ℝ)) t d ht).const_mul (lpsQuadraticPhase a c r))
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,mul_one] using h


lemma lpsUnaryQuadraticGauss_one (a : ℤ) : lpsUnaryQuadraticGauss a 1 = 1 := by
  simp [lpsUnaryQuadraticGauss,lpsQuadraticPhase]

lemma lpsUnaryQuadraticGauss_one_two : lpsUnaryQuadraticGauss 1 2 = 0 := by
  simp only [lpsUnaryQuadraticGauss,Fin.sum_univ_two,lpsQuadraticPhase]
  norm_num
  have he : 2*(Real.pi:ℂ)*Complex.I/2=(Real.pi:ℂ)*Complex.I := by ring
  rw [he,Complex.exp_pi_mul_I]
  ring

end QEC.Coding.TannerLiftedProduct
