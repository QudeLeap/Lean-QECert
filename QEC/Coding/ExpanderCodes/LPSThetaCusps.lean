import QEC.Coding.ExpanderCodes.LPSThetaCharacteristics

/-!
# Actual LPS theta rational-cusp transforms and boundedness

For every actual determinant-one integer matrix, the named four-factor LPS
product has a finite limit after Mathlib's weight-two slash. Positive lower-left
entry gives the exact finite characteristic transform and Gauss-sum constant;
negative entries reduce by even weight, and zero entries reduce to integer
translations using the determinant. Full imaginary-part-filter convergence
implies boundedness at every rational cusp, uniformly over the real coordinate.

This supplies the cusp constants needed by genuine congruence-subgroup
modularity and an Eisenstein correction matching all cusps. It does not prove
scalar Gamma0 invariance, construct a ModularForm/CuspForm, or establish the
arithmetic Fourier growth or PK22 main theorem.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm

/-- Apply the actual rational S expansion using the determinant-one Mobius identity. -/
lemma lpsTheta_mobius_scaled (a b d : ℤ) (c s : ℕ) [NeZero c] (hs : 0<s)
    (hdet : a*d-b*(c:ℤ)=1) (z : ℂ) (hz : 0<z.im) :
    jacobiTheta (2*(s:ℂ)*(((a:ℂ)*z+(b:ℂ))/((c:ℂ)*z+(d:ℂ)))) =
      (-Complex.I*((z+(d:ℂ)/(c:ℂ))/(2*(s:ℂ))))^(1/2:ℂ) *
        lpsThetaGaussSum ((s:ℤ)*a) c ((z+(d:ℂ)/(c:ℂ))/(2*(s:ℂ))) := by
  have hcR : 0<(c:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne c)
  have hc : (c:ℂ)≠0 := by exact_mod_cast NeZero.ne c
  have hsR : 0<(s:ℝ) := by exact_mod_cast hs
  have hs0 : (s:ℂ)≠0 := by exact_mod_cast ne_of_gt hs
  have hden : (c:ℂ)*z+(d:ℂ)≠0 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.add_im,Complex.mul_im,Complex.natCast_re,Complex.natCast_im,
      Complex.intCast_im,zero_mul,add_zero,Complex.zero_im] at hi
    exact (mul_pos hcR hz).ne' hi
  have hden' : z*(c:ℂ)+(d:ℂ)≠0 := by simpa only [mul_comm z (c:ℂ)] using hden
  have hd : (a:ℂ)*(d:ℂ)-(b:ℂ)*(c:ℂ)=1 := by exact_mod_cast hdet
  have hphi : ((a:ℂ)*z+(b:ℂ))/((c:ℂ)*z+(d:ℂ)) =
      (a:ℂ)/(c:ℂ)-1/((c:ℂ)*((c:ℂ)*z+(d:ℂ))) := by
    field_simp [hc,hden,hden']
    linear_combination -hd
  let u := (z+(d:ℂ)/(c:ℂ))/(2*(s:ℂ))
  have hu : 0<u.im := by
    dsimp [u]
    rw [show 2*(s:ℂ)=((2*(s:ℝ):ℝ):ℂ) by push_cast;rfl,Complex.div_ofReal_im]
    simp only [Complex.add_im,Complex.div_im,Complex.intCast_im,Complex.natCast_im,
      mul_zero,zero_mul,sub_self,zero_div,add_zero]
    exact div_pos hz (by positivity)
  have hu0 : u≠0 := by
    apply ne_of_apply_ne Complex.im
    simpa only [Complex.zero_im] using ne_of_gt hu
  have hbig : 0<((c:ℂ)^2*u).im := by
    rw [← Complex.ofReal_natCast,← Complex.ofReal_pow,Complex.mul_im]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
    exact mul_pos (sq_pos_of_pos hcR) hu
  have harg : 2*(s:ℂ)*(((a:ℂ)*z+(b:ℂ))/((c:ℂ)*z+(d:ℂ))) =
      -1/((c:ℂ)^2*u)+2*(((s:ℤ)*a:ℤ):ℂ)/(c:ℂ) := by
    rw [hphi]
    dsimp [u]
    push_cast
    field_simp [hc,hs0,hden]
    ring
  rw [harg,lpsTheta_rational_S ((s:ℤ)*a) c ((c:ℂ)^2*u) hbig]
  have hf := scaled_half_factor (c:ℝ) hcR (-Complex.I*u)
    (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hu0)
  simp only [Complex.ofReal_natCast] at hf
  have he : -Complex.I*((c:ℂ)^2*u)=(c:ℂ)^2*(-Complex.I*u) := by ring
  rw [he,hf]
  have hdv : ((c:ℂ)^2*u)/(c:ℂ)^2=u := by field_simp
  simp only [hdv]
  rw [mul_div_cancel_left₀ _ hc]
  rfl


/-- Collect the four branch-compatible square roots of the existing LPS product. -/
lemma lpsStandardTheta_mobius_raw (q : ℕ) (hq : 0<q) (a b d : ℤ) (c : ℕ) [NeZero c]
    (hdet : a*d-b*(c:ℤ)=1) (z : ℂ) (hz : 0<z.im) :
    lpsStandardTheta q (((a:ℂ)*z+(b:ℂ))/((c:ℂ)*z+(d:ℂ))) =
      -((z+(d:ℂ)/(c:ℂ))^2/(32*(q:ℂ)^3)) *
        lpsThetaGaussSum a c ((z+(d:ℂ)/(c:ℂ))/2) *
        lpsThetaGaussSum (4*(q:ℤ)^2*a) c ((z+(d:ℂ)/(c:ℂ))/(8*(q:ℂ)^2))^3 := by
  have qn : (q:ℂ)≠0 := by exact_mod_cast ne_of_gt hq
  have h2 := lpsTheta_mobius_scaled a b d c 1 (by norm_num) hdet z hz
  norm_num only [Nat.cast_one,mul_one,one_mul,Int.cast_ofNat] at h2
  have h8 := lpsTheta_mobius_scaled a b d c (4*q^2) (by positivity) hdet z hz
  norm_num only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow] at h8
  rw [show (2:ℂ)*(4*(q:ℂ)^2)=8*(q:ℂ)^2 by ring] at h8
  let w := z+(d:ℂ)/(c:ℂ)
  have hw : 0<w.im := by
    simpa [w,Complex.div_im] using hz
  have wn : w≠0 := by
    apply ne_of_apply_ne Complex.im
    simpa only [Complex.zero_im] using ne_of_gt hw
  have hn2 : -Complex.I*(w/2)≠0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
    (div_ne_zero wn (by norm_num))
  have hf := scaled_half_factor (1/(2*(q:ℝ))) (by positivity) (-Complex.I*(w/2)) hn2
  have he : ((1/(2*(q:ℝ)):ℝ):ℂ)^2*(-Complex.I*(w/2))=-Complex.I*(w/(8*(q:ℂ)^2)) := by
    push_cast
    field_simp
    ring
  rw [he] at hf
  unfold lpsStandardTheta lpsAnalyticThetaProduct
  have harg : (((2*q)^2:ℕ):ℂ)*(2*(((a:ℂ)*z+(b:ℂ))/((c:ℂ)*z+(d:ℂ)))) =
      (8*(q:ℂ)^2)*(((a:ℂ)*z+(b:ℂ))/((c:ℂ)*z+(d:ℂ))) := by push_cast;ring
  rw [harg,h2,h8]
  change (-Complex.I*(w/2))^(1/2:ℂ)*lpsThetaGaussSum a c (w/2)*
      ((-Complex.I*(w/(8*(q:ℂ)^2)))^(1/2:ℂ)*lpsThetaGaussSum (4*(q:ℤ)^2*a) c (w/(8*(q:ℂ)^2)))^3 = _
  rw [hf]
  have hfour : ((-Complex.I*(w/2))^(1/2:ℂ))^4=(-Complex.I*(w/2))^2 := by
    rw [show (4:ℕ)=2*2 by norm_num,pow_mul,show (1/2:ℂ)=(2:ℂ)⁻¹ by norm_num,
      Complex.cpow_ofNat_inv_pow]
  calc
    _ = ((-Complex.I*(w/2))^(1/2:ℂ))^4 * (((1/(2*(q:ℝ)):ℝ):ℂ)^3) *
        lpsThetaGaussSum a c (w/2)*lpsThetaGaussSum (4*(q:ℤ)^2*a) c (w/(8*(q:ℂ)^2))^3 := by ring
    _ = _ := by
      rw [hfour]
      push_cast
      field_simp
      simp only [Complex.I_sq]
      ring


open scoped MatrixGroups ModularForm

/-- Exact Mathlib weight-two slash, including its sign and c-squared normalization. -/
lemma lpsStandardTheta_slash_pos_c (q : ℕ) (hq : 0<q) (γ : SL(2,ℤ)) (hc : 0<γ 1 0)
    (z : UpperHalfPlane) :
    ((fun w : UpperHalfPlane => lpsStandardTheta q w) ∣[(2:ℤ)] γ) z =
      -(32*(q:ℂ)^3*((γ 1 0).toNat:ℂ)^2)⁻¹ *
        lpsThetaGaussSum (γ 0 0) (γ 1 0).toNat ((z+(γ 1 1:ℂ)/(γ 1 0:ℂ))/2) *
        lpsThetaGaussSum (4*(q:ℤ)^2*γ 0 0) (γ 1 0).toNat
          ((z+(γ 1 1:ℂ)/(γ 1 0:ℂ))/(8*(q:ℂ)^2))^3 := by
  let c := (γ 1 0).toNat
  have hcn : 0<c := by omega
  let : NeZero c := ⟨ne_of_gt hcn⟩
  have hci : (c:ℤ)=γ 1 0 := Int.toNat_of_nonneg hc.le
  have hcc : (c:ℂ)=(γ 1 0:ℂ) := by exact_mod_cast hci
  have hd : γ 0 0*γ 1 1-γ 0 1*(c:ℤ)=1 := by
    rw [hci]
    simpa only [Matrix.det_fin_two] using γ.det_coe
  have hm : ((γ • z : UpperHalfPlane):ℂ)=((γ 0 0:ℂ)*z+(γ 0 1:ℂ))/((c:ℂ)*z+(γ 1 1:ℂ)) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp [hcc]
  have hD : (c:ℂ)*z+(γ 1 1:ℂ)≠0 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.add_im,Complex.mul_im,Complex.natCast_re,Complex.natCast_im,
      Complex.intCast_im,zero_mul,add_zero,Complex.zero_im] at hi
    exact (mul_pos (show 0<(c:ℝ) by exact_mod_cast hcn) z.im_pos).ne' hi
  have qn : (q:ℂ)≠0 := by exact_mod_cast ne_of_gt hq
  have cn : (c:ℂ)≠0 := by exact_mod_cast ne_of_gt hcn
  rw [ModularForm.SL_slash_apply,hm,lpsStandardTheta_mobius_raw q hq (γ 0 0) (γ 0 1) (γ 1 1) c hd z z.im_pos]
  simp only [ModularGroup.denom_apply,zpow_neg,zpow_ofNat]
  rw [← hcc]
  change -( ((z:ℂ)+(γ 1 1:ℂ)/(c:ℂ))^2/(32*(q:ℂ)^3)) *
      lpsThetaGaussSum (γ 0 0) c (((z:ℂ)+(γ 1 1:ℂ)/(c:ℂ))/2) *
      lpsThetaGaussSum (4*(q:ℤ)^2*γ 0 0) c (((z:ℂ)+(γ 1 1:ℂ)/(c:ℂ))/(8*(q:ℂ)^2))^3 *
      (((c:ℂ)*(z:ℂ)+(γ 1 1:ℂ))^2)⁻¹ =
      -(32*(q:ℂ)^3*(c:ℂ)^2)⁻¹ *
        lpsThetaGaussSum (γ 0 0) c (((z:ℂ)+(γ 1 1:ℂ)/(c:ℂ))/2) *
        lpsThetaGaussSum (4*(q:ℤ)^2*γ 0 0) c (((z:ℂ)+(γ 1 1:ℂ)/(c:ℂ))/(8*(q:ℂ)^2))^3
  have hD' : (z:ℂ)*(c:ℂ)+(γ 1 1:ℂ)≠0 := by simpa only [mul_comm (z:ℂ) (c:ℂ)] using hD
  field_simp [qn,cn,hD,hD']

/-- The genuine positive-denominator cusp constant is its finite Gauss product. -/
lemma tendsto_lpsStandardTheta_slash_pos_c (q : ℕ) (hq : 0<q) (γ : SL(2,ℤ)) (hc : 0<γ 1 0) :
    Tendsto (((fun w : UpperHalfPlane => lpsStandardTheta q w) ∣[(2:ℤ)] γ))
      UpperHalfPlane.atImInfty
      (𝓝 (-(32*(q:ℂ)^3*((γ 1 0).toNat:ℂ)^2)⁻¹ *
        lpsUnaryQuadraticGauss (γ 0 0) (γ 1 0).toNat *
        lpsUnaryQuadraticGauss (4*(q:ℤ)^2*γ 0 0) (γ 1 0).toNat ^3)) := by
  have h1 := tendsto_lpsThetaGaussSum_affine (γ 0 0) (γ 1 0).toNat 2
    ((γ 1 1:ℝ)/(γ 1 0:ℝ)) (by norm_num)
  have h8 := tendsto_lpsThetaGaussSum_affine (4*(q:ℤ)^2*γ 0 0) (γ 1 0).toNat
    (8*(q:ℝ)^2) ((γ 1 1:ℝ)/(γ 1 0:ℝ)) (by positivity)
  have h := (h1.mul (h8.pow 3)).const_mul (-(32*(q:ℂ)^3*((γ 1 0).toNat:ℂ)^2)⁻¹)
  simp only [Complex.ofReal_div,Complex.ofReal_intCast,Complex.ofReal_mul,Complex.ofReal_ofNat,
    Complex.ofReal_pow,Complex.ofReal_natCast] at h
  have he : ((fun w : UpperHalfPlane => lpsStandardTheta q w) ∣[(2:ℤ)] γ)=
      (fun z : UpperHalfPlane => -(32*(q:ℂ)^3*((γ 1 0).toNat:ℂ)^2)⁻¹ *
        lpsThetaGaussSum (γ 0 0) (γ 1 0).toNat (((z:ℂ)+(γ 1 1:ℂ)/(γ 1 0:ℂ))/2) *
        lpsThetaGaussSum (4*(q:ℤ)^2*γ 0 0) (γ 1 0).toNat
          (((z:ℂ)+(γ 1 1:ℂ)/(γ 1 0:ℂ))/(8*(q:ℂ)^2))^3) := by
    funext z
    exact lpsStandardTheta_slash_pos_c q hq γ hc z
  rw [he]
  simpa only [mul_assoc] using h


/-- Weight two removes the matrix-negation sign without changing its action. -/
lemma lpsStandardTheta_slash_neg_matrix (q : ℕ) (γ : SL(2,ℤ)) :
    ((fun w : UpperHalfPlane => lpsStandardTheta q w) ∣[(2:ℤ)] (-γ)) =
      ((fun w : UpperHalfPlane => lpsStandardTheta q w) ∣[(2:ℤ)] γ) := by
  funext z
  rw [ModularForm.SL_slash_apply,ModularForm.SL_slash_apply,ModularGroup.SL_neg_smul]
  simp only [ModularGroup.denom_apply]
  have hd : ((-γ) 1 0 : ℂ)*z+((-γ) 1 1 : ℂ) = -((γ 1 0 : ℂ)*z+(γ 1 1 : ℂ)) := by
    simp
    ring
  rw [hd]
  simp only [zpow_neg,zpow_ofNat,neg_sq]

/-- Determinant one forces either diagonal sign, giving an integer translation. -/
lemma lpsStandardTheta_slash_zero_c (q : ℕ) (γ : SL(2,ℤ)) (hc : γ 1 0=0) :
    ((fun w : UpperHalfPlane => lpsStandardTheta q w) ∣[(2:ℤ)] γ) =
      (fun w : UpperHalfPlane => lpsStandardTheta q w) := by
  have hdet : γ 0 0*γ 1 1=1 := by
    simpa only [Matrix.det_fin_two,hc,mul_zero,sub_zero] using γ.det_coe
  have hp : Function.Periodic (lpsStandardTheta q) 1 := lpsStandardTheta_add_one q
  have hshift (n : ℤ) (z : ℂ) : lpsStandardTheta q (z+(n:ℂ))=lpsStandardTheta q z := by
    simpa only [mul_one] using hp.int_mul n z
  have hm (z : UpperHalfPlane) : ((γ • z : UpperHalfPlane):ℂ) =
      ((γ 0 0:ℂ)*z+(γ 0 1:ℂ))/((γ 1 0:ℂ)*z+(γ 1 1:ℂ)) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp
  funext z
  rw [ModularForm.SL_slash_apply]
  change lpsStandardTheta q ((γ • z : UpperHalfPlane):ℂ) *
    (((γ 1 0:ℂ)*z+(γ 1 1:ℂ)) ^ (-(2:ℤ))) = lpsStandardTheta q z
  rw [hm]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨ha,hd⟩ | ⟨ha,hd⟩
  · simpa [hc,ha,hd] using hshift (γ 0 1) z
  · simpa [hc,ha,hd,sub_eq_add_neg,div_neg,neg_add,add_comm] using hshift (-γ 0 1) z

/-- Every actual rational-cusp slash has a finite full-filter limit. -/
lemma exists_tendsto_lpsStandardTheta_slash (q : ℕ) (hq : 0<q) (γ : SL(2,ℤ)) :
    ∃ v : ℂ, Tendsto ((fun w : UpperHalfPlane => lpsStandardTheta q w) ∣[(2:ℤ)] γ)
      UpperHalfPlane.atImInfty (𝓝 v) := by
  rcases lt_trichotomy (γ 1 0) 0 with hn | hz | hp
  · have hpos : 0<(-γ) 1 0 := by simpa using neg_pos.mpr hn
    have h := tendsto_lpsStandardTheta_slash_pos_c q hq (-γ) hpos
    rw [lpsStandardTheta_slash_neg_matrix] at h
    exact ⟨_,h⟩
  · rw [lpsStandardTheta_slash_zero_c q γ hz]
    exact ⟨1,tendsto_lpsStandardTheta_im_infty q hq⟩
  · exact ⟨_,tendsto_lpsStandardTheta_slash_pos_c q hq γ hp⟩

/-- Every actual rational-cusp slash is bounded along the complete imaginary-part filter. -/
lemma lpsStandardTheta_isBoundedAtImInfty_slash (q : ℕ) (hq : 0<q) (γ : SL(2,ℤ)) :
    UpperHalfPlane.IsBoundedAtImInfty ((fun w : UpperHalfPlane => lpsStandardTheta q w) ∣[(2:ℤ)] γ) := by
  obtain ⟨v,hv⟩ := exists_tendsto_lpsStandardTheta_slash q hq γ
  exact hv.isBigO_one ℝ

end QEC.Coding.TannerLiftedProduct
