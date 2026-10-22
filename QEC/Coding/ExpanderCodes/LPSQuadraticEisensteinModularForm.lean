import QEC.Coding.ExpanderCodes.LPSQuadraticEisensteinSeries

/-!
# Genuine modularity of the quadratic-character E2 twist

The determinant-derived unit gives an actual finite residue permutation. An
explicit integral determinant-one conjugate proves the translated E2 slash
law; its identical defect cancels against the genuine zero character sum.
This proves weight-two invariance on Gamma0(q^2). Actual E2 slash boundedness
and rational translation of rational cusps supply the full all-cusp condition,
so the existing finite sum is a genuine Mathlib ModularForm with its actual
character-weighted divisor coefficients.

The complete all-cusp theta correction, its centered coefficient estimate,
sparse-CSS runtime and the arbitrary-finite-field PK22 main theorem remain
unproved. Zero constant at infinity is not asserted to imply cuspidality.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

/-- The arithmetic residue compatibility gives a genuine determinant-one integer matrix. -/
lemma lpsE2ShiftConjugate_det (q : ℕ) (γ : SL(2,ℤ)) (k r s t : ℤ)
    (hC : γ 1 0=(q:ℤ)^2*k) (hrs : r*γ 1 1-s*γ 0 0=(q:ℤ)*t) :
    Matrix.det !![γ 0 0+r*(q:ℤ)*k,γ 0 1+t-r*s*k;(q:ℤ)^2*k,γ 1 1-s*(q:ℤ)*k]=1 := by
  have hd : γ 0 0*γ 1 1-γ 0 1*γ 1 0=1 := by
    simpa only [Matrix.det_fin_two] using γ.det_coe
  rw [hC] at hd
  rw [Matrix.det_fin_two]
  change (γ 0 0+r*(q:ℤ)*k)*(γ 1 1-s*(q:ℤ)*k)-
    (γ 0 1+t-r*s*k)*((q:ℤ)^2*k)=1
  linear_combination hd+(q:ℤ)*k*hrs

/-- The translated conjugate is constructed as an actual integral special-linear matrix. -/
def lpsE2ShiftConjugate (q : ℕ) (γ : SL(2,ℤ)) (k r s t : ℤ)
    (hC : γ 1 0=(q:ℤ)^2*k) (hrs : r*γ 1 1-s*γ 0 0=(q:ℤ)*t) : SL(2,ℤ) :=
  ⟨!![γ 0 0+r*(q:ℤ)*k,γ 0 1+t-r*s*k;(q:ℤ)^2*k,γ 1 1-s*(q:ℤ)*k],
    lpsE2ShiftConjugate_det q γ k r s t hC hrs⟩

/-- The arithmetic translated denominator equals the original denominator. -/
lemma lpsE2ShiftConjugate_denom (q k s d z : ℂ) (hq : q≠0) :
    q^2*k*(z+s/q)+(d-s*q*k)=q^2*k*z+d := by
  field_simp [hq]
  ring

/-- The actual matrix entries prove the translated upper-half-plane action. -/
lemma lpsE2ShiftConjugate_action (q : ℕ) [NeZero q] (γ δ : SL(2,ℤ)) (k r s t : ℤ)
    (hC : γ 1 0=(q:ℤ)^2*k) (hrs : r*γ 1 1-s*γ 0 0=(q:ℤ)*t)
    (h00 : δ 0 0=γ 0 0+r*(q:ℤ)*k) (h01 : δ 0 1=γ 0 1+t-r*s*k)
    (h10 : δ 1 0=(q:ℤ)^2*k) (h11 : δ 1 1=γ 1 1-s*(q:ℤ)*k) (z : ℍ) :
    δ • (((s:ℝ)/(q:ℝ)) +ᵥ z) = ((r:ℝ)/(q:ℝ)) +ᵥ (γ • z) := by
  apply UpperHalfPlane.ext
  have hqC : (q:ℂ)≠0 := by exact_mod_cast NeZero.ne q
  have hcc : (γ 1 0:ℂ)=(q:ℂ)^2*(k:ℂ) := by exact_mod_cast hC
  have hrsc : (r:ℂ)*(γ 1 1:ℂ)-(s:ℂ)*(γ 0 0:ℂ)=(q:ℂ)*(t:ℂ) := by
    exact_mod_cast hrs
  have hd : (γ 1 0:ℂ)*(z:ℂ)+(γ 1 1:ℂ)≠0 := by
    simpa only [ModularGroup.denom_apply] using UpperHalfPlane.denom_ne_zero γ z
  simp only [UpperHalfPlane.coe_specialLinearGroup_apply,UpperHalfPlane.coe_vadd]
  simp only [algebraMap_int_eq,Int.coe_castRingHom,Complex.ofReal_intCast,
    Complex.ofReal_div,Complex.ofReal_natCast]
  rw [h00,h01,h10,h11]
  push_cast
  rw [show (s:ℂ)/(q:ℂ)+(z:ℂ)=(z:ℂ)+(s:ℂ)/(q:ℂ) by ring,
    lpsE2ShiftConjugate_denom (q:ℂ) (k:ℂ) (s:ℂ) (γ 1 1:ℂ) (z:ℂ) hqC]
  rw [hcc] at hd ⊢
  field_simp [hqC,hd]
  linear_combination -hrsc

/-- The genuine E2 law and arithmetic action give the identical translated slash defect. -/
lemma lpsE2_shift_slash_of_entries (q : ℕ) [NeZero q] (γ δ : SL(2,ℤ)) (k r s t : ℤ)
    (hC : γ 1 0=(q:ℤ)^2*k) (hrs : r*γ 1 1-s*γ 0 0=(q:ℤ)*t)
    (h00 : δ 0 0=γ 0 0+r*(q:ℤ)*k) (h01 : δ 0 1=γ 0 1+t-r*s*k)
    (h10 : δ 1 0=(q:ℤ)^2*k) (h11 : δ 1 1=γ 1 1-s*(q:ℤ)*k) (z : ℍ) :
    (((fun w : ℍ => EisensteinSeries.E2 (((r:ℝ)/(q:ℝ)) +ᵥ w)) ∣[(2:ℤ)] γ) z) =
      EisensteinSeries.E2 (((s:ℝ)/(q:ℝ)) +ᵥ z) -
        (1/(2*riemannZeta 2)) * EisensteinSeries.D2 γ z := by
  have hqC : (q:ℂ)≠0 := by exact_mod_cast NeZero.ne q
  have hc : δ 1 0=γ 1 0 := h10.trans hC.symm
  have hd : UpperHalfPlane.denom δ ((((s:ℝ)/(q:ℝ)) +ᵥ z:ℍ):ℂ) =
      UpperHalfPlane.denom γ (z:ℂ) := by
    rw [ModularGroup.denom_apply,ModularGroup.denom_apply]
    simp only [UpperHalfPlane.coe_vadd,
      Complex.ofReal_div,Complex.ofReal_intCast,Complex.ofReal_natCast]
    rw [h10,h11,hC]
    push_cast
    rw [show (s:ℂ)/(q:ℂ)+(z:ℂ)=(z:ℂ)+(s:ℂ)/(q:ℂ) by ring]
    exact lpsE2ShiftConjugate_denom (q:ℂ) (k:ℂ) (s:ℂ) (γ 1 1:ℂ) (z:ℂ) hqC
  have hd2 : EisensteinSeries.D2 δ (((s:ℝ)/(q:ℝ)) +ᵥ z) =
      EisensteinSeries.D2 γ z := by
    simp only [EisensteinSeries.D2]
    rw [hc,hd]
  have h := congrFun (EisensteinSeries.E2_slash_action δ) (((s:ℝ)/(q:ℝ)) +ᵥ z)
  simp only [ModularForm.SL_slash_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
    Int.reduceNeg,zpow_neg,zpow_ofNat] at h ⊢
  rw [lpsE2ShiftConjugate_action q γ δ k r s t hC hrs h00 h01 h10 h11 z,hd,hd2] at h
  exact h

/-- The constructed integer conjugate proves the actual translated E2 slash law. -/
lemma lpsE2_real_shift_slash (q : ℕ) [NeZero q] (γ : SL(2,ℤ)) (k r s t : ℤ)
    (hC : γ 1 0=(q:ℤ)^2*k) (hrs : r*γ 1 1-s*γ 0 0=(q:ℤ)*t) (z : ℍ) :
    (((fun w : ℍ => EisensteinSeries.E2 (((r:ℝ)/(q:ℝ)) +ᵥ w)) ∣[(2:ℤ)] γ) z) =
      EisensteinSeries.E2 (((s:ℝ)/(q:ℝ)) +ᵥ z) -
        (1/(2*riemannZeta 2)) * EisensteinSeries.D2 γ z := by
  let δ := lpsE2ShiftConjugate q γ k r s t hC hrs
  exact lpsE2_shift_slash_of_entries q γ δ k r s t hC hrs rfl rfl rfl rfl z

/-- An actual nonzero square has quadratic-character value one. -/
lemma lpsQuadraticE2Character_square (q : ℕ) [Fact q.Prime] (d : ZMod q) (hd : d≠0) :
    lpsQuadraticE2Character q (d^2)=1 := by
  have hq := (quadraticChar_isQuadratic (ZMod q)).comp (Int.castRingHom ℂ)
  have h : (lpsQuadraticE2Character q)^2=1 := hq.sq_eq_one
  rw [map_pow,← MulChar.pow_apply' (lpsQuadraticE2Character q) (by norm_num : (2:ℕ)≠0),h,
    MulChar.one_apply (isUnit_iff_ne_zero.mpr hd)]

/-- A genuine unit square gives a bijection of the finite residue representatives. -/
noncomputable def lpsE2ResiduePermutation (q : ℕ) [Fact q.Prime] (d : ZMod q) (hd : d≠0) :
    Equiv.Perm (Fin q) :=
  (ZMod.finEquiv q).toEquiv.trans ((Equiv.mulLeft₀ (d^2) (pow_ne_zero 2 hd)).trans
    (ZMod.finEquiv q).toEquiv.symm)

/-- The constructed residue permutation has the intended field action. -/
lemma lpsE2ResiduePermutation_cast (q : ℕ) [Fact q.Prime] (d : ZMod q) (hd : d≠0)
    (r : Fin q) : ((lpsE2ResiduePermutation q d hd r).val:ZMod q)=d^2*(r.val:ZMod q) := by
  rw [lpsFin_cast_finEquiv,lpsFin_cast_finEquiv]
  exact (ZMod.finEquiv q).apply_symm_apply _

/-- The actual square permutation preserves the quadratic-character weight. -/
lemma lpsE2ResiduePermutation_character (q : ℕ) [Fact q.Prime] (d : ZMod q) (hd : d≠0)
    (r : Fin q) : lpsQuadraticE2Character q ((lpsE2ResiduePermutation q d hd r).val:ZMod q)=
      lpsQuadraticE2Character q (r.val:ZMod q) := by
  rw [lpsE2ResiduePermutation_cast,map_mul,lpsQuadraticE2Character_square q d hd,one_mul]

/-- Actual level membership gives the integer lower-left divisibility witness. -/
lemma lpsE2Gamma0_lower_entry (q : ℕ) (γ : SL(2,ℤ))
    (hγ : γ∈CongruenceSubgroup.Gamma0 (q^2)) : ∃ k : ℤ,γ 1 0=(q:ℤ)^2*k := by
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) (q^2)).mp
    (CongruenceSubgroup.Gamma0_mem.mp hγ)
  obtain ⟨k,hk⟩ := h
  exact ⟨k,by simpa only [Nat.cast_pow] using hk⟩

/-- The actual matrix determinant and level give the unit diagonal identity. -/
lemma lpsE2Gamma0_diagonal (q : ℕ) [Fact q.Prime] (γ : SL(2,ℤ)) (k : ℤ)
    (hC : γ 1 0=(q:ℤ)^2*k) : (γ 0 0:ZMod q)*(γ 1 1:ZMod q)=1 := by
  have hd : γ 0 0*γ 1 1-γ 0 1*γ 1 0=1 := by
    simpa only [Matrix.det_fin_two] using γ.det_coe
  have h : (γ 0 0:ZMod q)*(γ 1 1:ZMod q)-(γ 0 1:ZMod q)*(γ 1 0:ZMod q)=1 := by
    simpa only [map_sub,map_mul,map_one,Int.coe_castRingHom] using
      congrArg (Int.castRingHom (ZMod q)) hd
  have hc : (γ 1 0:ZMod q)=0 := by
    rw [hC]
    simp
  simpa only [hc,mul_zero,sub_zero] using h

/-- The actual residue permutation yields the integer translation compatibility. -/
lemma lpsE2Gamma0_shift_compatibility (q : ℕ) [Fact q.Prime] (γ : SL(2,ℤ))
    (hAD : (γ 0 0:ZMod q)*(γ 1 1:ZMod q)=1) (hd : (γ 1 1:ZMod q)≠0) (r : Fin q) :
    ∃ t : ℤ,(r.val:ℤ)*γ 1 1-
      ((lpsE2ResiduePermutation q (γ 1 1:ZMod q) hd r).val:ℤ)*γ 0 0=(q:ℤ)*t := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp
  push_cast
  rw [lpsE2ResiduePermutation_cast]
  calc
    (r.val:ZMod q)*(γ 1 1:ZMod q)-(γ 1 1:ZMod q)^2*(r.val:ZMod q)*(γ 0 0:ZMod q) =
      (r.val:ZMod q)*(γ 1 1:ZMod q)*(1-(γ 0 0:ZMod q)*(γ 1 1:ZMod q)) := by ring
    _ = 0 := by rw [hAD];ring

/-- The genuine nontrivial character sum vanishes at zero frequency. -/
lemma lpsQuadraticE2Character_sum_zero (q : ℕ) [Fact q.Prime] (hq2 : q≠2) :
    (∑ r : Fin q,lpsQuadraticE2Character q (r.val:ZMod q))=0 := by
  simpa only [Nat.cast_zero,Int.cast_zero,mul_zero,AddChar.map_zero_eq_one,mul_one,
    MulChar.map_zero,zero_mul] using lpsQuadraticE2Character_fin_fourier q hq2 0

/-- The actual finite permutation cancels the E2 defect and proves weight-two invariance. -/
lemma lpsQuadraticE2Twist_slash_gamma0 (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 (q^2)) :
    (lpsQuadraticE2Twist q ∣[(2:ℤ)] γ)=lpsQuadraticE2Twist q := by
  classical
  obtain ⟨k,hC⟩ := lpsE2Gamma0_lower_entry q γ hγ
  have hAD := lpsE2Gamma0_diagonal q γ k hC
  have hd : (γ 1 1:ZMod q)≠0 := by
    intro hd
    rw [hd,mul_zero] at hAD
    exact zero_ne_one hAD
  let e := lpsE2ResiduePermutation q (γ 1 1:ZMod q) hd
  ext z
  have hr (r : Fin q) :
      EisensteinSeries.E2 (((r.val:ℝ)/(q:ℝ)) +ᵥ (γ • z)) *
        UpperHalfPlane.denom γ (z:ℂ)^(-(2:ℤ)) =
      EisensteinSeries.E2 ((((e r).val:ℝ)/(q:ℝ)) +ᵥ z) -
        (1/(2*riemannZeta 2))*EisensteinSeries.D2 γ z := by
    obtain ⟨t,hrs⟩ := lpsE2Gamma0_shift_compatibility q γ hAD hd r
    simpa only [ModularForm.SL_slash_apply,Int.cast_natCast] using
      lpsE2_real_shift_slash q γ k (r.val:ℤ) ((e r).val:ℤ) t hC hrs z
  have hs : (∑ r : Fin q,lpsQuadraticE2Character q (r.val:ZMod q)*
      EisensteinSeries.E2 ((((e r).val:ℝ)/(q:ℝ)) +ᵥ z)) =
      (∑ r : Fin q,lpsQuadraticE2Character q (r.val:ZMod q)*
      EisensteinSeries.E2 (((r.val:ℝ)/(q:ℝ)) +ᵥ z)) := by
    calc
      _ = ∑ r : Fin q,lpsQuadraticE2Character q ((e r).val:ZMod q)*
          EisensteinSeries.E2 ((((e r).val:ℝ)/(q:ℝ)) +ᵥ z) := by
        apply Finset.sum_congr rfl
        intro r h
        rw [lpsE2ResiduePermutation_character]
      _ = _ := Equiv.sum_comp e (fun r : Fin q => lpsQuadraticE2Character q (r.val:ZMod q)*
          EisensteinSeries.E2 (((r.val:ℝ)/(q:ℝ)) +ᵥ z))
  simp only [ModularForm.SL_slash_apply,lpsQuadraticE2Twist]
  rw [mul_assoc,Finset.sum_mul]
  simp_rw [mul_assoc,hr,mul_sub]
  rw [Finset.sum_sub_distrib,← Finset.sum_mul,lpsQuadraticE2Character_sum_zero q hq2,
    zero_mul,sub_zero,hs]

/-- The actual denominator norm bounds the slash defect in the full infinity filter. -/
lemma lpsE2Defect_isBoundedAtImInfty (γ : SL(2,ℤ)) :
    UpperHalfPlane.IsBoundedAtImInfty (EisensteinSeries.D2 γ) := by
  apply UpperHalfPlane.isBoundedAtImInfty_iff.mpr
  refine ⟨‖(2*Real.pi*Complex.I:ℂ)‖,1,?_⟩
  intro z hz
  by_cases hc : γ 1 0=0
  · simp [EisensteinSeries.D2,hc]
  · have hcC : (γ 1 0:ℂ)≠0 := by exact_mod_cast hc
    have he : EisensteinSeries.D2 γ z =
        (2*Real.pi*Complex.I:ℂ)/((z:ℂ)+(γ 1 1:ℂ)/(γ 1 0:ℂ)) := by
      rw [EisensteinSeries.D2,ModularGroup.denom_apply]
      field_simp [hcC]
    have hi : ((z:ℂ)+(γ 1 1:ℂ)/(γ 1 0:ℂ)).im=z.im := by
      simp [← Complex.ofReal_intCast,← Complex.ofReal_div]
    have hn : 1≤‖(z:ℂ)+(γ 1 1:ℂ)/(γ 1 0:ℂ)‖ :=
      hz.trans (hi ▸ Complex.im_le_norm _)
    rw [he,norm_div]
    exact div_le_self (norm_nonneg _) hn

/-- The genuine E2 transformation proves boundedness after every integral slash action. -/
lemma lpsE2_slash_isBoundedAtImInfty (γ : SL(2,ℤ)) :
    UpperHalfPlane.IsBoundedAtImInfty (EisensteinSeries.E2 ∣[(2:ℤ)] γ) := by
  rw [EisensteinSeries.E2_slash_action]
  exact EisensteinSeries.isBoundedAtImInfty_E2.sub
    (BoundedAtFilter.smul _ (lpsE2Defect_isBoundedAtImInfty γ))

/-- The actual integral cusp representatives prove boundedness at all rational cusps. -/
lemma lpsE2_bounded_at_SL2Z_cusps (c : OnePoint ℝ) (hc : IsCusp c 𝒮ℒ) :
    OnePoint.IsBoundedAt c EisensteinSeries.E2 2 := by
  apply (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr
  intro γ hγ
  exact lpsE2_slash_isBoundedAtImInfty γ

/-- The real translation matrix is the image of its actual rational matrix. -/
lemma lpsE2RealTranslation_rational_map (r : ℚ) :
    (Matrix.GeneralLinearGroup.upperRightHom r).map (Rat.castHom ℝ) =
      Matrix.SpecialLinearGroup.mapGL ℝ (lpsE2RealTranslation (r:ℝ)) := by
  apply Units.ext
  ext i j
  change (Rat.castHom ℝ) (Matrix.GeneralLinearGroup.upperRightHom r i j) =
    (algebraMap ℝ ℝ) (lpsE2RealTranslation (r:ℝ) i j)
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.upperRightHom,lpsE2RealTranslation,Matrix.of_apply]

/-- Actual rational general-linear transformations preserve the rational cusp set. -/
lemma lpsRationalGL_smul_cusp (g : GL (Fin 2) ℚ) (c : OnePoint ℝ) (hc : IsCusp c 𝒮ℒ) :
    IsCusp (g.map (Rat.castHom ℝ) • c) 𝒮ℒ := by
  let _ := CongruenceSubgroup.isArithmetic_conj_SL2Z g
  exact (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp (hc.smul _)

/-- The real translation slash action is exactly the actual translated E2 function. -/
lemma lpsE2RealTranslation_slash (r : ℝ) :
    (EisensteinSeries.E2 ∣[(2:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ (lpsE2RealTranslation r)) =
      (fun z : ℍ => EisensteinSeries.E2 (r +ᵥ z)) := by
  ext z
  rw [ModularForm.slash_apply]
  have hact : Matrix.SpecialLinearGroup.mapGL ℝ (lpsE2RealTranslation r) • z=r +ᵥ z :=
    lpsE2RealTranslation_action r z
  rw [hact]
  have hd : UpperHalfPlane.denom
      (Matrix.SpecialLinearGroup.mapGL ℝ (lpsE2RealTranslation r)) (z:ℂ)=1 := by
    change (((algebraMap ℝ ℝ) (lpsE2RealTranslation r 1 0):ℝ):ℂ)*(z:ℂ)+
      (((algebraMap ℝ ℝ) (lpsE2RealTranslation r 1 1):ℝ):ℂ)=1
    simp [lpsE2RealTranslation,Matrix.of_apply]
  simp [UpperHalfPlane.σ,hd]

/-- Actual rational translations transport E2 boundedness at every cusp. -/
lemma lpsE2_rational_shift_bounded_at_cusps (r : ℚ) (c : OnePoint ℝ) (hc : IsCusp c 𝒮ℒ) :
    OnePoint.IsBoundedAt c (fun z : ℍ => EisensteinSeries.E2 ((r:ℝ) +ᵥ z)) 2 := by
  rw [← lpsE2RealTranslation_slash]
  apply OnePoint.IsBoundedAt.smul_iff.mp
  have hs := lpsRationalGL_smul_cusp (Matrix.GeneralLinearGroup.upperRightHom r) c hc
  rw [lpsE2RealTranslation_rational_map] at hs
  exact lpsE2_bounded_at_SL2Z_cusps _ hs

/-- Fixed complex scalar multiplication preserves genuine cusp boundedness. -/
lemma lpsCuspBounded_const_smul (c : OnePoint ℝ) (f : ℍ→ℂ) (a : ℂ)
    (hf : OnePoint.IsBoundedAt c f 2) : OnePoint.IsBoundedAt c (a • f) 2 := by
  intro g hg
  rw [ModularForm.smul_slash]
  exact BoundedAtFilter.smul _ (hf g hg)

/-- The actual finite weighted sum is bounded at every rational cusp. -/
lemma lpsQuadraticE2Twist_bounded_at_cusps (q : ℕ) [Fact q.Prime]
    (c : OnePoint ℝ) (hc : IsCusp c 𝒮ℒ) :
    OnePoint.IsBoundedAt c (lpsQuadraticE2Twist q) 2 := by
  classical
  have hb (s : Finset (Fin q)) : OnePoint.IsBoundedAt c
      (∑ r ∈ s, lpsQuadraticE2Character q (r.val:ZMod q) •
        (fun z : ℍ => EisensteinSeries.E2 (((r.val:ℝ)/(q:ℝ)) +ᵥ z))) 2 := by
    induction s using Finset.induction_on with
    | empty =>
      intro g hg
      simp only [Finset.sum_empty,SlashAction.zero_slash]
      exact UpperHalfPlane.zero_form_isBoundedAtImInfty
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      apply OnePoint.IsBoundedAt.add _ ih
      apply lpsCuspBounded_const_smul
      simpa only [Rat.cast_div,Rat.cast_natCast] using
        lpsE2_rational_shift_bounded_at_cusps ((a.val:ℚ)/(q:ℚ)) c hc
  have h := lpsCuspBounded_const_smul c _
    (gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹ (hb Finset.univ)
  convert h using 1
  ext z
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,lpsQuadraticE2Twist]

/-- Proved invariance, holomorphicity and all-cusp boundedness construct the genuine modular form. -/
noncomputable def lpsQuadraticE2TwistModularForm (q : ℕ) [Fact q.Prime] (hq2 : q≠2) :
    ModularForm (CongruenceSubgroup.Gamma0 (q^2) : Subgroup (GL (Fin 2) ℝ)) 2 where
  toFun := lpsQuadraticE2Twist q
  slash_action_eq' := by
    intro g hg
    obtain ⟨γ,hγ,rfl⟩ := hg
    simpa [Matrix.SpecialLinearGroup.mapGL,← ModularForm.SL_slash] using
      lpsQuadraticE2Twist_slash_gamma0 q hq2 γ hγ
  holo' := lpsQuadraticE2Twist_mdifferentiable q
  bdd_at_cusps' := fun hc => lpsQuadraticE2Twist_bounded_at_cusps q _
    (hc.mono (Subgroup.map_le_range (Matrix.SpecialLinearGroup.mapGL ℝ) _))

/-- The genuine modular form retains the actual normalized E2 sum. -/
@[simp] lemma lpsQuadraticE2TwistModularForm_apply (q : ℕ) [Fact q.Prime] (hq2 : q≠2) (z : ℍ) :
    lpsQuadraticE2TwistModularForm q hq2 z=lpsQuadraticE2Twist q z := rfl

/-- The constructed modular form retains the actual character-weighted divisor coefficients. -/
lemma coeff_qExpansion_lpsQuadraticE2TwistModularForm (q : ℕ) [Fact q.Prime] (hq2 : q≠2) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsQuadraticE2TwistModularForm q hq2)) =
      -24*(ArithmeticFunction.sigma 1 n:ℂ)*lpsQuadraticE2Character q (n:ZMod q) :=
  lpsQuadraticE2Twist_coeff_qExpansion q hq2 n

end QEC.Coding.TannerLiftedProduct
