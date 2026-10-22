import QEC.Coding.ExpanderCodes.LPSQuadraticEisensteinCuspGeneral

/-!
# Genuine weight-two E2-difference modular forms

The actual E2(z) - m E2(m z) cancels the genuine E2 transformation defect. Its
integral dilation conjugate is constructed from level divisibility, and its
actual action, denominator and divided defect prove Gamma0(m) invariance.
Holomorphicity and full-filter constants at every cusp then construct the
actual Mathlib ModularForm. Genuine nome dilation and injective series
reindexing prove the convergent divisor-difference series; period-one analytic
uniqueness computes every actual q-expansion coefficient, including 1 - m at
zero.

The complete untwisted basis and its all-cusp constants support the LPS theta
Eisenstein correction. The additional character basis, full theta correction,
stronger coefficient growth, complete sparse-CSS runtime and exact PK22 main
theorem remain separate proof obligations. No target transformation, cusp
condition or coefficient is assumed, and no public lifecycle is advanced.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

/-- The actual E2 difference uses the genuine affine dilation with its required determinant multiplier. -/
noncomputable def lpsE2Difference (m : ℕ) (hm : 0 < m) (z : ℍ) : ℂ :=
  EisensteinSeries.E2 z-(m:ℂ)*EisensteinSeries.E2 (lpsE2AffineMatrix m hm 0 • z)

/-- Actual E2 and dilated E2 full-filter limits give the complete difference cusp vector. -/
lemma lpsE2Difference_cusp_tendsto (m : ℕ) (hm : 0 < m) (γ : SL(2,ℤ)) :
    Tendsto (lpsE2Difference m hm ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (1-((Int.gcd ((m:ℤ)*γ 0 0) (γ 1 0):ℕ):ℂ)^2/(m:ℂ))) := by
  have hE := lpsE2_slash_tendsto_one γ
  have hM := lpsE2Affine_cusp_tendsto m 1 hm (by decide) 0 γ
  simp only [Nat.cast_one,zero_mul,one_mul,add_zero,
    one_pow] at hM
  have h := hE.sub (hM.const_mul (m:ℂ))
  have hmC : (m:ℂ)≠0 := by exact_mod_cast hm.ne'
  have hv : 1-(m:ℂ)*(((Int.gcd ((m:ℤ)*γ 0 0) (γ 1 0):ℕ):ℂ)^2/(m:ℂ)^2) =
      1-((Int.gcd ((m:ℤ)*γ 0 0) (γ 1 0):ℕ):ℂ)^2/(m:ℂ) := by
    field_simp [hmC]
  rw [hv] at h
  convert h using 1
  funext z
  simp only [ModularForm.SL_slash_apply,lpsE2Difference]
  ring

/-- The genuine level divisibility and integral determinant identity prove the dilation conjugate determinant. -/
lemma lpsE2DilationConjugate_det (m : ℕ) (γ : SL(2,ℤ)) (k : ℤ)
    (hc : γ 1 0=(m:ℤ)*k) :
    Matrix.det !![γ 0 0,(m:ℤ)*γ 0 1;k,γ 1 1]=1 := by
  have hd : γ 0 0*γ 1 1-γ 0 1*γ 1 0=1 := by
    simpa only [Matrix.det_fin_two] using γ.det_coe
  rw [hc] at hd
  rw [Matrix.det_fin_two]
  change γ 0 0*γ 1 1-((m:ℤ)*γ 0 1)*k=1
  linear_combination hd

/-- Construct the actual integral determinant-one dilation conjugate, used by its slash semantics. -/
def lpsE2DilationConjugate (m : ℕ) (γ : SL(2,ℤ)) (k : ℤ)
    (hc : γ 1 0=(m:ℤ)*k) : SL(2,ℤ) :=
  ⟨!![γ 0 0,(m:ℤ)*γ 0 1;k,γ 1 1],lpsE2DilationConjugate_det m γ k hc⟩

/-- Arithmetic entries and the actual affine action prove the true conjugated dilation action. -/
lemma lpsE2DilationConjugate_action (m : ℕ) (hm : 0 < m) (γ δ : SL(2,ℤ))
    (k : ℤ) (hc : γ 1 0=(m:ℤ)*k)
    (h00 : δ 0 0=γ 0 0) (h01 : δ 0 1=(m:ℤ)*γ 0 1)
    (h10 : δ 1 0=k) (h11 : δ 1 1=γ 1 1) (z : ℍ) :
    δ • (lpsE2AffineMatrix m hm 0 • z) = lpsE2AffineMatrix m hm 0 • (γ • z) := by
  have hd : (γ 1 0:ℂ)*(z:ℂ)+(γ 1 1:ℂ)≠0 := by
    simpa only [ModularGroup.denom_apply] using UpperHalfPlane.denom_ne_zero γ z
  rw [hc] at hd
  push_cast at hd
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply,lpsE2AffineMatrix_action,
    lpsE2AffineMatrix_action,UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [Complex.ofReal_zero,add_zero,algebraMap_int_eq,Int.coe_castRingHom,
    Complex.ofReal_intCast]
  rw [h00,h01,h10,h11,hc]
  push_cast
  field_simp [hd]

/-- The genuine scaled lower row has the original actual denominator. -/
lemma lpsE2DilationConjugate_denom (m : ℕ) (hm : 0 < m) (γ δ : SL(2,ℤ))
    (k : ℤ) (hc : γ 1 0=(m:ℤ)*k) (h10 : δ 1 0=k) (h11 : δ 1 1=γ 1 1) (z : ℍ) :
    UpperHalfPlane.denom δ ((lpsE2AffineMatrix m hm 0 • z:ℍ):ℂ)=
      UpperHalfPlane.denom γ (z:ℂ) := by
  rw [ModularGroup.denom_apply,ModularGroup.denom_apply,lpsE2AffineMatrix_action,
    h10,h11,hc]
  push_cast
  ring

/-- The actual denominator and scaled lower-left entry give the true divided E2 defect. -/
lemma lpsE2DilationConjugate_D2 (m : ℕ) (hm : 0 < m) (γ δ : SL(2,ℤ))
    (k : ℤ) (hc : γ 1 0=(m:ℤ)*k) (h10 : δ 1 0=k) (h11 : δ 1 1=γ 1 1) (z : ℍ) :
    EisensteinSeries.D2 δ (lpsE2AffineMatrix m hm 0 • z)=
      (m:ℂ)⁻¹*EisensteinSeries.D2 γ z := by
  have hd : UpperHalfPlane.denom γ (z:ℂ)≠0 := UpperHalfPlane.denom_ne_zero γ z
  have hmC : (m:ℂ)≠0 := by exact_mod_cast hm.ne'
  simp only [EisensteinSeries.D2]
  rw [lpsE2DilationConjugate_denom m hm γ δ k hc h10 h11 z,h10,hc]
  push_cast
  field_simp [hmC,hd]

/-- The genuine E2 slash law and constructed action/denominator/defect prove the dilated slash formula. -/
lemma lpsE2Dilated_slash_of_entries (m : ℕ) (hm : 0 < m) (γ δ : SL(2,ℤ))
    (k : ℤ) (hc : γ 1 0=(m:ℤ)*k)
    (h00 : δ 0 0=γ 0 0) (h01 : δ 0 1=(m:ℤ)*γ 0 1)
    (h10 : δ 1 0=k) (h11 : δ 1 1=γ 1 1) (z : ℍ) :
    (((fun w : ℍ => EisensteinSeries.E2 (lpsE2AffineMatrix m hm 0 • w))
      ∣[(2:ℤ)] γ) z)=
      EisensteinSeries.E2 (lpsE2AffineMatrix m hm 0 • z)-
        (1/(2*riemannZeta 2))*(m:ℂ)⁻¹*EisensteinSeries.D2 γ z := by
  have h := congrFun (EisensteinSeries.E2_slash_action δ) (lpsE2AffineMatrix m hm 0 • z)
  simp only [ModularForm.SL_slash_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at h ⊢
  rw [lpsE2DilationConjugate_action m hm γ δ k hc h00 h01 h10 h11 z,
    lpsE2DilationConjugate_denom m hm γ δ k hc h10 h11 z,
    lpsE2DilationConjugate_D2 m hm γ δ k hc h10 h11 z] at h
  simpa only [mul_assoc] using h

/-- Instantiate the arithmetic helper with the actual constructed integral matrix. -/
lemma lpsE2Dilated_slash (m : ℕ) (hm : 0 < m) (γ : SL(2,ℤ)) (k : ℤ)
    (hc : γ 1 0=(m:ℤ)*k) (z : ℍ) :
    (((fun w : ℍ => EisensteinSeries.E2 (lpsE2AffineMatrix m hm 0 • w))
      ∣[(2:ℤ)] γ) z)=
      EisensteinSeries.E2 (lpsE2AffineMatrix m hm 0 • z)-
        (1/(2*riemannZeta 2))*(m:ℂ)⁻¹*EisensteinSeries.D2 γ z :=
  lpsE2Dilated_slash_of_entries m hm γ (lpsE2DilationConjugate m γ k hc) k hc rfl rfl rfl rfl z

/-- Actual level divisibility constructs the conjugate and cancellation proves genuine invariance. -/
lemma lpsE2Difference_slash_gamma0 (m : ℕ) (hm : 0 < m) (γ : SL(2,ℤ))
    (hγ : γ∈CongruenceSubgroup.Gamma0 m) :
    (lpsE2Difference m hm ∣[(2:ℤ)] γ)=lpsE2Difference m hm := by
  rw [CongruenceSubgroup.Gamma0_mem] at hγ
  have hdvd : (m:ℤ)∣γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) m).mp hγ
  obtain ⟨k,hk⟩ := hdvd
  have hmC : (m:ℂ)≠0 := by exact_mod_cast hm.ne'
  have hE := congrFun (EisensteinSeries.E2_slash_action γ)
  funext z
  have hM := lpsE2Dilated_slash m hm γ k hk z
  have hEz := hE z
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at hEz
  have he : ((lpsE2Difference m hm ∣[(2:ℤ)] γ) z)=
      ((EisensteinSeries.E2 ∣[(2:ℤ)] γ) z)-(m:ℂ)*
        (((fun w : ℍ => EisensteinSeries.E2 (lpsE2AffineMatrix m hm 0 • w))
          ∣[(2:ℤ)] γ) z) := by
    simp only [ModularForm.SL_slash_apply,lpsE2Difference]
    ring
  rw [he,hEz,hM,lpsE2Difference]
  have he : (m:ℂ)*((1/(2*riemannZeta 2))*(m:ℂ)⁻¹*EisensteinSeries.D2 γ z)=
      (1/(2*riemannZeta 2))*EisensteinSeries.D2 γ z := by
    calc _=((m:ℂ)*(m:ℂ)⁻¹)*((1/(2*riemannZeta 2))*EisensteinSeries.D2 γ z) := by ring
         _=_ := by rw [mul_inv_cancel₀ hmC];simp
  rw [mul_sub,he]
  ring

/-- Actual positive-determinant action preserves E2 holomorphicity and the genuine difference. -/
lemma lpsE2Difference_mdifferentiable (m : ℕ) (hm : 0 < m) : MDiff (lpsE2Difference m hm) := by
  have hp : 0<(lpsE2AffineMatrix m hm 0).det.val := by
    rw [lpsE2AffineMatrix_det]
    exact_mod_cast hm
  have h := E2_mdifferentiable.sub
    ((E2_mdifferentiable.comp (UpperHalfPlane.mdifferentiable_smul hp)).const_smul (m:ℂ))
  exact h

/-- The full-filter constant after every integral cusp gives actual boundedness at all rational cusps. -/
lemma lpsE2Difference_bounded_at_cusps (m : ℕ) (hm : 0 < m)
    (c : OnePoint ℝ) (hc : IsCusp c 𝒮ℒ) : OnePoint.IsBoundedAt c (lpsE2Difference m hm) 2 := by
  apply (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr
  intro γ hγ
  exact (lpsE2Difference_cusp_tendsto m hm γ).isBigO_one ℝ

/-- Proved invariance, holomorphicity and full cusp boundedness construct the genuine modular form. -/
noncomputable def lpsE2DifferenceModularForm (m : ℕ) (hm : 0 < m) :
    ModularForm (CongruenceSubgroup.Gamma0 m : Subgroup (GL (Fin 2) ℝ)) 2 where
  toFun := lpsE2Difference m hm
  slash_action_eq' := by
    intro g hg
    obtain ⟨γ,hγ,rfl⟩ := hg
    simpa [Matrix.SpecialLinearGroup.mapGL,← ModularForm.SL_slash] using
      lpsE2Difference_slash_gamma0 m hm γ hγ
  holo' := lpsE2Difference_mdifferentiable m hm
  bdd_at_cusps' := fun hc => lpsE2Difference_bounded_at_cusps m hm _
    (hc.mono (Subgroup.map_le_range (Matrix.SpecialLinearGroup.mapGL ℝ) _))

/-- The constructed modular form keeps the actual E2-difference function. -/
lemma lpsE2DifferenceModularForm_apply (m : ℕ) (hm : 0 < m) (z : ℍ) :
    lpsE2DifferenceModularForm m hm z=lpsE2Difference m hm z := rfl

/-- Actual T subgroup membership and true slash invariance prove period one. -/
lemma lpsE2Difference_add_one (m : ℕ) (hm : 0 < m) (z : ℍ) :
    lpsE2Difference m hm ((1:ℝ) +ᵥ z)=lpsE2Difference m hm z := by
  have ht : ModularGroup.T∈CongruenceSubgroup.Gamma0 m := by
    rw [CongruenceSubgroup.Gamma0_mem]
    simp [ModularGroup.T,Matrix.of_apply]
  have h := congrFun (lpsE2Difference_slash_gamma0 m hm ModularGroup.T ht) z
  rw [ModularForm.SL_slash_apply,UpperHalfPlane.modular_T_smul,ModularGroup.denom_apply] at h
  simpa [ModularGroup.T,Matrix.of_apply] using h

/-- The actual dilation action and exponential law give the true m-th-power nome. -/
lemma lpsE2AffineMatrix_qParam (m : ℕ) (hm : 0 < m) (z : ℍ) :
    Function.Periodic.qParam 1 ((lpsE2AffineMatrix m hm 0 • z:ℍ):ℂ)=
      Function.Periodic.qParam 1 (z:ℂ)^m := by
  rw [lpsE2AffineMatrix_action]
  simp only [Function.Periodic.qParam,Complex.ofReal_one,div_one,Complex.ofReal_zero,add_zero]
  rw [show 2*Real.pi*I*((m:ℂ)*(z:ℂ))=(m:ℂ)*(2*Real.pi*I*(z:ℂ)) by ring]
  exact Complex.exp_nat_mul _ m

/-- The actual reindexed E2 coefficient is zero outside multiples of the dilation. -/
noncomputable def lpsE2DilationCoefficient (m n : ℕ) : ℂ :=
  if m∣n then (if n/m=0 then 1 else -24*(ArithmeticFunction.sigma 1 (n/m):ℂ)) else 0

/-- Injective multiplication and zero off its range reindex the genuine convergent E2 series. -/
lemma lpsE2Dilated_hasSum (m : ℕ) (hm : 0 < m) (z : ℍ) :
    HasSum (fun n : ℕ => lpsE2DilationCoefficient m n*Function.Periodic.qParam 1 (z:ℂ)^n)
      (EisensteinSeries.E2 (lpsE2AffineMatrix m hm 0 • z)) := by
  let f : ℕ→ℂ := fun n => lpsE2DilationCoefficient m n*Function.Periodic.qParam 1 (z:ℂ)^n
  have hi : Function.Injective (fun n : ℕ => m*n) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left hm hab
  have ho : ∀ n, n∉Set.range (fun k : ℕ => m*k) → f n=0 := by
    intro n hn
    have hnd : ¬m∣n := by
      rintro ⟨k,hk⟩
      exact hn ⟨k,hk.symm⟩
    simp [f,lpsE2DilationCoefficient,hnd]
  have hs : HasSum (fun n : ℕ => (if n=0 then 1 else -24*(ArithmeticFunction.sigma 1 n:ℂ))*
      Function.Periodic.qParam 1 ((lpsE2AffineMatrix m hm 0 • z:ℍ):ℂ)^n)
      (EisensteinSeries.E2 (lpsE2AffineMatrix m hm 0 • z)) := by
    simpa only [smul_eq_mul,Function.Periodic.qParam,Complex.ofReal_one,div_one] using
      EisensteinSeries.hasSum_qExpansion_E2 (z:=lpsE2AffineMatrix m hm 0 • z)
  rw [lpsE2AffineMatrix_qParam] at hs
  have hcomp : HasSum (f ∘ (fun n : ℕ => m*n))
      (EisensteinSeries.E2 (lpsE2AffineMatrix m hm 0 • z)) := by
    apply hs.congr_fun
    intro n
    have hd : m∣m*n := dvd_mul_right _ _
    have hdiv : m*n/m=n := Nat.mul_div_cancel_left n hm
    simp only [Function.comp_def,f,lpsE2DilationCoefficient,if_pos hd,hdiv,pow_mul]
  exact (hi.hasSum_iff ho).mp hcomp

/-- The actual difference coefficient subtracts the determinant-scaled dilated E2 coefficient. -/
noncomputable def lpsE2DifferenceCoefficient (m n : ℕ) : ℂ :=
  (if n=0 then 1 else -24*(ArithmeticFunction.sigma 1 n:ℂ))-(m:ℂ)*lpsE2DilationCoefficient m n

/-- The genuine convergent E2 series and its dilated reindexing give the actual difference series. -/
lemma lpsE2Difference_hasSum (m : ℕ) (hm : 0 < m) (z : ℍ) :
    HasSum (fun n : ℕ => lpsE2DifferenceCoefficient m n*Function.Periodic.qParam 1 (z:ℂ)^n)
      (lpsE2Difference m hm z) := by
  have hE : HasSum (fun n : ℕ => (if n=0 then 1 else -24*(ArithmeticFunction.sigma 1 n:ℂ))*
      Function.Periodic.qParam 1 (z:ℂ)^n) (EisensteinSeries.E2 z) := by
    simpa only [smul_eq_mul,Function.Periodic.qParam,Complex.ofReal_one,div_one] using
      EisensteinSeries.hasSum_qExpansion_E2 (z:=z)
  have hM := (lpsE2Dilated_hasSum m hm z).mul_left (m:ℂ)
  have h := hE.sub hM
  change HasSum _ (lpsE2Difference m hm z) at h
  apply h.congr_fun
  intro n
  simp only [lpsE2DifferenceCoefficient]
  ring

/-- True periodicity, holomorphicity, boundedness and analytic uniqueness prove every actual coefficient. -/
lemma lpsE2Difference_coeff_qExpansion (m : ℕ) (hm : 0 < m) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsE2Difference m hm))=
      lpsE2DifferenceCoefficient m n := by
  have hp := lpsFunction_periodic_comp_ofComplex _ (lpsE2Difference_add_one m hm)
  have hh := lpsE2Difference_mdifferentiable m hm
  have hb : UpperHalfPlane.IsBoundedAtImInfty (lpsE2Difference m hm) := by
    have ht := lpsE2Difference_cusp_tendsto m hm (1:SL(2,ℤ))
    simp only [SlashAction.slash_one] at ht
    exact ht.isBigO_one ℝ
  have ha := UpperHalfPlane.analyticAt_cuspFunction_zero (by norm_num : (0:ℝ)<1) hp hh hb
  let f : C(ℍ,ℂ) := ⟨lpsE2Difference m hm,hh.continuous⟩
  symm
  exact UpperHalfPlane.qExpansion_coeff_unique f (by norm_num : (0:ℝ)<1) ha
    (fun z => by simpa only [smul_eq_mul,f,ContinuousMap.coe_mk] using
      lpsE2Difference_hasSum m hm z) n

/-- The genuine modular form retains the proved divisor-difference coefficients. -/
lemma coeff_qExpansion_lpsE2DifferenceModularForm (m : ℕ) (hm : 0 < m) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsE2DifferenceModularForm m hm))=
      lpsE2DifferenceCoefficient m n := lpsE2Difference_coeff_qExpansion m hm n

/-- The actual constant coefficient is one minus the dilation. -/
lemma lpsE2DifferenceCoefficient_zero (m : ℕ) : lpsE2DifferenceCoefficient m 0=1-(m:ℂ) := by
  simp [lpsE2DifferenceCoefficient,lpsE2DilationCoefficient]

/-- At nonzero indices outside dilation multiples the actual coefficient is the raw E2 divisor sum. -/
lemma lpsE2DifferenceCoefficient_of_not_dvd (m n : ℕ) (hn : n≠0) (hnd : ¬m∣n) :
    lpsE2DifferenceCoefficient m n= -24*(ArithmeticFunction.sigma 1 n:ℂ) := by
  simp [lpsE2DifferenceCoefficient,lpsE2DilationCoefficient,hn,hnd]

/-- The actual full-filter infinity constant is one minus the dilation. -/
lemma lpsE2Difference_tendsto_im_infty (m : ℕ) (hm : 0 < m) :
    Tendsto (lpsE2Difference m hm) UpperHalfPlane.atImInfty (𝓝 (1-(m:ℂ))) := by
  have h := lpsE2Difference_cusp_tendsto m hm (1:SL(2,ℤ))
  have hg : Int.gcd ((m:ℤ)*(1:SL(2,ℤ)) 0 0) ((1:SL(2,ℤ)) 1 0)=m := by
    simp
  rw [hg] at h
  simp only [SlashAction.slash_one] at h
  have hmC : (m:ℂ)≠0 := by exact_mod_cast hm.ne'
  have he : 1-(m:ℂ)^2/(m:ℂ)=1-(m:ℂ) := by field_simp [hmC]
  simpa only [he] using h

end QEC.Coding.TannerLiftedProduct
