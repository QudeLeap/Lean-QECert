import QEC.Coding.ExpanderCodes.LPSGaussEvaluation
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform

/-!
# The actual quadratic-character E2 series

For an odd residue prime q, the genuine complex quadratic character and its
nonzero standard Gauss sum define a finite normalized sum of translated E2
functions. The actual finite Fourier transform proves convergence and the
coefficient formula -24 * chi_q(n) * sigma_1(n), with zero constant at infinity.
Actual translation, holomorphicity and period-one proofs identify this with the
analytic q-expansion. No coefficient or transformation conclusion is assumed.

LPSQuadraticEisensteinModularForm proves level invariance and all-cusp boundedness.
This is an Eisenstein basis element for the LPS theta correction, not the full
correction or a cusp form. Strong coefficient growth and the exact PK22 theorem
remain proof obligations; the residue prime does not restrict the code alphabet.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

/-- The actual nontrivial quadratic character has its genuine finite Fourier transform. -/
lemma lpsQuadraticCharacter_fourier (F : Type*) [Field F] [Fintype F]
    (χ : MulChar F ℂ) (hχ : χ≠1) (hχq : χ.IsQuadratic) (ψ : AddChar F ℂ) (a : F) :
    (∑ r : F, χ r*ψ (a*r))=χ a*gaussSum χ ψ := by
  classical
  by_cases ha : a=0
  · subst a
    simp only [zero_mul,AddChar.map_zero_eq_one,mul_one,MulChar.map_zero,zero_mul]
    have h := gaussSum_one_right hχ
    simpa only [gaussSum,AddChar.one_apply,mul_one] using h
  · have hu : IsUnit a := isUnit_iff_ne_zero.mpr ha
    have h := gaussSum_mulShift_eq χ ψ hu.unit
    rw [hχq.inv] at h
    simpa only [gaussSum,AddChar.mulShift_apply,hu.unit_spec] using h

/-- The actual finite-field quadratic character is mapped to complex values. -/
noncomputable def lpsQuadraticE2Character (q : ℕ) [Fact q.Prime] : MulChar (ZMod q) ℂ :=
  (quadraticChar (ZMod q)).ringHomComp (Int.castRingHom ℂ)

/-- The genuine character-weighted translated E2 sum is normalized by its actual Gauss sum. -/
noncomputable def lpsQuadraticE2Twist (q : ℕ) [Fact q.Prime] (z : ℍ) : ℂ :=
  (gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹ *
    ∑ a : Fin q, lpsQuadraticE2Character q (a.val:ZMod q) *
      EisensteinSeries.E2 (((a.val:ℝ)/(q:ℝ)) +ᵥ z)

/-- Rational translation contributes the actual standard additive-character phase. -/
lemma lpsQParam_real_shift (N : ℕ) [NeZero N] (a : ℤ) (z : ℍ) :
    Function.Periodic.qParam 1 (((a:ℝ)/(N:ℝ)) +ᵥ z : ℍ) =
      ZMod.stdAddChar (a:ZMod N)*Function.Periodic.qParam 1 (z:ℂ) := by
  rw [ZMod.stdAddChar_coe]
  simp only [Function.Periodic.qParam,UpperHalfPlane.coe_vadd,Complex.ofReal_div,
    Complex.ofReal_intCast,Complex.ofReal_natCast,Complex.ofReal_one,div_one]
  rw [show (2:ℂ)*Real.pi*Complex.I*((a:ℂ)/(N:ℂ)+(z:ℂ)) =
    (2:ℂ)*Real.pi*Complex.I*(a:ℂ)/(N:ℂ)+(2:ℂ)*Real.pi*Complex.I*(z:ℂ) by ring,
    Complex.exp_add]

/-- The actual shifted E2 function has its convergent phased divisor series. -/
lemma lpsE2_real_shift_hasSum (N : ℕ) [NeZero N] (a : ℤ) (z : ℍ) :
    HasSum (fun n : ℕ =>
      (if n=0 then 1 else -24*ArithmeticFunction.sigma 1 n : ℂ) *
        ZMod.stdAddChar (((a*(n:ℤ)):ℤ):ZMod N) *
        Function.Periodic.qParam 1 (z:ℂ)^n)
      (EisensteinSeries.E2 (((a:ℝ)/(N:ℝ)) +ᵥ z)) := by
  have h : HasSum (fun n : ℕ =>
      (if n=0 then 1 else -24*ArithmeticFunction.sigma 1 n : ℂ) *
        Function.Periodic.qParam 1 ((((a:ℝ)/(N:ℝ)) +ᵥ z:ℍ):ℂ)^n)
      (EisensteinSeries.E2 (((a:ℝ)/(N:ℝ)) +ᵥ z)) := by
    simpa only [Function.Periodic.qParam,Complex.ofReal_one,div_one,smul_eq_mul] using
      EisensteinSeries.hasSum_qExpansion_E2 (z:=((a:ℝ)/(N:ℝ)) +ᵥ z)
  convert h using 1
  ext n
  rw [lpsQParam_real_shift,mul_pow]
  have hc := AddChar.map_nsmul_eq_pow (ZMod.stdAddChar (N:=N)) n (a:ZMod N)
  simp only [nsmul_eq_mul,Int.cast_mul,Int.cast_natCast] at hc ⊢
  rw [← hc]
  ring

/-- The odd-prime quadratic character is genuinely nontrivial. -/
lemma lpsQuadraticE2Character_ne_one (q : ℕ) [Fact q.Prime] (hq2 : q≠2) :
    lpsQuadraticE2Character q≠1 := by
  apply (MulChar.ringHomComp_ne_one_iff (by exact Int.cast_injective)).mpr
  apply quadraticChar_ne_one
  rw [ZMod.ringChar_zmod_n]
  exact hq2

/-- The actual primitive character Gauss sum supplies a valid normalization. -/
lemma lpsQuadraticE2Gauss_ne_zero (q : ℕ) [Fact q.Prime] (hq2 : q≠2) :
    gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q))≠0 := by
  apply gaussSum_ne_zero_of_nontrivial
  · rw [ZMod.card]
    exact_mod_cast NeZero.ne q
  · exact lpsQuadraticE2Character_ne_one q hq2
  · exact ZMod.isPrimitive_stdAddChar q

/-- The finite residue representatives give the same actual character Fourier transform. -/
lemma lpsQuadraticE2Character_fin_fourier (q : ℕ) [Fact q.Prime] (hq2 : q≠2) (n : ℕ) :
    (∑ a : Fin q, lpsQuadraticE2Character q (a.val:ZMod q) *
      ZMod.stdAddChar ((((a.val:ℤ)*(n:ℤ)):ℤ):ZMod q)) =
      lpsQuadraticE2Character q (n:ZMod q) *
        gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)) := by
  have h := lpsQuadraticCharacter_fourier (ZMod q) (lpsQuadraticE2Character q)
    (lpsQuadraticE2Character_ne_one q hq2) ((quadraticChar_isQuadratic (ZMod q)).comp _)
    (ZMod.stdAddChar (N:=q)) (n:ZMod q)
  have hs := (ZMod.finEquiv q).sum_comp (fun a : ZMod q =>
    lpsQuadraticE2Character q a*ZMod.stdAddChar ((n:ZMod q)*a))
  rw [← hs] at h
  change (∑ a : Fin q, lpsQuadraticE2Character q (ZMod.finEquiv q a) *
    ZMod.stdAddChar ((n:ZMod q)*ZMod.finEquiv q a)) = _ at h
  simpa only [← lpsFin_cast_finEquiv,Int.cast_mul,Int.cast_natCast,mul_comm] using h

/-- Finite Fourier summation computes the convergent divisor series of the actual twist. -/
lemma lpsQuadraticE2Twist_hasSum (q : ℕ) [Fact q.Prime] (hq2 : q≠2) (z : ℍ) :
    HasSum (fun n : ℕ => -24*(ArithmeticFunction.sigma 1 n:ℂ) *
      lpsQuadraticE2Character q (n:ZMod q) * Function.Periodic.qParam 1 (z:ℂ)^n)
      (lpsQuadraticE2Twist q z) := by
  classical
  have hsum := hasSum_sum (s:=Finset.univ) (fun (a : Fin q) ha =>
    (lpsE2_real_shift_hasSum q (a.val:ℤ) z).mul_left
      (lpsQuadraticE2Character q (a.val:ZMod q)))
  have h := hsum.mul_left (gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹
  change HasSum _ (lpsQuadraticE2Twist q z) at h
  convert h using 1
  ext n
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  rw [show (∑ a : Fin q, lpsQuadraticE2Character q (a.val:ZMod q) *
    (if n=0 then 1 else -24*ArithmeticFunction.sigma 1 n:ℂ) *
    ZMod.stdAddChar ((((a.val:ℤ)*(n:ℤ)):ℤ):ZMod q)) =
    (if n=0 then 1 else -24*ArithmeticFunction.sigma 1 n:ℂ) *
    (∑ a : Fin q, lpsQuadraticE2Character q (a.val:ZMod q)*
      ZMod.stdAddChar ((((a.val:ℤ)*(n:ℤ)):ℤ):ZMod q)) by
        rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro a ha;ring]
  rw [lpsQuadraticE2Character_fin_fourier q hq2]
  by_cases hn : n=0
  · subst n
    simp [MulChar.map_zero]
  · simp only [if_neg hn]
    have hg := lpsQuadraticE2Gauss_ne_zero q hq2
    field_simp [hg]

/-- The actual determinant-one real matrix realizes translation. -/
noncomputable def lpsE2RealTranslation (r : ℝ) : SL(2,ℝ) :=
  ⟨!![1,r;0,1],by simp [Matrix.det_fin_two,Matrix.of_apply]⟩

/-- The constructed real matrix acts by the intended translation. -/
lemma lpsE2RealTranslation_action (r : ℝ) (z : ℍ) :
    lpsE2RealTranslation r • z=r +ᵥ z := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply,UpperHalfPlane.coe_vadd]
  simp [lpsE2RealTranslation,Matrix.of_apply,add_comm]

/-- Actual E2 holomorphicity is preserved under the real translation action. -/
lemma lpsE2_real_shift_mdifferentiable (r : ℝ) :
    MDiff (fun z : ℍ => EisensteinSeries.E2 (r +ᵥ z)) := by
  have hpos : 0<(Matrix.SpecialLinearGroup.mapGL ℝ (lpsE2RealTranslation r)).det.val := by
    simp
  have h := E2_mdifferentiable.comp (UpperHalfPlane.mdifferentiable_smul hpos)
  have he : (fun z : ℍ => EisensteinSeries.E2
      (Matrix.SpecialLinearGroup.mapGL ℝ (lpsE2RealTranslation r) • z)) =
      (fun z : ℍ => EisensteinSeries.E2 (r +ᵥ z)) := by
    funext z
    apply congrArg EisensteinSeries.E2
    change lpsE2RealTranslation r • z=r +ᵥ z
    exact lpsE2RealTranslation_action r z
  change MDiff (fun z : ℍ => EisensteinSeries.E2
    (Matrix.SpecialLinearGroup.mapGL ℝ (lpsE2RealTranslation r) • z)) at h
  rw [he] at h
  exact h

/-- The actual finite weighted sum is holomorphic on the upper half plane. -/
lemma lpsQuadraticE2Twist_mdifferentiable (q : ℕ) [Fact q.Prime] :
    MDiff (fun z : ℍ => lpsQuadraticE2Twist q z) := by
  classical
  unfold lpsQuadraticE2Twist
  have h : MDiff (∑ a : Fin q, lpsQuadraticE2Character q (a.val:ZMod q) •
    (fun z : ℍ => EisensteinSeries.E2 (((a.val:ℝ)/(q:ℝ)) +ᵥ z))) :=
    MDifferentiable.sum (fun (a : Fin q) ha =>
      MDifferentiable.const_smul _ (lpsE2_real_shift_mdifferentiable ((a.val:ℝ)/(q:ℝ))))
  have h2 := MDifferentiable.const_smul
    (gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹ h
  convert h2 using 1
  ext z
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]

/-- The genuine convergent series supplies boundedness in the full infinity filter. -/
lemma lpsQuadraticE2Twist_isBoundedAtImInfty (q : ℕ) [Fact q.Prime] (hq2 : q≠2) :
    UpperHalfPlane.IsBoundedAtImInfty (fun z : ℍ => lpsQuadraticE2Twist q z) := by
  apply UpperHalfPlane.isBoundedAtImInfty_of_hasSum_qExpansion (by norm_num : (0:ℝ)<1)
  intro z
  simpa only [smul_eq_mul] using lpsQuadraticE2Twist_hasSum q hq2 z

/-- The genuine E2 transformation under T gives period one. -/
lemma lpsE2_add_one (z : ℍ) : EisensteinSeries.E2 ((1:ℝ) +ᵥ z)=EisensteinSeries.E2 z := by
  have h := congrFun (EisensteinSeries.E2_slash_action ModularGroup.T) z
  rw [EisensteinSeries.D2_T] at h
  rw [ModularForm.SL_slash_apply,UpperHalfPlane.modular_T_smul] at h
  rw [ModularGroup.denom_apply] at h
  simpa [ModularGroup.T,Matrix.of_apply] using h

/-- The actual twist inherits period one from each E2 translate. -/
lemma lpsQuadraticE2Twist_add_one (q : ℕ) [Fact q.Prime] (z : ℍ) :
    lpsQuadraticE2Twist q ((1:ℝ) +ᵥ z)=lpsQuadraticE2Twist q z := by
  unfold lpsQuadraticE2Twist
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  rw [show ((a.val:ℝ)/(q:ℝ)) +ᵥ ((1:ℝ) +ᵥ z) =
    (1:ℝ) +ᵥ (((a.val:ℝ)/(q:ℝ)) +ᵥ z) by
      rw [← add_vadd,← add_vadd,add_comm],lpsE2_add_one]

/-- Actual translation periodicity extends through the upper-half-plane retraction. -/
lemma lpsFunction_periodic_comp_ofComplex (f : ℍ→ℂ)
    (hf : ∀ z, f ((1:ℝ) +ᵥ z)=f z) : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1 := by
  intro z
  by_cases hz : 0<z.im
  · have hz1 : 0<(z+1).im := by simpa using hz
    simp only [Function.comp_apply,UpperHalfPlane.ofComplex_apply_of_im_pos hz,
      UpperHalfPlane.ofComplex_apply_of_im_pos hz1]
    have he : (⟨z+1,hz1⟩:ℍ)=(1:ℝ) +ᵥ (⟨z,hz⟩:ℍ) := by
      apply UpperHalfPlane.ext
      simp only [UpperHalfPlane.coe_vadd,Complex.ofReal_one]
      ring
    rw [he,hf]
  · have hz0 : z.im≤0 := le_of_not_gt hz
    have hz1 : (z+1).im≤0 := by simpa using hz0
    simp only [Function.comp_apply,UpperHalfPlane.ofComplex_apply_of_im_nonpos hz0,
      UpperHalfPlane.ofComplex_apply_of_im_nonpos hz1]

/-- The actual analytic q-expansion has the proved character-weighted divisor coefficients. -/
lemma lpsQuadraticE2Twist_coeff_qExpansion (q : ℕ) [Fact q.Prime] (hq2 : q≠2) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (fun z : ℍ => lpsQuadraticE2Twist q z)) =
      -24*(ArithmeticFunction.sigma 1 n:ℂ)*lpsQuadraticE2Character q (n:ZMod q) := by
  have hp := lpsFunction_periodic_comp_ofComplex _ (lpsQuadraticE2Twist_add_one q)
  have hm := lpsQuadraticE2Twist_mdifferentiable q
  have hb := lpsQuadraticE2Twist_isBoundedAtImInfty q hq2
  have ha := UpperHalfPlane.analyticAt_cuspFunction_zero (by norm_num : (0:ℝ)<1) hp hm hb
  let f : C(ℍ,ℂ) := ⟨fun z => lpsQuadraticE2Twist q z,hm.continuous⟩
  symm
  exact UpperHalfPlane.qExpansion_coeff_unique f (by norm_num : (0:ℝ)<1) ha
    (fun z => by simpa only [smul_eq_mul,f,ContinuousMap.coe_mk] using lpsQuadraticE2Twist_hasSum q hq2 z) n

end QEC.Coding.TannerLiftedProduct
