import QEC.Coding.ExpanderCodes.LPSChi4Eisenstein

/-!
# The actual iterated quadratic-character Eisenstein basis

The genuine chi4-weighted quarter-translates of the actual prime-character E2
form construct the iterated basis. Real translated HasSum and the proved full
chi4 Fourier transform give its convergent divisor series with both actual
character factors. Holomorphicity, periodicity and analytic uniqueness prove
every genuine q-expansion coefficient, including the nonunit zeros.

Level divisibility and determinant arithmetic modulo four construct integral
shift conjugates whose lower rows retain the prime level. Actual action and
denominator proofs transport the genuine prime-form invariance, constructing
a weight-two Mathlib ModularForm on Gamma0((4q)^2). Positive affine dilations
expand into a double finite E2 sum; actual full-filter limits compute every
signed rational-cusp constant as the double character-weighted squared-gcd sum.
Infinity vanishes, which does not assert cuspidality at other cusps.

The full theta all-cusp correction, actual CuspForm and stronger coefficient
growth, complete sparse-CSS runtime and exact arbitrary-finite-field PK22 theorem
remain proof obligations. No target Fourier, modularity, cusp or coefficient
conclusion is supplied as an input, and no public binding changes.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

/-- The actual normalized quarter-translate sum of the genuine prime-character E2 form defines the iterated basis. -/
noncomputable def lpsChi4PrimeE2Twist (q : ℕ) [Fact q.Prime] (z : ℍ) : ℂ :=
  (gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹ *
    ∑ r : Fin 4,lpsChi4E2Character (r.val:ZMod 4)*
      lpsQuadraticE2Twist q (((r.val:ℝ)/4) +ᵥ z)

/-- Actual quarter translation and the standard additive phase transform the genuine prime-character convergent series. -/
lemma lpsQuadraticE2_real_shift_hasSum (q : ℕ) [Fact q.Prime] (hq2 : q≠2) (a : ℤ) (z : ℍ) :
    HasSum (fun n : ℕ => -24*(ArithmeticFunction.sigma 1 n:ℂ)*lpsQuadraticE2Character q (n:ZMod q)*
      ZMod.stdAddChar (((a*(n:ℤ)):ℤ):ZMod 4)*Function.Periodic.qParam 1 (z:ℂ)^n)
      (lpsQuadraticE2Twist q (((a:ℝ)/4) +ᵥ z)) := by
  have h := lpsQuadraticE2Twist_hasSum q hq2 (((a:ℝ)/4) +ᵥ z)
  convert h using 1
  ext n
  have hshift := lpsQParam_real_shift 4 a z
  norm_num only [Nat.cast_ofNat] at hshift
  rw [hshift,mul_pow]
  have hc := AddChar.map_nsmul_eq_pow (ZMod.stdAddChar (N:=4)) n (a:ZMod 4)
  simp only [nsmul_eq_mul,Int.cast_mul,Int.cast_natCast] at hc ⊢
  rw [←hc]
  ring

/-- The genuine quarter-translated series and full chi4 Fourier transform prove the iterated convergent divisor series. -/
lemma lpsChi4PrimeE2Twist_hasSum (q : ℕ) [Fact q.Prime] (hq2 : q≠2) (z : ℍ) :
    HasSum (fun n : ℕ => -24*(ArithmeticFunction.sigma 1 n:ℂ)*lpsQuadraticE2Character q (n:ZMod q)*
      lpsChi4E2Character (n:ZMod 4)*Function.Periodic.qParam 1 (z:ℂ)^n)
      (lpsChi4PrimeE2Twist q z) := by
  classical
  have hs := hasSum_sum (s:=Finset.univ) (fun (r : Fin 4) hr =>
    (lpsQuadraticE2_real_shift_hasSum q hq2 (r.val:ℤ) z).mul_left
      (lpsChi4E2Character (r.val:ZMod 4)))
  have h := hs.mul_left (gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹
  change HasSum _ (lpsChi4PrimeE2Twist q z) at h
  apply h.congr_fun
  intro n
  have hf := lpsChi4E2Character_fin_fourier (n:ZMod 4)
  have hf' : (∑ r : Fin 4,lpsChi4E2Character (r.val:ZMod 4)*
      ZMod.stdAddChar ((((r.val:ℤ)*(n:ℤ)):ℤ):ZMod 4))=
      lpsChi4E2Character (n:ZMod 4)*gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)) := by
    simpa only [Int.cast_mul,Int.cast_natCast,mul_comm] using hf
  have he : (∑ r : Fin 4,lpsChi4E2Character (r.val:ZMod 4)*
      (-24*(ArithmeticFunction.sigma 1 n:ℂ)*lpsQuadraticE2Character q (n:ZMod q)*
        ZMod.stdAddChar ((((r.val:ℤ)*(n:ℤ)):ℤ):ZMod 4)*Function.Periodic.qParam 1 (z:ℂ)^n))=
      (-24*(ArithmeticFunction.sigma 1 n:ℂ)*lpsQuadraticE2Character q (n:ZMod q)*
        Function.Periodic.qParam 1 (z:ℂ)^n)*
      (∑ r : Fin 4,lpsChi4E2Character (r.val:ZMod 4)*
        ZMod.stdAddChar ((((r.val:ℤ)*(n:ℤ)):ℤ):ZMod 4)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  rw [he,hf']
  field_simp [lpsChi4E2Gauss_ne_zero]

/-- The actual positive-determinant translation action preserves holomorphicity of an actual function. -/
lemma lpsFunction_real_shift_mdifferentiable (f : ℍ→ℂ) (hf : MDiff f) (r : ℝ) :
    MDiff (fun z : ℍ => f (r +ᵥ z)) := by
  have hp : 0<(Matrix.SpecialLinearGroup.mapGL ℝ (lpsE2RealTranslation r)).det.val := by simp
  have h := hf.comp (UpperHalfPlane.mdifferentiable_smul hp)
  have he : (fun z : ℍ => f (Matrix.SpecialLinearGroup.mapGL ℝ (lpsE2RealTranslation r) • z))=
      (fun z : ℍ => f (r +ᵥ z)) := by
    funext z
    apply congrArg f
    change lpsE2RealTranslation r • z=r +ᵥ z
    exact lpsE2RealTranslation_action r z
  change MDiff (fun z : ℍ => f (Matrix.SpecialLinearGroup.mapGL ℝ (lpsE2RealTranslation r) • z)) at h
  rw [he] at h
  exact h

/-- Finite true translations of the genuine prime-character form prove holomorphicity of the iterated function. -/
lemma lpsChi4PrimeE2Twist_mdifferentiable (q : ℕ) [Fact q.Prime] : MDiff (lpsChi4PrimeE2Twist q) := by
  classical
  unfold lpsChi4PrimeE2Twist
  have h : MDiff (∑ r : Fin 4,lpsChi4E2Character (r.val:ZMod 4) •
      (fun z : ℍ => lpsQuadraticE2Twist q (((r.val:ℝ)/4) +ᵥ z))) :=
    MDifferentiable.sum (fun (r : Fin 4) hr =>
      MDifferentiable.const_smul _ (lpsFunction_real_shift_mdifferentiable _
        (lpsQuadraticE2Twist_mdifferentiable q) ((r.val:ℝ)/4)))
  have h2 := MDifferentiable.const_smul
    (gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹ h
  have he : ((gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹ •
      (∑ r : Fin 4,lpsChi4E2Character (r.val:ZMod 4) •
        (fun z : ℍ => lpsQuadraticE2Twist q (((r.val:ℝ)/4) +ᵥ z))))=
      (fun z : ℍ => (gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹ *
        ∑ r : Fin 4,lpsChi4E2Character (r.val:ZMod 4)*lpsQuadraticE2Twist q (((r.val:ℝ)/4) +ᵥ z)) := by
    funext z
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [he] at h2
  exact h2

/-- Actual prime-twist periodicity and commuting real translations prove period one of the iterated sum. -/
lemma lpsChi4PrimeE2Twist_add_one (q : ℕ) [Fact q.Prime] (z : ℍ) :
    lpsChi4PrimeE2Twist q ((1:ℝ) +ᵥ z)=lpsChi4PrimeE2Twist q z := by
  unfold lpsChi4PrimeE2Twist
  apply congrArg (fun w : ℂ => (gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹*w)
  apply Finset.sum_congr rfl
  intro r hr
  have he : ((r.val:ℝ)/4) +ᵥ ((1:ℝ) +ᵥ z)=
      (1:ℝ) +ᵥ (((r.val:ℝ)/4) +ᵥ z) := by rw [←add_vadd,←add_vadd,add_comm]
  have hf := lpsQuadraticE2Twist_add_one q (((r.val:ℝ)/4) +ᵥ z)
  rw [←he] at hf
  exact congrArg (fun w : ℂ => lpsChi4E2Character (r.val:ZMod 4)*w) hf

/-- The actual convergent iterated series proves boundedness in the full infinity filter. -/
lemma lpsChi4PrimeE2Twist_isBoundedAtImInfty (q : ℕ) [Fact q.Prime] (hq2 : q≠2) :
    UpperHalfPlane.IsBoundedAtImInfty (lpsChi4PrimeE2Twist q) := by
  apply UpperHalfPlane.isBoundedAtImInfty_of_hasSum_qExpansion (by norm_num : (0:ℝ)<1)
  intro z
  simpa only [smul_eq_mul] using lpsChi4PrimeE2Twist_hasSum q hq2 z

/-- True analytic uniqueness computes every actual coefficient with both quadratic-character factors. -/
lemma lpsChi4PrimeE2Twist_coeff_qExpansion (q : ℕ) [Fact q.Prime] (hq2 : q≠2) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsChi4PrimeE2Twist q))=
      -24*(ArithmeticFunction.sigma 1 n:ℂ)*lpsQuadraticE2Character q (n:ZMod q)*lpsChi4E2Character (n:ZMod 4) := by
  have hp := lpsFunction_periodic_comp_ofComplex _ (lpsChi4PrimeE2Twist_add_one q)
  have hm := lpsChi4PrimeE2Twist_mdifferentiable q
  have hb := lpsChi4PrimeE2Twist_isBoundedAtImInfty q hq2
  have ha := UpperHalfPlane.analyticAt_cuspFunction_zero (by norm_num : (0:ℝ)<1) hp hm hb
  let f : C(ℍ,ℂ) := ⟨lpsChi4PrimeE2Twist q,hm.continuous⟩
  symm
  exact UpperHalfPlane.qExpansion_coeff_unique f (by norm_num : (0:ℝ)<1) ha
    (fun z => by simpa only [smul_eq_mul,f,ContinuousMap.coe_mk] using lpsChi4PrimeE2Twist_hasSum q hq2 z) n


/-- Actual integer entries give the true translated denominator, instantiated with constructed conjugates. -/
lemma lpsE2ShiftConjugate_actual_denom (N : ℕ) [NeZero N] (γ δ : SL(2,ℤ)) (k s : ℤ)
    (hC : γ 1 0=(N:ℤ)^2*k) (h10 : δ 1 0=(N:ℤ)^2*k)
    (h11 : δ 1 1=γ 1 1-s*(N:ℤ)*k) (z : ℍ) :
    UpperHalfPlane.denom δ ((((s:ℝ)/(N:ℝ)) +ᵥ z:ℍ):ℂ)=UpperHalfPlane.denom γ (z:ℂ) := by
  have hN : (N:ℂ)≠0 := by exact_mod_cast NeZero.ne N
  rw [ModularGroup.denom_apply,ModularGroup.denom_apply]
  simp only [UpperHalfPlane.coe_vadd,Complex.ofReal_div,Complex.ofReal_intCast,Complex.ofReal_natCast]
  rw [h10,h11,hC]
  push_cast
  rw [show (s:ℂ)/(N:ℂ)+(z:ℂ)=(z:ℂ)+(s:ℂ)/(N:ℂ) by ring]
  exact lpsE2ShiftConjugate_denom (N:ℂ) (k:ℂ) (s:ℂ) (γ 1 1:ℂ) (z:ℂ) hN

/-- The constructed conjugate belongs to the genuine prime level, so its actual form invariance proves each translated slash. -/
lemma lpsChi4PrimeE2Shift_slash (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (γ : SL(2,ℤ)) (k r t : ℤ) (hC : γ 1 0=(4:ℤ)^2*((q:ℤ)^2*k))
    (hrs : r*γ 1 1-r*γ 0 0=(4:ℤ)*t) (z : ℍ) :
    (((fun w : ℍ => lpsQuadraticE2Twist q (((r:ℝ)/4) +ᵥ w)) ∣[(2:ℤ)] γ) z)=
      lpsQuadraticE2Twist q (((r:ℝ)/4) +ᵥ z) := by
  let δ := lpsE2ShiftConjugate 4 γ ((q:ℤ)^2*k) r r t hC hrs
  have hδ : δ∈CongruenceSubgroup.Gamma0 (q^2) := by
    rw [CongruenceSubgroup.Gamma0_mem]
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (δ 1 0) (q^2)).mpr
    refine ⟨16*k,?_⟩
    change (4:ℤ)^2*((q:ℤ)^2*k)=(q^2:ℕ)*(16*k)
    push_cast
    ring
  have ha := lpsE2ShiftConjugate_action 4 γ δ ((q:ℤ)^2*k) r r t hC hrs rfl rfl rfl rfl z
  have hd := lpsE2ShiftConjugate_actual_denom 4 γ δ ((q:ℤ)^2*k) r hC rfl rfl z
  norm_num only [Nat.cast_ofNat] at hd
  have h := congrFun (lpsQuadraticE2Twist_slash_gamma0 q hq2 δ hδ) (((r:ℝ)/4) +ᵥ z)
  simp only [ModularForm.SL_slash_apply] at h ⊢
  norm_num only [Nat.cast_ofNat] at ha
  rw [ha,hd] at h
  exact h

/-- True determinant arithmetic modulo four constructs compatible shifts and proves the actual iterated level invariance. -/
lemma lpsChi4PrimeE2Twist_slash_gamma0 (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 ((4*q)^2)) :
    (lpsChi4PrimeE2Twist q ∣[(2:ℤ)] γ)=lpsChi4PrimeE2Twist q := by
  classical
  obtain ⟨k,hC⟩ := lpsE2Gamma0_lower_entry (4*q) γ hγ
  have hC4 : γ 1 0=(4:ℤ)^2*((q:ℤ)^2*k) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat,mul_pow,mul_assoc] using hC
  have hAD : (γ 0 0:ZMod 4)*(γ 1 1:ZMod 4)=1 := by
    have hd : γ 0 0*γ 1 1-γ 0 1*γ 1 0=1 := by
      simpa only [Matrix.det_fin_two] using γ.det_coe
    have h : (γ 0 0:ZMod 4)*(γ 1 1:ZMod 4)-(γ 0 1:ZMod 4)*(γ 1 0:ZMod 4)=1 := by
      simpa only [map_sub,map_mul,map_one,Int.coe_castRingHom] using congrArg (Int.castRingHom (ZMod 4)) hd
    have hc : (γ 1 0:ZMod 4)=0 := by
      rw [hC4]
      push_cast
      have hz : (16:ZMod 4)=0 := by decide
      rw [hz]
      simp
    simpa only [hc,mul_zero,sub_zero] using h
  have hEq : (γ 0 0:ZMod 4)=(γ 1 1:ZMod 4) := by
    have he : ∀ a d : ZMod 4,a*d=1 → a=d := by decide
    exact he _ _ hAD
  ext z
  have hr (r : Fin 4) : lpsQuadraticE2Twist q (((r.val:ℝ)/4) +ᵥ (γ • z))*
      UpperHalfPlane.denom γ (z:ℂ)^(-(2:ℤ))=lpsQuadraticE2Twist q (((r.val:ℝ)/4) +ᵥ z) := by
    have ht : (4:ℤ)∣(r.val:ℤ)*γ 1 1-(r.val:ℤ)*γ 0 0 := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp
      push_cast
      rw [hEq]
      ring
    obtain ⟨t,ht⟩ := ht
    simpa only [ModularForm.SL_slash_apply,Int.cast_natCast] using
      lpsChi4PrimeE2Shift_slash q hq2 γ k (r.val:ℤ) t hC4 ht z
  simp only [ModularForm.SL_slash_apply,lpsChi4PrimeE2Twist]
  rw [mul_assoc,Finset.sum_mul]
  simp_rw [mul_assoc,hr]


/-- The genuine positive-determinant affine action dilates the actual iterated function. -/
noncomputable def lpsChi4PrimeE2Dilate (q m : ℕ) [Fact q.Prime] (hm : 0 < m) (z : ℍ) : ℂ :=
  lpsChi4PrimeE2Twist q (lpsE2AffineMatrix m hm 0 • z)

/-- The actual rational shift identity expands the dilated iterated basis into the double finite E2 sum. -/
lemma lpsChi4PrimeE2Dilate_eq (q m : ℕ) [Fact q.Prime] (hm : 0 < m) :
    lpsChi4PrimeE2Dilate q m hm=(fun z : ℍ =>
      (gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹ *
        ∑ r : Fin 4,lpsChi4E2Character (r.val:ZMod 4)*
          ((gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹ *
            ∑ a : Fin q,lpsQuadraticE2Character q (a.val:ZMod q)*EisensteinSeries.E2
              (lpsE2AffineMatrix m hm (((q*r.val+4*a.val:ℕ):ℝ)/((4*q:ℕ):ℝ)) • z))) := by
  funext z
  unfold lpsChi4PrimeE2Dilate lpsChi4PrimeE2Twist lpsQuadraticE2Twist
  apply congrArg (fun w : ℂ => (gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹*w)
  apply Finset.sum_congr rfl
  intro r hr
  apply congrArg (fun w : ℂ => lpsChi4E2Character (r.val:ZMod 4)*w)
  apply congrArg (fun w : ℂ => (gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹*w)
  apply Finset.sum_congr rfl
  intro a ha
  apply congrArg (fun w : ℂ => lpsQuadraticE2Character q (a.val:ZMod q)*w)
  apply congrArg EisensteinSeries.E2
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_vadd,UpperHalfPlane.coe_vadd,lpsE2AffineMatrix_action,lpsE2AffineMatrix_action]
  simp only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_zero,add_zero]
  have hqC : (q:ℂ)≠0 := by exact_mod_cast NeZero.ne q
  push_cast
  field_simp [hqC]
  ring

/-- The actual slash action distributes over finite scalar-weighted functions, used at both summation levels. -/
lemma lpsFiniteWeighted_SL_slash (α : Type*) [Fintype α] (G : ℂ) (c : α→ℂ)
    (f : α→ℍ→ℂ) (γ : SL(2,ℤ)) :
    ((fun z => G*∑ i : α,c i*f i z) ∣[(2:ℤ)] γ)=
      (fun z => G*∑ i : α,c i*((f i ∣[(2:ℤ)] γ) z)) := by
  classical
  funext z
  simp only [ModularForm.SL_slash_apply]
  rw [mul_assoc,Finset.sum_mul]
  apply congrArg (fun w : ℂ => G*w)
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- True affine E2 limits and both finite weighted sums prove the entire actual positive-dilation cusp vector. -/
lemma lpsChi4PrimeE2Dilate_cusp_tendsto (q m : ℕ) [Fact q.Prime] (hm : 0 < m) (γ : SL(2,ℤ)) :
    Tendsto (lpsChi4PrimeE2Dilate q m hm ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 ((gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹ *
        ∑ r : Fin 4,lpsChi4E2Character (r.val:ZMod 4)*
          ((gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹ *
            ∑ a : Fin q,lpsQuadraticE2Character q (a.val:ZMod q)*
              (((Int.gcd (((4*q:ℕ):ℤ)*(m:ℤ)*γ 0 0+((q*r.val+4*a.val:ℕ):ℤ)*γ 1 0)
                (((4*q:ℕ):ℤ)*γ 1 0):ℕ):ℂ)^2/(((4*q:ℕ):ℂ)^2*(m:ℂ)^2))))) := by
  classical
  have hp : 0 < 4*q := Nat.mul_pos (by decide) (Fact.out : q.Prime).pos
  have hs := tendsto_finsetSum Finset.univ (fun (r : Fin 4) hr =>
    ((tendsto_finsetSum Finset.univ (fun (a : Fin q) ha =>
      (lpsE2Affine_cusp_tendsto m (4*q) hm hp ((q*r.val+4*a.val:ℕ):ℤ) γ).const_mul
        (lpsQuadraticE2Character q (a.val:ZMod q)))).const_mul
      (gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹).const_mul
        (lpsChi4E2Character (r.val:ZMod 4)))
  have h := hs.const_mul (gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹
  rw [lpsChi4PrimeE2Dilate_eq,lpsFiniteWeighted_SL_slash]
  simp_rw [lpsFiniteWeighted_SL_slash]
  simpa only [Int.cast_natCast] using h

/-- The actual dilation by one is the original iterated basis function. -/
lemma lpsChi4PrimeE2Dilate_one (q : ℕ) [Fact q.Prime] :
    lpsChi4PrimeE2Dilate q 1 (by decide)=lpsChi4PrimeE2Twist q := by
  funext z
  unfold lpsChi4PrimeE2Dilate
  apply congrArg (lpsChi4PrimeE2Twist q)
  apply UpperHalfPlane.ext
  rw [lpsE2AffineMatrix_action]
  simp

/-- The full signed rational-cusp limits prove actual boundedness at every rational cusp. -/
lemma lpsChi4PrimeE2Twist_bounded_at_cusps (q : ℕ) [Fact q.Prime]
    (c : OnePoint ℝ) (hc : IsCusp c 𝒮ℒ) : OnePoint.IsBoundedAt c (lpsChi4PrimeE2Twist q) 2 := by
  apply (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr
  intro γ hγ
  have ht := lpsChi4PrimeE2Dilate_cusp_tendsto q 1 (by decide) γ
  rw [lpsChi4PrimeE2Dilate_one] at ht
  exact ht.isBigO_one ℝ

/-- Proved invariance, holomorphicity and all-cusp boundedness construct the actual level-squared weight-two modular form. -/
noncomputable def lpsChi4PrimeE2TwistModularForm (q : ℕ) [Fact q.Prime] (hq2 : q≠2) :
    ModularForm (CongruenceSubgroup.Gamma0 ((4*q)^2) : Subgroup (GL (Fin 2) ℝ)) 2 where
  toFun := lpsChi4PrimeE2Twist q
  slash_action_eq' := by
    intro g hg
    obtain ⟨γ,hγ,rfl⟩ := hg
    simpa [Matrix.SpecialLinearGroup.mapGL,←ModularForm.SL_slash] using lpsChi4PrimeE2Twist_slash_gamma0 q hq2 γ hγ
  holo' := lpsChi4PrimeE2Twist_mdifferentiable q
  bdd_at_cusps' := fun hc => lpsChi4PrimeE2Twist_bounded_at_cusps q _
    (hc.mono (Subgroup.map_le_range (Matrix.SpecialLinearGroup.mapGL ℝ) _))

/-- The bundled form retains the genuine quarter-translate function. -/
lemma lpsChi4PrimeE2TwistModularForm_apply (q : ℕ) [Fact q.Prime] (hq2 : q≠2) (z : ℍ) :
    lpsChi4PrimeE2TwistModularForm q hq2 z=lpsChi4PrimeE2Twist q z := rfl

/-- The genuine modular form keeps every actual coefficient with both character factors. -/
lemma coeff_qExpansion_lpsChi4PrimeE2TwistModularForm (q : ℕ) [Fact q.Prime] (hq2 : q≠2) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsChi4PrimeE2TwistModularForm q hq2))=
      -24*(ArithmeticFunction.sigma 1 n:ℂ)*lpsQuadraticE2Character q (n:ZMod q)*lpsChi4E2Character (n:ZMod 4) :=
  lpsChi4PrimeE2Twist_coeff_qExpansion q hq2 n



/-- Dilation one gives the complete actual double-weighted gcd cusp vector of the undilated form. -/
lemma lpsChi4PrimeE2Twist_cusp_gcd_tendsto (q : ℕ) [Fact q.Prime] (γ : SL(2,ℤ)) :
    Tendsto (lpsChi4PrimeE2Twist q ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 ((gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹ *
        ∑ r : Fin 4,lpsChi4E2Character (r.val:ZMod 4)*
          ((gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹ *
            ∑ a : Fin q,lpsQuadraticE2Character q (a.val:ZMod q)*
              (((Int.gcd (((4*q:ℕ):ℤ)*γ 0 0+((q*r.val+4*a.val:ℕ):ℤ)*γ 1 0)
                (((4*q:ℕ):ℤ)*γ 1 0):ℕ):ℂ)^2/((4*q:ℕ):ℂ)^2)))) := by
  simpa only [lpsChi4PrimeE2Dilate_one,Nat.cast_one,Int.cast_one,mul_one,one_pow] using
    lpsChi4PrimeE2Dilate_cusp_tendsto q 1 (by decide) γ

/-- The true zero coefficient and analytic cusp-function continuity prove the full-filter infinity limit. -/
lemma lpsChi4PrimeE2Twist_tendsto_zero (q : ℕ) [Fact q.Prime] (hq2 : q≠2) :
    Tendsto (lpsChi4PrimeE2Twist q) UpperHalfPlane.atImInfty (𝓝 0) := by
  have hp := lpsFunction_periodic_comp_ofComplex _ (lpsChi4PrimeE2Twist_add_one q)
  have ha := UpperHalfPlane.analyticAt_cuspFunction_zero (by norm_num : (0:ℝ)<1) hp
    (lpsChi4PrimeE2Twist_mdifferentiable q) (lpsChi4PrimeE2Twist_isBoundedAtImInfty q hq2)
  have hc : UpperHalfPlane.cuspFunction 1 (lpsChi4PrimeE2Twist q) 0=0 := by
    have h := lpsChi4PrimeE2Twist_coeff_qExpansion q hq2 0
    simpa [UpperHalfPlane.qExpansion_coeff,MulChar.map_zero] using h
  have he : (fun z : ℍ => UpperHalfPlane.cuspFunction 1 (lpsChi4PrimeE2Twist q)
      (Function.Periodic.qParam 1 (z:ℂ)))=lpsChi4PrimeE2Twist q := by
    funext z
    exact UpperHalfPlane.eq_cuspFunction z (by norm_num) hp
  have h := ha.continuousAt.tendsto.comp (UpperHalfPlane.qParam_tendsto_atImInfty (by norm_num : (0:ℝ)<1))
  simpa only [Function.comp_def,hc,he] using h

end QEC.Coding.TannerLiftedProduct
