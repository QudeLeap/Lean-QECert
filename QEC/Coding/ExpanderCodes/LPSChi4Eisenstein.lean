import QEC.Coding.ExpanderCodes.LPSQuadraticEisensteinCuspGeneral

/-!
# The actual primitive modulus-four Eisenstein basis

Mathlib's genuine chi4 and the standard additive character give the true
nonzero Gauss normalization and full finite Fourier transform, including both
nonunit frequencies. The actual finite translated E2 sum has its convergent
character-weighted divisor series and genuine analytic q-expansion.

Level divisibility and determinant arithmetic modulo four construct actual
integral shift conjugates. Their genuine E2 defects cancel by the actual zero
character sum. Holomorphicity and the full-filter constants at every rational
cusp construct a Mathlib weight-two ModularForm on Gamma0(16). The complete
positive-dilation cusp vector is proved as an actual finite weighted gcd sum.
Infinity vanishes, while the quarter-cusp constant is nonzero; this basis is
therefore not a CuspForm.

The iterated prime-character basis, full theta Eisenstein correction, stronger
coefficient growth, complete sparse-CSS runtime and exact arbitrary-finite-field
PK22 theorem remain proof obligations. No target Fourier identity, modularity,
cusp condition or coefficient bound is assumed, and no public binding changes.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

/-- The genuine Mathlib primitive modulus-four quadratic character is mapped to complex values. -/
noncomputable def lpsChi4E2Character : MulChar (ZMod 4) ℂ :=
  ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

/-- The complex character has the actual integer-character values, used in finite arithmetic and fixtures. -/
lemma lpsChi4E2Character_apply (a : ZMod 4) : lpsChi4E2Character a=(ZMod.χ₄ a:ℂ) := rfl

/-- All four actual values include zero at both nonunits and opposite signs on the units. -/
lemma lpsChi4E2Character_values : lpsChi4E2Character 0=0 ∧ lpsChi4E2Character 1=1 ∧
    lpsChi4E2Character 2=0 ∧ lpsChi4E2Character 3= -1 := by
  norm_num [lpsChi4E2Character_apply,ZMod.χ₄_apply]

/-- The genuine standard character at three is minus its value at one, used by Gauss and Fourier evaluation. -/
lemma lpsChi4Phase_three : ZMod.stdAddChar (3:ZMod 4)= -ZMod.stdAddChar (1:ZMod 4) := by
  rw [show (3:ZMod 4)=1+2 by decide,AddChar.map_add_eq_mul,lpsChar_four_two]
  ring

/-- The four actual terms evaluate the true Gauss sum as twice the quarter-turn phase. -/
lemma lpsChi4E2Gauss_eq : gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4))=
    2*ZMod.stdAddChar (1:ZMod 4) := by
  have hs := (ZMod.finEquiv 4).sum_comp (fun a : ZMod 4 =>
    lpsChi4E2Character a*ZMod.stdAddChar a)
  rw [gaussSum,←hs]
  change (∑ a : Fin 4,lpsChi4E2Character (ZMod.finEquiv 4 a)*ZMod.stdAddChar (ZMod.finEquiv 4 a))=_
  simp only [←lpsFin_cast_finEquiv]
  rw [Fin.sum_univ_four]
  norm_num [lpsChi4E2Character_apply,ZMod.χ₄_apply,lpsChi4Phase_three]
  ring

/-- The genuine phase square proves Gauss square minus four, without an assumed normalization. -/
lemma lpsChi4E2Gauss_sq : gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4))^2= -4 := by
  rw [lpsChi4E2Gauss_eq,mul_pow]
  have h := lpsChar_four_odd_square 1 (by decide)
  norm_num at h ⊢
  rw [h]
  norm_num

/-- The actual nonzero Gauss square validates normalization of the E2 twist. -/
lemma lpsChi4E2Gauss_ne_zero : gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4))≠0 := by
  intro h
  have hs := lpsChi4E2Gauss_sq
  rw [h] at hs
  norm_num at hs

/-- Every frequency, including composite-modulus nonunits, has the actual character Fourier transform. -/
lemma lpsChi4E2Character_fin_fourier (n : ZMod 4) :
    (∑ a : Fin 4,lpsChi4E2Character (a.val:ZMod 4)*ZMod.stdAddChar (n*(a.val:ZMod 4)))=
      lpsChi4E2Character n*gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)) := by
  rw [Fin.sum_univ_four,lpsChi4E2Gauss_eq]
  norm_num [lpsChi4E2Character_apply,ZMod.χ₄_apply]
  have hc := lpsChi4E2Character_values
  fin_cases n
  · change ZMod.stdAddChar (0:ZMod 4)-ZMod.stdAddChar (0:ZMod 4)=lpsChi4E2Character 0*(2*ZMod.stdAddChar (1:ZMod 4))
    rw [hc.1]
    ring
  · change ZMod.stdAddChar (1:ZMod 4)-ZMod.stdAddChar (3:ZMod 4)=lpsChi4E2Character 1*(2*ZMod.stdAddChar (1:ZMod 4))
    rw [hc.2.1,lpsChi4Phase_three]
    ring
  · change ZMod.stdAddChar (2:ZMod 4)-ZMod.stdAddChar (2:ZMod 4)=lpsChi4E2Character 2*(2*ZMod.stdAddChar (1:ZMod 4))
    rw [hc.2.2.1]
    ring
  · change ZMod.stdAddChar (3:ZMod 4)-ZMod.stdAddChar (1:ZMod 4)=lpsChi4E2Character 3*(2*ZMod.stdAddChar (1:ZMod 4))
    rw [hc.2.2.2,lpsChi4Phase_three]
    ring

/-- The four actual character values have sum zero, cancelling the true E2 defect. -/
lemma lpsChi4E2Character_sum_zero : (∑ a : Fin 4,lpsChi4E2Character (a.val:ZMod 4))=0 := by
  norm_num [Fin.sum_univ_four,lpsChi4E2Character_apply,ZMod.χ₄_apply]

/-- The actual normalized finite sum of translated E2 functions defines the modulus-four basis element. -/
noncomputable def lpsChi4E2Twist (z : ℍ) : ℂ :=
  (gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹*
    ∑ a : Fin 4,lpsChi4E2Character (a.val:ZMod 4)*EisensteinSeries.E2 (((a.val:ℝ)/4) +ᵥ z)

/-- The genuine translated E2 series and full finite Fourier transform compute the convergent twist series. -/
lemma lpsChi4E2Twist_hasSum (z : ℍ) :
    HasSum (fun n : ℕ => -24*(ArithmeticFunction.sigma 1 n:ℂ) *
      lpsChi4E2Character (n:ZMod 4) * Function.Periodic.qParam 1 (z:ℂ)^n)
      (lpsChi4E2Twist z) := by
  classical
  have hsum := hasSum_sum (s:=Finset.univ) (fun (a : Fin 4) ha =>
    (lpsE2_real_shift_hasSum 4 (a.val:ℤ) z).mul_left
      (lpsChi4E2Character (a.val:ZMod 4)))
  have h := hsum.mul_left (gaussSum (lpsChi4E2Character) (ZMod.stdAddChar (N:=4)))⁻¹
  change HasSum _ (lpsChi4E2Twist z) at h
  convert h using 1
  ext n
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  rw [show (∑ a : Fin 4, lpsChi4E2Character (a.val:ZMod 4) *
    (if n=0 then 1 else -24*ArithmeticFunction.sigma 1 n:ℂ) *
    ZMod.stdAddChar ((((a.val:ℤ)*(n:ℤ)):ℤ):ZMod 4)) =
    (if n=0 then 1 else -24*ArithmeticFunction.sigma 1 n:ℂ) *
    (∑ a : Fin 4, lpsChi4E2Character (a.val:ZMod 4)*
      ZMod.stdAddChar ((((a.val:ℤ)*(n:ℤ)):ℤ):ZMod 4)) by
        rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro a ha;ring]
  have hfour := lpsChi4E2Character_fin_fourier (n:ZMod 4)
  have hfour' : (∑ a : Fin 4,lpsChi4E2Character (a.val:ZMod 4)*
    ZMod.stdAddChar ((((a.val:ℤ)*(n:ℤ)):ℤ):ZMod 4))=
    lpsChi4E2Character (n:ZMod 4)*gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)) := by
      simpa only [Int.cast_mul,Int.cast_natCast,mul_comm] using hfour
  rw [hfour']
  by_cases hn : n=0
  · subst n
    simp [lpsChi4E2Character_values.1]
  · simp only [if_neg hn]
    have hg := lpsChi4E2Gauss_ne_zero
    field_simp [hg]


/-- Actual E2 holomorphicity and finite translated summation prove holomorphicity of the twist. -/
lemma lpsChi4E2Twist_mdifferentiable :
    MDiff (fun z : ℍ => lpsChi4E2Twist z) := by
  classical
  unfold lpsChi4E2Twist
  have h : MDiff (∑ a : Fin 4, lpsChi4E2Character (a.val:ZMod 4) •
    (fun z : ℍ => EisensteinSeries.E2 (((a.val:ℝ)/(4:ℝ)) +ᵥ z))) :=
    MDifferentiable.sum (fun (a : Fin 4) ha =>
      MDifferentiable.const_smul _ (lpsE2_real_shift_mdifferentiable ((a.val:ℝ)/(4:ℝ))))
  have h2 := MDifferentiable.const_smul
    (gaussSum (lpsChi4E2Character) (ZMod.stdAddChar (N:=4)))⁻¹ h
  convert h2 using 1
  ext z
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]

/-- The genuine convergent q-series proves boundedness in the full infinity filter. -/
lemma lpsChi4E2Twist_isBoundedAtImInfty :
    UpperHalfPlane.IsBoundedAtImInfty (fun z : ℍ => lpsChi4E2Twist z) := by
  apply UpperHalfPlane.isBoundedAtImInfty_of_hasSum_qExpansion (by norm_num : (0:ℝ)<1)
  intro z
  simpa only [smul_eq_mul] using lpsChi4E2Twist_hasSum z


/-- Actual E2 periodicity proves period one for every genuine translated summand. -/
lemma lpsChi4E2Twist_add_one (z : ℍ) :
    lpsChi4E2Twist ((1:ℝ) +ᵥ z)=lpsChi4E2Twist z := by
  unfold lpsChi4E2Twist
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  rw [show ((a.val:ℝ)/(4:ℝ)) +ᵥ ((1:ℝ) +ᵥ z) =
    (1:ℝ) +ᵥ (((a.val:ℝ)/(4:ℝ)) +ᵥ z) by
      rw [← add_vadd,← add_vadd,add_comm],lpsE2_add_one]


/-- Analytic uniqueness identifies every actual twist coefficient with the character-weighted divisor sum. -/
lemma lpsChi4E2Twist_coeff_qExpansion (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (fun z : ℍ => lpsChi4E2Twist z)) =
      -24*(ArithmeticFunction.sigma 1 n:ℂ)*lpsChi4E2Character (n:ZMod 4) := by
  have hp := lpsFunction_periodic_comp_ofComplex _ (lpsChi4E2Twist_add_one)
  have hm := lpsChi4E2Twist_mdifferentiable
  have hb := lpsChi4E2Twist_isBoundedAtImInfty
  have ha := UpperHalfPlane.analyticAt_cuspFunction_zero (by norm_num : (0:ℝ)<1) hp hm hb
  let f : C(ℍ,ℂ) := ⟨fun z => lpsChi4E2Twist z,hm.continuous⟩
  symm
  exact UpperHalfPlane.qExpansion_coeff_unique f (by norm_num : (0:ℝ)<1) ha
    (fun z => by simpa only [smul_eq_mul,f,ContinuousMap.coe_mk] using lpsChi4E2Twist_hasSum z) n


/-- The actual positive-determinant affine action dilates the genuine modulus-four twist. -/
noncomputable def lpsChi4E2Dilate (m : ℕ) (hm : 0 < m) (z : ℍ) : ℂ :=
  lpsChi4E2Twist (lpsE2AffineMatrix m hm 0 • z)

/-- Actual translation after dilation expands the true dilated function as a finite affine E2 sum. -/
lemma lpsChi4E2Dilate_eq (m : ℕ) (hm : 0 < m) :
    lpsChi4E2Dilate m hm = (fun z : ℍ =>
      (gaussSum (lpsChi4E2Character) (ZMod.stdAddChar (N:=4)))⁻¹ *
        ∑ r : Fin 4,lpsChi4E2Character (r.val:ZMod 4)*
          EisensteinSeries.E2 (lpsE2AffineMatrix m hm ((r.val:ℝ)/(4:ℝ)) • z)) := by
  funext z
  simp only [lpsChi4E2Dilate,lpsChi4E2Twist,lpsE2AffineMatrix_translation]

/-- Full-filter affine E2 limits give every actual dilated cusp constant as a weighted gcd sum. -/
lemma lpsChi4E2Dilate_cusp_tendsto (m : ℕ) (hm : 0 < m)
    (γ : SL(2,ℤ)) :
    Tendsto (lpsChi4E2Dilate m hm ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 ((gaussSum (lpsChi4E2Character) (ZMod.stdAddChar (N:=4)))⁻¹ *
        ∑ r : Fin 4,lpsChi4E2Character (r.val:ZMod 4)*
          (((Int.gcd ((4:ℤ)*(m:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0)
            ((4:ℤ)*γ 1 0):ℕ):ℂ)^2/((4:ℂ)^2*(m:ℂ)^2)))) := by
  classical
  have hs := tendsto_finsetSum Finset.univ (fun (r : Fin 4) hr =>
    (lpsE2Affine_cusp_tendsto m 4 hm (by decide : 0 < 4) (r.val:ℤ) γ).const_mul
      (lpsChi4E2Character (r.val:ZMod 4)))
  have h := hs.const_mul (gaussSum (lpsChi4E2Character) (ZMod.stdAddChar (N:=4)))⁻¹
  have he : (lpsChi4E2Dilate m hm ∣[(2:ℤ)] γ) = (fun z : ℍ =>
      (gaussSum (lpsChi4E2Character) (ZMod.stdAddChar (N:=4)))⁻¹ *
        ∑ r : Fin 4,lpsChi4E2Character (r.val:ZMod 4)*
          (((fun w : ℍ => EisensteinSeries.E2
            (lpsE2AffineMatrix m hm ((r.val:ℝ)/(4:ℝ)) • w)) ∣[(2:ℤ)] γ) z)) := by
    rw [lpsChi4E2Dilate_eq]
    funext z
    simp only [ModularForm.SL_slash_apply]
    rw [mul_assoc,Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    ring
  rw [he]
  simpa only [Int.cast_natCast,Nat.cast_ofNat] using h

/-- The actual dilation by one is the original twist function. -/
lemma lpsChi4E2Dilate_one :
    lpsChi4E2Dilate 1 (by decide)=lpsChi4E2Twist := by
  funext z
  unfold lpsChi4E2Dilate
  congr 1
  apply UpperHalfPlane.ext
  rw [lpsE2AffineMatrix_action]
  simp

/-- The proved dilation-one identity gives the complete actual undilated cusp vector. -/
lemma lpsChi4E2Twist_cusp_gcd_tendsto (γ : SL(2,ℤ)) :
    Tendsto (lpsChi4E2Twist ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 ((gaussSum (lpsChi4E2Character) (ZMod.stdAddChar (N:=4)))⁻¹ *
        ∑ r : Fin 4,lpsChi4E2Character (r.val:ZMod 4)*
          (((Int.gcd ((4:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0)
            ((4:ℤ)*γ 1 0):ℕ):ℂ)^2/(4:ℂ)^2))) := by
  simpa only [lpsChi4E2Dilate_one,Nat.cast_one,Int.cast_one,mul_one,one_pow] using
    lpsChi4E2Dilate_cusp_tendsto 1 (by decide) γ


/-- Level divisibility and finite unit arithmetic construct shift conjugates whose true E2 defects cancel. -/
lemma lpsChi4E2Twist_slash_gamma0 (γ : SL(2,ℤ))
    (hγ : γ∈CongruenceSubgroup.Gamma0 16) :
    (lpsChi4E2Twist ∣[(2:ℤ)] γ)=lpsChi4E2Twist := by
  classical
  obtain ⟨k,hC⟩ := lpsE2Gamma0_lower_entry 4 γ hγ
  have hAD : (γ 0 0:ZMod 4)*(γ 1 1:ZMod 4)=1 := by
    have hd : γ 0 0*γ 1 1-γ 0 1*γ 1 0=1 := by
      simpa only [Matrix.det_fin_two] using γ.det_coe
    have h : (γ 0 0:ZMod 4)*(γ 1 1:ZMod 4)-(γ 0 1:ZMod 4)*(γ 1 0:ZMod 4)=1 := by
      simpa only [map_sub,map_mul,map_one,Int.coe_castRingHom] using
        congrArg (Int.castRingHom (ZMod 4)) hd
    have hc : (γ 1 0:ZMod 4)=0 := by
      rw [hC]
      push_cast
      have hz : (16:ZMod 4)=0 := by decide
      rw [hz]
      simp
    simpa only [hc,mul_zero,sub_zero] using h
  have hEq : (γ 0 0:ZMod 4)=(γ 1 1:ZMod 4) := by
    have he : ∀ a d : ZMod 4,a*d=1 → a=d := by decide
    exact he _ _ hAD
  ext z
  have hr (r : Fin 4) : EisensteinSeries.E2 (((r.val:ℝ)/4) +ᵥ (γ • z))*
      UpperHalfPlane.denom γ (z:ℂ)^(-(2:ℤ))=
      EisensteinSeries.E2 (((r.val:ℝ)/4) +ᵥ z)-
        (1/(2*riemannZeta 2))*EisensteinSeries.D2 γ z := by
    have ht : (4:ℤ)∣(r.val:ℤ)*γ 1 1-(r.val:ℤ)*γ 0 0 := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp
      push_cast
      rw [hEq]
      ring
    obtain ⟨t,ht⟩ := ht
    simpa only [ModularForm.SL_slash_apply,Int.cast_natCast,Nat.cast_ofNat] using
      lpsE2_real_shift_slash 4 γ k (r.val:ℤ) (r.val:ℤ) t hC ht z
  simp only [ModularForm.SL_slash_apply,lpsChi4E2Twist]
  rw [mul_assoc,Finset.sum_mul]
  simp_rw [mul_assoc,hr,mul_sub]
  rw [Finset.sum_sub_distrib,←Finset.sum_mul,lpsChi4E2Character_sum_zero,
    zero_mul,sub_zero]

/-- The complete full-filter cusp vector proves genuine boundedness at every rational cusp. -/
lemma lpsChi4E2Twist_bounded_at_cusps (c : OnePoint ℝ) (hc : IsCusp c 𝒮ℒ) :
    OnePoint.IsBoundedAt c lpsChi4E2Twist 2 := by
  apply (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr
  intro γ hγ
  exact (lpsChi4E2Twist_cusp_gcd_tendsto γ).isBigO_one ℝ

/-- Proved invariance, holomorphicity and all-cusp boundedness construct the actual weight-two modular form. -/
noncomputable def lpsChi4E2TwistModularForm :
    ModularForm (CongruenceSubgroup.Gamma0 16 : Subgroup (GL (Fin 2) ℝ)) 2 where
  toFun := lpsChi4E2Twist
  slash_action_eq' := by
    intro g hg
    obtain ⟨γ,hγ,rfl⟩ := hg
    simpa [Matrix.SpecialLinearGroup.mapGL,←ModularForm.SL_slash] using
      lpsChi4E2Twist_slash_gamma0 γ hγ
  holo' := lpsChi4E2Twist_mdifferentiable
  bdd_at_cusps' := fun hc => lpsChi4E2Twist_bounded_at_cusps _
    (hc.mono (Subgroup.map_le_range (Matrix.SpecialLinearGroup.mapGL ℝ) _))

/-- The genuine modular form keeps the actual normalized translated E2 function. -/
lemma lpsChi4E2TwistModularForm_apply (z : ℍ) : lpsChi4E2TwistModularForm z=lpsChi4E2Twist z := rfl

/-- The actual modular form retains every proved character-weighted divisor coefficient. -/
lemma coeff_qExpansion_lpsChi4E2TwistModularForm (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 lpsChi4E2TwistModularForm)=
      -24*(ArithmeticFunction.sigma 1 n:ℂ)*lpsChi4E2Character (n:ZMod 4) :=
  lpsChi4E2Twist_coeff_qExpansion n


/-- The actual zero coefficient and analytic cusp function prove vanishing at infinity in the full filter. -/
lemma lpsChi4E2Twist_tendsto_zero :
    Tendsto (lpsChi4E2Twist) UpperHalfPlane.atImInfty (𝓝 0) := by
  have hp := lpsFunction_periodic_comp_ofComplex _ (lpsChi4E2Twist_add_one)
  have ha := UpperHalfPlane.analyticAt_cuspFunction_zero (by norm_num : (0:ℝ)<1) hp
    (lpsChi4E2Twist_mdifferentiable) (lpsChi4E2Twist_isBoundedAtImInfty)
  have hc : UpperHalfPlane.cuspFunction 1 (lpsChi4E2Twist) 0=0 := by
    have h := lpsChi4E2Twist_coeff_qExpansion 0
    simpa [UpperHalfPlane.qExpansion_coeff,MulChar.map_zero] using h
  have he : (fun z : ℍ => UpperHalfPlane.cuspFunction 1 (lpsChi4E2Twist)
      (Function.Periodic.qParam 1 (z:ℂ)))=lpsChi4E2Twist := by
    funext z
    exact UpperHalfPlane.eq_cuspFunction z (by norm_num) hp
  have h := ha.continuousAt.tendsto.comp
    (UpperHalfPlane.qParam_tendsto_atImInfty (by norm_num : (0:ℝ)<1))
  simpa only [Function.comp_def,hc,he] using h


/-- The complete actual cusp vector computes the nonzero quarter-cusp constant minus twelve over Gauss. -/
lemma lpsChi4E2Twist_quarter_cusp_tendsto :
    Tendsto (lpsChi4E2Twist ∣[(2:ℤ)] lpsE2PrimeCuspMatrix 4) UpperHalfPlane.atImInfty
      (𝓝 (-12/gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))) := by
  have h := lpsChi4E2Twist_cusp_gcd_tendsto (lpsE2PrimeCuspMatrix 4)
  have he : (gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹*
      (∑ r : Fin 4,lpsChi4E2Character (r.val:ZMod 4)*
        (((Int.gcd ((4:ℤ)*(lpsE2PrimeCuspMatrix 4) 0 0+(r.val:ℤ)*(lpsE2PrimeCuspMatrix 4) 1 0)
          ((4:ℤ)*(lpsE2PrimeCuspMatrix 4) 1 0):ℕ):ℂ)^2/(4:ℂ)^2))=
      -12/gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)) := by
    norm_num [Fin.sum_univ_four,lpsE2PrimeCuspMatrix,Matrix.of_apply,
      lpsChi4E2Character_apply,ZMod.χ₄_apply]
    ring
  rw [he] at h
  exact h

/-- The genuine nonzero Gauss normalization rejects vanishing at the quarter cusp. -/
lemma lpsChi4E2Twist_quarter_cusp_not_zero :
    ¬UpperHalfPlane.IsZeroAtImInfty (lpsChi4E2Twist ∣[(2:ℤ)] lpsE2PrimeCuspMatrix 4) := by
  intro hz
  have he := tendsto_nhds_unique lpsChi4E2Twist_quarter_cusp_tendsto hz
  exact (div_ne_zero (by norm_num : (-12:ℂ)≠0) lpsChi4E2Gauss_ne_zero) he

/-- The actual quarter-cusp limit excludes any cusp form with the same underlying function. -/
lemma lpsChi4E2Twist_not_cuspForm :
    ¬∃ f : CuspForm (CongruenceSubgroup.Gamma0 16 : Subgroup (GL (Fin 2) ℝ)) 2,
      (f:ℍ→ℂ)=lpsChi4E2Twist := by
  rintro ⟨f,hf⟩
  have hz := CuspFormClass.zero_at_infty_slash f (g:=lpsE2PrimeCuspMatrix 4)
  rw [hf] at hz
  exact lpsChi4E2Twist_quarter_cusp_not_zero hz

end QEC.Coding.TannerLiftedProduct
