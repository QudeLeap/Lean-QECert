import QEC.Coding.ExpanderCodes.LPSCharacterEisensteinCusps

/-!
# Full cusp formulas for the genuine character dilations

The actual gcd-reduced first column constructs an explicit determinant-one
matrix. True weighted gcd sums transport the complete F4 and Fq cusp formulas
through every positive dilation. A coprime dilation preserves denominator
power divisibility and gives the actual character multiplier, including signed
and zero denominators. These derived limits support the weighted theta
Eisenstein comparison; all-cusp cancellation and coefficient growth remain
separate proof obligations.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

/-- Primitivity reduces the actual dilated first-column gcd to the dilation-denominator gcd. -/
lemma lpsEisensteinDilation_column_gcd (m : ℕ) (γ : SL(2,ℤ)) :
    Int.gcd ((m:ℤ)*γ 0 0) (γ 1 0)=Int.gcd (m:ℤ) (γ 1 0) := by
  exact Int.gcd_mul_left_left_of_gcd_eq_one (lpsSL2Z_firstColumn_gcd_one γ)

/-- A positive dilation keeps the actual integer first-column gcd positive. -/
lemma lpsEisensteinDilation_column_gcd_pos (m : ℕ) (hm : 0<m) (γ : SL(2,ℤ)) :
    0<Int.gcd ((m:ℤ)*γ 0 0) (γ 1 0) := by
  rw [lpsEisensteinDilation_column_gcd]
  exact Int.gcd_pos_iff.mpr (Or.inl (by exact_mod_cast hm.ne'))

/-- The explicit Bezout matrix of the true gcd-reduced dilated cusp column. -/
def lpsEisensteinDilationCuspMatrix (m : ℕ) (hm : 0<m) (γ : SL(2,ℤ)) : SL(2,ℤ) :=
  lpsE2IntegerPrimitiveColumn
    (((m:ℤ)*γ 0 0)/(Int.gcd ((m:ℤ)*γ 0 0) (γ 1 0):ℤ))
    ((γ 1 0)/(Int.gcd ((m:ℤ)*γ 0 0) (γ 1 0):ℤ))
    (Int.gcd_div_gcd_div_gcd (lpsEisensteinDilation_column_gcd_pos m hm γ))

/-- The constructed determinant-one cusp matrix has the true reduced first column. -/
lemma lpsEisensteinDilationCuspMatrix_column (m : ℕ) (hm : 0<m) (γ : SL(2,ℤ)) :
    (m:ℤ)*γ 0 0=(Int.gcd (m:ℤ) (γ 1 0):ℤ)*lpsEisensteinDilationCuspMatrix m hm γ 0 0 ∧
      γ 1 0=(Int.gcd (m:ℤ) (γ 1 0):ℤ)*lpsEisensteinDilationCuspMatrix m hm γ 1 0 := by
  have hA := Int.mul_ediv_cancel_of_dvd (Int.gcd_dvd_left ((m:ℤ)*γ 0 0) (γ 1 0))
  have hC := Int.mul_ediv_cancel_of_dvd (Int.gcd_dvd_right ((m:ℤ)*γ 0 0) (γ 1 0))
  constructor
  · change (m:ℤ)*γ 0 0=(Int.gcd (m:ℤ) (γ 1 0):ℤ)*
      (((m:ℤ)*γ 0 0)/(Int.gcd ((m:ℤ)*γ 0 0) (γ 1 0):ℤ))
    rw [lpsEisensteinDilation_column_gcd] at hA ⊢
    exact hA.symm
  · change γ 1 0=(Int.gcd (m:ℤ) (γ 1 0):ℤ)*
      ((γ 1 0)/(Int.gcd ((m:ℤ)*γ 0 0) (γ 1 0):ℤ))
    rw [lpsEisensteinDilation_column_gcd] at hC ⊢
    exact hC.symm

/-- The actual affine cusp gcd scales by the true dilation-denominator gcd. -/
lemma lpsEisensteinDilationCuspGcd (N r : ℤ) (m : ℕ) (hm : 0<m) (γ : SL(2,ℤ)) :
    Int.gcd (N*(m:ℤ)*γ 0 0+r*γ 1 0) (N*γ 1 0)=
      Int.gcd (m:ℤ) (γ 1 0)*
        Int.gcd (N*lpsEisensteinDilationCuspMatrix m hm γ 0 0+
          r*lpsEisensteinDilationCuspMatrix m hm γ 1 0)
          (N*lpsEisensteinDilationCuspMatrix m hm γ 1 0) := by
  have h := lpsEisensteinDilationCuspMatrix_column m hm γ
  have heA : N*(m:ℤ)*γ 0 0+r*γ 1 0=(Int.gcd (m:ℤ) (γ 1 0):ℤ)*
      (N*lpsEisensteinDilationCuspMatrix m hm γ 0 0+
        r*lpsEisensteinDilationCuspMatrix m hm γ 1 0) := by
    linear_combination N*h.1+r*h.2
  have heC : N*γ 1 0=(Int.gcd (m:ℤ) (γ 1 0):ℤ)*
      (N*lpsEisensteinDilationCuspMatrix m hm γ 1 0) := by linear_combination N*h.2
  rw [heA,heC,Int.gcd_mul_left,Int.natAbs_natCast]

/-- Every actual finite weighted gcd vector retains its precise dilation scaling. -/
lemma lpsEisensteinDilation_weightedCuspGcd (N m : ℕ) (hm : 0<m)
    (γ : SL(2,ℤ)) (w : Fin N→ℂ) :
    (∑ r : Fin N,w r*((Int.gcd ((N:ℤ)*(m:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0)
      ((N:ℤ)*γ 1 0):ℂ)^2/((N:ℂ)^2*(m:ℂ)^2)))=
      ((Int.gcd (m:ℤ) (γ 1 0):ℂ)^2/(m:ℂ)^2)*
        (∑ r : Fin N,w r*((Int.gcd ((N:ℤ)*lpsEisensteinDilationCuspMatrix m hm γ 0 0+
          (r.val:ℤ)*lpsEisensteinDilationCuspMatrix m hm γ 1 0)
          ((N:ℤ)*lpsEisensteinDilationCuspMatrix m hm γ 1 0):ℂ)^2/(N:ℂ)^2)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [lpsEisensteinDilationCuspGcd N r.val m hm γ]
  simp only [Nat.cast_mul]
  ring

/-- At every signed integer cusp the actual modulus-four dilation has the gcd-scaled character limit. -/
lemma lpsChi4E2Dilate_cusp_character_tendsto (m : ℕ) (hm : 0<m) (γ : SL(2,ℤ)) :
    Tendsto (lpsChi4E2Dilate m hm ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (((Int.gcd (m:ℤ) (γ 1 0):ℂ)^2/(m:ℂ)^2)*
        lpsChi4EisensteinCuspConstant (lpsEisensteinDilationCuspMatrix m hm γ))) := by
  have ht := lpsChi4E2Dilate_cusp_tendsto m hm γ
  have he := tendsto_nhds_unique (lpsChi4E2Twist_cusp_gcd_tendsto
    (lpsEisensteinDilationCuspMatrix m hm γ))
    (lpsChi4E2Twist_cusp_character_tendsto (lpsEisensteinDilationCuspMatrix m hm γ))
  have hs := lpsEisensteinDilation_weightedCuspGcd 4 m hm γ
    (fun r => lpsChi4E2Character (r.val:ZMod 4))
  norm_num only [Nat.cast_ofNat] at hs ht he
  rw [hs] at ht
  rw [mul_left_comm (gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹
    ((Int.gcd (m:ℤ) (γ 1 0):ℂ)^2/(m:ℂ)^2),he] at ht
  exact ht

/-- At every signed integer cusp the actual quadratic dilation has the gcd-scaled character limit. -/
lemma lpsQuadraticE2Dilate_cusp_character_tendsto (q m : ℕ) [Fact q.Prime]
    (hq2 : q≠2) (hm : 0<m) (γ : SL(2,ℤ)) :
    Tendsto (lpsQuadraticE2Dilate q m hm ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (((Int.gcd (m:ℤ) (γ 1 0):ℂ)^2/(m:ℂ)^2)*
        lpsQuadraticEisensteinCuspConstant q (lpsEisensteinDilationCuspMatrix m hm γ))) := by
  have ht := lpsQuadraticE2Dilate_cusp_tendsto q m hm γ
  have he := tendsto_nhds_unique (lpsQuadraticE2Twist_cusp_gcd_tendsto q
    (lpsEisensteinDilationCuspMatrix m hm γ))
    (lpsQuadraticE2Twist_cusp_character_tendsto q hq2 (lpsEisensteinDilationCuspMatrix m hm γ))
  rw [lpsEisensteinDilation_weightedCuspGcd q m hm γ
    (fun r => lpsQuadraticE2Character q (r.val:ZMod q))] at ht
  rw [mul_left_comm (gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹
    ((Int.gcd (m:ℤ) (γ 1 0):ℂ)^2/(m:ℂ)^2),he] at ht
  exact ht

/-- A dilation coprime to a modulus preserves every power-divisibility condition on the reduced denominator. -/
lemma lpsEisensteinDilationCuspMatrix_prime_pow_dvd (p m : ℕ) (hm : 0<m)
    (hmp : m.Coprime p) (γ : SL(2,ℤ)) (e : ℕ) :
    (p:ℤ)^e∣γ 1 0 ↔ (p:ℤ)^e∣lpsEisensteinDilationCuspMatrix m hm γ 1 0 := by
  have hd : Int.gcd (m:ℤ) (γ 1 0)∣m := by
    simpa only [Int.natAbs_natCast] using
      (Int.ofNat_dvd_left.mp (Int.gcd_dvd_left (m:ℤ) (γ 1 0)))
  have hc := (hmp.coprime_dvd_left hd).symm.pow_left e
  have hI : Int.gcd ((p:ℤ)^e) (Int.gcd (m:ℤ) (γ 1 0):ℤ)=1 := by
    simpa only [Int.gcd_def,Int.natAbs_pow,Int.natAbs_natCast] using hc.gcd_eq_one
  have hcol := (lpsEisensteinDilationCuspMatrix_column m hm γ).2
  constructor
  · intro h
    rw [hcol] at h
    exact Int.dvd_of_dvd_mul_right_of_gcd_one h hI
  · intro h
    rw [hcol]
    exact dvd_mul_of_dvd_right h _

/-- A prime-unit dilation multiplies the reduced quadratic cusp constant by its actual character value. -/
lemma lpsQuadraticEisensteinCuspConstant_dilation (q m : ℕ) [Fact q.Prime]
    (hm : 0<m) (hmq : m.Coprime q) (γ : SL(2,ℤ)) :
    lpsQuadraticEisensteinCuspConstant q (lpsEisensteinDilationCuspMatrix m hm γ)=
      lpsQuadraticE2Character q (m:ZMod q)*lpsQuadraticEisensteinCuspConstant q γ := by
  let δ := lpsEisensteinDilationCuspMatrix m hm γ
  let d : ℕ := Int.gcd (m:ℤ) (γ 1 0)
  have hcol : (m:ℤ)*γ 0 0=(d:ℤ)*δ 0 0 ∧ γ 1 0=(d:ℤ)*δ 1 0 :=
    lpsEisensteinDilationCuspMatrix_column m hm γ
  have h1 := lpsEisensteinDilationCuspMatrix_prime_pow_dvd q m hm hmq γ 1
  simp only [pow_one] at h1
  have h2 := lpsEisensteinDilationCuspMatrix_prime_pow_dvd q m hm hmq γ 2
  change (q:ℤ)∣γ 1 0 ↔ (q:ℤ)∣δ 1 0 at h1
  change (q:ℤ)^2∣γ 1 0 ↔ (q:ℤ)^2∣δ 1 0 at h2
  change lpsQuadraticEisensteinCuspConstant q δ=_
  unfold lpsQuadraticEisensteinCuspConstant
  by_cases hC : (q:ℤ)∣γ 1 0
  · rw [if_pos hC,if_pos (h1.mp hC)]
    by_cases hC2 : (q:ℤ)^2∣γ 1 0
    · rw [if_pos hC2,if_pos (h2.mp hC2),mul_zero]
    · rw [if_neg hC2,if_neg (fun h => hC2 (h2.mpr h))]
      have hδC := h1.mp hC
      have hq : (q:ℤ)≠0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
      have hD : ((γ 1 0/(q:ℤ):ℤ):ZMod q)≠0 := by
        intro hz
        have hDq := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hz
        have hh : (q:ℤ)^2∣(q:ℤ)*(γ 1 0/(q:ℤ)) := by
          rw [pow_two,mul_dvd_mul_iff_left hq];exact hDq
        rw [Int.mul_ediv_cancel_of_dvd hC] at hh
        exact hC2 hh
      have hδD : ((δ 1 0/(q:ℤ):ℤ):ZMod q)≠0 := by
        intro hz
        have hDq := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hz
        have hh : (q:ℤ)^2∣(q:ℤ)*(δ 1 0/(q:ℤ)) := by
          rw [pow_two,mul_dvd_mul_iff_left hq];exact hDq
        rw [Int.mul_ediv_cancel_of_dvd hδC] at hh
        exact hC2 (h2.mpr hh)
      have hDD : γ 1 0/(q:ℤ)=(d:ℤ)*(δ 1 0/(q:ℤ)) := by
        calc
          γ 1 0/(q:ℤ)=((d:ℤ)*δ 1 0)/(q:ℤ) := congrArg (·/(q:ℤ)) hcol.2
          _=(d:ℤ)*(δ 1 0/(q:ℤ)) := Int.mul_ediv_assoc _ hδC
      have hAF : (m:ZMod q)*(γ 0 0:ZMod q)=(d:ZMod q)*(δ 0 0:ZMod q) := by
        have h := congrArg (fun x : ℤ => (x:ZMod q)) hcol.1
        simpa only [Int.cast_mul,Int.cast_natCast] using h
      have hDF : ((γ 1 0/(q:ℤ):ℤ):ZMod q)=
          (d:ZMod q)*((δ 1 0/(q:ℤ):ℤ):ZMod q) := by
        have h := congrArg (fun x : ℤ => (x:ZMod q)) hDD
        simpa only [Int.cast_mul,Int.cast_natCast] using h
      have hx : (δ 0 0:ZMod q)*((γ 1 0/(q:ℤ):ℤ):ZMod q)=
          (m:ZMod q)*(γ 0 0:ZMod q)*((δ 1 0/(q:ℤ):ℤ):ZMod q) := by
        rw [hDF,hAF];ring
      have he : -(δ 0 0:ZMod q)/((δ 1 0/(q:ℤ):ℤ):ZMod q)=
          (m:ZMod q)*(-(γ 0 0:ZMod q)/((γ 1 0/(q:ℤ):ℤ):ZMod q)) := by
        field_simp [hD,hδD]
        linear_combination -hx
      rw [he,map_mul]
      ring
  · rw [if_neg hC,if_neg (fun h => hC (h1.mpr h)),mul_zero]


/-- The signed remainder-four condition is precisely divisibility by four without divisibility by eight. -/
lemma lpsInt_mod_eight_four_iff (C : ℤ) : C%8=4 ↔ (4:ℤ)∣C ∧ ¬(8:ℤ)∣C := by
  simp only [Int.dvd_iff_emod_eq_zero]
  omega

/-- A modulus-four unit dilation multiplies the reduced cusp constant by its actual character value. -/
lemma lpsChi4EisensteinCuspConstant_dilation (m : ℕ) (hm : 0<m)
    (hm4 : m.Coprime 4) (γ : SL(2,ℤ)) :
    lpsChi4EisensteinCuspConstant (lpsEisensteinDilationCuspMatrix m hm γ)=
      lpsChi4E2Character (m:ZMod 4)*lpsChi4EisensteinCuspConstant γ := by
  let δ := lpsEisensteinDilationCuspMatrix m hm γ
  let d : ℕ := Int.gcd (m:ℤ) (γ 1 0)
  have hcol : (m:ℤ)*γ 0 0=(d:ℤ)*δ 0 0 ∧ γ 1 0=(d:ℤ)*δ 1 0 :=
    lpsEisensteinDilationCuspMatrix_column m hm γ
  have hd : d∣m := by
    simpa only [Int.natAbs_natCast] using
      (Int.ofNat_dvd_left.mp (Int.gcd_dvd_left (m:ℤ) (γ 1 0)))
  have hd4 : IsUnit (d:ZMod 4) :=
    (ZMod.isUnit_iff_coprime d 4).mpr (hm4.coprime_dvd_left hd)
  have hm2 : m.Coprime 2 := hm4.coprime_dvd_right (by decide : (2:ℕ)∣4)
  have h4 := lpsEisensteinDilationCuspMatrix_prime_pow_dvd 2 m hm hm2 γ 2
  have h8 := lpsEisensteinDilationCuspMatrix_prime_pow_dvd 2 m hm hm2 γ 3
  norm_num only [Int.reducePow] at h4 h8
  change (4:ℤ)∣γ 1 0 ↔ (4:ℤ)∣δ 1 0 at h4
  change (8:ℤ)∣γ 1 0 ↔ (8:ℤ)∣δ 1 0 at h8
  have hs : γ 1 0%8=4 ↔ δ 1 0%8=4 := by
    rw [lpsInt_mod_eight_four_iff,lpsInt_mod_eight_four_iff,h4,h8]
  change lpsChi4EisensteinCuspConstant δ=_
  unfold lpsChi4EisensteinCuspConstant
  by_cases hC : γ 1 0%8=4
  · rw [if_pos hC,if_pos (hs.mp hC)]
    have hδC := (lpsInt_mod_eight_four_iff (δ 1 0)).mp (hs.mp hC)
    have hDD : γ 1 0/4=(d:ℤ)*(δ 1 0/4) := by
      calc
        γ 1 0/4=((d:ℤ)*δ 1 0)/4 := congrArg (·/4) hcol.2
        _=(d:ℤ)*(δ 1 0/4) := Int.mul_ediv_assoc _ hδC.1
    have hx : (m:ℤ)*(γ 0 0*(γ 1 0/4))=(d:ℤ)^2*(δ 0 0*(δ 1 0/4)) := by
      calc
        (m:ℤ)*(γ 0 0*(γ 1 0/4))=((m:ℤ)*γ 0 0)*(γ 1 0/4) := by ring
        _=((d:ℤ)*δ 0 0)*((d:ℤ)*(δ 1 0/4)) := congrArg₂ (·*·) hcol.1 hDD
        _=(d:ℤ)^2*(δ 0 0*(δ 1 0/4)) := by ring
    have hF : (m:ZMod 4)*(((γ 0 0*(γ 1 0/4)):ℤ):ZMod 4)=
        (d:ZMod 4)^2*(((δ 0 0*(δ 1 0/4)):ℤ):ZMod 4) := by
      have h := congrArg (fun x : ℤ => (x:ZMod 4)) hx
      simpa only [Int.cast_mul,Int.cast_natCast,Int.cast_pow] using h
    have hc := congrArg lpsChi4E2Character hF
    rw [map_mul,map_mul,lpsChi4E2Character_square _ hd4,one_mul] at hc
    rw [←hc]
    ring
  · rw [if_neg hC,if_neg (fun h => hC (hs.mpr h)),mul_zero]

/-- The actual prime-unit dilation cusp limit is its original character constant times the derived gcd factor. -/
lemma lpsQuadraticE2Dilate_cusp_coprime_tendsto (q m : ℕ) [Fact q.Prime]
    (hq2 : q≠2) (hm : 0<m) (hmq : m.Coprime q) (γ : SL(2,ℤ)) :
    Tendsto (lpsQuadraticE2Dilate q m hm ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (((Int.gcd (m:ℤ) (γ 1 0):ℂ)^2/(m:ℂ)^2)*
        (lpsQuadraticE2Character q (m:ZMod q)*lpsQuadraticEisensteinCuspConstant q γ))) := by
  have h := lpsQuadraticE2Dilate_cusp_character_tendsto q m hq2 hm γ
  rw [lpsQuadraticEisensteinCuspConstant_dilation q m hm hmq γ] at h
  exact h

/-- The actual modulus-four unit dilation cusp limit is its original character constant times the derived gcd factor. -/
lemma lpsChi4E2Dilate_cusp_coprime_tendsto (m : ℕ) (hm : 0<m)
    (hm4 : m.Coprime 4) (γ : SL(2,ℤ)) :
    Tendsto (lpsChi4E2Dilate m hm ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (((Int.gcd (m:ℤ) (γ 1 0):ℂ)^2/(m:ℂ)^2)*
        (lpsChi4E2Character (m:ZMod 4)*lpsChi4EisensteinCuspConstant γ))) := by
  have h := lpsChi4E2Dilate_cusp_character_tendsto m hm γ
  rw [lpsChi4EisensteinCuspConstant_dilation m hm hm4 γ] at h
  exact h

end QEC.Coding.TannerLiftedProduct
