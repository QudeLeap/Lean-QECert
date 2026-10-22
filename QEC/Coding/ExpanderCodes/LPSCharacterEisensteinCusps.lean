import QEC.Coding.ExpanderCodes.LPSModularDilation

/-!
# Character formulas at every Eisenstein cusp

The genuine determinant-one identity reduces unit-shift gcds to the squared
modulus. Complete finite character sums give full-filter limits for F4 and Fq
at every integer cusp matrix, including signed and zero denominators. A general
coprime-column gcd factorization gives the Kq limit as the product of those
constants. No cusp identity or conclusion is assumed.

These are internal arithmetic components of the standard theta Eisenstein
comparison. Its dilation, all-cusp cancellation, coefficient growth and the
exact PK22 main theorem remain subsequent proof obligations.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

/-- The determinant-one identity bounds the actual undilated cusp gcd by the modulus squared. -/
lemma lpsEisensteinCuspGcd_dvd_square (N : ℤ) (γ : SL(2,ℤ)) (r : ℤ) :
    Int.gcd (N*γ 0 0+r*γ 1 0) (N*γ 1 0) ∣ N.natAbs^2 := by
  let g := Int.gcd (N*γ 0 0+r*γ 1 0) (N*γ 1 0)
  have hA : (g:ℤ)∣N*γ 0 0+r*γ 1 0 := Int.gcd_dvd_left _ _
  have hC : (g:ℤ)∣N*γ 1 0 := Int.gcd_dvd_right _ _
  have hd : γ 0 0*γ 1 1-γ 0 1*γ 1 0=1 := by
    simpa only [Matrix.det_fin_two] using γ.det_coe
  have he : (N*γ 1 1)*(N*γ 0 0+r*γ 1 0)-
      (N*γ 0 1+r*γ 1 1)*(N*γ 1 0)=N^2 := by
    linear_combination N^2*hd
  have h := dvd_sub (dvd_mul_of_dvd_right hA (N*γ 1 1))
    (dvd_mul_of_dvd_right hC (N*γ 0 1+r*γ 1 1))
  rw [he] at h
  simpa only [Int.natAbs_pow] using (Int.ofNat_dvd_left.mp h)

/-- Every genuine determinant-one integer matrix has a primitive first column. -/
lemma lpsSL2Z_firstColumn_gcd_one (γ : SL(2,ℤ)) : Int.gcd (γ 0 0) (γ 1 0)=1 := by
  let g := Int.gcd (γ 0 0) (γ 1 0)
  have hA : (g:ℤ)∣γ 0 0 := Int.gcd_dvd_left _ _
  have hC : (g:ℤ)∣γ 1 0 := Int.gcd_dvd_right _ _
  have hd : γ 0 0*γ 1 1-γ 0 1*γ 1 0=1 := by
    simpa only [Matrix.det_fin_two] using γ.det_coe
  have h := dvd_sub (dvd_mul_of_dvd_left hA (γ 1 1))
    (dvd_mul_of_dvd_left hC (γ 0 1))
  rw [mul_comm (γ 1 0) (γ 0 1),hd] at h
  exact Nat.dvd_one.mp (Int.ofNat_dvd_left.mp h)

/-- For a unit translation residue the actual cusp gcd reduces to the fixed squared modulus. -/
lemma lpsEisensteinCuspGcd_unit_reduce (N : ℤ) (γ : SL(2,ℤ)) (r : ℤ)
    (hr : r.natAbs.Coprime (N.natAbs^2)) :
    Int.gcd (N*γ 0 0+r*γ 1 0) (N*γ 1 0)=
      Int.gcd (N*γ 0 0+r*γ 1 0) (N^2) := by
  apply Nat.dvd_antisymm
  · apply Int.dvd_gcd (Int.gcd_dvd_left _ _)
    have h := lpsEisensteinCuspGcd_dvd_square N γ r
    exact Int.ofNat_dvd_left.mpr (by simpa only [Int.natAbs_pow] using h)
  · let d := Int.gcd (N*γ 0 0+r*γ 1 0) (N^2)
    have hx : (d:ℤ)∣N*γ 0 0+r*γ 1 0 := Int.gcd_dvd_left _ _
    have hN : (d:ℤ)∣N^2 := Int.gcd_dvd_right _ _
    have hNd : d∣N.natAbs^2 := by
      simpa only [Int.natAbs_pow] using (Int.ofNat_dvd_left.mp hN)
    have hc : Int.gcd (d:ℤ) r=1 := by
      simpa only [Int.gcd_def,Int.natAbs_natCast] using (hr.coprime_dvd_right hNd).symm.gcd_eq_one
    have he : N*(N*γ 0 0+r*γ 1 0)-γ 0 0*N^2=(N*γ 1 0)*r := by ring
    have hh := dvd_sub (dvd_mul_of_dvd_right hx N) (dvd_mul_of_dvd_right hN (γ 0 0))
    rw [he] at hh
    exact Int.dvd_gcd hx (Int.dvd_of_dvd_mul_left_of_gcd_one hh hc)

/-- The two nonzero modulus-four character terms have the exact signed gcd difference at every primitive column. -/
lemma lpsChi4EisensteinCuspGcd_difference (A C : ℤ)
    (hp : ¬(2∣A ∧ 2∣C)) :
    (((Int.gcd (4*A+C) 16:ℕ):ℂ)^2-((Int.gcd (4*A+3*C) 16:ℕ):ℂ)^2)=
      if C%8=4 then -192*lpsChi4E2Character ((A*(C/4):ℤ):ZMod 4) else 0 := by
  have h1 : Int.gcd (4*A+C) 16=Int.gcd (4*(A%4)+C%16) 16 := by
    rw [←Int.gcd_emod (4*A+C) 16,←Int.gcd_emod (4*(A%4)+C%16) 16]
    congr 1
    omega
  have h3 : Int.gcd (4*A+3*C) 16=Int.gcd (4*(A%4)+3*(C%16)) 16 := by
    rw [←Int.gcd_emod (4*A+3*C) 16,←Int.gcd_emod (4*(A%4)+3*(C%16)) 16]
    congr 1
    omega
  have hdiv : (C/4)%4=(C%16)/4 := by omega
  have hcast : ((A*(C/4):ℤ):ZMod 4)=((A%4)*((C%16)/4):ℤ) := by
    push_cast
    rw [←ZMod.intCast_mod A 4,←ZMod.intCast_mod (C/4) 4]
    norm_num only [Nat.cast_ofNat]
    rw [hdiv]
  have hp' : ¬((A%4)%2=0 ∧ (C%16)%2=0) := by
    simpa only [Int.emod_emod_of_dvd A (by norm_num : (2:ℤ)∣4),
      Int.emod_emod_of_dvd C (by norm_num : (2:ℤ)∣16),Int.dvd_iff_emod_eq_zero] using hp
  have h8 : C%8=(C%16)%8 := by omega
  rw [h1,h3,hcast,h8]
  have ha0 : 0≤A%4 := Int.emod_nonneg _ (by norm_num)
  have ha4 : A%4<4 := Int.emod_lt_of_pos _ (by norm_num)
  have hc0 : 0≤C%16 := Int.emod_nonneg _ (by norm_num)
  have hc16 : C%16<16 := Int.emod_lt_of_pos _ (by norm_num)
  generalize A%4=a at *
  generalize C%16=c at *
  interval_cases a <;> interval_cases c
  all_goals norm_num at hp'
  all_goals norm_num [lpsChi4E2Character_apply,ZMod.χ₄_apply]

/-- The gcd with a prime squared is classified by its two actual divisibility tests. -/
lemma lpsIntGcd_prime_sq (q : ℕ) [Fact q.Prime] (x : ℤ) :
    Int.gcd x ((q:ℤ)^2)=
      if (q:ℤ)^2∣x then q^2 else if (q:ℤ)∣x then q else 1 := by
  by_cases h2 : (q:ℤ)^2∣x
  · rw [if_pos h2,Int.gcd_eq_natAbs_right h2]
    simp
  · rw [if_neg h2]
    by_cases h1 : (q:ℤ)∣x
    · rw [if_pos h1]
      obtain ⟨y,rfl⟩ := h1
      have hy : ¬q∣y.natAbs := by
        intro hd
        obtain ⟨t,ht⟩ := Int.ofNat_dvd_left.mpr hd
        exact h2 ⟨t,by rw [ht];ring⟩
      have hc : Int.gcd y (q:ℤ)=1 := by
        simpa only [Int.gcd_def,Int.natAbs_natCast] using
          ((Fact.out : q.Prime).coprime_iff_not_dvd.mpr hy).symm.gcd_eq_one
      rw [pow_two,Int.gcd_mul_left,hc]
      simp
    · rw [if_neg h1]
      have hx : ¬q∣x.natAbs := by
        intro hd
        exact h1 (Int.ofNat_dvd_left.mpr hd)
      simpa only [Int.gcd_def,Int.natAbs_pow,Int.natAbs_natCast] using
        ((Fact.out : q.Prime).coprime_pow_of_not_dvd (m:=2) hx).gcd_eq_one

/-- Primitivity excludes simultaneous even entries in the genuine first column. -/
lemma lpsSL2Z_firstColumn_not_both_even (γ : SL(2,ℤ)) :
    ¬((2:ℤ)∣γ 0 0 ∧ (2:ℤ)∣γ 1 0) := by
  intro h
  have hg := Int.dvd_gcd h.1 h.2
  rw [lpsSL2Z_firstColumn_gcd_one] at hg
  norm_num at hg

/-- The complete signed character formula for the modulus-four Eisenstein cusp constant. -/
noncomputable def lpsChi4EisensteinCuspConstant (γ : SL(2,ℤ)) : ℂ :=
  if γ 1 0%8=4 then 3*gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4))*
    lpsChi4E2Character (((γ 0 0*(γ 1 0/4)):ℤ):ZMod 4) else 0

/-- The actual modulus-four twist has the full-filter character limit at every integer cusp matrix. -/
lemma lpsChi4E2Twist_cusp_character_tendsto (γ : SL(2,ℤ)) :
    Tendsto (lpsChi4E2Twist ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (lpsChi4EisensteinCuspConstant γ)) := by
  have ht := lpsChi4E2Twist_cusp_gcd_tendsto γ
  have hg1 := lpsEisensteinCuspGcd_unit_reduce 4 γ 1 (by norm_num)
  have hg3 := lpsEisensteinCuspGcd_unit_reduce 4 γ 3 (by norm_num)
  norm_num only [Int.natAbs_natCast,Nat.reducePow,Int.reducePow,one_mul] at hg1 hg3
  have hd := lpsChi4EisensteinCuspGcd_difference (γ 0 0) (γ 1 0)
    (lpsSL2Z_firstColumn_not_both_even γ)
  have he : (gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹ *
      (∑ r : Fin 4,lpsChi4E2Character (r.val:ZMod 4)*
        ((Int.gcd ((4:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0) ((4:ℤ)*γ 1 0):ℂ)^2/(4:ℂ)^2))=
      lpsChi4EisensteinCuspConstant γ := by
    rw [Fin.sum_univ_four]
    change (gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹ *
      (lpsChi4E2Character 0*((Int.gcd (4*γ 0 0+0*γ 1 0) (4*γ 1 0):ℂ)^2/(4:ℂ)^2)+
       lpsChi4E2Character 1*((Int.gcd (4*γ 0 0+1*γ 1 0) (4*γ 1 0):ℂ)^2/(4:ℂ)^2)+
       lpsChi4E2Character 2*((Int.gcd (4*γ 0 0+2*γ 1 0) (4*γ 1 0):ℂ)^2/(4:ℂ)^2)+
       lpsChi4E2Character 3*((Int.gcd (4*γ 0 0+3*γ 1 0) (4*γ 1 0):ℂ)^2/(4:ℂ)^2))=_
    rw [lpsChi4E2Character_values.1,lpsChi4E2Character_values.2.1,
      lpsChi4E2Character_values.2.2.1,lpsChi4E2Character_values.2.2.2]
    simp only [zero_mul,zero_add,add_zero,one_mul,neg_one_mul]
    rw [hg1,hg3]
    rw [show (((Int.gcd (4*γ 0 0+γ 1 0) 16:ℕ):ℂ)^2/(4:ℂ)^2+
        -(((Int.gcd (4*γ 0 0+3*γ 1 0) 16:ℕ):ℂ)^2/(4:ℂ)^2))=
      (((Int.gcd (4*γ 0 0+γ 1 0) 16:ℕ):ℂ)^2-
        ((Int.gcd (4*γ 0 0+3*γ 1 0) 16:ℕ):ℂ)^2)/(4:ℂ)^2 by ring,hd]
    unfold lpsChi4EisensteinCuspConstant
    split_ifs with hc
    · have hs := lpsChi4E2Gauss_sq
      have hn := lpsChi4E2Gauss_ne_zero
      field_simp [hn]
      linear_combination -48*lpsChi4E2Character (((γ 0 0*(γ 1 0/4)):ℤ):ZMod 4)*hs
    · simp
  rw [he] at ht
  exact ht

/-- The nontrivial character sum selects the unique root of the genuine finite-field linear expression. -/
lemma lpsQuadraticEisensteinCusp_delta (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (A D : ZMod q) (hD : D≠0) :
    (∑ r : ZMod q,lpsQuadraticE2Character q r*(if A+r*D=0 then (q:ℂ)^2 else 1))=
      ((q:ℂ)^2-1)*lpsQuadraticE2Character q (-A/D) := by
  classical
  have hc : (∑ r : ZMod q,lpsQuadraticE2Character q r)=0 :=
    MulChar.sum_eq_zero_of_ne_one (lpsQuadraticE2Character_ne_one q hq2)
  have he (r : ZMod q) : A+r*D=0 ↔ r= -A/D := by
    constructor
    · intro h
      apply (eq_div_iff hD).mpr
      linear_combination h
    · intro h
      have hh := (eq_div_iff hD).mp h
      linear_combination hh
  simp_rw [he]
  have hs : (∑ r : ZMod q,lpsQuadraticE2Character q r*(if r= -A/D then (q:ℂ)^2 else 1))=
      (∑ r : ZMod q,lpsQuadraticE2Character q r)+
        ((q:ℂ)^2-1)*(∑ r : ZMod q,if r= -A/D then lpsQuadraticE2Character q r else 0) := by
    rw [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    split_ifs <;> ring
  rw [hs,hc]
  simp

/-- A nonzero canonical prime-modulus residue is coprime to the modulus squared. -/
lemma lpsPrimeCuspShift_unit (q : ℕ) [Fact q.Prime] (r : Fin q) (hr : r≠0) :
    r.val.Coprime (q^2) := by
  have hp : 0<r.val := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact hr (Fin.ext hz)
  have hn : ¬q∣r.val := by
    intro h
    exact (Nat.le_of_dvd hp h).not_gt r.isLt
  exact (Fact.out : q.Prime).coprime_pow_of_not_dvd hn

/-- If the residue prime does not divide the cusp denominator every unit-shift gcd is one. -/
lemma lpsQuadraticEisensteinCuspGcd_of_not_dvd (q : ℕ) [Fact q.Prime]
    (γ : SL(2,ℤ)) (r : Fin q) (hr : r≠0) (hC : ¬(q:ℤ)∣γ 1 0) :
    Int.gcd ((q:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0) ((q:ℤ)*γ 1 0)=1 := by
  have hunit := lpsPrimeCuspShift_unit q r hr
  have hrc : (r.val:ZMod q)≠0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff r.val q).mp hz
    have hcq := hunit.coprime_dvd_right (dvd_pow_self q (by decide : (2:ℕ)≠0))
    exact ((Fact.out : q.Prime).coprime_iff_not_dvd.mp hcq.symm) hd
  have hc : (γ 1 0:ZMod q)≠0 := by
    intro hz
    exact hC ((ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) q).mp hz)
  have hx : ¬(q:ℤ)∣(q:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0 := by
    intro hd
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr hd
    have he : (((q:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0:ℤ):ZMod q)=
        (r.val:ZMod q)*(γ 1 0:ZMod q) := by push_cast;simp
    rw [he] at hz
    exact (mul_ne_zero hrc hc) hz
  have hx2 : ¬(q:ℤ)^2∣(q:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0 := by
    intro hd
    exact hx ((dvd_pow_self (q:ℤ) (by decide : (2:ℕ)≠0)).trans hd)
  rw [lpsEisensteinCuspGcd_unit_reduce (q:ℤ) γ r.val (by simpa using hunit),
    lpsIntGcd_prime_sq,if_neg hx2,if_neg hx]

/-- The actual quadratic character has zero total over the canonical finite residues. -/
lemma lpsQuadraticE2Character_fin_sum_zero (q : ℕ) [Fact q.Prime] (hq2 : q≠2) :
    (∑ r : Fin q,lpsQuadraticE2Character q (r.val:ZMod q))=0 := by
  have hs := (ZMod.finEquiv q).sum_comp (lpsQuadraticE2Character q)
  have hc := MulChar.sum_eq_zero_of_ne_one (lpsQuadraticE2Character_ne_one q hq2)
  rw [hc] at hs
  change (∑ r : Fin q,lpsQuadraticE2Character q (ZMod.finEquiv q r))=0 at hs
  simpa only [←lpsFin_cast_finEquiv] using hs

/-- The full cusp limit vanishes when the residue prime does not divide the denominator. -/
lemma lpsQuadraticE2Twist_cusp_not_dvd_tendsto_zero (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (γ : SL(2,ℤ)) (hC : ¬(q:ℤ)∣γ 1 0) :
    Tendsto (lpsQuadraticE2Twist q ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty (𝓝 0) := by
  have ht := lpsQuadraticE2Twist_cusp_gcd_tendsto q γ
  have hs : (∑ r : Fin q,lpsQuadraticE2Character q (r.val:ZMod q)*
      ((Int.gcd ((q:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0) ((q:ℤ)*γ 1 0):ℂ)^2/(q:ℂ)^2))=
      (1/(q:ℂ)^2)*(∑ r : Fin q,lpsQuadraticE2Character q (r.val:ZMod q)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases hz : r=0
    · subst r
      simp only [Fin.val_zero,Nat.cast_zero,MulChar.map_zero,zero_mul,mul_zero]
    · rw [lpsQuadraticEisensteinCuspGcd_of_not_dvd q γ r hz hC]
      simp only [Nat.cast_one,one_pow]
      ring
  rw [hs,lpsQuadraticE2Character_fin_sum_zero q hq2,mul_zero,mul_zero] at ht
  exact ht

/-- A denominator divisible by the residue prime yields the exact unique-root gcd classification. -/
lemma lpsQuadraticEisensteinCuspGcd_of_dvd (q : ℕ) [Fact q.Prime]
    (γ : SL(2,ℤ)) (r : Fin q) (hr : r≠0) (D : ℤ) (hC : γ 1 0=(q:ℤ)*D) :
    Int.gcd ((q:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0) ((q:ℤ)*γ 1 0)=
      if (((γ 0 0+(r.val:ℤ)*D):ℤ):ZMod q)=0 then q^2 else q := by
  have hunit := lpsPrimeCuspShift_unit q r hr
  have hq : (q:ℤ)≠0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have he : (q:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0=(q:ℤ)*(γ 0 0+(r.val:ℤ)*D) := by
    rw [hC];ring
  have hd : (q:ℤ)∣(q:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0 := by
    rw [he];exact dvd_mul_right _ _
  have hd2 : (q:ℤ)^2∣(q:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0 ↔
      (((γ 0 0+(r.val:ℤ)*D):ℤ):ZMod q)=0 := by
    rw [he,pow_two,mul_dvd_mul_iff_left hq]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).symm
  rw [lpsEisensteinCuspGcd_unit_reduce (q:ℤ) γ r.val (by simpa using hunit),
    lpsIntGcd_prime_sq]
  by_cases hz : (((γ 0 0+(r.val:ℤ)*D):ℤ):ZMod q)=0
  · rw [if_pos (hd2.mpr hz),if_pos hz]
  · rw [if_neg (fun h => hz (hd2.mp h)),if_pos hd,if_neg hz]

/-- The genuine weighted gcd term equals the finite-field root indicator, including the zero residue. -/
lemma lpsQuadraticEisensteinCuspGcd_weighted_of_dvd (q : ℕ) [Fact q.Prime]
    (γ : SL(2,ℤ)) (D : ℤ) (hC : γ 1 0=(q:ℤ)*D) (r : Fin q) :
    lpsQuadraticE2Character q (r.val:ZMod q)*
      ((Int.gcd ((q:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0) ((q:ℤ)*γ 1 0):ℂ)^2/(q:ℂ)^2)=
      lpsQuadraticE2Character q (r.val:ZMod q)*
        (if (γ 0 0:ZMod q)+(r.val:ZMod q)*(D:ZMod q)=0 then (q:ℂ)^2 else 1) := by
  by_cases hr : r=0
  · subst r
    simp only [Fin.val_zero,Nat.cast_zero,MulChar.map_zero,zero_mul]
  · rw [lpsQuadraticEisensteinCuspGcd_of_dvd q γ r hr D hC]
    have he : (((γ 0 0+(r.val:ℤ)*D):ℤ):ZMod q)=
        (γ 0 0:ZMod q)+(r.val:ZMod q)*(D:ZMod q) := by push_cast;rfl
    rw [he]
    have hq : (q:ℂ)≠0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
    split_ifs
    · simp only [Nat.cast_pow]
      field_simp
    · simp [hq]

/-- When the denominator has exactly one prime factor its full cusp limit is the actual root character. -/
lemma lpsQuadraticE2Twist_cusp_dvd_character_tendsto (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (γ : SL(2,ℤ)) (D : ℤ) (hC : γ 1 0=(q:ℤ)*D) (hD : (D:ZMod q)≠0) :
    Tendsto (lpsQuadraticE2Twist q ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 ((gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹ *
        ((q:ℂ)^2-1)*lpsQuadraticE2Character q (-(γ 0 0:ZMod q)/(D:ZMod q)))) := by
  have ht := lpsQuadraticE2Twist_cusp_gcd_tendsto q γ
  have hs := (ZMod.finEquiv q).sum_comp (fun r : ZMod q =>
    lpsQuadraticE2Character q r*(if (γ 0 0:ZMod q)+r*(D:ZMod q)=0 then (q:ℂ)^2 else 1))
  rw [lpsQuadraticEisensteinCusp_delta q hq2 _ _ hD] at hs
  change (∑ r : Fin q,lpsQuadraticE2Character q (ZMod.finEquiv q r)*
    (if (γ 0 0:ZMod q)+(ZMod.finEquiv q r)*(D:ZMod q)=0 then (q:ℂ)^2 else 1))=_ at hs
  simp only [←lpsFin_cast_finEquiv] at hs
  have he : (∑ r : Fin q,lpsQuadraticE2Character q (r.val:ZMod q)*
      ((Int.gcd ((q:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0) ((q:ℤ)*γ 1 0):ℂ)^2/(q:ℂ)^2))=
      ((q:ℂ)^2-1)*lpsQuadraticE2Character q (-(γ 0 0:ZMod q)/(D:ZMod q)) := by
    simp_rw [lpsQuadraticEisensteinCuspGcd_weighted_of_dvd q γ D hC]
    exact hs
  rw [he] at ht
  simpa only [mul_assoc] using ht

/-- Primitivity makes the numerator a prime-modulus unit when the prime divides the denominator. -/
lemma lpsSL2Z_firstColumn_unit_of_prime_dvd (q : ℕ) [Fact q.Prime]
    (γ : SL(2,ℤ)) (hC : (q:ℤ)∣γ 1 0) : (γ 0 0:ZMod q)≠0 := by
  intro hz
  have hA := (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 0 0) q).mp hz
  have hg := Int.dvd_gcd hA hC
  rw [lpsSL2Z_firstColumn_gcd_one] at hg
  exact (Fact.out : q.Prime).not_dvd_one hg

/-- A denominator divisible by the prime squared makes the actual twist cusp limit vanish. -/
lemma lpsQuadraticE2Twist_cusp_square_dvd_tendsto_zero (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (γ : SL(2,ℤ)) (D : ℤ) (hC : γ 1 0=(q:ℤ)*D) (hD : (D:ZMod q)=0) :
    Tendsto (lpsQuadraticE2Twist q ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty (𝓝 0) := by
  have hCd : (q:ℤ)∣γ 1 0 := ⟨D,hC⟩
  have hA := lpsSL2Z_firstColumn_unit_of_prime_dvd q γ hCd
  have ht := lpsQuadraticE2Twist_cusp_gcd_tendsto q γ
  have he : (∑ r : Fin q,lpsQuadraticE2Character q (r.val:ZMod q)*
      ((Int.gcd ((q:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0) ((q:ℤ)*γ 1 0):ℂ)^2/(q:ℂ)^2))=
      (∑ r : Fin q,lpsQuadraticE2Character q (r.val:ZMod q)) := by
    simp_rw [lpsQuadraticEisensteinCuspGcd_weighted_of_dvd q γ D hC]
    simp only [hD,mul_zero,add_zero,if_neg hA,mul_one]
  rw [he,lpsQuadraticE2Character_fin_sum_zero q hq2,mul_zero] at ht
  exact ht

/-- The complete signed character formula for the actual quadratic Eisenstein cusp constant. -/
noncomputable def lpsQuadraticEisensteinCuspConstant (q : ℕ) [Fact q.Prime]
    (γ : SL(2,ℤ)) : ℂ :=
  if (q:ℤ)∣γ 1 0 then
    if (q:ℤ)^2∣γ 1 0 then 0 else
      (gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹ *
        ((q:ℂ)^2-1)*lpsQuadraticE2Character q (-(γ 0 0:ZMod q)/((γ 1 0/(q:ℤ):ℤ):ZMod q))
  else 0

/-- The actual quadratic twist has its full-filter character limit at every integer cusp matrix. -/
lemma lpsQuadraticE2Twist_cusp_character_tendsto (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (γ : SL(2,ℤ)) :
    Tendsto (lpsQuadraticE2Twist q ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (lpsQuadraticEisensteinCuspConstant q γ)) := by
  unfold lpsQuadraticEisensteinCuspConstant
  by_cases hC : (q:ℤ)∣γ 1 0
  · rw [if_pos hC]
    let D : ℤ := γ 1 0/(q:ℤ)
    have hCD : γ 1 0=(q:ℤ)*D := (Int.mul_ediv_cancel_of_dvd hC).symm
    have hq : (q:ℤ)≠0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
    have hd : (q:ℤ)^2∣γ 1 0 ↔ (q:ℤ)∣D := by
      rw [hCD,pow_two,mul_dvd_mul_iff_left hq]
    by_cases h2 : (q:ℤ)^2∣γ 1 0
    · rw [if_pos h2]
      have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd D q).mpr (hd.mp h2)
      exact lpsQuadraticE2Twist_cusp_square_dvd_tendsto_zero q hq2 γ D hCD hz
    · rw [if_neg h2]
      have hn : (D:ZMod q)≠0 := by
        intro hz
        exact h2 (hd.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd D q).mp hz))
      exact lpsQuadraticE2Twist_cusp_dvd_character_tendsto q hq2 γ D hCD hn
  · rw [if_neg hC]
    exact lpsQuadraticE2Twist_cusp_not_dvd_tendsto_zero q hq2 γ hC

/-- A unit translation residue makes the gcd with the squared modulus divide the scaled denominator. -/
lemma lpsGcdSquare_dvd_column (N A C r : ℤ) (hr : Int.gcd r (N^2)=1) :
    (Int.gcd (N*A+r*C) (N^2):ℤ)∣N*C := by
  let d := Int.gcd (N*A+r*C) (N^2)
  have hx : (d:ℤ)∣N*A+r*C := Int.gcd_dvd_left _ _
  have hN : (d:ℤ)∣N^2 := Int.gcd_dvd_right _ _
  have hNd : d∣N.natAbs^2 := by
    simpa only [Int.natAbs_pow] using (Int.ofNat_dvd_left.mp hN)
  have hc0 : r.natAbs.Coprime (N.natAbs^2) := by
    simpa only [Int.gcd_def,Int.natAbs_pow] using hr
  have hc : Int.gcd (d:ℤ) r=1 := by
    simpa only [Int.gcd_def,Int.natAbs_natCast] using (hc0.coprime_dvd_right hNd).symm.gcd_eq_one
  have he : N*(N*A+r*C)-A*N^2=(N*C)*r := by ring
  have hh := dvd_sub (dvd_mul_of_dvd_right hx N) (dvd_mul_of_dvd_right hN A)
  rw [he] at hh
  exact Int.dvd_of_dvd_mul_left_of_gcd_one hh hc

/-- A coprime scale and the corresponding translated column preserve the gcd with the squared modulus. -/
lemma lpsGcdSquare_coprime_scale (N M A C r s : ℤ)
    (hM : Int.gcd M N=1) (hr : Int.gcd r N=1) :
    Int.gcd (M*N*A+(M*r+N*s)*C) (N^2)=Int.gcd (N*A+r*C) (N^2) := by
  have ht : Int.gcd (M*r+N*s) N=1 := by
    rw [Int.gcd_add_mul_left_left,Int.gcd_mul_right_left_of_gcd_eq_one hM,hr]
  have hMp := Int.gcd_pow_right_of_gcd_eq_one (k:=2) hM
  have hrp := Int.gcd_pow_right_of_gcd_eq_one (k:=2) hr
  have htp := Int.gcd_pow_right_of_gcd_eq_one (k:=2) ht
  have hyC := lpsGcdSquare_dvd_column N A C r hrp
  have hxC := lpsGcdSquare_dvd_column N (M*A) C (M*r+N*s) htp
  rw [show N*(M*A)=M*N*A by ring] at hxC
  have he : M*N*A+(M*r+N*s)*C=M*(N*A+r*C)+s*(N*C) := by ring
  apply Nat.dvd_antisymm
  · let d := Int.gcd (M*N*A+(M*r+N*s)*C) (N^2)
    have hx : (d:ℤ)∣M*N*A+(M*r+N*s)*C := Int.gcd_dvd_left _ _
    have hN : (d:ℤ)∣N^2 := Int.gcd_dvd_right _ _
    have hNd : d∣N.natAbs^2 := by
      simpa only [Int.natAbs_pow] using (Int.ofNat_dvd_left.mp hN)
    have hc0 : M.natAbs.Coprime (N.natAbs^2) := by
      simpa only [Int.gcd_def,Int.natAbs_pow] using hMp
    have hc : Int.gcd (d:ℤ) M=1 := by
      simpa only [Int.gcd_def,Int.natAbs_natCast] using (hc0.coprime_dvd_right hNd).symm.gcd_eq_one
    have hmul := dvd_sub hx (dvd_mul_of_dvd_right hxC s)
    rw [he,add_sub_cancel_right] at hmul
    exact Int.dvd_gcd (Int.dvd_of_dvd_mul_right_of_gcd_one hmul hc) hN
  · apply Int.dvd_gcd
    · rw [he]
      exact dvd_add (dvd_mul_of_dvd_right (Int.gcd_dvd_left _ _) M)
        (dvd_mul_of_dvd_right hyC s)
    · exact Int.gcd_dvd_right _ _

/-- The integer gcd factors over a product of two coprime moduli. -/
lemma lpsIntGcd_coprime_mul (x N M : ℤ) (hNM : Int.gcd N M=1) :
    Int.gcd x (N*M)=Int.gcd x N*Int.gcd x M := by
  have hc : N.natAbs.Coprime M.natAbs := hNM
  simpa only [Int.gcd_def,Int.natAbs_mul] using hc.gcd_mul x.natAbs

/-- The actual primitive-column cusp gcd factors over coprime moduli and their CRT translation residues. -/
lemma lpsEisensteinCuspGcd_coprime_product (N M : ℤ) (γ : SL(2,ℤ)) (r s : ℤ)
    (hNM : Int.gcd N M=1) (hr : Int.gcd r N=1) (hs : Int.gcd s M=1) :
    Int.gcd ((N*M)*γ 0 0+(M*r+N*s)*γ 1 0) ((N*M)*γ 1 0)=
      Int.gcd (N*γ 0 0+r*γ 1 0) (N*γ 1 0)*
        Int.gcd (M*γ 0 0+s*γ 1 0) (M*γ 1 0) := by
  have hMN : Int.gcd M N=1 := by rw [Int.gcd_comm];exact hNM
  have htN : Int.gcd (M*r+N*s) N=1 := by
    rw [Int.gcd_add_mul_left_left,Int.gcd_mul_right_left_of_gcd_eq_one hMN,hr]
  have htM : Int.gcd (M*r+N*s) M=1 := by
    rw [add_comm,Int.gcd_add_mul_left_left,Int.gcd_mul_right_left_of_gcd_eq_one hNM,hs]
  have htNM : Int.gcd (M*r+N*s) (N*M)=1 := by
    have hN : (M*r+N*s).natAbs.Coprime N.natAbs := htN
    have hM : (M*r+N*s).natAbs.Coprime M.natAbs := htM
    simpa only [Int.gcd_def,Int.natAbs_mul] using (hN.mul_right hM).gcd_eq_one
  have htp := Int.gcd_pow_right_of_gcd_eq_one (k:=2) htNM
  have hrp := Int.gcd_pow_right_of_gcd_eq_one (k:=2) hr
  have hsp := Int.gcd_pow_right_of_gcd_eq_one (k:=2) hs
  have htC : (M*r+N*s).natAbs.Coprime ((N*M).natAbs^2) := by
    simpa only [Int.gcd_def,Int.natAbs_pow] using htp
  have hrC : r.natAbs.Coprime (N.natAbs^2) := by
    simpa only [Int.gcd_def,Int.natAbs_pow] using hrp
  have hsC : s.natAbs.Coprime (M.natAbs^2) := by
    simpa only [Int.gcd_def,Int.natAbs_pow] using hsp
  rw [lpsEisensteinCuspGcd_unit_reduce (N*M) γ (M*r+N*s) htC,
    lpsEisensteinCuspGcd_unit_reduce N γ r hrC,lpsEisensteinCuspGcd_unit_reduce M γ s hsC,
    mul_pow,lpsIntGcd_coprime_mul _ _ _ (Int.pow_gcd_pow_of_gcd_eq_one hNM)]
  have heN := lpsGcdSquare_coprime_scale N M (γ 0 0) (γ 1 0) r s hMN hr
  have heM := lpsGcdSquare_coprime_scale M N (γ 0 0) (γ 1 0) s r hNM hs
  rw [show M*N*γ 0 0+(M*r+N*s)*γ 1 0=(N*M)*γ 0 0+(M*r+N*s)*γ 1 0 by ring] at heN
  rw [show N*M*γ 0 0+(N*s+M*r)*γ 1 0=(N*M)*γ 0 0+(M*r+N*s)*γ 1 0 by ring] at heM
  rw [heN,heM]

/-- The actual double-character cusp term factors into its two genuine single-character gcd terms. -/
lemma lpsChi4PrimeEisensteinCuspGcd_weighted (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (γ : SL(2,ℤ)) (r : Fin 4) (a : Fin q) :
    lpsChi4E2Character (r.val:ZMod 4)*lpsQuadraticE2Character q (a.val:ZMod q)*
      ((Int.gcd (((4*q:ℕ):ℤ)*γ 0 0+((q*r.val+4*a.val:ℕ):ℤ)*γ 1 0)
        (((4*q:ℕ):ℤ)*γ 1 0):ℂ)^2/((4*q:ℕ):ℂ)^2)=
      (lpsChi4E2Character (r.val:ZMod 4)*
        ((Int.gcd ((4:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0) ((4:ℤ)*γ 1 0):ℂ)^2/(4:ℂ)^2))*
      (lpsQuadraticE2Character q (a.val:ZMod q)*
        ((Int.gcd ((q:ℤ)*γ 0 0+(a.val:ℤ)*γ 1 0) ((q:ℤ)*γ 1 0):ℂ)^2/(q:ℂ)^2)) := by
  by_cases hr : IsUnit (r.val:ZMod 4)
  · by_cases ha : a=0
    · subst a
      simp only [Fin.val_zero,Nat.cast_zero,MulChar.map_zero,mul_zero,zero_mul]
    · have hrc := (ZMod.isUnit_iff_coprime r.val 4).mp hr
      have hrI : Int.gcd (r.val:ℤ) 4=1 := by
        change Nat.gcd r.val 4=1
        exact hrc.gcd_eq_one
      have hac := (lpsPrimeCuspShift_unit q a ha).coprime_dvd_right
        (dvd_pow_self q (by decide : (2:ℕ)≠0))
      have haI : Int.gcd (a.val:ℤ) (q:ℤ)=1 := by
        simpa only [Int.gcd_def,Int.natAbs_natCast] using hac.gcd_eq_one
      have hq4 := ((Fact.out : q.Prime).odd_of_ne_two hq2).coprime_two_right.pow_right 2
      have h4q : Int.gcd 4 (q:ℤ)=1 := by
        change Nat.gcd 4 q=1
        exact hq4.symm.gcd_eq_one
      have hg := lpsEisensteinCuspGcd_coprime_product 4 q γ r.val a.val h4q hrI haI
      have he : Int.gcd (((4*q:ℕ):ℤ)*γ 0 0+((q*r.val+4*a.val:ℕ):ℤ)*γ 1 0)
          (((4*q:ℕ):ℤ)*γ 1 0)=
          Int.gcd ((4:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0) ((4:ℤ)*γ 1 0)*
            Int.gcd ((q:ℤ)*γ 0 0+(a.val:ℤ)*γ 1 0) ((q:ℤ)*γ 1 0) := by
        simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hg
      rw [he]
      push_cast
      ring
  · rw [MulChar.map_nonunit lpsChi4E2Character hr]
    simp

/-- The full signed cusp limit of the iterated twist is the product of the two actual single-character constants. -/
lemma lpsChi4PrimeE2Twist_cusp_character_tendsto (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (γ : SL(2,ℤ)) :
    Tendsto (lpsChi4PrimeE2Twist q ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (lpsChi4EisensteinCuspConstant γ*lpsQuadraticEisensteinCuspConstant q γ)) := by
  have ht := lpsChi4PrimeE2Dilate_cusp_tendsto q 1 (by decide) γ
  simp only [lpsChi4PrimeE2Dilate_one,Nat.cast_one,mul_one,one_pow] at ht
  have he4 := tendsto_nhds_unique (lpsChi4E2Twist_cusp_gcd_tendsto γ)
    (lpsChi4E2Twist_cusp_character_tendsto γ)
  have heq := tendsto_nhds_unique (lpsQuadraticE2Twist_cusp_gcd_tendsto q γ)
    (lpsQuadraticE2Twist_cusp_character_tendsto q hq2 γ)
  let v4 (r : Fin 4) : ℂ := lpsChi4E2Character (r.val:ZMod 4)*
    ((Int.gcd ((4:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0) ((4:ℤ)*γ 1 0):ℂ)^2/(4:ℂ)^2)
  let vq (a : Fin q) : ℂ := lpsQuadraticE2Character q (a.val:ZMod q)*
    ((Int.gcd ((q:ℤ)*γ 0 0+(a.val:ℤ)*γ 1 0) ((q:ℤ)*γ 1 0):ℂ)^2/(q:ℂ)^2)
  let vk (r : Fin 4) (a : Fin q) : ℂ := lpsChi4E2Character (r.val:ZMod 4)*
    lpsQuadraticE2Character q (a.val:ZMod q)*
    ((Int.gcd (((4*q:ℕ):ℤ)*γ 0 0+((q*r.val+4*a.val:ℕ):ℤ)*γ 1 0)
      (((4*q:ℕ):ℤ)*γ 1 0):ℂ)^2/((4*q:ℕ):ℂ)^2)
  have hv (r : Fin 4) (a : Fin q) : vk r a=v4 r*vq a :=
    lpsChi4PrimeEisensteinCuspGcd_weighted q hq2 γ r a
  have hs : (∑ r : Fin 4,∑ a : Fin q,vk r a)=
      (∑ r : Fin 4,v4 r)*(∑ a : Fin q,vq a) := by
    simp_rw [hv,←Finset.mul_sum]
    rw [Finset.sum_mul]
  have hf : (gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹ *
      (∑ r : Fin 4,lpsChi4E2Character (r.val:ZMod 4)*
        ((gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹ *
          ∑ a : Fin q,lpsQuadraticE2Character q (a.val:ZMod q)*
            ((Int.gcd (((4*q:ℕ):ℤ)*γ 0 0+((q*r.val+4*a.val:ℕ):ℤ)*γ 1 0)
              (((4*q:ℕ):ℤ)*γ 1 0):ℂ)^2/((4*q:ℕ):ℂ)^2)))=
      ((gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹ *
        (gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹)*
        (∑ r : Fin 4,∑ a : Fin q,vk r a) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro a ha
    dsimp only [vk]
    ring
  have he : ((gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹ *
      (gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹)*
      (∑ r : Fin 4,∑ a : Fin q,vk r a)=
      lpsChi4EisensteinCuspConstant γ*lpsQuadraticEisensteinCuspConstant q γ := by
    rw [hs,show ((gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹ *
        (gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹)*
        ((∑ r : Fin 4,v4 r)*(∑ a : Fin q,vq a))=
        ((gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹*(∑ r : Fin 4,v4 r))*
          ((gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹*(∑ a : Fin q,vq a)) by ring]
    exact congrArg₂ (·*·) he4 heq
  rw [hf,he] at ht
  exact ht

/-- The actual modulus-four character takes value one on the square of every unit. -/
lemma lpsChi4E2Character_square (d : ZMod 4) (hd : IsUnit d) :
    lpsChi4E2Character (d^2)=1 := by
  have hq := ZMod.isQuadratic_χ₄.comp (Int.castRingHom ℂ)
  have h : lpsChi4E2Character^2=1 := hq.sq_eq_one
  rw [map_pow,←MulChar.pow_apply' lpsChi4E2Character (by norm_num : (2:ℕ)≠0),h,
    MulChar.one_apply hd]

end QEC.Coding.TannerLiftedProduct
