import QEC.Coding.ExpanderCodes.LPSThetaEisensteinCusps

/-!
# Universal arithmetic matching of theta and correction cusp constants

The genuine mixed Gauss product splits through CRT at the two-primary,
residue-prime and coprime factors. Primitive matrix columns give units, and
complete local evaluations match the correction at every positive denominator.
These identities are consumed by the actual cuspidal remainder construction.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

/-- Extract the two-primary and residue-prime powers with a coprime positive cofactor. -/
lemma lpsThetaCuspModulus_decomposition (q N : ℕ) [Fact q.Prime] (hN : 0<N) :
    ∃ t v L : ℕ,0<L ∧ L.Coprime (2*q) ∧ N=2^t*q^v*L := by
  obtain ⟨t,n,hn2,heN⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' 2 (by decide)
  have hn : n≠0 := by intro h;rw [h,mul_zero] at heN;exact hN.ne' heN
  obtain ⟨v,L,hLq,hen⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn q (Fact.out : q.Prime).ne_one
  have hL : 0<L := by
    apply Nat.pos_of_ne_zero
    intro h
    rw [h,mul_zero] at hen
    exact hn hen
  have hL2 : ¬2∣L := by
    intro h
    apply hn2
    rw [hen]
    exact dvd_mul_of_dvd_right h _
  have hc2 := (Nat.prime_two.coprime_iff_not_dvd.mpr hL2).symm
  have hcq := ((Fact.out : q.Prime).coprime_iff_not_dvd.mpr hLq).symm
  refine ⟨t,v,L,hL,hc2.mul_right hcq,?_⟩
  rw [heN,hen]
  ring

/-- Apply genuine CRT twice and normalize the coprime odd cofactor. -/
lemma lpsThetaCuspGaussProduct_split (q t v L : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (hL : 0<L) (hcL : L.Coprime (2*q)) (a : ℤ)
    (ha : IsUnit (a:ZMod (2^t*q^v*L))) :
    lpsThetaCuspGaussProduct q a (2^t*q^v*L)=
      (L:ℂ)^2*lpsThetaCuspGaussProduct q (a*((q^v*L:ℕ):ℤ)) (2^t)*
        lpsThetaCuspGaussProduct q (a*((2^t*L:ℕ):ℤ)) (q^v) := by
  have hqpos : 0<q := (Fact.out : q.Prime).pos
  let : NeZero L := ⟨hL.ne'⟩
  let : NeZero (2^t*q^v*L) := ⟨by positivity⟩
  let : NeZero (q^v*L) := ⟨by positivity⟩
  have hL2 : L.Coprime 2 := hcL.coprime_dvd_right (dvd_mul_right _ _)
  have hLq : L.Coprime q := hcL.coprime_dvd_right (dvd_mul_left _ _)
  have h2q := ((Fact.out : q.Prime).odd_of_ne_two hq2).coprime_two_left
  have h2rest : (2^t).Coprime (q^v*L) :=
    ((h2q.pow_right v).mul_right hL2.symm).pow_left t
  have hqL : (q^v).Coprime L := hLq.symm.pow_left v
  have hcofactor : (2^t*q^v).Coprime L := (hL2.symm.pow_left t).mul_left hqL
  have haL := lpsZMod_unit_descend (2^t*q^v*L) L (dvd_mul_left _ _) a ha
  have hau : IsUnit (((a*((2^t*q^v:ℕ):ℤ)):ℤ):ZMod L) := by
    simpa only [Int.cast_mul,Int.cast_natCast] using
      haL.mul ((ZMod.isUnit_iff_coprime (2^t*q^v) L).mpr hcofactor)
  have h2qu : IsUnit ((2*q:ℕ):ZMod L) := (ZMod.isUnit_iff_coprime (2*q) L).mpr hcL.symm
  have hodd : Odd L := hL2.odd_of_right
  rw [show 2^t*q^v*L=2^t*(q^v*L) by ring,
    lpsThetaCuspGaussProduct_coprime_mul q (2^t) (q^v*L) h2rest a,
    lpsThetaCuspGaussProduct_coprime_mul q (q^v) L hqL (a*((2^t:ℕ):ℤ))]
  have heL : (a*((2^t:ℕ):ℤ))*((q^v:ℕ):ℤ)=a*((2^t*q^v:ℕ):ℤ) := by push_cast;ring
  have heq : (a*((2^t:ℕ):ℤ))*(L:ℤ)=a*((2^t*L:ℕ):ℤ) := by push_cast;ring
  rw [heL,heq,lpsThetaCuspGaussProduct_odd_unit q L hodd _ hau h2qu]
  ring

/-- Quadratic inversion and the proved value at minus one remove the cusp quotient. -/
lemma lpsQuadraticE2Character_neg_div (q : ℕ) [Fact q.Prime] (hq4 : q%4=1)
    (A D : ZMod q) : lpsQuadraticE2Character q (-A/D)=lpsQuadraticE2Character q (A*D) := by
  have hχ : (lpsQuadraticE2Character q).IsQuadratic :=
    (quadraticChar_isQuadratic (ZMod q)).comp (Int.castRingHom ℂ)
  rw [div_eq_mul_inv,neg_eq_neg_one_mul,map_mul,map_mul,
    lpsQuadraticE2Character_neg_one q hq4,one_mul,←MulChar.inv_apply',hχ.inv,map_mul]

/-- Comparable powers have exactly the smaller power as their gcd. -/
lemma lpsNatGcd_same_base_powers (p a t : ℕ) : Nat.gcd (p^a) (p^t)=p^(min a t) := by
  rcases le_total a t with h | h
  · rw [min_eq_left h]
    exact Nat.gcd_eq_left_iff_dvd.mpr (pow_dvd_pow p h)
  · rw [min_eq_right h]
    exact Nat.gcd_eq_right_iff_dvd.mpr (pow_dvd_pow p h)

/-- A coprime cofactor leaves the exact minimum-exponent cusp gcd. -/
lemma lpsPrimePowerCuspGcd (p a t L : ℕ) (hc : p.Coprime L) :
    Int.gcd ((p^a:ℕ):ℤ) ((p^t*L:ℕ):ℤ)=p^(min a t) := by
  simp only [Int.gcd_def,Int.natAbs_natCast]
  rw [(hc.pow_left t).gcd_mul (p^a),(hc.pow_left a).gcd_eq_one,mul_one,
    lpsNatGcd_same_base_powers]

/-- Evaluate the complete two-power gcd vector in all denominator valuation cases. -/
lemma lpsThetaEisensteinTwoCuspFactor_of_column (t L : ℕ) (hL : Odd L)
    (γ : SL(2,ℤ)) (hC : γ 1 0=((2^t*L:ℕ):ℤ)) :
    lpsThetaEisensteinTwoCuspFactor γ=
      if t=0 then 3/4 else if t=1 then 0 else if t=2 then 6 else if t=3 then 0 else -24 := by
  unfold lpsThetaEisensteinTwoCuspFactor
  simp_rw [hC,lpsPrimePowerCuspGcd 2 _ t L hL.coprime_two_left]
  by_cases h0 : t=0
  · subst t
    norm_num [lpsThetaEisensteinTwoWeight,Fin.sum_univ_succ]
  · rw [if_neg h0]
    by_cases h1 : t=1
    · subst t
      norm_num [lpsThetaEisensteinTwoWeight,Fin.sum_univ_succ]
    · rw [if_neg h1]
      by_cases h2 : t=2
      · subst t
        norm_num [lpsThetaEisensteinTwoWeight,Fin.sum_univ_succ]
      · rw [if_neg h2]
        by_cases h3 : t=3
        · subst t
          norm_num [lpsThetaEisensteinTwoWeight,Fin.sum_univ_succ]
        · rw [if_neg h3]
          have ht : 4≤t := by omega
          have hm (a : Fin 5) : min a.val t=a.val := min_eq_left (by omega)
          simp_rw [hm]
          norm_num [lpsThetaEisensteinTwoWeight,Fin.sum_univ_succ]

/-- Evaluate the complete residue-prime gcd vector at every valuation. -/
lemma lpsThetaEisensteinPrimeCuspFactor_of_column (q v L : ℕ) [Fact q.Prime]
    (hc : q.Coprime L) (γ : SL(2,ℤ)) (hC : γ 1 0=((q^v*L:ℕ):ℤ)) :
    lpsThetaEisensteinPrimeCuspFactor q γ=
      if v=0 then ((q:ℂ)^2-1)/(q:ℂ)^2 else if v=1 then 0 else (q:ℂ)*((q:ℂ)^2-1) := by
  unfold lpsThetaEisensteinPrimeCuspFactor
  simp_rw [hC,lpsPrimePowerCuspGcd q _ v L hc]
  have hq : (q:ℂ)≠0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  by_cases h0 : v=0
  · subst v
    norm_num [lpsThetaEisensteinPrimeWeight,Fin.sum_univ_succ]
    field_simp [hq]
    ring
  · rw [if_neg h0]
    by_cases h1 : v=1
    · subst v
      norm_num [lpsThetaEisensteinPrimeWeight,Fin.sum_univ_succ]
      field_simp [hq]
      ring
    · rw [if_neg h1]
      have hv : 2≤v := by omega
      have hm (b : Fin 3) : min b.val v=b.val := min_eq_left (by omega)
      simp_rw [hm]
      norm_num [lpsThetaEisensteinPrimeWeight,Fin.sum_univ_succ]
      field_simp [hq]
      ring

/-- Denominator prime-power divisibility is exactly the exponent comparison. -/
lemma lpsPrimePowerCusp_denominator_dvd (p e t L : ℕ) (hp : p.Prime) (hc : p.Coprime L) :
    (p:ℤ)^e∣((p^t*L:ℕ):ℤ) ↔ e≤t := by
  rw [←Nat.cast_pow,Int.ofNat_dvd]
  constructor
  · intro h
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp ((hc.pow_left e).dvd_of_dvd_mul_right h)
  · intro h
    exact (pow_dvd_pow p h).trans (dvd_mul_right _ _)

/-- Only two-adic valuation two supports the genuine modulus-four character constant. -/
lemma lpsChi4EisensteinCuspConstant_of_column (t L : ℕ) (hL : Odd L)
    (γ : SL(2,ℤ)) (hC : γ 1 0=((2^t*L:ℕ):ℤ)) :
    lpsChi4EisensteinCuspConstant γ=
      if t=2 then 3*gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4))*
        lpsChi4E2Character (((γ 0 0*(L:ℤ)):ℤ):ZMod 4) else 0 := by
  have h4 := lpsPrimePowerCusp_denominator_dvd 2 2 t L Nat.prime_two hL.coprime_two_left
  have h8 := lpsPrimePowerCusp_denominator_dvd 2 3 t L Nat.prime_two hL.coprime_two_left
  norm_num only [Int.reducePow] at h4 h8
  have hs : γ 1 0%8=4 ↔ t=2 := by
    rw [lpsInt_mod_eight_four_iff,hC,h4,h8]
    omega
  unfold lpsChi4EisensteinCuspConstant
  by_cases ht : t=2
  · subst t
    have hdiv : γ 1 0/4=(L:ℤ) := by rw [hC];norm_num
    rw [if_pos (hs.mpr rfl),if_pos rfl,hdiv]
  · rw [if_neg (fun h => ht (hs.mp h)),if_neg ht]

/-- Only residue-prime valuation one supports the genuine quadratic character constant. -/
lemma lpsQuadraticEisensteinCuspConstant_of_column (q v L : ℕ) [Fact q.Prime]
    (hq4 : q%4=1) (hc : q.Coprime L) (γ : SL(2,ℤ)) (hC : γ 1 0=((q^v*L:ℕ):ℤ)) :
    lpsQuadraticEisensteinCuspConstant q γ=
      if v=1 then ((q:ℂ)^2-1)/gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q))*
        lpsQuadraticE2Character q (((γ 0 0*(L:ℤ)):ℤ):ZMod q) else 0 := by
  have h1 := lpsPrimePowerCusp_denominator_dvd q 1 v L (Fact.out : q.Prime) hc
  have h2 := lpsPrimePowerCusp_denominator_dvd q 2 v L (Fact.out : q.Prime) hc
  simp only [pow_one] at h1
  have h1C : (q:ℤ)∣γ 1 0 ↔ 1≤v := by simpa only [hC] using h1
  have h2C : (q:ℤ)^2∣γ 1 0 ↔ 2≤v := by simpa only [hC] using h2
  unfold lpsQuadraticEisensteinCuspConstant
  simp_rw [h1C,h2C]
  by_cases hv : v=1
  · subst v
    have hdiv : γ 1 0/(q:ℤ)=(L:ℤ) := by
      rw [hC,pow_one,Nat.cast_mul]
      exact Int.mul_ediv_cancel_left _ (by exact_mod_cast (Fact.out : q.Prime).ne_zero)
    rw [if_pos (by omega),if_neg (by omega),if_pos rfl,hdiv,
      lpsQuadraticE2Character_neg_div q hq4]
    push_cast
    ring
  · rw [if_neg hv]
    by_cases hv0 : v=0
    · subst v
      rw [if_neg (by omega)]
    · have hv2 : 2≤v := by omega
      rw [if_pos (by omega),if_pos hv2]

/-- The actual two-primary Gauss factor equals the full gcd-character cusp factor. -/
lemma lpsThetaCuspGaussProduct_two_factor (q t L : ℕ) (hq : Odd q) (hL : Odd L)
    (γ : SL(2,ℤ)) (hC : γ 1 0=((2^t*L:ℕ):ℤ))
    (ha : IsUnit ((γ 0 0 * (L : ℤ) : ℤ) : ZMod (2 ^ t))) :
    lpsThetaCuspGaussProduct q (γ 0 0*(L:ℤ)) (2^t)=
      (4/3:ℂ)*((2^t:ℕ):ℂ)^2*
        (lpsThetaEisensteinTwoCuspFactor γ+lpsChi4EisensteinCuspConstant γ) := by
  rw [lpsThetaEisensteinTwoCuspFactor_of_column t L hL γ hC,
    lpsChi4EisensteinCuspConstant_of_column t L hL γ hC]
  by_cases h0 : t=0
  · subst t
    rw [pow_zero,lpsThetaCuspGaussProduct_one]
    norm_num
  · rw [if_neg h0]
    by_cases h1 : t=1
    · subst t
      norm_num only [Nat.reducePow] at ha ⊢
      rw [lpsThetaCuspGaussProduct_two q _ ha]
      norm_num
    · rw [if_neg h1]
      by_cases h2 : t=2
      · subst t
        norm_num only [Nat.reducePow] at ha ⊢
        rw [lpsThetaCuspGaussProduct_four_character q _ ha]
        norm_num
        ring
      · rw [if_neg h2,if_neg h2]
        by_cases h3 : t=3
        · subst t
          norm_num only [Nat.reducePow] at ha ⊢
          rw [lpsThetaCuspGaussProduct_eight q hq _ ha]
          norm_num
        · rw [if_neg h3]
          have ht : 4≤t := by omega
          obtain ⟨e,he⟩ := Nat.exists_eq_add_of_le ht
          have he' : t=e+4 := by omega
          rw [he'] at ha ⊢
          rw [lpsThetaCuspGaussProduct_two_pow_ge_four q hq e _ ha]
          ring

/-- The actual residue-prime Gauss factor equals the full gcd-character cusp factor. -/
lemma lpsThetaCuspGaussProduct_prime_factor (q v L : ℕ) [Fact q.Prime]
    (hq4 : q%4=1) (hc : q.Coprime L) (γ : SL(2,ℤ)) (hC : γ 1 0=((q^v*L:ℕ):ℤ))
    (ha : IsUnit ((γ 0 0 * (L : ℤ) : ℤ) : ZMod (q ^ v))) :
    lpsThetaCuspGaussProduct q (γ 0 0*(L:ℤ)) (q^v)=
      (q:ℂ)^2/((q:ℂ)^2-1)*((q^v:ℕ):ℂ)^2*
        (lpsThetaEisensteinPrimeCuspFactor q γ+lpsQuadraticEisensteinCuspConstant q γ) := by
  have hq2 : q≠2 := by intro h;subst q;norm_num at hq4
  have hq : (q:ℂ)≠0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hqs : (q:ℂ)^2-1≠0 := by
    have hr : (1:ℝ)<(q:ℝ) := by exact_mod_cast (Fact.out : q.Prime).one_lt
    have hs : (q:ℝ)^2-1≠0 := by nlinarith
    exact_mod_cast hs
  have hG := lpsQuadraticE2Gauss_ne_zero q hq2
  rw [lpsThetaEisensteinPrimeCuspFactor_of_column q v L hc γ hC,
    lpsQuadraticEisensteinCuspConstant_of_column q v L hq4 hc γ hC]
  by_cases h0 : v=0
  · subst v
    rw [pow_zero,lpsThetaCuspGaussProduct_one]
    norm_num
    field_simp
  · rw [if_neg h0]
    by_cases h1 : v=1
    · subst v
      have ha' : IsUnit ((γ 0 0 * (L : ℤ) : ℤ) : ZMod q) :=
        Eq.mp (congrArg (fun N => IsUnit ((γ 0 0 * (L : ℤ) : ℤ) : ZMod N)) (pow_one q)) ha
      simp only [pow_one]
      have hn : ((((γ 0 0*(L:ℤ)):ℤ):ZMod q))≠0 := isUnit_iff_ne_zero.mp ha'
      rw [lpsThetaCuspGaussProduct_prime q hq2 _ hn]
      norm_num
      have hs := lpsQuadraticE2Gauss_sq q hq4
      field_simp [hqs,hG]
      rw [hs]
      ring
    · rw [if_neg h1,if_neg h1]
      have hv : 2≤v := by omega
      obtain ⟨e,he⟩ := Nat.exists_eq_add_of_le hv
      have he' : v=e+2 := by omega
      rw [he'] at ha ⊢
      rw [lpsThetaCuspGaussProduct_prime_pow_ge_two q hq2 e _ ha]
      field_simp [hqs]
      ring

/-- Determinant one provides an explicit inverse for the numerator modulo the denominator. -/
lemma lpsSL2Z_firstColumn_unit_modulus (N : ℕ) (γ : SL(2,ℤ))
    (hC : γ 1 0=(N:ℤ)) : IsUnit ((γ 0 0:ℤ):ZMod N) := by
  have hd : γ 0 0*γ 1 1-γ 0 1*γ 1 0=1 := by
    simpa only [Matrix.det_fin_two] using γ.property
  have hcast := congrArg (fun x : ℤ => (x:ZMod N)) hd
  have hN : (N:ZMod N)=0 := ZMod.natCast_self N
  rw [hC] at hcast
  push_cast at hcast
  simp only [hN,mul_zero,sub_zero] at hcast
  exact ⟨⟨_,_,hcast,by rw [mul_comm];exact hcast⟩,rfl⟩

/-- The genuine Gauss product matches both correction factors at every positive denominator. -/
lemma lpsThetaCuspGaussProduct_all_factors (q N : ℕ) [Fact q.Prime]
    (hq4 : q%4=1) (hN : 0<N) (γ : SL(2,ℤ)) (hC : γ 1 0=(N:ℤ)) :
    lpsThetaCuspGaussProduct q (γ 0 0) N=
      (4/3:ℂ)*(q:ℂ)^2/((q:ℂ)^2-1)*(N:ℂ)^2*
        (lpsThetaEisensteinTwoCuspFactor γ+lpsChi4EisensteinCuspConstant γ)*
        (lpsThetaEisensteinPrimeCuspFactor q γ+lpsQuadraticEisensteinCuspConstant q γ) := by
  have hq2 : q≠2 := by intro h;subst q;norm_num at hq4
  have hqodd := (Fact.out : q.Prime).odd_of_ne_two hq2
  let : NeZero N := ⟨hN.ne'⟩
  have ha := lpsSL2Z_firstColumn_unit_modulus N γ hC
  obtain ⟨t,v,L,hL,hcL,heN⟩ := lpsThetaCuspModulus_decomposition q N hN
  have hL2 : L.Coprime 2 := hcL.coprime_dvd_right (dvd_mul_right _ _)
  have hLq : L.Coprime q := hcL.coprime_dvd_right (dvd_mul_left _ _)
  have h2q : (2:ℕ).Coprime q := hqodd.coprime_two_left
  have hrest2 : Odd (q^v*L) := (hqodd.pow (n:=v)).mul hL2.odd_of_right
  have hrestq : q.Coprime (2^t*L) := (h2q.symm.pow_right t).mul_right hLq.symm
  have hu2 := lpsZMod_unit_descend N (2^t)
    (by rw [heN];exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _) (γ 0 0) ha
  have huq := lpsZMod_unit_descend N (q^v)
    (by rw [heN];exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _) (γ 0 0) ha
  have ha2 : IsUnit ((γ 0 0*((q^v*L:ℕ):ℤ):ℤ):ZMod (2^t)) := by
    have hc : (q^v*L).Coprime (2^t) :=
      ((h2q.symm.pow_left v).mul_left hL2).pow_right t
    simpa only [Int.cast_mul,Int.cast_natCast] using
      hu2.mul ((ZMod.isUnit_iff_coprime (q^v*L) (2^t)).mpr hc)
  have haq : IsUnit ((γ 0 0*((2^t*L:ℕ):ℤ):ℤ):ZMod (q^v)) := by
    simpa only [Int.cast_mul,Int.cast_natCast] using
      huq.mul ((ZMod.isUnit_iff_coprime (2^t*L) (q^v)).mpr (hrestq.symm.pow_right v))
  have hC2 : γ 1 0=((2^t*(q^v*L):ℕ):ℤ) := by rw [hC,heN,mul_assoc]
  have hCq : γ 1 0=((q^v*(2^t*L):ℕ):ℤ) := by rw [hC,heN];push_cast;ring
  rw [heN] at ha ⊢
  rw [lpsThetaCuspGaussProduct_split q t v L hq2 hL hcL _ ha,
    lpsThetaCuspGaussProduct_two_factor q t (q^v*L) hqodd hrest2 γ hC2 ha2,
    lpsThetaCuspGaussProduct_prime_factor q v (2^t*L) hq4 hrestq γ hCq haq]
  push_cast
  ring

/-- Normalize the full Gauss product to exactly the true Eisenstein correction constant. -/
lemma lpsThetaCuspGaussProduct_normalized (q N : ℕ) [Fact q.Prime]
    (hq4 : q%4=1) (hN : 0<N) (γ : SL(2,ℤ)) (hC : γ 1 0=(N:ℤ)) :
    -(32*(q:ℂ)^3*(N:ℂ)^2)⁻¹*lpsThetaCuspGaussProduct q (γ 0 0) N=
      -lpsThetaEisensteinNormalization q*
        (lpsThetaEisensteinTwoCuspFactor γ+lpsChi4EisensteinCuspConstant γ)*
        (lpsThetaEisensteinPrimeCuspFactor q γ+lpsQuadraticEisensteinCuspConstant q γ) := by
  have hq : (q:ℂ)≠0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hn : (N:ℂ)≠0 := by exact_mod_cast hN.ne'
  have hqs : (q:ℂ)^2-1≠0 := by
    have hr : (1:ℝ)<(q:ℝ) := by exact_mod_cast (Fact.out : q.Prime).one_lt
    have hs : (q:ℝ)^2-1≠0 := by nlinarith
    exact_mod_cast hs
  rw [lpsThetaCuspGaussProduct_all_factors q N hq4 hN γ hC]
  unfold lpsThetaEisensteinNormalization
  field_simp [hq,hn,hqs]
  ring

end QEC.Coding.TannerLiftedProduct
