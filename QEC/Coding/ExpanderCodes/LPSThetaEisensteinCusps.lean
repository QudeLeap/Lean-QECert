import QEC.Coding.ExpanderCodes.LPSThetaEisensteinCorrection
import QEC.Coding.ExpanderCodes.LPSThetaCuspLocalFactors

/-!
# The complete cusp vector of the actual theta Eisenstein correction

The genuine common-level basis limits, coprime gcd factorization and exact
character multipliers compute the weighted correction at every integer cusp
matrix. Its full-filter constant is minus the correction normalization times
(U2 + F4 constant) times (Uq + Fq constant). Negative and zero denominators are
included in this universal formula.

The theta Gauss-product comparison and resulting CuspForm must still be
proved; this module does not assert their completion or coefficient growth.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

/-- The actual finite two-power gcd factor in the correction cusp constant. -/
noncomputable def lpsThetaEisensteinTwoCuspFactor (γ : SL(2,ℤ)) : ℂ :=
  ∑ a : Fin 5,lpsThetaEisensteinTwoWeight a*
    (Int.gcd ((2^a.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((2^a.val:ℕ):ℂ)
/-- The actual finite residue-prime-power gcd factor in the correction cusp constant. -/
noncomputable def lpsThetaEisensteinPrimeCuspFactor (q : ℕ) (γ : SL(2,ℤ)) : ℂ :=
  ∑ b : Fin 3,lpsThetaEisensteinPrimeWeight q b*
    (Int.gcd ((q^b.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((q^b.val:ℕ):ℂ)

/-- The actual two-power weights have zero total, cancelling the untwisted constant contribution. -/
lemma lpsThetaEisensteinTwoWeight_sum : (∑ a : Fin 5,lpsThetaEisensteinTwoWeight a)=0 := by
  norm_num [lpsThetaEisensteinTwoWeight,Fin.sum_univ_succ]

/-- Every power of a residue prime congruent to one modulo four has modulus-four character one. -/
lemma lpsChi4E2Character_prime_pow (q : ℕ) (hq4 : q%4=1) (b : ℕ) :
    lpsChi4E2Character ((q^b:ℕ):ZMod 4)=1 := by
  have hq : (q:ZMod 4)=1 := by
    have h := (ZMod.natCast_eq_natCast_iff' q 1 4).mpr (by simpa using hq4)
    simpa only [Nat.cast_one] using h
  rw [Nat.cast_pow,map_pow,hq,lpsChi4E2Character_values.2.1,one_pow]

/-- The actual denominator gcd factors over coprime powers of two and the residue prime. -/
lemma lpsEisensteinCuspGcd_two_prime_product (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (a b : ℕ) (γ : SL(2,ℤ)) :
    Int.gcd ((2^a*q^b:ℕ):ℤ) (γ 1 0)=
      Int.gcd ((2^a:ℕ):ℤ) (γ 1 0)*Int.gcd ((q^b:ℕ):ℤ) (γ 1 0) := by
  have hc := ((Fact.out : q.Prime).odd_of_ne_two hq2).coprime_two_left.pow a b
  have hI : Int.gcd ((2^a:ℕ):ℤ) ((q^b:ℕ):ℤ)=1 := by
    simpa only [Int.gcd_def,Int.natAbs_natCast] using hc.gcd_eq_one
  rw [Nat.cast_mul,Int.gcd_comm,lpsIntGcd_coprime_mul _ _ _ hI]
  rw [Int.gcd_comm (γ 1 0),Int.gcd_comm (γ 1 0)]

/-- The complete untwisted weighted cusp vector is minus the product of the two true gcd factors. -/
lemma lpsThetaEisenstein_untwisted_cusp_sum (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (γ : SL(2,ℤ)) :
    (∑ a : Fin 5,∑ b : Fin 3,
      (lpsThetaEisensteinTwoWeight a*lpsThetaEisensteinPrimeWeight q b)*
        (1-(Int.gcd ((2^a.val*q^b.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((2^a.val*q^b.val:ℕ):ℂ)))=
      -lpsThetaEisensteinTwoCuspFactor γ*lpsThetaEisensteinPrimeCuspFactor q γ := by
  have he (a : Fin 5) (b : Fin 3) :
      (lpsThetaEisensteinTwoWeight a*lpsThetaEisensteinPrimeWeight q b)*
        (1-(Int.gcd ((2^a.val*q^b.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((2^a.val*q^b.val:ℕ):ℂ))=
      lpsThetaEisensteinTwoWeight a*lpsThetaEisensteinPrimeWeight q b-
        (lpsThetaEisensteinTwoWeight a*(Int.gcd ((2^a.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((2^a.val:ℕ):ℂ))*
          (lpsThetaEisensteinPrimeWeight q b*(Int.gcd ((q^b.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((q^b.val:ℕ):ℂ)) := by
    rw [lpsEisensteinCuspGcd_two_prime_product q hq2]
    simp only [Nat.cast_mul]
    ring
  simp_rw [he,Finset.sum_sub_distrib]
  simp only [←Finset.mul_sum,←Finset.sum_mul,lpsThetaEisensteinTwoWeight_sum,
    zero_mul,zero_sub,lpsThetaEisensteinTwoCuspFactor,lpsThetaEisensteinPrimeCuspFactor,neg_mul]

/-- The genuine character-four weights and dilation factors reproduce the negative prime-power weights. -/
lemma lpsThetaEisensteinChi4Weight_scaled (q : ℕ) [Fact q.Prime] (b : Fin 3) :
    lpsThetaEisensteinChi4Weight q b/((q^b.val:ℕ):ℂ)^2=
      -lpsThetaEisensteinPrimeWeight q b/((q^b.val:ℕ):ℂ) := by
  have hq : (q:ℂ)≠0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  fin_cases b <;> norm_num [lpsThetaEisensteinChi4Weight,lpsThetaEisensteinPrimeWeight]
  all_goals field_simp [hq]
  all_goals ring

/-- The genuine quadratic weights and character multipliers reproduce the negative two-power weights. -/
lemma lpsThetaEisensteinQuadraticWeight_scaled (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (a : Fin 5) :
    lpsThetaEisensteinQuadraticWeight q a*lpsQuadraticE2Character q ((2^a.val:ℕ):ZMod q)/
      ((2^a.val:ℕ):ℂ)^2= -lpsThetaEisensteinTwoWeight a/((2^a.val:ℕ):ℂ) := by
  have hn : (2:ZMod q)≠0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff 2 q).mp hz
    exact hq2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) Nat.prime_two).mp hd)
  have hs : (lpsQuadraticE2Character q (2:ZMod q))^2=1 := by
    simpa only [map_pow] using lpsQuadraticE2Character_square q (2:ZMod q) hn
  have h4 : (lpsQuadraticE2Character q (2:ZMod q))^4=1 := by
    rw [show (4:ℕ)=2*2 by decide,pow_mul,hs,one_pow]
  have h16 : (lpsQuadraticE2Character q (2:ZMod q))^16=1 := by
    rw [show (16:ℕ)=2*8 by decide,pow_mul,hs,one_pow]
  rw [Nat.cast_pow,map_pow]
  fin_cases a <;> norm_num [lpsThetaEisensteinQuadraticWeight,lpsThetaEisensteinTwoWeight,hs,h4,h16]
  all_goals linear_combination 3*hs

/-- The complete modulus-four dilation coefficients sum to the negative prime-power gcd factor. -/
lemma lpsThetaEisenstein_chi4_cusp_sum (q : ℕ) [Fact q.Prime] (γ : SL(2,ℤ)) :
    (∑ b : Fin 3,lpsThetaEisensteinChi4Weight q b*
      ((Int.gcd ((q^b.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((q^b.val:ℕ):ℂ)^2))=
      -lpsThetaEisensteinPrimeCuspFactor q γ := by
  have he (b : Fin 3) : lpsThetaEisensteinChi4Weight q b*
      ((Int.gcd ((q^b.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((q^b.val:ℕ):ℂ)^2)=
      -(lpsThetaEisensteinPrimeWeight q b*(Int.gcd ((q^b.val:ℕ):ℤ) (γ 1 0):ℂ)^2/
        ((q^b.val:ℕ):ℂ)) := by
    calc
      _=(lpsThetaEisensteinChi4Weight q b/((q^b.val:ℕ):ℂ)^2)*
        (Int.gcd ((q^b.val:ℕ):ℤ) (γ 1 0):ℂ)^2 := by ring
      _=_ := by rw [lpsThetaEisensteinChi4Weight_scaled];ring
  simp_rw [he]
  rw [Finset.sum_neg_distrib]
  rfl

/-- The complete prime-character dilation coefficients sum to the negative two-power gcd factor. -/
lemma lpsThetaEisenstein_quadratic_cusp_sum (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (γ : SL(2,ℤ)) :
    (∑ a : Fin 5,lpsThetaEisensteinQuadraticWeight q a*
      ((Int.gcd ((2^a.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((2^a.val:ℕ):ℂ)^2)*
        lpsQuadraticE2Character q ((2^a.val:ℕ):ZMod q))=
      -lpsThetaEisensteinTwoCuspFactor γ := by
  have he (a : Fin 5) : lpsThetaEisensteinQuadraticWeight q a*
      ((Int.gcd ((2^a.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((2^a.val:ℕ):ℂ)^2)*
        lpsQuadraticE2Character q ((2^a.val:ℕ):ZMod q)=
      -(lpsThetaEisensteinTwoWeight a*(Int.gcd ((2^a.val:ℕ):ℤ) (γ 1 0):ℂ)^2/
        ((2^a.val:ℕ):ℂ)) := by
    calc
      _=(lpsThetaEisensteinQuadraticWeight q a*lpsQuadraticE2Character q ((2^a.val:ℕ):ZMod q)/
        ((2^a.val:ℕ):ℂ)^2)*(Int.gcd ((2^a.val:ℕ):ℤ) (γ 1 0):ℂ)^2 := by ring
      _=_ := by rw [lpsThetaEisensteinQuadraticWeight_scaled q hq2];ring
  simp_rw [he]
  rw [Finset.sum_neg_distrib]
  rfl

/-- Every actual common-level E2 difference has its full signed denominator-gcd cusp limit. -/
lemma lpsE2DifferenceThetaBasis_cusp_tendsto (q : ℕ) [Fact q.Prime]
    (a : Fin 5) (b : Fin 3) (γ : SL(2,ℤ)) :
    Tendsto ((lpsE2DifferenceThetaBasis q a b : ℍ→ℂ) ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (1-(Int.gcd ((2^a.val*q^b.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((2^a.val*q^b.val:ℕ):ℂ))) := by
  have h := lpsE2Difference_cusp_tendsto (2^a.val*q^b.val)
    (mul_pos (pow_pos (by decide) _) (pow_pos (Fact.out : q.Prime).pos _)) γ
  rw [lpsEisensteinDilation_column_gcd] at h
  exact h

/-- Every actual common-level modulus-four basis form has its proved gcd-scaled cusp constant. -/
lemma lpsChi4E2ThetaBasis_cusp_tendsto (q : ℕ) [Fact q.Prime] (hq4 : q%4=1)
    (b : Fin 3) (γ : SL(2,ℤ)) :
    Tendsto ((lpsChi4E2ThetaBasis q b : ℍ→ℂ) ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (((Int.gcd ((q^b.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((q^b.val:ℕ):ℂ)^2)*
        lpsChi4EisensteinCuspConstant γ)) := by
  have hq2 : q≠2 := by intro h;subst q;norm_num at hq4
  have hc := (((Fact.out : q.Prime).odd_of_ne_two hq2).coprime_two_right.pow_right 2).pow_left b.val
  norm_num only [Nat.reducePow] at hc
  have h := lpsChi4E2Dilate_cusp_coprime_tendsto (q^b.val) (pow_pos (Fact.out : q.Prime).pos _) hc γ
  rw [lpsChi4E2Character_prime_pow q hq4 b.val,one_mul] at h
  exact h

/-- Every actual common-level quadratic basis form has its proved character-scaled cusp constant. -/
lemma lpsQuadraticE2ThetaBasis_cusp_tendsto (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (a : Fin 5) (γ : SL(2,ℤ)) :
    Tendsto ((lpsQuadraticE2ThetaBasis q hq2 a : ℍ→ℂ) ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (((Int.gcd ((2^a.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((2^a.val:ℕ):ℂ)^2)*
        (lpsQuadraticE2Character q ((2^a.val:ℕ):ZMod q)*lpsQuadraticEisensteinCuspConstant q γ))) := by
  have hc := ((Fact.out : q.Prime).odd_of_ne_two hq2).coprime_two_left.pow_left a.val
  exact lpsQuadraticE2Dilate_cusp_coprime_tendsto q (2^a.val) hq2 (pow_pos (by decide) _) hc γ

/-- The genuine correction slash is the true weighted sum of the individual basis slashes. -/
lemma lpsThetaEisensteinCorrection_slash_eq (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (γ : SL(2,ℤ)) :
    ((lpsThetaEisensteinCorrection q hq2 : ℍ→ℂ) ∣[(2:ℤ)] γ)=
      (fun z => lpsThetaEisensteinNormalization q *
        ((∑ a : Fin 5,∑ b : Fin 3,
          (lpsThetaEisensteinTwoWeight a*lpsThetaEisensteinPrimeWeight q b)*
            (((lpsE2DifferenceThetaBasis q a b : ℍ→ℂ) ∣[(2:ℤ)] γ) z))+
          (∑ b : Fin 3,lpsThetaEisensteinChi4Weight q b*
            (((lpsChi4E2ThetaBasis q b : ℍ→ℂ) ∣[(2:ℤ)] γ) z))+
          (∑ a : Fin 5,lpsThetaEisensteinQuadraticWeight q a*
            (((lpsQuadraticE2ThetaBasis q hq2 a : ℍ→ℂ) ∣[(2:ℤ)] γ) z))-
          ((lpsChi4PrimeE2Twist q ∣[(2:ℤ)] γ) z))) := by
  have hk : (lpsChi4PrimeE2TwistModularForm q hq2 : ℍ→ℂ)=lpsChi4PrimeE2Twist q := by
    funext z
    exact lpsChi4PrimeE2TwistModularForm_apply q hq2 z
  simp only [lpsThetaEisensteinCorrection,FunLike.coe_smul,FunLike.coe_neg,FunLike.coe_add,
    FunLike.coe_sum,sub_eq_add_neg,SlashAction.add_slash,SlashAction.neg_slash,
    SlashAction.sum_slash,ModularForm.SL_smul_slash,hk]
  funext z
  simp only [Pi.smul_apply,Pi.add_apply,Pi.neg_apply,Finset.sum_apply,smul_eq_mul]

/-- At every integer cusp matrix the actual correction has the complete factored gcd-character constant. -/
lemma lpsThetaEisensteinCorrection_cusp_tendsto (q : ℕ) [Fact q.Prime] (hq4 : q%4=1)
    (γ : SL(2,ℤ)) :
    Tendsto ((lpsThetaEisensteinCorrection q (by intro h;subst q;norm_num at hq4) : ℍ→ℂ)
      ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (-lpsThetaEisensteinNormalization q *
        (lpsThetaEisensteinTwoCuspFactor γ+lpsChi4EisensteinCuspConstant γ)*
        (lpsThetaEisensteinPrimeCuspFactor q γ+lpsQuadraticEisensteinCuspConstant q γ))) := by
  have hq2 : q≠2 := by intro h;subst q;norm_num at hq4
  have hH := tendsto_finsetSum Finset.univ (fun (a : Fin 5) ha =>
    tendsto_finsetSum Finset.univ (fun (b : Fin 3) hb =>
      (lpsE2DifferenceThetaBasis_cusp_tendsto q a b γ).const_mul
        (lpsThetaEisensteinTwoWeight a*lpsThetaEisensteinPrimeWeight q b)))
  have h4 := tendsto_finsetSum Finset.univ (fun (b : Fin 3) hb =>
    (lpsChi4E2ThetaBasis_cusp_tendsto q hq4 b γ).const_mul (lpsThetaEisensteinChi4Weight q b))
  have hQ := tendsto_finsetSum Finset.univ (fun (a : Fin 5) ha =>
    (lpsQuadraticE2ThetaBasis_cusp_tendsto q hq2 a γ).const_mul (lpsThetaEisensteinQuadraticWeight q a))
  have hK := lpsChi4PrimeE2Twist_cusp_character_tendsto q hq2 γ
  have h := (((hH.add h4).add hQ).sub hK).const_mul (lpsThetaEisensteinNormalization q)
  have hs4 : (∑ b : Fin 3,lpsThetaEisensteinChi4Weight q b*
      (((Int.gcd ((q^b.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((q^b.val:ℕ):ℂ)^2)*
        lpsChi4EisensteinCuspConstant γ))=
      -lpsThetaEisensteinPrimeCuspFactor q γ*lpsChi4EisensteinCuspConstant γ := by
    have he (b : Fin 3) : lpsThetaEisensteinChi4Weight q b*
        (((Int.gcd ((q^b.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((q^b.val:ℕ):ℂ)^2)*
          lpsChi4EisensteinCuspConstant γ)=
        (lpsThetaEisensteinChi4Weight q b*
          ((Int.gcd ((q^b.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((q^b.val:ℕ):ℂ)^2))*
          lpsChi4EisensteinCuspConstant γ := by ring
    simp_rw [he]
    rw [←Finset.sum_mul,lpsThetaEisenstein_chi4_cusp_sum]
  have hsQ : (∑ a : Fin 5,lpsThetaEisensteinQuadraticWeight q a*
      (((Int.gcd ((2^a.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((2^a.val:ℕ):ℂ)^2)*
        (lpsQuadraticE2Character q ((2^a.val:ℕ):ZMod q)*lpsQuadraticEisensteinCuspConstant q γ)))=
      -lpsThetaEisensteinTwoCuspFactor γ*lpsQuadraticEisensteinCuspConstant q γ := by
    have he (a : Fin 5) : lpsThetaEisensteinQuadraticWeight q a*
        (((Int.gcd ((2^a.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((2^a.val:ℕ):ℂ)^2)*
          (lpsQuadraticE2Character q ((2^a.val:ℕ):ZMod q)*lpsQuadraticEisensteinCuspConstant q γ))=
        (lpsThetaEisensteinQuadraticWeight q a*
          ((Int.gcd ((2^a.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((2^a.val:ℕ):ℂ)^2)*
            lpsQuadraticE2Character q ((2^a.val:ℕ):ZMod q))*lpsQuadraticEisensteinCuspConstant q γ := by ring
    simp_rw [he]
    rw [←Finset.sum_mul,lpsThetaEisenstein_quadratic_cusp_sum q hq2]
  rw [lpsThetaEisenstein_untwisted_cusp_sum q hq2,hs4,hsQ] at h
  have hc : lpsThetaEisensteinNormalization q *
      ((-lpsThetaEisensteinTwoCuspFactor γ*lpsThetaEisensteinPrimeCuspFactor q γ+
        -lpsThetaEisensteinPrimeCuspFactor q γ*lpsChi4EisensteinCuspConstant γ)+
        -lpsThetaEisensteinTwoCuspFactor γ*lpsQuadraticEisensteinCuspConstant q γ-
        lpsChi4EisensteinCuspConstant γ*lpsQuadraticEisensteinCuspConstant q γ)=
      -lpsThetaEisensteinNormalization q *
        (lpsThetaEisensteinTwoCuspFactor γ+lpsChi4EisensteinCuspConstant γ)*
        (lpsThetaEisensteinPrimeCuspFactor q γ+lpsQuadraticEisensteinCuspConstant q γ) := by ring
  rw [hc,←lpsThetaEisensteinCorrection_slash_eq q hq2 γ] at h
  exact h

end QEC.Coding.TannerLiftedProduct
