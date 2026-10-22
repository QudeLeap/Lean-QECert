import QEC.Coding.ExpanderCodes.LPSCharacterEisensteinDilation

/-!
# The actual weighted theta Eisenstein correction

The complete weighted sum of genuine common-level modular forms has its true
analytic q-expansion. Its infinity constant is one, and every even power of an
odd index coprime to the residue prime has coefficient twice the divisor sum
divided by the PSL cardinality. The explicit weight vector is a derived
candidate; the all-cusp matching proof must establish its mathematical role.
No cusp cancellation, coefficient growth or PK22 main theorem is asserted here.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

/-- The explicit two-adic weights in the standard theta Eisenstein correction. -/
noncomputable def lpsThetaEisensteinTwoWeight (a : Fin 5) : ℂ :=
  ![1,-(3/2),5/2,0,-2] a
/-- The explicit residue-prime weights in the standard theta Eisenstein correction. -/
noncomputable def lpsThetaEisensteinPrimeWeight (q : ℕ) (b : Fin 3) : ℂ :=
  ![1,-((q:ℂ)+1)/(q:ℂ),(q:ℂ)] b
/-- The actual modulus-four character-basis coefficients in the correction. -/
noncomputable def lpsThetaEisensteinChi4Weight (q : ℕ) (b : Fin 3) : ℂ :=
  ![-1,(q:ℂ)+1,-(q:ℂ)^3] b
/-- The actual quadratic-character basis coefficients in the correction. -/
noncomputable def lpsThetaEisensteinQuadraticWeight (q : ℕ) [Fact q.Prime] (a : Fin 5) : ℂ :=
  ![-1,3*lpsQuadraticE2Character q (2:ZMod q),-10,0,32] a
/-- The actual complex normalization of the standard theta correction. -/
noncomputable def lpsThetaEisensteinNormalization (q : ℕ) : ℂ :=
  (24*(q:ℂ)*((q:ℂ)^2-1))⁻¹

/-- The genuine common-level modular form built from the complete weighted Eisenstein basis. -/
noncomputable def lpsThetaEisensteinCorrection (q : ℕ) [Fact q.Prime] (hq2 : q≠2) :
    ModularForm (CongruenceSubgroup.Gamma0 ((4*q)^2) : Subgroup (GL (Fin 2) ℝ)) 2 :=
  lpsThetaEisensteinNormalization q •
    ((∑ a : Fin 5,∑ b : Fin 3,
      (lpsThetaEisensteinTwoWeight a*lpsThetaEisensteinPrimeWeight q b) •
        lpsE2DifferenceThetaBasis q a b) +
      (∑ b : Fin 3,lpsThetaEisensteinChi4Weight q b • lpsChi4E2ThetaBasis q b) +
      (∑ a : Fin 5,lpsThetaEisensteinQuadraticWeight q a • lpsQuadraticE2ThetaBasis q hq2 a) -
      lpsChi4PrimeE2TwistModularForm q hq2)

/-- The actual period-one analytic q-expansion coefficient is a complex linear map. -/
noncomputable def lpsModularForm_coefficientLinearMap (N n : ℕ) :
    ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2 →ₗ[ℂ] ℂ where
  toFun f := PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)
  map_add' f g := by
    have hp : (1:ℝ)∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
    have h := congrArg (PowerSeries.coeff n)
      (ModularForm.qExpansion_add (by norm_num : (0:ℝ)<1) hp f g)
    simpa only [FunLike.coe_add,map_add] using h
  map_smul' a f := by
    have hp : (1:ℝ)∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
    have h := congrArg (PowerSeries.coeff n)
      (ModularForm.qExpansion_smul (by norm_num : (0:ℝ)<1) hp a f)
    simpa only [FunLike.coe_smul,PowerSeries.coeff_smul,smul_eq_mul,RingHom.id_apply] using h


/-- The complete coefficient vector of the actual weighted modular form. -/
noncomputable def lpsThetaEisensteinCorrectionCoefficient (q : ℕ) [Fact q.Prime] (n : ℕ) : ℂ :=
  lpsThetaEisensteinNormalization q *
    ((∑ a : Fin 5,∑ b : Fin 3,
      (lpsThetaEisensteinTwoWeight a*lpsThetaEisensteinPrimeWeight q b) *
        lpsE2DifferenceCoefficient (2^a.val*q^b.val) n) +
      (∑ b : Fin 3,lpsThetaEisensteinChi4Weight q b *
        (if q^b.val∣n then -24*(ArithmeticFunction.sigma 1 (n/q^b.val):ℂ)*
          lpsChi4E2Character ((n/q^b.val:ℕ):ZMod 4) else 0)) +
      (∑ a : Fin 5,lpsThetaEisensteinQuadraticWeight q a *
        (if 2^a.val∣n then -24*(ArithmeticFunction.sigma 1 (n/2^a.val):ℂ)*
          lpsQuadraticE2Character q ((n/2^a.val:ℕ):ZMod q) else 0)) -
      (-24*(ArithmeticFunction.sigma 1 n:ℂ)*lpsQuadraticE2Character q (n:ZMod q)*lpsChi4E2Character (n:ZMod 4)))

/-- Linearity and the genuine analytic basis coefficients compute every correction coefficient. -/
lemma coeff_qExpansion_lpsThetaEisensteinCorrection (q : ℕ) [Fact q.Prime] (hq2 : q≠2) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsThetaEisensteinCorrection q hq2))=
      lpsThetaEisensteinCorrectionCoefficient q n := by
  change lpsModularForm_coefficientLinearMap ((4*q)^2) n
    (lpsThetaEisensteinCorrection q hq2)=_
  rw [lpsThetaEisensteinCorrection,map_smul,map_sub,map_add,map_add]
  simp only [map_sum,map_smul,smul_eq_mul]
  change lpsThetaEisensteinNormalization q *
    ((∑ a : Fin 5,∑ b : Fin 3,
      (lpsThetaEisensteinTwoWeight a*lpsThetaEisensteinPrimeWeight q b) *
        PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsE2DifferenceThetaBasis q a b))) +
      (∑ b : Fin 3,lpsThetaEisensteinChi4Weight q b *
        PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsChi4E2ThetaBasis q b))) +
      (∑ a : Fin 5,lpsThetaEisensteinQuadraticWeight q a *
        PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsQuadraticE2ThetaBasis q hq2 a))) -
      PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsChi4PrimeE2TwistModularForm q hq2)))=_
  simp only [coeff_qExpansion_lpsE2DifferenceThetaBasis,coeff_qExpansion_lpsChi4E2ThetaBasis,
    coeff_qExpansion_lpsQuadraticE2ThetaBasis,coeff_qExpansion_lpsChi4PrimeE2TwistModularForm,
    lpsThetaEisensteinCorrectionCoefficient]


/-- The actual complete correction has constant coefficient one. -/
lemma lpsThetaEisensteinCorrectionCoefficient_zero (q : ℕ) [Fact q.Prime] :
    lpsThetaEisensteinCorrectionCoefficient q 0=1 := by
  have hqC : (q:ℂ)≠0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hq2C : (q:ℂ)^2-1≠0 := by
    have hr : (1:ℝ)<(q:ℝ) := by exact_mod_cast (Fact.out : q.Prime).one_lt
    have hx : (q:ℝ)^2-1≠0 := by nlinarith
    exact_mod_cast hx
  norm_num [lpsThetaEisensteinCorrectionCoefficient,lpsThetaEisensteinNormalization,
    lpsE2DifferenceCoefficient_zero,lpsThetaEisensteinTwoWeight,lpsThetaEisensteinPrimeWeight,
    lpsThetaEisensteinChi4Weight,lpsThetaEisensteinQuadraticWeight,Fin.sum_univ_succ,
    MulChar.map_zero,Nat.cast_mul,Nat.cast_pow]
  field_simp [hqC,hq2C]
  ring

/-- At odd prime-unit indices with unit character values the complete coefficient is four times the divisor sum over the group normalization. -/
lemma lpsThetaEisensteinCorrectionCoefficient_of_unit_characters (q : ℕ) [Fact q.Prime]
    (n : ℕ) (h2 : ¬2∣n) (hq : ¬q∣n)
    (hc4 : lpsChi4E2Character (n:ZMod 4)=1)
    (hcq : lpsQuadraticE2Character q (n:ZMod q)=1) :
    lpsThetaEisensteinCorrectionCoefficient q n=
      4*(ArithmeticFunction.sigma 1 n:ℂ)/((q:ℂ)*((q:ℂ)^2-1)) := by
  have hn : n≠0 := by intro hn;subst n;exact h2 (dvd_zero _)
  have hpd (a b : ℕ) (hab : 0<a ∨ 0<b) : ¬2^a*q^b∣n := by
    intro hd
    rcases hab with ha | hb
    · exact h2 ((dvd_pow_self 2 ha.ne').trans ((dvd_mul_right (2^a) (q^b)).trans hd))
    · exact hq ((dvd_pow_self q hb.ne').trans ((dvd_mul_left (q^b) (2^a)).trans hd))
  have hq2 : ¬q^2∣n := fun hd => hq ((dvd_pow_self q (by decide : (2:ℕ)≠0)).trans hd)
  have h4 : ¬4∣n := fun hd => h2 ((by decide : (2:ℕ)∣4).trans hd)
  have h8 : ¬8∣n := fun hd => h2 ((by decide : (2:ℕ)∣8).trans hd)
  have h16 : ¬16∣n := fun hd => h2 ((by decide : (2:ℕ)∣16).trans hd)
  have hqC : (q:ℂ)≠0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hq2C : (q:ℂ)^2-1≠0 := by
    have hr : (1:ℝ)<(q:ℝ) := by exact_mod_cast (Fact.out : q.Prime).one_lt
    have hx : (q:ℝ)^2-1≠0 := by nlinarith
    exact_mod_cast hx
  have hH (a b : ℕ) : lpsE2DifferenceCoefficient (2^a*q^b) n=
      if a=0 ∧ b=0 then 0 else -24*(ArithmeticFunction.sigma 1 n:ℂ) := by
    by_cases ha : a=0
    · subst a
      by_cases hb : b=0
      · subst b
        simp [lpsE2DifferenceCoefficient,lpsE2DilationCoefficient]
      · rw [lpsE2DifferenceCoefficient_of_not_dvd _ n hn (hpd _ _ (Or.inr (Nat.pos_of_ne_zero hb)))]
        simp [hb]
    · rw [lpsE2DifferenceCoefficient_of_not_dvd _ n hn (hpd _ _ (Or.inl (Nat.pos_of_ne_zero ha)))]
      simp [ha]
  simp only [lpsThetaEisensteinCorrectionCoefficient]
  simp_rw [hH]
  norm_num [Fin.sum_univ_succ,lpsThetaEisensteinTwoWeight,lpsThetaEisensteinPrimeWeight,
    lpsThetaEisensteinChi4Weight,lpsThetaEisensteinQuadraticWeight,hq,hq2,h2,h4,h8,h16,hcq,hc4]
  simp only [lpsThetaEisensteinNormalization]
  field_simp [hqC,hq2C]
  ring

/-- At every even power of an odd prime-unit index the actual correction coefficient is twice the divisor sum divided by the PSL cardinality. -/
lemma coeff_qExpansion_lpsThetaEisensteinCorrection_even_power (p q : ℕ) [Fact q.Prime]
    (hq2 : q≠2) (hp : Odd p) (hpq : ¬q∣p) (n : ℕ) :
    PowerSeries.coeff (p^(2*n)) (UpperHalfPlane.qExpansion 1 (lpsThetaEisensteinCorrection q hq2))=
      4*(ArithmeticFunction.sigma 1 (p^(2*n)):ℂ)/((q:ℂ)*((q:ℂ)^2-1)) := by
  have h2 : ¬2∣p^(2*n) := (hp.pow).not_two_dvd_nat
  have hq : ¬q∣p^(2*n) := fun hd => hpq ((Fact.out : q.Prime).dvd_of_dvd_pow hd)
  have hc4 : lpsChi4E2Character ((p^(2*n):ℕ):ZMod 4)=1 := by
    have hc : (p^n).Coprime 4 := by
      have h := (hp.pow : Odd (p^n)).coprime_two_right.pow_right 2
      norm_num only [Nat.reducePow] at h
      exact h
    have hu : IsUnit ((p^n:ℕ):ZMod 4) := (ZMod.isUnit_iff_coprime (p^n) 4).mpr hc
    rw [show p^(2*n)=(p^n)^2 by rw [mul_comm,pow_mul],Nat.cast_pow]
    exact lpsChi4E2Character_square _ hu
  have hcq : lpsQuadraticE2Character q ((p^(2*n):ℕ):ZMod q)=1 := by
    have hn : ((p^n:ℕ):ZMod q)≠0 := by
      intro hz
      have hd : q∣p^n := (ZMod.natCast_eq_zero_iff (p^n) q).mp hz
      exact hpq ((Fact.out : q.Prime).dvd_of_dvd_pow hd)
    rw [show p^(2*n)=(p^n)^2 by rw [mul_comm,pow_mul],Nat.cast_pow]
    exact lpsQuadraticE2Character_square q _ hn
  rw [coeff_qExpansion_lpsThetaEisensteinCorrection]
  exact lpsThetaEisensteinCorrectionCoefficient_of_unit_characters q _ h2 hq hc4 hcq

/-- The genuine analytic cusp function gives the full infinity limit of every period-one modular form. -/
lemma lpsModularForm_tendsto_constantCoefficient (N : ℕ)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    Tendsto (f:ℍ→ℂ) UpperHalfPlane.atImInfty
      (𝓝 (PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 f))) := by
  have hper : (1:ℝ)∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  have hp := SlashInvariantFormClass.periodic_comp_ofComplex f hper
  have ha := ModularFormClass.analyticAt_cuspFunction_zero f (by norm_num : (0:ℝ)<1) hper
  have hc : UpperHalfPlane.cuspFunction 1 f 0=PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 f) := by
    simp [UpperHalfPlane.qExpansion_coeff]
  have he : (fun z : ℍ => UpperHalfPlane.cuspFunction 1 f
      (Function.Periodic.qParam 1 (z:ℂ)))=(f:ℍ→ℂ) := by
    funext z
    exact UpperHalfPlane.eq_cuspFunction z (by norm_num) hp
  have h := ha.continuousAt.tendsto.comp
    (UpperHalfPlane.qParam_tendsto_atImInfty (by norm_num : (0:ℝ)<1))
  simpa only [Function.comp_def,hc,he] using h

/-- The true correction modular form has full-filter infinity limit one. -/
lemma lpsThetaEisensteinCorrection_tendsto_one (q : ℕ) [Fact q.Prime] (hq2 : q≠2) :
    Tendsto (lpsThetaEisensteinCorrection q hq2 : ℍ→ℂ) UpperHalfPlane.atImInfty (𝓝 1) := by
  have h := lpsModularForm_tendsto_constantCoefficient ((4*q)^2) (lpsThetaEisensteinCorrection q hq2)
  rw [coeff_qExpansion_lpsThetaEisensteinCorrection,lpsThetaEisensteinCorrectionCoefficient_zero] at h
  exact h

end QEC.Coding.TannerLiftedProduct
