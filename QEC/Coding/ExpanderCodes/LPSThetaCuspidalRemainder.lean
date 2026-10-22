import QEC.Coding.ExpanderCodes.LPSThetaCuspFactorization
import QEC.Coding.ExpanderCodes.LPSThetaModularForm
import QEC.Coding.ExpanderCodes.LPSModularTraceBridge

/-!
# The actual theta Eisenstein split and cuspidal trace residual

Positive denominators use the universal Gauss-product identity; matrix negation
and determinant-one translations cover the remaining signed and zero columns.
The actual theta minus the complete correction is a Mathlib weight-two CuspForm
on Gamma0((4q)^2), with true function and q-expansion identities. Its coefficient
is the centered LPS trace residual after retaining the signed 2*(-p)^n term.

This constructs the genuine cuspidal object. The stronger arithmetic coefficient
growth required by the PK22 main theorem is a subsequent proof obligation.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

/-- The actual theta slash converges to the correction constant at every positive column. -/
lemma lpsStandardTheta_cusp_correction_tendsto_pos (q : ℕ) [Fact q.Prime]
    (hq4 : q%4=1) (γ : SL(2,ℤ)) (hc : 0<γ 1 0) :
    Tendsto ((fun z : ℍ => lpsStandardTheta q z) ∣[(2:ℤ)] γ)
      UpperHalfPlane.atImInfty
      (𝓝 (-lpsThetaEisensteinNormalization q *
        (lpsThetaEisensteinTwoCuspFactor γ+lpsChi4EisensteinCuspConstant γ)*
        (lpsThetaEisensteinPrimeCuspFactor q γ+lpsQuadraticEisensteinCuspConstant q γ))) := by
  have h := tendsto_lpsStandardTheta_slash_pos_c q (Fact.out : q.Prime).pos γ hc
  have hN : 0<(γ 1 0).toNat := by omega
  have hC : γ 1 0=((γ 1 0).toNat:ℤ) := (Int.toNat_of_nonneg hc.le).symm
  have he := lpsThetaCuspGaussProduct_normalized q (γ 1 0).toNat hq4 hN γ hC
  have h' : Tendsto ((fun z : ℍ => lpsStandardTheta q z) ∣[(2:ℤ)] γ)
      UpperHalfPlane.atImInfty
      (𝓝 (-(32*(q:ℂ)^3*((γ 1 0).toNat:ℂ)^2)⁻¹*
        lpsThetaCuspGaussProduct q (γ 0 0) (γ 1 0).toNat)) := by
    simpa only [lpsThetaCuspGaussProduct,mul_assoc] using h
  rw [he] at h'
  exact h'

/-- Every weight-two function has the same slash under matrix negation. -/
lemma lpsWeightTwo_slash_neg_matrix (f : ℍ→ℂ) (γ : SL(2,ℤ)) :
    (f ∣[(2:ℤ)] (-γ))=(f ∣[(2:ℤ)] γ) := by
  funext z
  rw [ModularForm.SL_slash_apply,ModularForm.SL_slash_apply,ModularGroup.SL_neg_smul]
  simp only [ModularGroup.denom_apply]
  have hd : ((-γ) 1 0 : ℂ)*z+((-γ) 1 1 : ℂ) = -((γ 1 0 : ℂ)*z+(γ 1 1 : ℂ)) := by
    simp
    ring
  rw [hd]
  simp only [zpow_neg,zpow_ofNat,neg_sq]

/-- A zero lower-left column lies in every Gamma0 and fixes the actual modular form. -/
lemma lpsWeightTwoModularForm_slash_zero_c (N : ℕ)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (γ : SL(2,ℤ)) (hc : γ 1 0=0) : ((f:ℍ→ℂ) ∣[(2:ℤ)] γ)=(f:ℍ→ℂ) := by
  have hγ : γ∈CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem,hc]
    simp
  have hg : Matrix.SpecialLinearGroup.mapGL ℝ γ∈
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) := ⟨γ,hγ,rfl⟩
  simpa [Matrix.SpecialLinearGroup.mapGL,←ModularForm.SL_slash,
    ModularForm.toSlashInvariantForm_coe] using
    SlashInvariantFormClass.slash_action_eq
      (Γ := (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) (k := (2:ℤ))
      f (Matrix.SpecialLinearGroup.mapGL ℝ γ) hg

/-- The genuine remainder vanishes along the full imaginary-part filter for every integer cusp matrix. -/
lemma lpsThetaCuspidalRemainder_slash_tendsto_zero (q : ℕ) [Fact q.Prime]
    (hq4 : q%4=1) (γ : SL(2,ℤ)) :
    Tendsto (((fun z : ℍ => lpsStandardTheta q z)-
      (lpsThetaEisensteinCorrection q (by intro h;subst q;norm_num at hq4):ℍ→ℂ)) ∣[(2:ℤ)] γ)
      UpperHalfPlane.atImInfty (𝓝 0) := by
  have hq2 : q≠2 := by intro h;subst q;norm_num at hq4
  rw [sub_eq_add_neg,SlashAction.add_slash,SlashAction.neg_slash]
  change Tendsto (fun z : ℍ =>
    ((fun w : ℍ => lpsStandardTheta q w) ∣[(2:ℤ)] γ) z-
    ((lpsThetaEisensteinCorrection q hq2:ℍ→ℂ) ∣[(2:ℤ)] γ) z)
    UpperHalfPlane.atImInfty (𝓝 0)
  rcases lt_trichotomy (γ 1 0) 0 with hn | hz | hp
  · have hpos : 0<(-γ) 1 0 := by simpa using neg_pos.mpr hn
    have h := (lpsStandardTheta_cusp_correction_tendsto_pos q hq4 (-γ) hpos).sub
      (lpsThetaEisensteinCorrection_cusp_tendsto q hq4 (-γ))
    simpa only [sub_self,lpsWeightTwo_slash_neg_matrix] using h
  · rw [lpsStandardTheta_slash_zero_c q γ hz,
      lpsWeightTwoModularForm_slash_zero_c _ _ γ hz]
    simpa only [sub_self] using (tendsto_lpsStandardTheta_im_infty q (Fact.out : q.Prime).pos).sub
      (lpsThetaEisensteinCorrection_tendsto_one q hq2)
  · have h := (lpsStandardTheta_cusp_correction_tendsto_pos q hq4 γ hp).sub
      (lpsThetaEisensteinCorrection_cusp_tendsto q hq4 γ)
    simpa only [sub_self] using h

/-- Raise the actual theta modular form to the identical correction level. -/
noncomputable def lpsStandardThetaCommonLevel (q : ℕ) (hq : 0<q) :
    ModularForm (CongruenceSubgroup.Gamma0 ((4*q)^2) : Subgroup (GL (Fin 2) ℝ)) 2 :=
  lpsModularForm_raiseLevel (16*q^2) ((4*q)^2)
    (by
      have he : (4*q)^2=16*q^2 := by ring
      rw [he]) (lpsStandardThetaModularForm q hq)

/-- The common-level theta retains the exact original analytic function. -/
@[simp] lemma lpsStandardThetaCommonLevel_apply (q : ℕ) (hq : 0<q) (z : ℍ) :
    lpsStandardThetaCommonLevel q hq z=lpsStandardTheta q z := rfl

/-- The actual common-level theta minus the actual complete Eisenstein correction. -/
noncomputable def lpsThetaCuspidalRemainderModularForm (q : ℕ) [Fact q.Prime] (hq2 : q≠2) :
    ModularForm (CongruenceSubgroup.Gamma0 ((4*q)^2) : Subgroup (GL (Fin 2) ℝ)) 2 :=
  lpsStandardThetaCommonLevel q (Fact.out : q.Prime).pos-lpsThetaEisensteinCorrection q hq2

/-- The modular remainder is the pointwise difference of the two genuine functions. -/
@[simp] lemma lpsThetaCuspidalRemainderModularForm_apply (q : ℕ) [Fact q.Prime]
    (hq2 : q≠2) (z : ℍ) : lpsThetaCuspidalRemainderModularForm q hq2 z=
      lpsStandardTheta q z-lpsThetaEisensteinCorrection q hq2 z := rfl

/-- Construct the actual Mathlib CuspForm using proved vanishing at every rational cusp. -/
noncomputable def lpsThetaCuspidalRemainder (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) :
    CuspForm (CongruenceSubgroup.Gamma0 ((4*q)^2) : Subgroup (GL (Fin 2) ℝ)) 2 where
  toSlashInvariantForm := (lpsThetaCuspidalRemainderModularForm q
    (by intro h;subst q;norm_num at hq4)).toSlashInvariantForm
  holo' := (lpsThetaCuspidalRemainderModularForm q
    (by intro h;subst q;norm_num at hq4)).holo'
  zero_at_cusps' := by
    intro c hc
    have hcSL : IsCusp c 𝒮ℒ := hc.mono
      (Subgroup.map_le_range (Matrix.SpecialLinearGroup.mapGL ℝ) _)
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hcSL]
    intro γ _
    have hq2 : q≠2 := by intro h;subst q;norm_num at hq4
    change Tendsto ((lpsThetaCuspidalRemainderModularForm q hq2:ℍ→ℂ) ∣[(2:ℤ)] γ)
      UpperHalfPlane.atImInfty (𝓝 0)
    have he : (lpsThetaCuspidalRemainderModularForm q hq2:ℍ→ℂ)=
        (fun z : ℍ => lpsStandardTheta q z)-(lpsThetaEisensteinCorrection q hq2:ℍ→ℂ) := rfl
    rw [he]
    exact lpsThetaCuspidalRemainder_slash_tendsto_zero q hq4 γ

/-- The bundled CuspForm retains the actual theta minus correction function. -/
@[simp] lemma lpsThetaCuspidalRemainder_apply (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) (z : ℍ) :
    lpsThetaCuspidalRemainder q hq4 z=lpsStandardTheta q z-
      lpsThetaEisensteinCorrection q (by intro h;subst q;norm_num at hq4) z := rfl

/-- Every genuine cuspidal coefficient is the representation count minus the full correction coefficient. -/
lemma coeff_qExpansion_lpsThetaCuspidalRemainder (q : ℕ) [Fact q.Prime]
    (hq4 : q%4=1) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsThetaCuspidalRemainder q hq4))=
      ((PowerSeries.coeff n (lpsTraceThetaSeries q):ℕ):ℂ)-lpsThetaEisensteinCorrectionCoefficient q n := by
  have hq2 : q≠2 := by intro h;subst q;norm_num at hq4
  have hp : (1:ℝ)∈(CongruenceSubgroup.Gamma0 ((4*q)^2) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  change PowerSeries.coeff n (UpperHalfPlane.qExpansion 1
    ((lpsStandardThetaCommonLevel q (Fact.out : q.Prime).pos:ℍ→ℂ)-
      (lpsThetaEisensteinCorrection q hq2:ℍ→ℂ)))=_
  rw [ModularForm.qExpansion_sub (by norm_num : (0:ℝ)<1) hp
    (lpsStandardThetaCommonLevel q (Fact.out : q.Prime).pos) (lpsThetaEisensteinCorrection q hq2),map_sub,
    coeff_qExpansion_lpsThetaEisensteinCorrection]
  congr 1
  exact coeff_qExpansion_lpsStandardTheta q (Fact.out : q.Prime).pos n

/-- The genuine CuspForm has zero constant coefficient. -/
lemma coeff_qExpansion_lpsThetaCuspidalRemainder_zero (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) :
    PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 (lpsThetaCuspidalRemainder q hq4))=0 := by
  have hp : (1:ℝ)∈(CongruenceSubgroup.Gamma0 ((4*q)^2) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  exact CuspFormClass.qExpansion_coeff_zero (lpsThetaCuspidalRemainder q hq4) (by norm_num) hp

/-- The actual even-power coefficient subtracts exactly twice the divisor sum divided by PSL cardinality. -/
lemma coeff_qExpansion_lpsThetaCuspidalRemainder_even_power (p q : ℕ) [Fact q.Prime]
    (hq4 : q%4=1) (hp : Odd p) (hpq : ¬q∣p) (n : ℕ) :
    PowerSeries.coeff (p^(2*n)) (UpperHalfPlane.qExpansion 1 (lpsThetaCuspidalRemainder q hq4))=
      ((PowerSeries.coeff (p^(2*n)) (lpsTraceThetaSeries q):ℕ):ℂ)-
        4*(ArithmeticFunction.sigma 1 (p^(2*n)):ℂ)/((q:ℂ)*((q:ℂ)^2-1)) := by
  rw [coeff_qExpansion_lpsThetaCuspidalRemainder]
  have h := coeff_qExpansion_lpsThetaEisensteinCorrection_even_power p q
    (by intro h;subst q;norm_num at hq4) hp hpq n
  rw [coeff_qExpansion_lpsThetaEisensteinCorrection] at h
  rw [h]

/-- The true correction coefficient times actual PSL cardinality is twice the prime-power divisor sum. -/
lemma lpsThetaEisensteinCorrection_even_coefficient_card (p : ℕ)
    (a : LPSResiduePrime p) (n : ℕ) :
    (Fintype.card PSL(2,ZMod a.q):ℂ)*
      PowerSeries.coeff (p^(2*n)) (UpperHalfPlane.qExpansion 1
        (lpsThetaEisensteinCorrection a.q (by intro h;have hm:=a.modFour;omega)))=
      2*(∑ i∈Finset.range (2*n+1),(p:ℂ)^i) := by
  have hp2 : p≠2 := by intro h;have hm:=a.degreeModFour;omega
  have hpq : ¬a.q∣p := fun h => a.ne_degreePrime ((Nat.dvd_prime a.degreePrime).mp h |>.resolve_left a.prime.ne_one)
  rw [coeff_qExpansion_lpsThetaEisensteinCorrection_even_power p a.q _
    (a.degreePrime.odd_of_ne_two hp2) hpq n,ArithmeticFunction.sigma_one_apply_prime_pow a.degreePrime]
  have hqn : 1≤a.q^2 := by have h:=a.prime.one_lt;nlinarith
  have hcard : 2*(Fintype.card PSL(2,ZMod a.q):ℂ)=(a.q:ℂ)*((a.q:ℂ)^2-1) := by
    have h := congrArg (fun x : ℕ => (x:ℂ)) a.two_mul_card_psl
    push_cast [Nat.cast_sub hqn] at h
    exact h
  have hq : (a.q:ℂ)≠0 := by exact_mod_cast a.prime.ne_zero
  have hqs : (a.q:ℂ)^2-1≠0 := by
    have hr : (1:ℝ)<(a.q:ℝ) := by exact_mod_cast a.prime.one_lt
    have hs : (a.q:ℝ)^2-1≠0 := by nlinarith
    exact_mod_cast hs
  push_cast
  field_simp [hq,hqs]
  linear_combination 2*(∑ i∈Finset.range (2*n+1),(p:ℂ)^i)*hcard

/-- Identify the exact centered trace with the genuine cusp coefficient and the retained signed term. -/
lemma lpsCenteredThetaResidual_even_eq_cuspidal_coefficient (p : ℕ)
    (a : LPSResiduePrime p) (n : ℕ) :
    lpsCenteredThetaResidual a (2*n)=
      (Fintype.card PSL(2,ZMod a.q):ℝ)*
        (PowerSeries.coeff (p^(2*n)) (UpperHalfPlane.qExpansion 1
          (lpsThetaCuspidalRemainder a.q a.modFour))).re+2*(-(p:ℝ))^n := by
  have hcoeff : PowerSeries.coeff (p^(2*n)) (UpperHalfPlane.qExpansion 1
      (lpsThetaCuspidalRemainder a.q a.modFour))=
      PowerSeries.coeff (p^(2*n)) (UpperHalfPlane.qExpansion 1
        (fun z : ℍ => lpsStandardTheta a.q z))-
      PowerSeries.coeff (p^(2*n)) (UpperHalfPlane.qExpansion 1
        (lpsThetaEisensteinCorrection a.q (by intro h;have hm:=a.modFour;omega))) := by
    rw [coeff_qExpansion_lpsThetaCuspidalRemainder,
      coeff_qExpansion_lpsStandardTheta a.q a.prime.pos _,coeff_qExpansion_lpsThetaEisensteinCorrection]
  have hcard := congrArg Complex.re (lpsThetaEisensteinCorrection_even_coefficient_card p a n)
  have hs : (∑ i∈Finset.range (2*n+1),(p:ℂ)^i)=
      ((∑ i∈Finset.range (2*n+1),(p:ℝ)^i):ℂ) := by push_cast;rfl
  have hsRe : (∑ i∈Finset.range (2*n+1),(p:ℂ)^i).re=
      ∑ i∈Finset.range (2*n+1),(p:ℝ)^i := by
    change Complex.reCLM (∑ i∈Finset.range (2*n+1),(p:ℂ)^i)=_
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    have he : (p:ℂ)^i=Complex.ofReal ((p:ℝ)^i) := by simp
    rw [he]
    rfl
  norm_num only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,
    zero_mul,mul_zero,sub_zero,hsRe] at hcard
  norm_num at hcard
  rw [lpsCenteredThetaResidual_even_eq_qExpansion_sub_explicit,hcoeff,Complex.sub_re]
  linear_combination hcard

/-- Transport the remaining trace bound to the actual cuspidal coefficient without assuming that bound. -/
lemma hasFourSqrtCenteredThetaCoefficientBound_iff_cuspidal_coefficient (p : ℕ)
    (a : LPSResiduePrime p) :
    HasFourSqrtCenteredThetaCoefficientBound a ↔ ∃ C : ℝ,0≤C ∧ ∀ n : ℕ,
      |(Fintype.card PSL(2,ZMod a.q):ℝ)*
        (PowerSeries.coeff (p^(2*n)) (UpperHalfPlane.qExpansion 1
          (lpsThetaCuspidalRemainder a.q a.modFour))).re+2*(-(p:ℝ))^n|≤
        C*(((2*n+1:ℕ):ℝ)*(4*(p:ℝ))^n) := by
  unfold HasFourSqrtCenteredThetaCoefficientBound
  simp only [lpsCenteredThetaResidual_even_eq_cuspidal_coefficient]

end QEC.Coding.TannerLiftedProduct
