import QEC.Coding.ExpanderCodes.LPSCuspPeterssonPositive
import QEC.Coding.ExpanderCodes.LPSThetaRankinDensity

/-!
# LPSThetaPeterssonPositive

The actual first coefficient of the theta-minus-complete-correction cusp form is strictly positive. This proves the form is nonzero and its true Petersson square mass is positive; Cauchy-Schwarz gives a concrete pairing bound. Stronger coefficient growth, complete sparse CSS runtime and the PK22 main theorem remain unproved.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal ComplexConjugate

noncomputable section
/-- The true first coefficient is positive: a norm-one representation exceeds the complete correction. -/
lemma coeff_qExpansion_lpsThetaCuspidalRemainder_one_re_pos (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) :
    0<(PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1 (lpsThetaCuspidalRemainder q hq4))).re := by
  have hq2 : q≠2 := by intro h;subst q;norm_num at hq4
  have hqpos := (Fact.out : q.Prime).pos
  have hm : (1:LPSQuaternion)∈lpsTraceQuadraticShell q 1 := by
    apply (mem_lpsTraceQuadraticShell_iff hqpos _).mpr
    simp [lpsTraceQuadraticForm]
  have hc : (1:ℝ)≤(lpsTraceQuadraticShell q 1).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨1,hm⟩
  have hcor := coeff_qExpansion_lpsThetaEisensteinCorrection_even_power 1 q hq2
    (by decide : Odd (1:ℕ)) (by simpa using (Fact.out : q.Prime).ne_one) 0
  simp only [Nat.mul_zero,pow_zero, coeff_qExpansion_lpsThetaEisensteinCorrection] at hcor
  have hcoef := coeff_qExpansion_lpsThetaCuspidalRemainder q hq4 1
  rw [hcor,coeff_lpsTraceThetaSeries] at hcoef
  have hs : ArithmeticFunction.sigma 1 1=1 := by simp
  rw [hs] at hcoef
  have hqr : (2:ℝ)≤q := by exact_mod_cast (Fact.out : q.Prime).two_le
  have hqs : (3:ℝ)≤(q:ℝ)^2-1 := by nlinarith
  have hden : (6:ℝ)≤(q:ℝ)*((q:ℝ)^2-1) := by
    nlinarith [mul_le_mul hqr hqs (by norm_num : (0:ℝ)≤3) (by positivity : (0:ℝ)≤q)]
  have hcval : (PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1 (lpsThetaCuspidalRemainder q hq4))).re =
      ((lpsTraceQuadraticShell q 1).card:ℝ)-4/((q:ℝ)*((q:ℝ)^2-1)) := by
    rw [hcoef]
    norm_cast
  rw [hcval]
  have hfrac : (4:ℝ)/((q:ℝ)*((q:ℝ)^2-1))<1 := by
    apply (div_lt_one (by linarith)).mpr
    linarith
  linarith

/-- The actual theta-minus-complete-correction cusp form is nonzero at every prime level q = 1 mod 4. -/
lemma lpsThetaCuspidalRemainder_ne_zero (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) :
    lpsThetaCuspidalRemainder q hq4≠0 := by
  intro hz
  have hp := coeff_qExpansion_lpsThetaCuspidalRemainder_one_re_pos q hq4
  have hfun : (lpsThetaCuspidalRemainder q hq4:ℍ→ℂ)=0 := by rw [hz];rfl
  rw [hfun,UpperHalfPlane.qExpansion_zero] at hp
  simp at hp

/-- The genuine theta square integral is strictly positive, using the actual first coefficient and integral nondegeneracy. -/
lemma lpsThetaRankinMass_pos (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) :
    0<lpsThetaRankinMass q hq4 := by
  let : NeZero ((4*q)^2) := ⟨by have := (Fact.out : q.Prime).pos;positivity⟩
  exact (lpsCuspPeterssonMass_pos_iff ((4*q)^2) (lpsThetaCuspidalRemainder q hq4)).mpr
    (lpsThetaCuspidalRemainder_ne_zero q hq4)

/-- The actual theta pairing is bounded by its genuine mass and the other form's square integral. -/
lemma lpsThetaPeterssonPairing_norm_sq_le_mass_mul_mass (q : ℕ) [Fact q.Prime] (hq4 : q%4=1)
    (g : CuspForm (CongruenceSubgroup.Gamma0 ((4*q)^2) : Subgroup (GL (Fin 2) ℝ)) 2) :
    let : NeZero ((4*q)^2) := ⟨by have := (Fact.out : q.Prime).pos;positivity⟩
    ‖lpsCuspPeterssonPairing ((4*q)^2) (lpsThetaCuspidalRemainder q hq4) g‖^2 ≤
      lpsThetaRankinMass q hq4*(∫τ in ModularGroup.fd,lpsCuspPeterssonDensity ((4*q)^2) g τ) := by
  let : NeZero ((4*q)^2) := ⟨by have := (Fact.out : q.Prime).pos;positivity⟩
  have h := lpsCuspPeterssonPairing_norm_sq_le ((4*q)^2) (lpsThetaCuspidalRemainder q hq4) g
  rw [lpsCuspPeterssonPairing_self_eq,lpsCuspPeterssonPairing_self_eq] at h
  exact h

end
end QEC.Coding.TannerLiftedProduct
