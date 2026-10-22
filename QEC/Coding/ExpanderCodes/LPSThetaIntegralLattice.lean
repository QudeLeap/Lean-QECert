import QEC.Coding.ExpanderCodes.LPSCuspIntegralHecke
import QEC.Coding.ExpanderCodes.LPSThetaPeterssonPositive

/-!
# LPSThetaIntegralLattice

The denominator 48*q^2*(q^2-1) clears the complete original theta Eisenstein correction, including two-adic halves, prime denominators and signed character terms. The scaled original theta cusp remainder is a nonzero integral lattice vector.
No lattice, finite generation, stability, annihilator or integrality conclusion is assumed.
The arithmetic magnitude estimate and public PK22 theorem remain unproved.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Polynomial
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section

/-- Safe uniform integer denominator of the actual complete theta correction. -/
def lpsThetaIntegerDenominator (q : ℕ) : ℤ := 48*(q : ℤ)^2*((q : ℤ)^2-1)

/-- Actual common normalization is cleared, including two-adic halves and prime denominators. -/
lemma lpsThetaIntegerDenominator_normalization (q : ℕ) [Fact q.Prime] :
    (lpsThetaIntegerDenominator q : ℂ)*lpsThetaEisensteinNormalization q = 2*(q : ℂ) := by
  have hqZ : (q : ℤ)≠0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hq2 : (q : ℤ)^2-1≠0 := by
    have hq : 2≤(q : ℤ) := by exact_mod_cast (Fact.out : q.Prime).two_le
    nlinarith
  have hqC : (q : ℂ)≠0 := by exact_mod_cast hqZ
  have hqC2 : (q : ℂ)^2-1≠0 := by exact_mod_cast hq2
  simp only [lpsThetaIntegerDenominator, Int.cast_mul, Int.cast_pow, Int.cast_sub,
    Int.cast_natCast, Int.cast_ofNat, Int.cast_one, lpsThetaEisensteinNormalization]
  field_simp
  ring

/-- Every actual full correction coefficient has the same cleared integer denominator. -/
lemma lpsThetaCorrection_scaled_integer (q : ℕ) [Fact q.Prime] (n : ℕ) :
    ∃ z : ℤ, (lpsThetaIntegerDenominator q : ℂ)*lpsThetaEisensteinCorrectionCoefficient q n = (z : ℂ) := by
  classical
  let S : Subring ℂ := (Int.castRingHom ℂ).range
  have hi (z : ℤ) : (z : ℂ)∈S := ⟨z, rfl⟩
  have hn (m : ℕ) : (m : ℂ)∈S := ⟨(m : ℤ), by simp⟩
  have h24 : (-24 : ℂ)∈S := by simpa only [Int.cast_neg, Int.cast_ofNat] using hi (-24)
  have hbase (m : ℕ) : (if m=0 then 1 else -24*(ArithmeticFunction.sigma 1 m : ℂ))∈S := by
    split_ifs
    · exact S.one_mem
    · exact S.mul_mem h24 (hn _)
  have hdil (m r : ℕ) : lpsE2DilationCoefficient m r∈S := by
    rw [lpsE2DilationCoefficient]
    by_cases hm : m ∣ r
    · simp only [if_pos hm]
      exact hbase _
    · simp only [if_neg hm]
      exact S.zero_mem
  have hdiff (m r : ℕ) : lpsE2DifferenceCoefficient m r∈S := by
    rw [lpsE2DifferenceCoefficient]
    exact S.sub_mem (hbase r) (S.mul_mem (hn m) (hdil m r))
  have hchi (r : ZMod 4) : lpsChi4E2Character r∈S := by
    exact ⟨ZMod.χ₄ r, rfl⟩
  have hquad (r : ZMod q) : lpsQuadraticE2Character q r∈S := by
    exact ⟨quadraticChar (ZMod q) r, rfl⟩
  have htwo (a : Fin 5) : 2*lpsThetaEisensteinTwoWeight a∈S := by
    convert hi (![2,-3,5,0,-4] a) using 1
    fin_cases a <;> norm_num [lpsThetaEisensteinTwoWeight]
  have hprime (b : Fin 3) : (q : ℂ)*lpsThetaEisensteinPrimeWeight q b∈S := by
    have hqC : (q : ℂ)≠0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
    convert hi (![(q : ℤ),-((q : ℤ)+1),(q : ℤ)^2] b) using 1
    fin_cases b <;> simp [lpsThetaEisensteinPrimeWeight] <;> field_simp
  have hchiW (b : Fin 3) : lpsThetaEisensteinChi4Weight q b∈S := by
    convert hi (![-1,(q : ℤ)+1,-(q : ℤ)^3] b) using 1
    fin_cases b <;> simp [lpsThetaEisensteinChi4Weight]
  have hquadW (a : Fin 5) : lpsThetaEisensteinQuadraticWeight q a∈S := by
    convert hi (![-1,3*quadraticChar (ZMod q) (2 : ZMod q),-10,0,32] a) using 1
    fin_cases a <;> simp [lpsThetaEisensteinQuadraticWeight, lpsQuadraticE2Character,
      MulChar.ringHomComp_apply]
  have hmul : (2*(q : ℂ))∈S := S.mul_mem (hn 2) (hn q)
  have hc : (lpsThetaIntegerDenominator q : ℂ)*lpsThetaEisensteinCorrectionCoefficient q n∈S := by
    rw [lpsThetaEisensteinCorrectionCoefficient, ← mul_assoc,
      lpsThetaIntegerDenominator_normalization, mul_sub, mul_add, mul_add]
    apply S.sub_mem
    · apply S.add_mem
      · apply S.add_mem
        · rw [Finset.mul_sum]
          apply S.sum_mem
          intro a _
          rw [Finset.mul_sum]
          apply S.sum_mem
          intro b _
          rw [show 2*(q : ℂ)*((lpsThetaEisensteinTwoWeight a*lpsThetaEisensteinPrimeWeight q b)*
            lpsE2DifferenceCoefficient (2^a.val*q^b.val) n) =
            (2*lpsThetaEisensteinTwoWeight a)*((q : ℂ)*lpsThetaEisensteinPrimeWeight q b)*
            lpsE2DifferenceCoefficient (2^a.val*q^b.val) n by ring]
          exact S.mul_mem (S.mul_mem (htwo a) (hprime b)) (hdiff _ _)
        · apply S.mul_mem hmul
          apply S.sum_mem
          intro b _
          apply S.mul_mem (hchiW b)
          split_ifs
          · exact S.mul_mem (S.mul_mem h24 (hn _)) (hchi _)
          · exact S.zero_mem
      · apply S.mul_mem hmul
        apply S.sum_mem
        intro a _
        apply S.mul_mem (hquadW a)
        split_ifs
        · exact S.mul_mem (S.mul_mem h24 (hn _)) (hquad _)
        · exact S.zero_mem
    · exact S.mul_mem hmul (S.mul_mem (S.mul_mem (S.mul_mem h24 (hn _)) (hquad _)) (hchi _))
  obtain ⟨z, hz⟩ := hc
  exact ⟨z, hz.symm⟩

/-- The scaled ORIGINAL theta cusp remainder is in the actual all-integer cusp lattice. -/
lemma lpsTheta_scaled_memIntegralLattice (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) :
    lpsThetaIntegerDenominator q • lpsThetaCuspidalRemainder q hq4 ∈
      lpsIntegralCuspLattice ((4*q)^2) := by
  intro n
  rw [map_smul, ← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul]
  change ∃ z : ℤ, (lpsThetaIntegerDenominator q : ℂ)*
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsThetaCuspidalRemainder q hq4)) = (z : ℂ)
  rw [coeff_qExpansion_lpsThetaCuspidalRemainder, mul_sub]
  obtain ⟨z, hz⟩ := lpsThetaCorrection_scaled_integer q n
  refine ⟨lpsThetaIntegerDenominator q*((PowerSeries.coeff n (lpsTraceThetaSeries q) : ℕ) : ℤ)-z, ?_⟩
  rw [hz, Int.cast_sub, Int.cast_mul, Int.cast_natCast]

/-- The proved denominator is nonzero at every actual residue prime. -/
lemma lpsThetaIntegerDenominator_ne_zero (q : ℕ) [Fact q.Prime] :
    lpsThetaIntegerDenominator q≠0 := by
  have hq : 2≤(q : ℤ) := by exact_mod_cast (Fact.out : q.Prime).two_le
  unfold lpsThetaIntegerDenominator
  have hq2 : 0<(q : ℤ)^2-1 := by nlinarith
  positivity

/-- The concrete arithmetic theta lattice vector is genuine and nonzero. -/
lemma lpsTheta_scaled_ne_zero (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) :
    lpsThetaIntegerDenominator q • lpsThetaCuspidalRemainder q hq4 ≠ 0 := by
  rw [← Int.cast_smul_eq_zsmul ℂ]
  have hd : (lpsThetaIntegerDenominator q : ℂ)≠0 := by
    exact_mod_cast lpsThetaIntegerDenominator_ne_zero q
  exact smul_ne_zero hd (lpsThetaCuspidalRemainder_ne_zero q hq4)

end
end QEC.Coding.TannerLiftedProduct
