import QEC.Coding.ExpanderCodes.JacobiCubeReindex
import QEC.Coding.ExpanderCodes.JacobiTripleProductCore

/-!
# Specialized Jacobi triple-product identities

This module transports the bivariate formal-power-series Jacobi triple
product to rational coefficients and connects it to the theta products used
in the four-square proof.
-/

namespace QEC.Coding.TannerLiftedProduct

open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology

set_option linter.style.haveILetI false

/-- Evaluate the Laurent variable at `1` and extend integer coefficients to
the rationals. -/
noncomputable def jacobiLaurentEvalOne : LaurentPolynomial ℤ →+* ℚ :=
  LaurentPolynomial.eval₂ (Int.castRingHom ℚ) 1

/-- Coefficientwise specialization of the bivariate JTP at the Laurent
variable `1`. -/
noncomputable def jacobiPowerSeriesEvalOne :
    JacobiTripleProductCore.R →+* ℚ⟦X⟧ :=
  PowerSeries.map jacobiLaurentEvalOne

@[simp] theorem jacobiLaurentEvalOne_T (m : ℤ) :
    jacobiLaurentEvalOne (LaurentPolynomial.T m) = 1 := by
  simp [jacobiLaurentEvalOne]

@[simp] theorem jacobiPowerSeriesEvalOne_X :
    jacobiPowerSeriesEvalOne JacobiTripleProductCore.q = PowerSeries.X := by
  simp [jacobiPowerSeriesEvalOne, JacobiTripleProductCore.q]

theorem continuous_jacobiPowerSeriesEvalOne :
    letI := JacobiTripleProductCore.piTop
    Continuous jacobiPowerSeriesEvalOne := by
  letI : TopologicalSpace (LaurentPolynomial ℤ) := ⊥
  letI : DiscreteTopology (LaurentPolynomial ℤ) := ⟨rfl⟩
  letI := JacobiTripleProductCore.piTop
  rw [continuous_iff_continuousAt]
  intro f
  rw [ContinuousAt,
    PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  change Filter.Tendsto
    (fun g : JacobiTripleProductCore.R =>
      jacobiLaurentEvalOne (PowerSeries.coeff n g))
    (nhds f)
    (nhds (jacobiLaurentEvalOne (PowerSeries.coeff n f)))
  exact (continuous_of_discreteTopology.comp
    (PowerSeries.WithPiTopology.continuous_coeff
      (LaurentPolynomial ℤ) n)).continuousAt

@[simp] theorem jacobiPowerSeriesEvalOne_C_T (m : ℤ) :
    jacobiPowerSeriesEvalOne
        (PowerSeries.C (LaurentPolynomial.T m)) = 1 := by
  rw [jacobiPowerSeriesEvalOne, PowerSeries.map_C]
  simp

/-- Mapping a specialized q-Pochhammer product through evaluation at the
Laurent variable `1` commutes with its convergent infinite product. -/
theorem jacobiPowerSeriesEvalOne_qPochhammerInf
    (A : JacobiTripleProductCore.R) :
    letI := JacobiTripleProductCore.piTop
    Multipliable (fun n : ℕ =>
        1 - A * (JacobiTripleProductCore.q ^ 2) ^ n) →
    jacobiPowerSeriesEvalOne
        (JacobiTripleProductCore.qPochhammerInf A
          (JacobiTripleProductCore.q ^ 2)) =
      (∏' n : ℕ,
        ((1 : ℚ⟦X⟧) - jacobiPowerSeriesEvalOne A *
          PowerSeries.X ^ (2 * n))) := by
  letI : TopologicalSpace (LaurentPolynomial ℤ) := ⊥
  letI : DiscreteTopology (LaurentPolynomial ℤ) := ⟨rfl⟩
  letI := JacobiTripleProductCore.piTop
  intro hA
  rw [JacobiTripleProductCore.qPochhammerInf_eq_tprod _ _ hA]
  rw [hA.map_tprod jacobiPowerSeriesEvalOne
    continuous_jacobiPowerSeriesEvalOne]
  simp only [map_sub, map_one, map_mul, map_pow,
    jacobiPowerSeriesEvalOne_X]
  simp_rw [← pow_mul]

/-- The product side of the bivariate JTP specializes to the rational
integer-theta product. -/
theorem jacobiPowerSeriesEvalOne_lhs :
    jacobiPowerSeriesEvalOne JacobiTripleProductCore.lhs =
      jacobiThetaProduct := by
  letI : TopologicalSpace (LaurentPolynomial ℤ) := ⊥
  letI : DiscreteTopology (LaurentPolynomial ℤ) := ⟨rfl⟩
  letI := JacobiTripleProductCore.piTop
  have hSecond : Multipliable (fun n : ℕ =>
      1 - (-JacobiTripleProductCore.q * JacobiTripleProductCore.a) *
        (JacobiTripleProductCore.q ^ 2) ^ n) := by
    exact (JacobiTripleProductCore.factors_multipliable
      JacobiTripleProductCore.a).congr fun n => by ring
  rw [JacobiTripleProductCore.lhs]
  simp only [map_mul]
  rw [jacobiPowerSeriesEvalOne_qPochhammerInf _
      JacobiTripleProductCore.multipliable_factors,
    jacobiPowerSeriesEvalOne_qPochhammerInf _ hSecond,
    jacobiPowerSeriesEvalOne_qPochhammerInf _
      JacobiTripleProductCore.multipliable_P3_factors]
  simp only [map_pow, map_neg, map_mul,
    jacobiPowerSeriesEvalOne_X, jacobiPowerSeriesEvalOne_C_T]
  simp_rw [show ∀ n : ℕ,
      (1 : ℚ⟦X⟧) - PowerSeries.X ^ 2 * PowerSeries.X ^ (2 * n) =
        1 - PowerSeries.X ^ (2 * (n + 1)) by
          intro n
          rw [← pow_add]
          congr 2
          omega]
  simp_rw [show ∀ n : ℕ,
      (1 : ℚ⟦X⟧) - (-PowerSeries.X * 1) * PowerSeries.X ^ (2 * n) =
        1 + PowerSeries.X ^ (2 * n + 1) by
          intro n
          rw [show 2 * n + 1 = 1 + 2 * n by omega, pow_add]
          ring]
  rw [jacobiThetaProduct, tprod_jacobi_theta_factor]
  ring

/-- The series side of the bivariate JTP specializes coefficientwise to the
rational integer-theta series. -/
theorem jacobiPowerSeriesEvalOne_rhs :
    jacobiPowerSeriesEvalOne JacobiTripleProductCore.rhs =
      rationalIntegerThetaSeries := by
  letI : TopologicalSpace (LaurentPolynomial ℤ) := ⊥
  letI : DiscreteTopology (LaurentPolynomial ℤ) := ⟨rfl⟩
  letI := JacobiTripleProductCore.piTop
  ext n
  simp only [jacobiPowerSeriesEvalOne, PowerSeries.coeff_map,
    coeff_rationalIntegerThetaSeries]
  have hCoeff : Summable (fun m : ℤ =>
      PowerSeries.coeff n
        (PowerSeries.C (LaurentPolynomial.T m) *
          JacobiTripleProductCore.q ^ m.natAbs ^ 2)) :=
    JacobiTripleProductCore.summable_rhs_terms.map
      (PowerSeries.coeff n)
      (PowerSeries.WithPiTopology.continuous_coeff
        (LaurentPolynomial ℤ) n)
  rw [JacobiTripleProductCore.rhs,
    JacobiTripleProductCore.summable_rhs_terms.map_tsum
      (PowerSeries.coeff n)
      (PowerSeries.WithPiTopology.continuous_coeff
        (LaurentPolynomial ℤ) n),
    hCoeff.map_tsum jacobiLaurentEvalOne continuous_of_discreteTopology]
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow,
    mul_ite, mul_one, mul_zero]
  rw [tsum_eq_sum (s := integerSquareRoots n) (fun m hm => by
    rw [if_neg]
    · simp
    · intro hsq
      apply hm
      rw [mem_integerSquareRoots_iff]
      rw [← sq_abs m, ← Int.natCast_natAbs m, ← Nat.cast_pow]
      exact_mod_cast hsq.symm)]
  calc
    _ = ∑ _m ∈ integerSquareRoots n, (1 : ℚ) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [if_pos]
      · exact jacobiLaurentEvalOne_T m
      · rw [mem_integerSquareRoots_iff] at hm
        rw [← Nat.cast_inj (R := ℤ), Nat.cast_pow,
          Int.natCast_natAbs, sq_abs, hm]
    _ = _ := by simp

/-- Jacobi's theta product identity over rational formal power series. -/
theorem jacobiThetaProduct_eq_rationalIntegerThetaSeries :
    jacobiThetaProduct = rationalIntegerThetaSeries := by
  letI : TopologicalSpace (LaurentPolynomial ℤ) := ⊥
  letI : DiscreteTopology (LaurentPolynomial ℤ) := ⟨rfl⟩
  letI := JacobiTripleProductCore.piTop
  have h := congrArg jacobiPowerSeriesEvalOne
    JacobiTripleProductCore.jacobi_triple_product
  rw [jacobiPowerSeriesEvalOne_lhs,
    jacobiPowerSeriesEvalOne_rhs] at h
  exact h

end QEC.Coding.TannerLiftedProduct
