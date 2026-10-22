import QEC.Coding.ExpanderCodes.JacobiThetaProduct
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Lambert-series form of Jacobi's divisor sum

This module formalizes the final coefficient extraction in Jacobi's
four-square proof: the Lambert series indexed by positive divisors not
divisible by four has coefficient equal to the corresponding divisor sum.
-/

namespace QEC.Coding.TannerLiftedProduct

open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Topology

/-- The formal geometric series `1 + X + X² + ⋯`. -/
noncomputable def jacobiGeometricSeries : ℚ⟦X⟧ :=
  PowerSeries.mk fun _ => 1

@[simp] theorem coeff_jacobiGeometricSeries (n : ℕ) :
    PowerSeries.coeff n jacobiGeometricSeries = 1 := by
  simp [jacobiGeometricSeries]

/-- Substitution in the geometric series produces the inverse of `1 - a`
whenever substitution at `a` is defined. -/
theorem jacobiGeometricSeries_subst_mul_one_sub
    {a : ℚ⟦X⟧} (hs : PowerSeries.HasSubst a) :
    (jacobiGeometricSeries.subst a) * (1 - a) = 1 := by
  change (PowerSeries.mk 1 : ℚ⟦X⟧).subst a * (1 - a) = 1
  have hsubst_one : (1 : ℚ⟦X⟧).subst a = 1 := by
    rw [← PowerSeries.coe_substAlgHom hs]
    exact map_one (PowerSeries.substAlgHom hs)
  have hone :
      ((1 : ℚ⟦X⟧) - PowerSeries.X).subst a = 1 - a := by
    rw [PowerSeries.subst_sub hs]
    rw [hsubst_one, PowerSeries.subst_X hs]
  rw [← hone, ← PowerSeries.subst_mul hs]
  rw [PowerSeries.mk_one_mul_one_sub_eq_one]
  exact hsubst_one

/-- Substituting `X^d` in the geometric series produces the inverse of
`1 - X^d`. -/
theorem jacobiGeometricSeries_subst_mul_one_sub_X_pow
    {d : ℕ} (hd : d ≠ 0) :
    (jacobiGeometricSeries.subst (PowerSeries.X ^ d)) *
      ((1 : ℚ⟦X⟧) - PowerSeries.X ^ d) = 1 :=
  jacobiGeometricSeries_subst_mul_one_sub
    (PowerSeries.HasSubst.X_pow hd)

/-- Substitution at `-X^d` produces the inverse of `1 + X^d`. -/
theorem jacobiGeometricSeries_subst_neg_X_pow_mul_one_add_X_pow
    {d : ℕ} (hd : d ≠ 0) :
    (jacobiGeometricSeries.subst (-(PowerSeries.X ^ d))) *
      ((1 : ℚ⟦X⟧) + PowerSeries.X ^ d) = 1 := by
  have hs : PowerSeries.HasSubst (-(PowerSeries.X ^ d) : ℚ⟦X⟧) := by
    apply PowerSeries.HasSubst.of_constantCoeff_zero
    have hx : MvPowerSeries.constantCoeff (PowerSeries.X : ℚ⟦X⟧) = 0 :=
      PowerSeries.constantCoeff_X
    rw [map_neg, map_pow, hx, zero_pow hd, neg_zero]
  simpa only [sub_neg_eq_add] using
    jacobiGeometricSeries_subst_mul_one_sub hs

/-- Logarithmic-derivative summand for `1 - X^d`. -/
noncomputable def jacobiMinusLogDerivative (d : ℕ) : ℚ⟦X⟧ :=
  -(PowerSeries.C (d : ℚ) * PowerSeries.X ^ (d - 1) *
    jacobiGeometricSeries.subst (PowerSeries.X ^ d))

/-- Multiplying the minus-factor logarithmic derivative by its factor
recovers the ordinary derivative. -/
theorem one_sub_X_pow_mul_jacobiMinusLogDerivative
    {d : ℕ} (hd : d ≠ 0) :
    ((1 : ℚ⟦X⟧) - PowerSeries.X ^ d) * jacobiMinusLogDerivative d =
      PowerSeries.derivative ℚ
        ((1 : ℚ⟦X⟧) - PowerSeries.X ^ d) := by
  rw [derivative_one_sub_X_pow, jacobiMinusLogDerivative]
  have hinv := jacobiGeometricSeries_subst_mul_one_sub_X_pow hd
  calc
    ((1 : ℚ⟦X⟧) - PowerSeries.X ^ d) *
        -(PowerSeries.C (d : ℚ) * PowerSeries.X ^ (d - 1) *
          jacobiGeometricSeries.subst (PowerSeries.X ^ d)) =
      -(PowerSeries.C (d : ℚ) * PowerSeries.X ^ (d - 1) *
        (jacobiGeometricSeries.subst (PowerSeries.X ^ d) *
          ((1 : ℚ⟦X⟧) - PowerSeries.X ^ d))) := by ring
    _ = -(PowerSeries.C (d : ℚ) * PowerSeries.X ^ (d - 1)) := by
      rw [hinv]
      ring

/-- Logarithmic-derivative summand for `1 + X^d`. -/
noncomputable def jacobiPlusLogDerivative (d : ℕ) : ℚ⟦X⟧ :=
  PowerSeries.C (d : ℚ) * PowerSeries.X ^ (d - 1) *
    jacobiGeometricSeries.subst (-(PowerSeries.X ^ d))

/-- Multiplying the plus-factor logarithmic derivative by its factor
recovers the ordinary derivative. -/
theorem one_add_X_pow_mul_jacobiPlusLogDerivative
    {d : ℕ} (hd : d ≠ 0) :
    ((1 : ℚ⟦X⟧) + PowerSeries.X ^ d) * jacobiPlusLogDerivative d =
      PowerSeries.derivative ℚ
        ((1 : ℚ⟦X⟧) + PowerSeries.X ^ d) := by
  rw [derivative_one_add_X_pow, jacobiPlusLogDerivative]
  have hinv := jacobiGeometricSeries_subst_neg_X_pow_mul_one_add_X_pow hd
  calc
    ((1 : ℚ⟦X⟧) + PowerSeries.X ^ d) *
        (PowerSeries.C (d : ℚ) * PowerSeries.X ^ (d - 1) *
          jacobiGeometricSeries.subst (-(PowerSeries.X ^ d))) =
      PowerSeries.C (d : ℚ) * PowerSeries.X ^ (d - 1) *
        (jacobiGeometricSeries.subst (-(PowerSeries.X ^ d)) *
          ((1 : ℚ⟦X⟧) + PowerSeries.X ^ d)) := by ring
    _ = PowerSeries.C (d : ℚ) * PowerSeries.X ^ (d - 1) := by
      rw [hinv]
      ring

/-- The minus logarithmic-derivative term has no coefficients below degree
`d - 1`. -/
theorem order_jacobiMinusLogDerivative_ge (d : ℕ) :
    (d - 1 : ℕ∞) ≤ (jacobiMinusLogDerivative d).order := by
  rw [jacobiMinusLogDerivative, PowerSeries.order_neg]
  have hreorder :
      PowerSeries.C (d : ℚ) * PowerSeries.X ^ (d - 1) *
          jacobiGeometricSeries.subst (PowerSeries.X ^ d) =
        PowerSeries.X ^ (d - 1) *
          (PowerSeries.C (d : ℚ) *
            jacobiGeometricSeries.subst (PowerSeries.X ^ d)) := by ring
  rw [hreorder]
  calc
    (d - 1 : ℕ∞) = (PowerSeries.X ^ (d - 1) : ℚ⟦X⟧).order :=
      (PowerSeries.order_X_pow (R := ℚ) (d - 1)).symm
    _ =
        (PowerSeries.X ^ (d - 1) : ℚ⟦X⟧).order + 0 := (add_zero _).symm
    _ ≤ (PowerSeries.X ^ (d - 1) : ℚ⟦X⟧).order +
        (PowerSeries.C (d : ℚ) *
          jacobiGeometricSeries.subst (PowerSeries.X ^ d)).order :=
      by
        gcongr
        exact bot_le
    _ ≤ _ := PowerSeries.le_order_mul _ _

/-- The plus logarithmic-derivative term has no coefficients below degree
`d - 1`. -/
theorem order_jacobiPlusLogDerivative_ge (d : ℕ) :
    (d - 1 : ℕ∞) ≤ (jacobiPlusLogDerivative d).order := by
  rw [jacobiPlusLogDerivative]
  have hreorder :
      PowerSeries.C (d : ℚ) * PowerSeries.X ^ (d - 1) *
          jacobiGeometricSeries.subst (-(PowerSeries.X ^ d)) =
        PowerSeries.X ^ (d - 1) *
          (PowerSeries.C (d : ℚ) *
            jacobiGeometricSeries.subst (-(PowerSeries.X ^ d))) := by ring
  rw [hreorder]
  calc
    (d - 1 : ℕ∞) = (PowerSeries.X ^ (d - 1) : ℚ⟦X⟧).order :=
      (PowerSeries.order_X_pow (R := ℚ) (d - 1)).symm
    _ =
        (PowerSeries.X ^ (d - 1) : ℚ⟦X⟧).order + 0 := (add_zero _).symm
    _ ≤ (PowerSeries.X ^ (d - 1) : ℚ⟦X⟧).order +
        (PowerSeries.C (d : ℚ) *
          jacobiGeometricSeries.subst (-(PowerSeries.X ^ d))).order :=
      by
        gcongr
        exact bot_le
    _ ≤ _ := PowerSeries.le_order_mul _ _

/-- The even-minus logarithmic derivative family is summable. -/
theorem summable_jacobi_even_minus_logDerivative :
    Summable (fun n : ℕ => jacobiMinusLogDerivative (2 * (n + 1))) := by
  apply PowerSeries.WithPiTopology.summable_of_tendsto_order_atTop_nhds_top ℚ
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun k =>
    Filter.eventually_atTop.mpr ⟨k + 1, fun n hn => ?_⟩
  refine lt_of_lt_of_le ?_ (order_jacobiMinusLogDerivative_ge (2 * (n + 1)))
  norm_cast
  omega

/-- The odd-plus logarithmic derivative family is summable. -/
theorem summable_jacobi_odd_plus_logDerivative :
    Summable (fun n : ℕ => jacobiPlusLogDerivative (2 * n + 1)) := by
  apply PowerSeries.WithPiTopology.summable_of_tendsto_order_atTop_nhds_top ℚ
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun k =>
    Filter.eventually_atTop.mpr ⟨k + 1, fun n hn => ?_⟩
  refine lt_of_lt_of_le ?_ (order_jacobiPlusLogDerivative_ge (2 * n + 1))
  norm_cast
  omega

/-- The even-plus logarithmic derivative family is summable. -/
theorem summable_jacobi_even_plus_logDerivative :
    Summable (fun n : ℕ => jacobiPlusLogDerivative (2 * (n + 1))) := by
  apply PowerSeries.WithPiTopology.summable_of_tendsto_order_atTop_nhds_top ℚ
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun k =>
    Filter.eventually_atTop.mpr ⟨k + 1, fun n hn => ?_⟩
  refine lt_of_lt_of_le ?_ (order_jacobiPlusLogDerivative_ge (2 * (n + 1)))
  norm_cast
  omega

/-- Logarithmic derivative of the combined theta-product factor. -/
noncomputable def jacobiThetaLogDerivativeSummand (n : ℕ) : ℚ⟦X⟧ :=
  jacobiMinusLogDerivative (2 * (n + 1)) +
    2 * jacobiPlusLogDerivative (2 * n + 1)

theorem summable_jacobiThetaLogDerivativeSummand :
    Summable jacobiThetaLogDerivativeSummand := by
  exact summable_jacobi_even_minus_logDerivative.add
    (Summable.mul_left 2 summable_jacobi_odd_plus_logDerivative)

/-- The supplied logarithmic derivative is correct for every combined
theta-product factor. -/
theorem jacobi_theta_factor_mul_logDerivative (n : ℕ) :
    (((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) *
        (1 + PowerSeries.X ^ (2 * n + 1)) ^ 2) *
      jacobiThetaLogDerivativeSummand n =
    PowerSeries.derivative ℚ
      (((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) *
        (1 + PowerSeries.X ^ (2 * n + 1)) ^ 2) := by
  have he := one_sub_X_pow_mul_jacobiMinusLogDerivative
    (show 2 * (n + 1) ≠ 0 by omega)
  have ho := one_add_X_pow_mul_jacobiPlusLogDerivative
    (show 2 * n + 1 ≠ 0 by omega)
  rw [(PowerSeries.derivative ℚ).leibniz,
    PowerSeries.derivative_pow]
  simp only [smul_eq_mul, jacobiThetaLogDerivativeSummand]
  rw [← he, ← ho]
  ring

/-- The full logarithmic derivative of the Jacobi theta product. -/
noncomputable def jacobiThetaLogDerivative : ℚ⟦X⟧ :=
  ∑' n, jacobiThetaLogDerivativeSummand n

/-- Infinite-product differentiation for the Jacobi theta product. -/
theorem derivative_jacobiThetaProduct :
    PowerSeries.derivative ℚ jacobiThetaProduct =
      jacobiThetaProduct * jacobiThetaLogDerivative := by
  rw [jacobiThetaProduct, jacobiThetaLogDerivative]
  exact derivative_tprod_eq_tprod_mul_tsum _ _
    multipliable_jacobi_theta_factor
    summable_jacobiThetaLogDerivativeSummand
    jacobi_theta_factor_mul_logDerivative

/-- Logarithmic derivative of the combined triangular-product factor. -/
noncomputable def jacobiTriangularLogDerivativeSummand (n : ℕ) : ℚ⟦X⟧ :=
  jacobiMinusLogDerivative (2 * (n + 1)) +
    2 * jacobiPlusLogDerivative (2 * (n + 1))

theorem summable_jacobiTriangularLogDerivativeSummand :
    Summable jacobiTriangularLogDerivativeSummand := by
  exact summable_jacobi_even_minus_logDerivative.add
    (Summable.mul_left 2 summable_jacobi_even_plus_logDerivative)

/-- The supplied logarithmic derivative is correct for every combined
triangular-product factor. -/
theorem jacobi_triangular_factor_mul_logDerivative (n : ℕ) :
    (((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) *
        (1 + PowerSeries.X ^ (2 * (n + 1))) ^ 2) *
      jacobiTriangularLogDerivativeSummand n =
    PowerSeries.derivative ℚ
      (((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) *
        (1 + PowerSeries.X ^ (2 * (n + 1))) ^ 2) := by
  have he := one_sub_X_pow_mul_jacobiMinusLogDerivative
    (show 2 * (n + 1) ≠ 0 by omega)
  have ho := one_add_X_pow_mul_jacobiPlusLogDerivative
    (show 2 * (n + 1) ≠ 0 by omega)
  rw [(PowerSeries.derivative ℚ).leibniz,
    PowerSeries.derivative_pow]
  simp only [smul_eq_mul, jacobiTriangularLogDerivativeSummand]
  rw [← he, ← ho]
  ring

/-- The full logarithmic derivative of the Jacobi triangular product. -/
noncomputable def jacobiTriangularLogDerivative : ℚ⟦X⟧ :=
  ∑' n, jacobiTriangularLogDerivativeSummand n

/-- Infinite-product differentiation for the Jacobi triangular product. -/
theorem derivative_jacobiTriangularProduct :
    PowerSeries.derivative ℚ jacobiTriangularProduct =
      jacobiTriangularProduct * jacobiTriangularLogDerivative := by
  rw [jacobiTriangularProduct, jacobiTriangularLogDerivative]
  exact derivative_tprod_eq_tprod_mul_tsum _ _
    multipliable_jacobi_triangular_factor
    summable_jacobiTriangularLogDerivativeSummand
    jacobi_triangular_factor_mul_logDerivative

/-- The logarithmic-derivative difference controlling the Wronskian of the
two Jacobi products. -/
noncomputable def jacobiLogDerivativeDifference : ℚ⟦X⟧ :=
  jacobiTriangularLogDerivative - jacobiThetaLogDerivative

/-- The Wronskian `βγ' - β'γ` factors by `βγ`; this is the algebraic
bridge between the cube identity and the Lambert-series correction. -/
theorem jacobiThetaTriangular_wronskian :
    jacobiThetaProduct *
        PowerSeries.derivative ℚ jacobiTriangularProduct -
      PowerSeries.derivative ℚ jacobiThetaProduct *
        jacobiTriangularProduct =
      (jacobiThetaProduct * jacobiTriangularProduct) *
        jacobiLogDerivativeDifference := by
  rw [derivative_jacobiThetaProduct,
    derivative_jacobiTriangularProduct, jacobiLogDerivativeDifference]
  ring

/-- The right-hand side of Jacobi's cube/reindex identity is already a
product of `βγ` and one explicit logarithmic-derivative correction. -/
theorem jacobi_cube_correction_factorization :
    jacobiThetaProduct * jacobiTriangularProduct +
        PowerSeries.C 4 * PowerSeries.X *
          (jacobiThetaProduct *
              PowerSeries.derivative ℚ jacobiTriangularProduct -
            PowerSeries.derivative ℚ jacobiThetaProduct *
              jacobiTriangularProduct) =
      (jacobiThetaProduct * jacobiTriangularProduct) *
        (1 + PowerSeries.C 4 * PowerSeries.X *
          jacobiLogDerivativeDifference) := by
  rw [jacobiThetaTriangular_wronskian]
  ring

/-- The `d`-th Lambert summand, represented coefficientwise. It contributes
`d` in every positive degree divisible by `d`. -/
noncomputable def jacobiLambertTerm (d : ℕ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => if 0 < n ∧ d ∣ n then d else 0

@[simp] theorem coeff_jacobiLambertTerm (d n : ℕ) :
    PowerSeries.coeff n (jacobiLambertTerm d) =
      if 0 < n ∧ d ∣ n then (d : ℚ) else 0 := by
  simp [jacobiLambertTerm]

/-- For positive `d`, the coefficientwise Lambert summand is the familiar
formal fraction `d * (X^d + X^(2d) + ⋯)`. -/
theorem jacobiLambertTerm_eq_geometric {d : ℕ} (hd : d ≠ 0) :
    jacobiLambertTerm d =
      PowerSeries.C (d : ℚ) *
        ((jacobiGeometricSeries.subst (PowerSeries.X ^ d)) - 1) := by
  ext n
  rw [coeff_jacobiLambertTerm, PowerSeries.coeff_C_mul, map_sub]
  rw [PowerSeries.coeff_subst_X_pow hd, coeff_jacobiGeometricSeries]
  by_cases hn : n = 0
  · subst n
    simp
  · by_cases hdvd : d ∣ n <;> simp [hn, hdvd]

private theorem summable_jacobiLambertTerms :
    Summable (fun d : ℕ => if 4 ∣ d then 0 else jacobiLambertTerm d) := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro n
  apply summable_of_hasFiniteSupport
  refine (Finset.Iic n).finite_toSet.subset ?_
  intro d hd
  simp only [Function.mem_support] at hd
  by_contra hdnle
  by_cases h4 : 4 ∣ d
  · simp [h4] at hd
  · simp only [h4, if_false, coeff_jacobiLambertTerm] at hd
    by_cases hcond : 0 < n ∧ d ∣ n
    · exact hdnle (by simpa using Nat.le_of_dvd hcond.1 hcond.2)
    · simp [hcond] at hd

/-- Rational Lambert series occurring at the end of Jacobi's four-square
argument. -/
noncomputable def jacobiLambertSeries : ℚ⟦X⟧ :=
  1 + PowerSeries.C 8 *
    ∑' d : ℕ, if 4 ∣ d then 0 else jacobiLambertTerm d

/-- Coefficients of the Lambert series are exactly eight times the sum of
positive divisors not divisible by four. -/
theorem coeff_jacobiLambertSeries (n : ℕ) :
    PowerSeries.coeff n jacobiLambertSeries =
      if n = 0 then 1
      else 8 * ∑ d ∈ n.divisors, if 4 ∣ d then 0 else d := by
  by_cases hn : n = 0
  · subst n
    rw [jacobiLambertSeries, map_add, PowerSeries.coeff_C_mul]
    rw [summable_jacobiLambertTerms.map_tsum
      (PowerSeries.coeff 0)
      (PowerSeries.WithPiTopology.continuous_coeff ℚ 0)]
    have hzero :
        (∑' i : ℕ,
          PowerSeries.constantCoeff
            (if 4 ∣ i then 0 else jacobiLambertTerm i)) = 0 := by
      have hfun :
          (fun i : ℕ => PowerSeries.constantCoeff
            (if 4 ∣ i then 0 else jacobiLambertTerm i)) = 0 := by
        funext i
        by_cases h4 : 4 ∣ i
        · simp [h4]
        · rw [if_neg h4, ← PowerSeries.coeff_zero_eq_constantCoeff]
          simp
      rw [hfun]
      change (∑' _ : ℕ, (0 : ℚ)) = 0
      exact tsum_zero
    simpa [← PowerSeries.coeff_zero_eq_constantCoeff] using hzero
  · rw [jacobiLambertSeries, map_add, PowerSeries.coeff_C_mul]
    rw [summable_jacobiLambertTerms.map_tsum
      (PowerSeries.coeff n)
      (PowerSeries.WithPiTopology.continuous_coeff ℚ n)]
    rw [tsum_eq_sum (s := n.divisors)]
    · rw [PowerSeries.coeff_one]
      simp only [hn, if_false, zero_add]
      push_cast
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      by_cases h4 : 4 ∣ d <;> simp [h4, hnpos, hdvd]
    · intro d hd
      have hnotdvd : ¬ d ∣ n := by
        intro hdvd
        exact hd (Nat.mem_divisors.mpr ⟨hdvd, hn⟩)
      by_cases h4 : 4 ∣ d <;> simp [h4, hnotdvd]

/-- The natural-coefficient divisor-sum series after extension of scalars to
the rationals. -/
noncomputable def rationalJacobiFourSquareSeries : ℚ⟦X⟧ :=
  PowerSeries.map (Nat.castRingHom ℚ) jacobiFourSquareSeries

/-- The coefficientwise divisor-sum definition agrees with its Lambert-series
presentation. -/
theorem jacobiLambertSeries_eq_rationalJacobiFourSquareSeries :
    jacobiLambertSeries = rationalJacobiFourSquareSeries := by
  ext n
  rw [coeff_jacobiLambertSeries]
  simp [rationalJacobiFourSquareSeries, jacobiFourSquareSeries]

/-- Equality after coefficient extension to `ℚ` reflects the original
natural-coefficient Jacobi theta identity. -/
theorem integerThetaSeries_pow_four_eq_jacobi_of_rational
    (h : rationalIntegerThetaSeries ^ 4 = jacobiLambertSeries) :
    integerThetaSeries ^ 4 = jacobiFourSquareSeries := by
  apply PowerSeries.map_injective (Nat.castRingHom ℚ) Nat.cast_injective
  rw [map_pow]
  change rationalIntegerThetaSeries ^ 4 = rationalJacobiFourSquareSeries
  exact h.trans jacobiLambertSeries_eq_rationalJacobiFourSquareSeries

end QEC.Coding.TannerLiftedProduct
