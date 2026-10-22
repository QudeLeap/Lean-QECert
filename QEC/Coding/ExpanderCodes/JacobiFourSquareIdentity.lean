import QEC.Coding.ExpanderCodes.JacobiTriangularProduct
import QEC.Coding.ExpanderCodes.JacobiLambertSeries
import QEC.Coding.ExpanderCodes.JacobiTripleProductSpecialization

/-!
# Jacobi's four-square theta identity

This module closes the product/series argument after the two specialized
triple-product identities.  It first proves the alternating theta identity;
the final substitution `X ↦ -X` then produces Jacobi's positive theta and
Lambert series.
-/

namespace QEC.Coding.TannerLiftedProduct

open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology

/-- The cube-product identity, parity reindexing, and the two theta-product
specializations combine to identify the fourth power of the alternating
theta product with the logarithmic-derivative correction. -/
theorem jacobiAlternatingThetaProduct_pow_four_eq_logDerivativeCorrection :
    jacobiAlternatingThetaProduct ^ 4 =
      1 + PowerSeries.C 4 * PowerSeries.X *
        jacobiLogDerivativeDifference := by
  apply (isUnit_jacobiThetaProduct.mul
    isUnit_jacobiTriangularProduct).mul_right_cancel
  calc
    jacobiAlternatingThetaProduct ^ 4 *
        (jacobiThetaProduct * jacobiTriangularProduct) =
      jacobiEulerSixProduct :=
        jacobiAlternatingThetaProduct_pow_four_mul_theta_triangular
    _ = jacobiSignedCubeSeries ^ 2 :=
      JacobiCubeProduct.jacobiSignedCubeSeries_sq_eq_jacobiEulerSixProduct.symm
    _ = rationalIntegerThetaSeries * rationalTriangularThetaSeries +
        PowerSeries.C 4 * PowerSeries.X *
          (rationalIntegerThetaSeries *
              PowerSeries.derivative ℚ rationalTriangularThetaSeries -
            PowerSeries.derivative ℚ rationalIntegerThetaSeries *
              rationalTriangularThetaSeries) :=
      jacobiSignedCubeSeries_sq_eq_theta_wronskian
    _ = jacobiThetaProduct * jacobiTriangularProduct +
        PowerSeries.C 4 * PowerSeries.X *
          (jacobiThetaProduct *
              PowerSeries.derivative ℚ jacobiTriangularProduct -
            PowerSeries.derivative ℚ jacobiThetaProduct *
              jacobiTriangularProduct) := by
      rw [← jacobiThetaProduct_eq_rationalIntegerThetaSeries,
        ← JacobiTriangularProduct.jacobiTriangularProduct_eq_rationalTriangularThetaSeries]
    _ = (jacobiThetaProduct * jacobiTriangularProduct) *
        (1 + PowerSeries.C 4 * PowerSeries.X *
          jacobiLogDerivativeDifference) :=
      jacobi_cube_correction_factorization
    _ = (1 + PowerSeries.C 4 * PowerSeries.X *
          jacobiLogDerivativeDifference) *
        (jacobiThetaProduct * jacobiTriangularProduct) := by ring

/-- Continuous substitution of `-X` for `X`. -/
noncomputable def substNegX : PowerSeries ℚ →+* PowerSeries ℚ :=
  PowerSeries.evalNegHom

@[simp] theorem coeff_substNegX (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (substNegX f) =
      (-1 : ℚ) ^ n * PowerSeries.coeff n f := by
  exact PowerSeries.coeff_rescale f (-1) n

theorem continuous_substNegX : Continuous substNegX := by
  rw [continuous_iff_continuousAt]
  intro f
  rw [ContinuousAt,
    PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  simp only [coeff_substNegX]
  exact tendsto_const_nhds.mul
    ((PowerSeries.WithPiTopology.continuous_coeff ℚ n).tendsto f)

@[simp] theorem substNegX_X :
    substNegX PowerSeries.X = -(PowerSeries.X : PowerSeries ℚ) := by
  exact PowerSeries.rescale_neg_one_X

private theorem neg_X_pow_even (n : ℕ) :
    (-(PowerSeries.X : PowerSeries ℚ)) ^ (2 * n) =
      PowerSeries.X ^ (2 * n) := by
  rw [neg_pow, (even_two_mul n).neg_one_pow]
  ring

private theorem neg_X_pow_odd (n : ℕ) :
    (-(PowerSeries.X : PowerSeries ℚ)) ^ (2 * n + 1) =
      -(PowerSeries.X ^ (2 * n + 1)) := by
  rw [pow_add, neg_X_pow_even]
  ring

theorem substNegX_jacobiAlternatingThetaProduct :
    substNegX jacobiAlternatingThetaProduct = jacobiThetaProduct := by
  rw [jacobiAlternatingThetaProduct,
    multipliable_jacobiAlternatingThetaFactor.map_tprod
      substNegX continuous_substNegX,
    jacobiThetaProduct]
  apply tprod_congr
  intro n
  simp only [map_mul, map_sub, map_one, map_pow]
  rw [substNegX_X]
  rw [neg_X_pow_even, neg_X_pow_odd]
  ring

private theorem isUnit_one_sub_X_pow {d : ℕ} (hd : d ≠ 0) :
    IsUnit ((1 : PowerSeries ℚ) - PowerSeries.X ^ d) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp [hd]

private theorem isUnit_one_add_X_pow {d : ℕ} (hd : d ≠ 0) :
    IsUnit ((1 : PowerSeries ℚ) + PowerSeries.X ^ d) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp [hd]

theorem jacobiLambertTerm_eq_X_pow_mul_geometric {d : ℕ} (hd : d ≠ 0) :
    jacobiLambertTerm d =
      PowerSeries.C (d : ℚ) * PowerSeries.X ^ d *
        jacobiGeometricSeries.subst (PowerSeries.X ^ d) := by
  rw [jacobiLambertTerm_eq_geometric hd]
  have hinv :
      jacobiGeometricSeries.subst
          ((PowerSeries.X : PowerSeries ℚ) ^ d) *
        (1 - (PowerSeries.X : PowerSeries ℚ) ^ d) = 1 :=
    jacobiGeometricSeries_subst_mul_one_sub_X_pow hd
  have htail :
      jacobiGeometricSeries.subst
          ((PowerSeries.X : PowerSeries ℚ) ^ d) - 1 =
        (PowerSeries.X : PowerSeries ℚ) ^ d *
          jacobiGeometricSeries.subst
            ((PowerSeries.X : PowerSeries ℚ) ^ d) := by
    linear_combination hinv
  rw [htail]
  ring

private theorem substNegX_geometric_neg_odd (n : ℕ) :
    substNegX
        (jacobiGeometricSeries.subst
          (-(PowerSeries.X ^ (2 * n + 1)))) =
      jacobiGeometricSeries.subst
        (PowerSeries.X ^ (2 * n + 1)) := by
  have hd : 2 * n + 1 ≠ 0 := by omega
  apply (isUnit_one_sub_X_pow hd).mul_right_cancel
  have hmap :
      substNegX
          ((1 : PowerSeries ℚ) + PowerSeries.X ^ (2 * n + 1)) =
        1 - PowerSeries.X ^ (2 * n + 1) := by
    simp only [map_add, map_one, map_pow, substNegX_X]
    rw [neg_X_pow_odd]
    ring
  calc
    substNegX
          (jacobiGeometricSeries.subst
            (-(PowerSeries.X ^ (2 * n + 1)))) *
        (1 - PowerSeries.X ^ (2 * n + 1)) =
      substNegX
          (jacobiGeometricSeries.subst
            (-(PowerSeries.X ^ (2 * n + 1)))) *
        substNegX
          ((1 : PowerSeries ℚ) + PowerSeries.X ^ (2 * n + 1)) := by
            rw [hmap]
    _ = substNegX
        (jacobiGeometricSeries.subst
            (-(PowerSeries.X ^ (2 * n + 1))) *
          ((1 : PowerSeries ℚ) + PowerSeries.X ^ (2 * n + 1))) := by
            rw [map_mul]
    _ = substNegX 1 := congrArg substNegX
      (jacobiGeometricSeries_subst_neg_X_pow_mul_one_add_X_pow hd)
    _ = 1 := map_one substNegX
    _ = jacobiGeometricSeries.subst
          (PowerSeries.X ^ (2 * n + 1)) *
        (1 - PowerSeries.X ^ (2 * n + 1)) :=
      (jacobiGeometricSeries_subst_mul_one_sub_X_pow hd).symm

private theorem substNegX_geometric_neg_even (n : ℕ) :
    substNegX
        (jacobiGeometricSeries.subst
          (-(PowerSeries.X ^ (2 * (n + 1))))) =
      jacobiGeometricSeries.subst
        (-(PowerSeries.X ^ (2 * (n + 1)))) := by
  have hd : 2 * (n + 1) ≠ 0 := by omega
  apply (isUnit_one_add_X_pow hd).mul_right_cancel
  have hmap :
      substNegX
          ((1 : PowerSeries ℚ) + PowerSeries.X ^ (2 * (n + 1))) =
        1 + PowerSeries.X ^ (2 * (n + 1)) := by
    simp only [map_add, map_one, map_pow, substNegX_X]
    rw [neg_X_pow_even]
  calc
    substNegX
          (jacobiGeometricSeries.subst
            (-(PowerSeries.X ^ (2 * (n + 1))))) *
        (1 + PowerSeries.X ^ (2 * (n + 1))) =
      substNegX
          (jacobiGeometricSeries.subst
            (-(PowerSeries.X ^ (2 * (n + 1))))) *
        substNegX
          ((1 : PowerSeries ℚ) + PowerSeries.X ^ (2 * (n + 1))) := by
            rw [hmap]
    _ = substNegX
        (jacobiGeometricSeries.subst
            (-(PowerSeries.X ^ (2 * (n + 1)))) *
          ((1 : PowerSeries ℚ) + PowerSeries.X ^ (2 * (n + 1)))) := by
            rw [map_mul]
    _ = substNegX 1 := congrArg substNegX
      (jacobiGeometricSeries_subst_neg_X_pow_mul_one_add_X_pow hd)
    _ = 1 := map_one substNegX
    _ = jacobiGeometricSeries.subst
          (-(PowerSeries.X ^ (2 * (n + 1)))) *
        (1 + PowerSeries.X ^ (2 * (n + 1))) :=
      (jacobiGeometricSeries_subst_neg_X_pow_mul_one_add_X_pow hd).symm

@[simp] theorem substNegX_C (q : ℚ) :
    substNegX (PowerSeries.C q) = PowerSeries.C q := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp
  · simp [coeff_substNegX, PowerSeries.coeff_C, hn]

theorem substNegX_X_mul_jacobiPlusLogDerivative_odd (n : ℕ) :
    substNegX
        (PowerSeries.X * jacobiPlusLogDerivative (2 * n + 1)) =
      -jacobiLambertTerm (2 * n + 1) := by
  have hd : 2 * n + 1 ≠ 0 := by omega
  rw [jacobiPlusLogDerivative]
  simp only [map_mul, map_pow, substNegX_X, substNegX_C]
  rw [show 2 * n + 1 - 1 = 2 * n by omega,
    neg_X_pow_even, substNegX_geometric_neg_odd,
    jacobiLambertTerm_eq_X_pow_mul_geometric hd]
  ring

private theorem geometric_double_mul_one_add (d : ℕ) (hd : d ≠ 0) :
    jacobiGeometricSeries.subst
          ((PowerSeries.X : PowerSeries ℚ) ^ (2 * d)) *
        (1 + (PowerSeries.X : PowerSeries ℚ) ^ d) =
      jacobiGeometricSeries.subst
        ((PowerSeries.X : PowerSeries ℚ) ^ d) := by
  apply (isUnit_one_sub_X_pow hd).mul_right_cancel
  calc
    (jacobiGeometricSeries.subst (PowerSeries.X ^ (2 * d)) *
          (1 + PowerSeries.X ^ d)) *
        (1 - PowerSeries.X ^ d) =
      jacobiGeometricSeries.subst (PowerSeries.X ^ (2 * d)) *
        (1 - PowerSeries.X ^ (2 * d)) := by
          rw [show 2 * d = d * 2 by omega, pow_mul]
          ring
    _ = 1 := jacobiGeometricSeries_subst_mul_one_sub_X_pow
      (show 2 * d ≠ 0 by omega)
    _ = jacobiGeometricSeries.subst (PowerSeries.X ^ d) *
        (1 - PowerSeries.X ^ d) :=
      (jacobiGeometricSeries_subst_mul_one_sub_X_pow hd).symm

private theorem plusFraction_eq_lambert_sub_double (d : ℕ) (hd : d ≠ 0) :
    PowerSeries.C (d : ℚ) * PowerSeries.X ^ d *
        jacobiGeometricSeries.subst (-(PowerSeries.X ^ d)) =
      jacobiLambertTerm d - jacobiLambertTerm (2 * d) := by
  rw [jacobiLambertTerm_eq_X_pow_mul_geometric hd,
    jacobiLambertTerm_eq_X_pow_mul_geometric
      (show 2 * d ≠ 0 by omega)]
  apply (isUnit_one_add_X_pow hd).mul_right_cancel
  have hneg := jacobiGeometricSeries_subst_neg_X_pow_mul_one_add_X_pow hd
  have hpos := jacobiGeometricSeries_subst_mul_one_sub_X_pow hd
  have hdouble := geometric_double_mul_one_add d hd
  calc
    (PowerSeries.C (d : ℚ) * PowerSeries.X ^ d *
          jacobiGeometricSeries.subst (-(PowerSeries.X ^ d))) *
        (1 + PowerSeries.X ^ d) =
      PowerSeries.C (d : ℚ) * PowerSeries.X ^ d := by
        rw [mul_assoc, hneg]
        ring
    _ = PowerSeries.C (d : ℚ) * PowerSeries.X ^ d *
          jacobiGeometricSeries.subst (PowerSeries.X ^ d) *
          (1 + PowerSeries.X ^ d) -
        PowerSeries.C ((2 * d : ℕ) : ℚ) * PowerSeries.X ^ (2 * d) *
          (jacobiGeometricSeries.subst (PowerSeries.X ^ (2 * d)) *
            (1 + PowerSeries.X ^ d)) := by
      rw [hdouble]
      have hC : PowerSeries.C (((2 * d : ℕ) : ℚ)) =
          2 * PowerSeries.C (d : ℚ) := by
        push_cast
        rw [map_mul]
        change (2 : PowerSeries ℚ) * PowerSeries.C (d : ℚ) = _
        rfl
      have hpow :
          (PowerSeries.X : PowerSeries ℚ) ^ (d * 2) =
            (PowerSeries.X ^ d : PowerSeries ℚ) ^ 2 :=
        pow_mul _ _ _
      rw [hC, show 2 * d = d * 2 by omega]
      calc
        PowerSeries.C (d : ℚ) * PowerSeries.X ^ d =
            PowerSeries.C (d : ℚ) * PowerSeries.X ^ d *
              (jacobiGeometricSeries.subst (PowerSeries.X ^ d) *
                (1 - PowerSeries.X ^ d)) := by rw [hpos]; ring
        _ = _ := by rw [hpow]; ring
    _ = (PowerSeries.C (d : ℚ) * PowerSeries.X ^ d *
          jacobiGeometricSeries.subst (PowerSeries.X ^ d) -
        PowerSeries.C ((2 * d : ℕ) : ℚ) * PowerSeries.X ^ (2 * d) *
          jacobiGeometricSeries.subst (PowerSeries.X ^ (2 * d))) *
        (1 + PowerSeries.X ^ d) := by
      ring

theorem substNegX_X_mul_jacobiPlusLogDerivative_even (n : ℕ) :
    substNegX
        (PowerSeries.X * jacobiPlusLogDerivative (2 * (n + 1))) =
      jacobiLambertTerm (2 * (n + 1)) -
        jacobiLambertTerm (4 * (n + 1)) := by
  let d := 2 * (n + 1)
  have hd : d ≠ 0 := by simp [d]
  rw [jacobiPlusLogDerivative]
  simp only [map_mul, map_pow, substNegX_X, substNegX_C]
  rw [show d - 1 = 2 * n + 1 by simp [d]; omega,
    neg_X_pow_odd n, substNegX_geometric_neg_even]
  have h := plusFraction_eq_lambert_sub_double d hd
  rw [show 2 * d = 4 * (n + 1) by simp [d]; ring] at h
  rw [show d = 2 * (n + 1) by rfl] at h
  convert h using 1
  all_goals ring

private theorem summable_jacobiPlusDifference :
    Summable (fun n : ℕ =>
      jacobiPlusLogDerivative (2 * (n + 1)) -
        jacobiPlusLogDerivative (2 * n + 1)) :=
  summable_jacobi_even_plus_logDerivative.sub
    summable_jacobi_odd_plus_logDerivative

theorem jacobiLogDerivativeDifference_eq_two_mul_tsum_plusDifference :
    jacobiLogDerivativeDifference =
      2 * ∑' n : ℕ,
        (jacobiPlusLogDerivative (2 * (n + 1)) -
          jacobiPlusLogDerivative (2 * n + 1)) := by
  rw [jacobiLogDerivativeDifference, jacobiTriangularLogDerivative,
    jacobiThetaLogDerivative]
  have hdiff := summable_jacobiTriangularLogDerivativeSummand.hasSum.sub
    summable_jacobiThetaLogDerivativeSummand.hasSum
  rw [← hdiff.tsum_eq]
  rw [← summable_jacobiPlusDifference.tsum_mul_left 2]
  apply tsum_congr
  intro n
  rw [jacobiTriangularLogDerivativeSummand,
    jacobiThetaLogDerivativeSummand]
  ring

private theorem summable_X_mul_jacobiPlusDifference :
    Summable (fun n : ℕ =>
      PowerSeries.X *
        (jacobiPlusLogDerivative (2 * (n + 1)) -
          jacobiPlusLogDerivative (2 * n + 1))) :=
  summable_jacobiPlusDifference.mul_left PowerSeries.X

theorem X_mul_jacobiLogDerivativeDifference_eq_tsum :
    PowerSeries.X * jacobiLogDerivativeDifference =
      2 * ∑' n : ℕ,
        PowerSeries.X *
          (jacobiPlusLogDerivative (2 * (n + 1)) -
            jacobiPlusLogDerivative (2 * n + 1)) := by
  rw [jacobiLogDerivativeDifference_eq_two_mul_tsum_plusDifference]
  calc
    PowerSeries.X *
        (2 * ∑' n : ℕ,
          (jacobiPlusLogDerivative (2 * (n + 1)) -
            jacobiPlusLogDerivative (2 * n + 1))) =
      2 * (PowerSeries.X *
        ∑' n : ℕ,
          (jacobiPlusLogDerivative (2 * (n + 1)) -
            jacobiPlusLogDerivative (2 * n + 1))) := by ring
    _ = _ := by
      rw [← summable_jacobiPlusDifference.tsum_mul_left PowerSeries.X]

theorem substNegX_X_mul_logDerivativeDifference :
    substNegX (PowerSeries.X * jacobiLogDerivativeDifference) =
      2 * ∑' n : ℕ,
        (jacobiLambertTerm (2 * (n + 1)) -
          jacobiLambertTerm (4 * (n + 1)) +
          jacobiLambertTerm (2 * n + 1)) := by
  rw [X_mul_jacobiLogDerivativeDifference_eq_tsum,
    map_mul, map_ofNat]
  rw [summable_X_mul_jacobiPlusDifference.map_tsum
    substNegX continuous_substNegX]
  congr 1
  apply tsum_congr
  intro n
  simp only [map_mul, map_sub]
  rw [mul_sub, ← map_mul,
    substNegX_X_mul_jacobiPlusLogDerivative_even,
    ← map_mul, substNegX_X_mul_jacobiPlusLogDerivative_odd]
  ring

theorem jacobiLambertTerm_zero : jacobiLambertTerm 0 = 0 := by
  ext n
  simp [coeff_jacobiLambertTerm]

theorem summable_all_jacobiLambertTerms : Summable jacobiLambertTerm := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro n
  apply summable_of_hasFiniteSupport
  refine (Finset.Iic n).finite_toSet.subset ?_
  intro d hd
  simp only [Function.mem_support] at hd
  by_contra hdnle
  rw [coeff_jacobiLambertTerm] at hd
  by_cases hcond : 0 < n ∧ d ∣ n
  · exact hdnle (by simpa using Nat.le_of_dvd hcond.1 hcond.2)
  · simp [hcond] at hd

private theorem summable_jacobiLambertTerms_comp_ge
    (g : ℕ → ℕ) (hg : ∀ n, n ≤ g n) :
    Summable (fun n : ℕ => jacobiLambertTerm (g n)) := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro k
  apply summable_of_hasFiniteSupport
  refine (Finset.range (k + 1)).finite_toSet.subset ?_
  intro n hn
  simp only [Function.mem_support] at hn
  by_contra hmem
  have hnlarge : k + 1 ≤ n := by
    simpa only [Finset.mem_coe, Finset.mem_range, not_lt] using hmem
  rw [coeff_jacobiLambertTerm] at hn
  by_cases hcond : 0 < k ∧ g n ∣ k
  · have hle := Nat.le_of_dvd hcond.1 hcond.2
    have hgn := hg n
    omega
  · simp [hcond] at hn

private theorem summable_even_jacobiLambertTerms :
    Summable (fun n : ℕ => jacobiLambertTerm (2 * n)) :=
  summable_jacobiLambertTerms_comp_ge _ (by intro n; omega)

private theorem summable_odd_jacobiLambertTerms :
    Summable (fun n : ℕ => jacobiLambertTerm (2 * n + 1)) :=
  summable_jacobiLambertTerms_comp_ge _ (by intro n; omega)

private theorem summable_four_jacobiLambertTerms :
    Summable (fun n : ℕ => jacobiLambertTerm (4 * n)) :=
  summable_jacobiLambertTerms_comp_ge _ (by intro n; omega)

private theorem summable_positiveEven_jacobiLambertTerms :
    Summable (fun n : ℕ => jacobiLambertTerm (2 * (n + 1))) := by
  exact summable_jacobiLambertTerms_comp_ge _ (by intro n; omega)

private theorem summable_positiveFour_jacobiLambertTerms :
    Summable (fun n : ℕ => jacobiLambertTerm (4 * (n + 1))) := by
  exact summable_jacobiLambertTerms_comp_ge _ (by intro n; omega)

theorem tsum_lambert_even_sub_four_add_odd :
    (∑' n : ℕ,
        (jacobiLambertTerm (2 * (n + 1)) -
          jacobiLambertTerm (4 * (n + 1)) +
          jacobiLambertTerm (2 * n + 1))) =
      (∑' d : ℕ, jacobiLambertTerm d) -
        ∑' n : ℕ, jacobiLambertTerm (4 * n) := by
  have hcombined :=
    (summable_positiveEven_jacobiLambertTerms.hasSum.sub
      summable_positiveFour_jacobiLambertTerms.hasSum).add
      summable_odd_jacobiLambertTerms.hasSum
  rw [hcombined.tsum_eq]
  have hevenShift := summable_even_jacobiLambertTerms.tsum_eq_zero_add
  have hfourShift := summable_four_jacobiLambertTerms.tsum_eq_zero_add
  simp [jacobiLambertTerm_zero] at hevenShift hfourShift
  have hsplit := tsum_even_add_odd
    summable_even_jacobiLambertTerms
    summable_odd_jacobiLambertTerms
  rw [← hevenShift, ← hfourShift]
  linear_combination hsplit

private def fourMultipleEquiv :
    ℕ ≃ {d : ℕ // 4 ∣ d} where
  toFun n := ⟨4 * n, Nat.dvd_mul_right 4 n⟩
  invFun d := d.1 / 4
  left_inv := by
    intro n
    simp [Nat.mul_comm]
  right_inv := by
    intro d
    apply Subtype.ext
    exact Nat.mul_div_cancel' d.2

private def fourPartitionEquiv :
    (ℕ ⊕ {d : ℕ // ¬4 ∣ d}) ≃ ℕ where
  toFun s := match s with
    | Sum.inl n => 4 * n
    | Sum.inr d => d.1
  invFun d := if hd : 4 ∣ d then Sum.inl (d / 4) else Sum.inr ⟨d, hd⟩
  left_inv := by
    intro s
    rcases s with n | d
    · simp
    · simp [d.2]
  right_inv := by
    intro d
    simp only
    split_ifs with hd
    · exact Nat.mul_div_cancel' hd
    · rfl

private theorem summable_notFour_jacobiLambertTerms :
    Summable (fun d : {d : ℕ // ¬4 ∣ d} => jacobiLambertTerm d.1) := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro k
  apply summable_of_hasFiniteSupport
  let s : Finset {d : ℕ // ¬4 ∣ d} :=
    (Finset.Iic k).preimage Subtype.val Subtype.val_injective.injOn
  refine s.finite_toSet.subset ?_
  intro d hd
  simp only [Function.mem_support] at hd
  by_contra hmem
  have hdlarge : k < d.1 := by
    simpa [s] using hmem
  rw [coeff_jacobiLambertTerm] at hd
  by_cases hcond : 0 < k ∧ d.1 ∣ k
  · have := Nat.le_of_dvd hcond.1 hcond.2
    omega
  · simp [hcond] at hd

set_option maxHeartbeats 800000 in
theorem tsum_lambert_not_four_dvd :
    (∑' d : ℕ, if 4 ∣ d then 0 else jacobiLambertTerm d) =
      (∑' d : ℕ, jacobiLambertTerm d) -
        ∑' n : ℕ, jacobiLambertTerm (4 * n) := by
  have hmultiple :
      (∑' n : ℕ, jacobiLambertTerm (4 * n)) =
        ∑' d : {d : ℕ // 4 ∣ d}, jacobiLambertTerm d.1 := by
    exact fourMultipleEquiv.tsum_eq
      (fun d : {d : ℕ // 4 ∣ d} => jacobiLambertTerm d.1)
  have hmask :
      (∑' d : ℕ, if 4 ∣ d then 0 else jacobiLambertTerm d) =
        ∑' d : {d : ℕ // ¬4 ∣ d}, jacobiLambertTerm d.1 := by
    calc
      (∑' d : ℕ, if 4 ∣ d then 0 else jacobiLambertTerm d) =
          ∑' d : ℕ, {d : ℕ | ¬4 ∣ d}.indicator jacobiLambertTerm d := by
        apply tsum_congr
        intro d
        by_cases hd : 4 ∣ d <;> simp [hd]
      _ = ∑' d : {d : ℕ // ¬4 ∣ d}, jacobiLambertTerm d.1 :=
        (tsum_subtype {d : ℕ | ¬4 ∣ d} jacobiLambertTerm).symm
  have hpartition :
      (∑' d : {d : ℕ // 4 ∣ d}, jacobiLambertTerm d.1) +
          (∑' d : {d : ℕ // ¬4 ∣ d}, jacobiLambertTerm d.1) =
        ∑' d : ℕ, jacobiLambertTerm d := by
    have hsc : HasSum
        (fun d : {d : ℕ // ¬4 ∣ d} => jacobiLambertTerm d.1)
        (∑' d : {d : ℕ // ¬4 ∣ d}, jacobiLambertTerm d.1) :=
      summable_notFour_jacobiLambertTerms.hasSum
    have hwhole : HasSum jacobiLambertTerm
        ((∑' d : {d : ℕ // 4 ∣ d}, jacobiLambertTerm d.1) +
          ∑' d : {d : ℕ // ¬4 ∣ d}, jacobiLambertTerm d.1) := by
      let g : ℕ ⊕ {d : ℕ // ¬4 ∣ d} → PowerSeries ℚ := fun d =>
        match d with
        | Sum.inl n => jacobiLambertTerm (4 * n)
        | Sum.inr d => jacobiLambertTerm d.1
      have hleft : HasSum (g ∘ Sum.inl)
          (∑' n : ℕ, jacobiLambertTerm (4 * n)) := by
        change HasSum (fun n : ℕ => jacobiLambertTerm (4 * n))
          (∑' n : ℕ, jacobiLambertTerm (4 * n))
        exact summable_four_jacobiLambertTerms.hasSum
      have hright : HasSum (g ∘ Sum.inr)
          (∑' d : {d : ℕ // ¬4 ∣ d}, jacobiLambertTerm d.1) := by
        change HasSum
          (fun d : {d : ℕ // ¬4 ∣ d} => jacobiLambertTerm d.1)
          (∑' d : {d : ℕ // ¬4 ∣ d}, jacobiLambertTerm d.1)
        exact hsc
      apply fourPartitionEquiv.hasSum_iff.mp
      rw [← hmultiple]
      refine (hleft.sum hright).congr_fun ?_
      intro d
      rcases d with d | d
      · rfl
      · rfl
    exact hwhole.tsum_eq.symm
  rw [hmask, hmultiple]
  apply eq_sub_iff_add_eq.mpr
  simpa [add_comm] using hpartition

theorem tsum_lambert_even_sub_four_add_odd_eq_not_four_dvd :
    (∑' n : ℕ,
        (jacobiLambertTerm (2 * (n + 1)) -
          jacobiLambertTerm (4 * (n + 1)) +
          jacobiLambertTerm (2 * n + 1))) =
      ∑' d : ℕ, if 4 ∣ d then 0 else jacobiLambertTerm d := by
  rw [tsum_lambert_even_sub_four_add_odd,
    tsum_lambert_not_four_dvd]

theorem substNegX_logDerivativeCorrection_eq_jacobiLambertSeries :
    substNegX
        (1 + PowerSeries.C 4 * PowerSeries.X *
          jacobiLogDerivativeDifference) =
      jacobiLambertSeries := by
  simp only [map_add, map_one, map_mul, substNegX_C]
  rw [mul_assoc, ← map_mul,
    substNegX_X_mul_logDerivativeDifference,
    tsum_lambert_even_sub_four_add_odd_eq_not_four_dvd,
    jacobiLambertSeries]
  have hC : PowerSeries.C (8 : ℚ) =
      PowerSeries.C (4 : ℚ) * 2 := by
    change PowerSeries.C (8 : ℚ) =
      PowerSeries.C (4 : ℚ) * PowerSeries.C (2 : ℚ)
    rw [← map_mul]
    norm_num
  rw [hC]
  ring

/-- Rational Jacobi four-square identity. -/
theorem rationalIntegerThetaSeries_pow_four_eq_jacobiLambertSeries :
    rationalIntegerThetaSeries ^ 4 = jacobiLambertSeries := by
  have h := congrArg substNegX
    jacobiAlternatingThetaProduct_pow_four_eq_logDerivativeCorrection
  rw [map_pow, substNegX_jacobiAlternatingThetaProduct,
    substNegX_logDerivativeCorrection_eq_jacobiLambertSeries] at h
  rw [← jacobiThetaProduct_eq_rationalIntegerThetaSeries]
  exact h

/-- Jacobi's four-square theta identity over natural coefficients. -/
theorem integerThetaSeries_pow_four_eq_jacobiFourSquareSeries :
    integerThetaSeries ^ 4 = jacobiFourSquareSeries :=
  integerThetaSeries_pow_four_eq_jacobi_of_rational
    rationalIntegerThetaSeries_pow_four_eq_jacobiLambertSeries

end QEC.Coding.TannerLiftedProduct
