import QEC.Coding.ExpanderCodes.JacobiThetaProduct

/-!
# Series-side ingredients for Jacobi's four-square identity

This module packages the bilateral triangular-number series and the two
weighted series that occur in the parity reindexing step of Jacobi's proof.
The derivative identities are proved coefficientwise; no triple-product or
four-square identity is assumed.
-/

namespace QEC.Coding.TannerLiftedProduct

open Finset PowerSeries

/-- The finite set of integral solutions of `z² + z = n`. -/
noncomputable def integerTriangularRoots (n : ℕ) : Finset ℤ :=
  (Finset.Icc (-((n : ℤ)) - 1) (n : ℤ)).filter fun z =>
    z ^ 2 + z = n

theorem mem_integerTriangularRoots_iff (n : ℕ) (z : ℤ) :
    z ∈ integerTriangularRoots n ↔ z ^ 2 + z = n := by
  rw [integerTriangularRoots, Finset.mem_filter]
  refine and_iff_right_of_imp fun hz => ?_
  simp only [Finset.mem_Icc]
  have hn : (0 : ℤ) ≤ n := by positivity
  constructor
  · by_cases h : -1 ≤ z
    · omega
    · nlinarith [sq_nonneg (z + 1)]
  · by_cases h : z ≤ 0
    · omega
    · nlinarith [sq_nonneg z]

@[simp] theorem integerTriangularRoots_zero :
    integerTriangularRoots 0 = {-1, 0} := by
  ext z
  rw [mem_integerTriangularRoots_iff]
  constructor
  · intro hz
    have : z * (z + 1) = 0 := by
      calc
        z * (z + 1) = z ^ 2 + z := by ring
        _ = 0 := hz
    rcases mul_eq_zero.mp this with h | h
    · simp [h]
    · have : z = -1 := by omega
      simp [this]
  · intro hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> norm_num

/-- The bilateral triangular-number series `Σ_{z : ℤ} X^(z²+z)`,
represented by its finite coefficient fibers. -/
noncomputable def rationalBilateralTriangularSeries : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => (integerTriangularRoots n).card

@[simp] theorem coeff_rationalBilateralTriangularSeries (n : ℕ) :
    PowerSeries.coeff n rationalBilateralTriangularSeries =
      (integerTriangularRoots n).card := by
  simp [rationalBilateralTriangularSeries]

@[simp] theorem constantCoeff_rationalBilateralTriangularSeries :
    PowerSeries.constantCoeff rationalBilateralTriangularSeries = 2 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp

/-- The normalized triangular theta series `½ Σ_{z : ℤ} X^(z²+z)`.
This is the series denoted `γ` in the four-square proof. -/
noncomputable def rationalTriangularThetaSeries : ℚ⟦X⟧ :=
  PowerSeries.C (1 / 2 : ℚ) * rationalBilateralTriangularSeries

@[simp] theorem coeff_rationalTriangularThetaSeries (n : ℕ) :
    PowerSeries.coeff n rationalTriangularThetaSeries =
      (integerTriangularRoots n).card / 2 := by
  simp [rationalTriangularThetaSeries, div_eq_mul_inv, mul_comm]

@[simp] theorem constantCoeff_rationalTriangularThetaSeries :
    PowerSeries.constantCoeff rationalTriangularThetaSeries = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp

/-- Weight each triangular root by `(2z+1)²`. -/
noncomputable def jacobiWeightedTriangularSeries : ℚ⟦X⟧ :=
  PowerSeries.mk fun n =>
    ∑ z ∈ integerTriangularRoots n, (2 * (z : ℚ) + 1) ^ 2

@[simp] theorem coeff_jacobiWeightedTriangularSeries (n : ℕ) :
    PowerSeries.coeff n jacobiWeightedTriangularSeries =
      ∑ z ∈ integerTriangularRoots n, (2 * (z : ℚ) + 1) ^ 2 := by
  simp [jacobiWeightedTriangularSeries]

/-- Weight each square root by `(2z)²`. -/
noncomputable def jacobiWeightedSquareSeries : ℚ⟦X⟧ :=
  PowerSeries.mk fun n =>
    ∑ z ∈ integerSquareRoots n, (2 * (z : ℚ)) ^ 2

@[simp] theorem coeff_jacobiWeightedSquareSeries (n : ℕ) :
    PowerSeries.coeff n jacobiWeightedSquareSeries =
      ∑ z ∈ integerSquareRoots n, (2 * (z : ℚ)) ^ 2 := by
  simp [jacobiWeightedSquareSeries]

/-- Multiplication by `X` restores the degree dropped by differentiation. -/
theorem coeff_X_mul_derivative (f : ℚ⟦X⟧) (n : ℕ) :
    PowerSeries.coeff n
        (PowerSeries.X * PowerSeries.derivative ℚ f) =
      (n : ℚ) * PowerSeries.coeff n f := by
  cases n with
  | zero => simp
  | succ n =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
      push_cast
      ring

/-- The triangular weight identity
`(2z+1)² = 1 + 4(z²+z)` becomes a derivative identity of series. -/
theorem jacobiWeightedTriangularSeries_eq_derivative :
    jacobiWeightedTriangularSeries =
      rationalBilateralTriangularSeries +
        PowerSeries.C 4 *
          (PowerSeries.X *
            PowerSeries.derivative ℚ rationalBilateralTriangularSeries) := by
  ext n
  rw [coeff_jacobiWeightedTriangularSeries, map_add,
    PowerSeries.coeff_C_mul, coeff_X_mul_derivative,
    coeff_rationalBilateralTriangularSeries]
  calc
    ∑ z ∈ integerTriangularRoots n, (2 * (z : ℚ) + 1) ^ 2 =
        ∑ _z ∈ integerTriangularRoots n, (1 + 4 * n : ℚ) := by
      apply Finset.sum_congr rfl
      intro z hz
      have hz' := (mem_integerTriangularRoots_iff n z).mp hz
      have hzq : (z : ℚ) ^ 2 + z = n := by exact_mod_cast hz'
      nlinarith
    _ = (integerTriangularRoots n).card +
        4 * ((n : ℚ) * (integerTriangularRoots n).card) := by
      simp
      ring

/-- The square weight identity `(2z)² = 4z²` similarly says that the
weighted square series is `4X` times the derivative of the theta series. -/
theorem jacobiWeightedSquareSeries_eq_derivative :
    jacobiWeightedSquareSeries =
      PowerSeries.C 4 *
        (PowerSeries.X *
          PowerSeries.derivative ℚ rationalIntegerThetaSeries) := by
  ext n
  rw [coeff_jacobiWeightedSquareSeries, PowerSeries.coeff_C_mul,
    coeff_X_mul_derivative, coeff_rationalIntegerThetaSeries]
  calc
    ∑ z ∈ integerSquareRoots n, (2 * (z : ℚ)) ^ 2 =
        ∑ _z ∈ integerSquareRoots n, (4 * n : ℚ) := by
      apply Finset.sum_congr rfl
      intro z hz
      have hz' := (mem_integerSquareRoots_iff n z).mp hz
      have hzq : (z : ℚ) ^ 2 = n := by exact_mod_cast hz'
      nlinarith
    _ = 4 * ((n : ℚ) * (integerSquareRoots n).card) := by
      simp
      ring

end QEC.Coding.TannerLiftedProduct
