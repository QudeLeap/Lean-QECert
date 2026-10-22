import QEC.Coding.ExpanderCodes.FourSquareTheta
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Infinite products used in Jacobi's four-square identity

This module instantiates the coefficientwise topology on formal power series
for the even and odd factors that occur in Jacobi's theta-product identities.
It supplies the convergence and product-splitting layer needed by the formal
power-series proof of Jacobi's four-square theorem.
-/

namespace QEC.Coding.TannerLiftedProduct

open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology

/-- Formal differentiation is continuous for the coefficientwise topology on
rational power series. -/
theorem continuous_powerSeries_derivative :
    Continuous (PowerSeries.derivative ℚ : ℚ⟦X⟧ → ℚ⟦X⟧) := by
  rw [continuous_iff_continuousAt]
  intro f
  rw [ContinuousAt, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  simp only [PowerSeries.coeff_derivative]
  change ContinuousAt
    ((fun g : ℚ⟦X⟧ => PowerSeries.coeff (n + 1) g) *
      (fun _ => (n + 1 : ℚ))) f
  exact ((PowerSeries.WithPiTopology.continuous_coeff ℚ (n + 1)).mul
    continuous_const).continuousAt

/-- Consequently formal differentiation commutes with any summable family of
rational power series. -/
theorem derivative_tsum {I : Type*} (f : I → ℚ⟦X⟧) (hf : Summable f) :
    PowerSeries.derivative ℚ (∑' i, f i) =
      ∑' i, PowerSeries.derivative ℚ (f i) := by
  exact hf.map_tsum (PowerSeries.derivative ℚ) continuous_powerSeries_derivative

/-- Formal derivative of an even/odd minus factor. -/
theorem derivative_one_sub_X_pow (d : ℕ) :
    PowerSeries.derivative ℚ
        ((1 : ℚ⟦X⟧) - PowerSeries.X ^ d) =
      -(PowerSeries.C (d : ℚ) * PowerSeries.X ^ (d - 1)) := by
  rw [map_sub, PowerSeries.derivative_one, PowerSeries.derivative_pow,
    PowerSeries.derivative_X]
  simp

/-- Formal derivative of an even/odd plus factor. -/
theorem derivative_one_add_X_pow (d : ℕ) :
    PowerSeries.derivative ℚ
        ((1 : ℚ⟦X⟧) + PowerSeries.X ^ d) =
      PowerSeries.C (d : ℚ) * PowerSeries.X ^ (d - 1) := by
  rw [map_add, PowerSeries.derivative_one, PowerSeries.derivative_pow,
    PowerSeries.derivative_X]
  simp

/-- Finite product rule after supplying a logarithmic derivative for every
factor. This formulation avoids division and is the finite approximation used
for Jacobi's infinite products. -/
theorem derivative_finset_prod_eq_prod_mul_sum
    {I : Type*} [DecidableEq I] (f l : I → ℚ⟦X⟧)
    (hlog : ∀ i, f i * l i = PowerSeries.derivative ℚ (f i))
    (s : Finset I) :
    PowerSeries.derivative ℚ (∏ i ∈ s, f i) =
      (∏ i ∈ s, f i) * ∑ i ∈ s, l i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      rw [(PowerSeries.derivative ℚ).leibniz, ih, ← hlog a]
      simp only [smul_eq_mul]
      ring

/-- Infinite product rule in logarithmic-derivative form for the
coefficientwise topology on rational formal power series. -/
theorem derivative_tprod_eq_tprod_mul_tsum
    {I : Type*} (f l : I → ℚ⟦X⟧)
    (hf : Multipliable f) (hl : Summable l)
    (hlog : ∀ i, f i * l i = PowerSeries.derivative ℚ (f i)) :
    PowerSeries.derivative ℚ (∏' i, f i) =
      (∏' i, f i) * ∑' i, l i := by
  classical
  have hprod : Filter.Tendsto
      (fun s : Finset I => ∏ i ∈ s, f i) Filter.atTop
      (nhds (∏' i, f i)) := hf.hasProd
  have hsum : Filter.Tendsto
      (fun s : Finset I => ∑ i ∈ s, l i) Filter.atTop
      (nhds (∑' i, l i)) := hl.hasSum
  have hderiv : Filter.Tendsto
      (fun s : Finset I => PowerSeries.derivative ℚ (∏ i ∈ s, f i))
      Filter.atTop (nhds (PowerSeries.derivative ℚ (∏' i, f i))) :=
    (show Filter.Tendsto (PowerSeries.derivative ℚ)
        (nhds (∏' i, f i))
        (nhds (PowerSeries.derivative ℚ (∏' i, f i))) from
      continuous_powerSeries_derivative.continuousAt).comp hprod
  have hmul : Filter.Tendsto
      (fun s : Finset I => (∏ i ∈ s, f i) * ∑ i ∈ s, l i)
      Filter.atTop (nhds ((∏' i, f i) * ∑' i, l i)) :=
    hprod.mul hsum
  rw [Filter.tendsto_congr' <| Filter.Eventually.of_forall fun s =>
    derivative_finset_prod_eq_prod_mul_sum f l hlog s] at hderiv
  exact tendsto_nhds_unique hderiv hmul

/-- The exponents `2, 4, 6, ...` tend to infinity. -/
theorem tendsto_two_mul_succ_atTop :
    Filter.Tendsto (fun n : ℕ => 2 * (n + 1)) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  filter_upwards [Filter.eventually_ge_atTop b] with a ha
  omega

/-- The exponents `1, 3, 5, ...` tend to infinity. -/
theorem tendsto_two_mul_add_one_atTop :
    Filter.Tendsto (fun n : ℕ => 2 * n + 1) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  filter_upwards [Filter.eventually_ge_atTop b] with a ha
  omega

private theorem tendsto_order_X_pow_two_mul_succ :
    Filter.Tendsto
      (fun n : ℕ => ((PowerSeries.X : ℚ⟦X⟧) ^ (2 * (n + 1))).order)
      Filter.atTop (nhds ⊤) := by
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun k =>
    Filter.eventually_atTop.mpr ⟨k, fun n hn => ?_⟩
  rw [PowerSeries.order_X_pow]
  norm_cast
  omega

private theorem tendsto_order_X_pow_two_mul_add_one :
    Filter.Tendsto
      (fun n : ℕ => ((PowerSeries.X : ℚ⟦X⟧) ^ (2 * n + 1)).order)
      Filter.atTop (nhds ⊤) := by
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun k =>
    Filter.eventually_atTop.mpr ⟨k, fun n hn => ?_⟩
  rw [PowerSeries.order_X_pow]
  norm_cast
  omega

/-- The even factors `1 - X^(2n+2)` form a convergent formal product. -/
theorem multipliable_jacobi_even_sub :
    Multipliable (fun n : ℕ =>
      (1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) := by
  simpa only [sub_eq_add_neg] using
    PowerSeries.WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top ℚ
      (f := fun n : ℕ => -((PowerSeries.X : ℚ⟦X⟧) ^ (2 * (n + 1)))) <| by
        simpa only [PowerSeries.order_neg] using tendsto_order_X_pow_two_mul_succ

/-- The even factors `1 + X^(2n+2)` form a convergent formal product. -/
theorem multipliable_jacobi_even_add :
    Multipliable (fun n : ℕ =>
      (1 : ℚ⟦X⟧) + PowerSeries.X ^ (2 * (n + 1))) :=
  PowerSeries.WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top ℚ
    tendsto_order_X_pow_two_mul_succ

/-- The odd factors `1 + X^(2n+1)` form a convergent formal product. -/
theorem multipliable_jacobi_odd_add :
    Multipliable (fun n : ℕ =>
      (1 : ℚ⟦X⟧) + PowerSeries.X ^ (2 * n + 1)) :=
  PowerSeries.WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top ℚ
    tendsto_order_X_pow_two_mul_add_one

/-- The odd factors `1 - X^(2n+1)` form a convergent formal product. -/
theorem multipliable_jacobi_odd_sub :
    Multipliable (fun n : ℕ =>
      (1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * n + 1)) := by
  simpa only [sub_eq_add_neg] using
    PowerSeries.WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top ℚ
      (f := fun n : ℕ => -((PowerSeries.X : ℚ⟦X⟧) ^ (2 * n + 1))) <| by
        simpa only [PowerSeries.order_neg] using tendsto_order_X_pow_two_mul_add_one

/-- The product combining one even-minus factor and two odd-plus factors
exists coefficientwise. -/
theorem multipliable_jacobi_theta_factor :
    Multipliable (fun n : ℕ =>
      ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) *
        (1 + PowerSeries.X ^ (2 * n + 1)) ^ 2) :=
  multipliable_jacobi_even_sub.mul (multipliable_jacobi_odd_add.pow 2)

/-- Split the combined Jacobi theta product into its even and odd products. -/
theorem tprod_jacobi_theta_factor :
    (∏' n : ℕ,
      ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) *
        (1 + PowerSeries.X ^ (2 * n + 1)) ^ 2) =
      (∏' n : ℕ, ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1)))) *
        (∏' n : ℕ, ((1 : ℚ⟦X⟧) + PowerSeries.X ^ (2 * n + 1))) ^ 2 := by
  calc
    _ = (∏' n : ℕ, ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1)))) *
        (∏' n : ℕ, ((1 : ℚ⟦X⟧) + PowerSeries.X ^ (2 * n + 1)) ^ 2) :=
      by simpa using
        multipliable_jacobi_even_sub.tprod_mul (multipliable_jacobi_odd_add.pow 2)
    _ = _ := congrArg
      (fun z => (∏' n : ℕ,
        ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1)))) * z)
      (multipliable_jacobi_odd_add.tprod_pow 2)

/-- The rational Jacobi product whose coefficients should count integral
squares. -/
noncomputable def jacobiThetaProduct : ℚ⟦X⟧ :=
  ∏' n : ℕ,
    ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) *
      (1 + PowerSeries.X ^ (2 * n + 1)) ^ 2

@[simp] theorem constantCoeff_jacobiThetaProduct :
    PowerSeries.constantCoeff jacobiThetaProduct = 1 := by
  rw [jacobiThetaProduct]
  calc
    PowerSeries.constantCoeff
        (∏' n : ℕ,
          ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) *
            (1 + PowerSeries.X ^ (2 * n + 1)) ^ 2) =
        ∏' n : ℕ,
          PowerSeries.constantCoeff
            (((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) *
              (1 + PowerSeries.X ^ (2 * n + 1)) ^ 2) :=
      multipliable_jacobi_theta_factor.map_tprod
        (PowerSeries.constantCoeff (R := ℚ))
        (PowerSeries.WithPiTopology.continuous_constantCoeff ℚ)
    _ = 1 := by simp

theorem isUnit_jacobiThetaProduct : IsUnit jacobiThetaProduct := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp

/-- The integer theta series after coefficient extension to the rationals. -/
noncomputable def rationalIntegerThetaSeries : ℚ⟦X⟧ :=
  PowerSeries.map (Nat.castRingHom ℚ) integerThetaSeries

@[simp] theorem coeff_rationalIntegerThetaSeries (n : ℕ) :
    PowerSeries.coeff n rationalIntegerThetaSeries =
      (integerSquareRoots n).card := by
  simp [rationalIntegerThetaSeries]

@[simp] theorem constantCoeff_rationalIntegerThetaSeries :
    PowerSeries.constantCoeff rationalIntegerThetaSeries = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp

theorem isUnit_rationalIntegerThetaSeries :
    IsUnit rationalIntegerThetaSeries := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp

/-- The sixth power of Euler's product, denoted `α` in the standard
formal-power-series proof of Jacobi's four-square theorem. -/
noncomputable def jacobiEulerSixProduct : ℚ⟦X⟧ :=
  ∏' n : ℕ, ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (n + 1)) ^ 6

theorem multipliable_jacobiEulerSixFactor :
    Multipliable (fun n : ℕ =>
      ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (n + 1)) ^ 6) :=
  (PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℚ).pow 6

/-- Euler's sixth-power product is the sixth power of Euler's product. -/
theorem jacobiEulerSixProduct_eq_tprod_pow :
    jacobiEulerSixProduct =
      (∏' n : ℕ,
        ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (n + 1))) ^ 6 := by
  rw [jacobiEulerSixProduct]
  exact (PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℚ).tprod_pow 6

@[simp] theorem constantCoeff_jacobiEulerSixProduct :
    PowerSeries.constantCoeff jacobiEulerSixProduct = 1 := by
  rw [jacobiEulerSixProduct]
  calc
    PowerSeries.constantCoeff
        (∏' n : ℕ, ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (n + 1)) ^ 6) =
      ∏' n : ℕ, PowerSeries.constantCoeff
        (((1 : ℚ⟦X⟧) - PowerSeries.X ^ (n + 1)) ^ 6) :=
      multipliable_jacobiEulerSixFactor.map_tprod
        (PowerSeries.constantCoeff (R := ℚ))
        (PowerSeries.WithPiTopology.continuous_constantCoeff ℚ)
    _ = 1 := by simp

theorem isUnit_jacobiEulerSixProduct :
    IsUnit jacobiEulerSixProduct := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp

/-- The square of Euler's product. -/
noncomputable def jacobiEulerSquareProduct : ℚ⟦X⟧ :=
  ∏' n : ℕ, ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (n + 1)) ^ 2

theorem multipliable_jacobiEulerSquareFactor :
    Multipliable (fun n : ℕ =>
      ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (n + 1)) ^ 2) :=
  (PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℚ).pow 2

/-- Euler's sixth-power product is the cube of its square product. -/
theorem jacobiEulerSixProduct_eq_squareProduct_cubed :
    jacobiEulerSixProduct = jacobiEulerSquareProduct ^ 3 := by
  rw [jacobiEulerSixProduct, jacobiEulerSquareProduct,
    ← multipliable_jacobiEulerSquareFactor.tprod_pow]
  apply tprod_congr
  intro n
  ring

@[simp] theorem constantCoeff_jacobiEulerSquareProduct :
    PowerSeries.constantCoeff jacobiEulerSquareProduct = 1 := by
  rw [jacobiEulerSquareProduct]
  calc
    PowerSeries.constantCoeff
        (∏' n : ℕ, ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (n + 1)) ^ 2) =
      ∏' n : ℕ, PowerSeries.constantCoeff
        (((1 : ℚ⟦X⟧) - PowerSeries.X ^ (n + 1)) ^ 2) :=
      multipliable_jacobiEulerSquareFactor.map_tprod
        (PowerSeries.constantCoeff (R := ℚ))
        (PowerSeries.WithPiTopology.continuous_constantCoeff ℚ)
    _ = 1 := by simp

theorem isUnit_jacobiEulerSquareProduct :
    IsUnit jacobiEulerSquareProduct := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp

/-- The product over the positive even minus factors. -/
noncomputable def jacobiEvenMinusProduct : ℚ⟦X⟧ :=
  ∏' n : ℕ, ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1)))

/-- The square product over the positive odd minus factors. -/
noncomputable def jacobiOddMinusSquareProduct : ℚ⟦X⟧ :=
  ∏' n : ℕ, ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * n + 1)) ^ 2

theorem multipliable_jacobiOddMinusSquareFactor :
    Multipliable (fun n : ℕ =>
      ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * n + 1)) ^ 2) :=
  multipliable_jacobi_odd_sub.pow 2

/-- The product obtained from the theta product by replacing `X` by `-X`.
Its series expansion is the alternating integer theta series once the
specialized Jacobi triple product is installed. -/
noncomputable def jacobiAlternatingThetaProduct : ℚ⟦X⟧ :=
  ∏' n : ℕ,
    ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) *
      (1 - PowerSeries.X ^ (2 * n + 1)) ^ 2

theorem multipliable_jacobiAlternatingThetaFactor :
    Multipliable (fun n : ℕ =>
      ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) *
        (1 - PowerSeries.X ^ (2 * n + 1)) ^ 2) :=
  multipliable_jacobi_even_sub.mul (multipliable_jacobi_odd_sub.pow 2)

theorem jacobiAlternatingThetaProduct_eq_even_mul_oddSquare :
    jacobiAlternatingThetaProduct =
      jacobiEvenMinusProduct * jacobiOddMinusSquareProduct := by
  rw [jacobiAlternatingThetaProduct, jacobiEvenMinusProduct,
    jacobiOddMinusSquareProduct]
  exact multipliable_jacobi_even_sub.tprod_mul
    multipliable_jacobiOddMinusSquareFactor

/-- Splitting all positive exponents into odd and even ones reconstructs
Euler's square product. -/
theorem jacobiOddMinusSquareProduct_mul_evenMinusSquareProduct :
    jacobiOddMinusSquareProduct *
      (∏' n : ℕ,
        ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) ^ 2) =
      jacobiEulerSquareProduct := by
  rw [jacobiOddMinusSquareProduct, jacobiEulerSquareProduct]
  let f : ℕ → ℚ⟦X⟧ := fun n =>
    ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (n + 1)) ^ 2
  have he : (fun k => f (2 * k)) = fun n =>
      ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * n + 1)) ^ 2 := by
    funext n
    rfl
  have ho : (fun k => f (2 * k + 1)) = fun n =>
      ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) ^ 2 := by
    funext n
    simp only [f]
    congr 3
  have hEven : Multipliable (fun k => f (2 * k)) := by
    rw [he]
    exact multipliable_jacobi_odd_sub.pow 2
  have hOdd : Multipliable (fun k => f (2 * k + 1)) := by
    rw [ho]
    exact multipliable_jacobi_even_sub.pow 2
  have h := tprod_even_mul_odd (f := f) hEven hOdd
  rw [he, ho] at h
  exact h

/-- The square product over the even minus factors. -/
noncomputable def jacobiEvenMinusSquareProduct : ℚ⟦X⟧ :=
  ∏' n : ℕ,
    ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) ^ 2

theorem multipliable_jacobiEvenMinusSquareFactor :
    Multipliable (fun n : ℕ =>
      ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) ^ 2) :=
  multipliable_jacobi_even_sub.pow 2

theorem jacobiEvenMinusSquareProduct_eq_evenMinusProduct_sq :
    jacobiEvenMinusSquareProduct = jacobiEvenMinusProduct ^ 2 := by
  rw [jacobiEvenMinusSquareProduct, jacobiEvenMinusProduct]
  exact multipliable_jacobi_even_sub.tprod_pow 2

/-- The alternating theta product times its even-minus denominator is
Euler's square product. This is the denominator-free form of the usual
specialized Jacobi product quotient. -/
theorem jacobiAlternatingThetaProduct_mul_evenMinusProduct :
    jacobiAlternatingThetaProduct * jacobiEvenMinusProduct =
      jacobiEulerSquareProduct := by
  rw [jacobiAlternatingThetaProduct_eq_even_mul_oddSquare]
  calc
    (jacobiEvenMinusProduct * jacobiOddMinusSquareProduct) *
        jacobiEvenMinusProduct =
      jacobiOddMinusSquareProduct * jacobiEvenMinusProduct ^ 2 := by ring
    _ = jacobiOddMinusSquareProduct * jacobiEvenMinusSquareProduct := by
      rw [jacobiEvenMinusSquareProduct_eq_evenMinusProduct_sq]
    _ = jacobiEulerSquareProduct :=
      jacobiOddMinusSquareProduct_mul_evenMinusSquareProduct

/-- The square product over all positive plus factors. -/
noncomputable def jacobiAllPlusSquareProduct : ℚ⟦X⟧ :=
  ∏' n : ℕ,
    ((1 : ℚ⟦X⟧) + PowerSeries.X ^ (n + 1)) ^ 2

theorem multipliable_jacobiAllPlusSquareFactor :
    Multipliable (fun n : ℕ =>
      ((1 : ℚ⟦X⟧) + PowerSeries.X ^ (n + 1)) ^ 2) := by
  let f : ℕ → ℚ⟦X⟧ := fun n =>
    ((1 : ℚ⟦X⟧) + PowerSeries.X ^ (n + 1)) ^ 2
  change Multipliable f
  apply Multipliable.even_mul_odd (f := f)
  · simpa only [f] using multipliable_jacobi_odd_add.pow 2
  · convert multipliable_jacobi_even_add.pow 2 using 1
    funext n
    simp only [f]
    congr 3

/-- Factoring `1 - X^(2k)` as `(1 - X^k)(1 + X^k)` identifies
the even-minus square product with the product of the two full square
products. -/
theorem jacobiEvenMinusSquareProduct_eq_eulerSquare_mul_allPlusSquare :
    jacobiEvenMinusSquareProduct =
      jacobiEulerSquareProduct * jacobiAllPlusSquareProduct := by
  rw [jacobiEvenMinusSquareProduct, jacobiEulerSquareProduct,
    jacobiAllPlusSquareProduct,
    ← multipliable_jacobiEulerSquareFactor.tprod_mul
      multipliable_jacobiAllPlusSquareFactor]
  apply tprod_congr
  intro n
  rw [show 2 * (n + 1) = (n + 1) * 2 by omega, pow_mul]
  ring

/-- Squaring the alternating theta product removes the even-factor
denominator: `δ² A₊ = E²` in the standard product notation. -/
theorem jacobiAlternatingThetaProduct_sq_mul_allPlusSquare :
    jacobiAlternatingThetaProduct ^ 2 * jacobiAllPlusSquareProduct =
      jacobiEulerSquareProduct := by
  apply isUnit_jacobiEulerSquareProduct.mul_left_cancel
  calc
    jacobiEulerSquareProduct *
        (jacobiAlternatingThetaProduct ^ 2 *
          jacobiAllPlusSquareProduct) =
      jacobiAlternatingThetaProduct ^ 2 *
        (jacobiEulerSquareProduct * jacobiAllPlusSquareProduct) := by ring
    _ = jacobiAlternatingThetaProduct ^ 2 *
        jacobiEvenMinusSquareProduct := by
      rw [jacobiEvenMinusSquareProduct_eq_eulerSquare_mul_allPlusSquare]
    _ = (jacobiAlternatingThetaProduct * jacobiEvenMinusProduct) ^ 2 := by
      rw [jacobiEvenMinusSquareProduct_eq_evenMinusProduct_sq]
      ring
    _ = jacobiEulerSquareProduct ^ 2 := by
      rw [jacobiAlternatingThetaProduct_mul_evenMinusProduct]
    _ = jacobiEulerSquareProduct * jacobiEulerSquareProduct := by ring

/-- Splitting positive integers into odd and even exponents splits the full
plus-square product into the two Jacobi subsequences. -/
theorem tprod_jacobi_odd_even_add_square :
    (∏' n : ℕ,
        ((1 : ℚ⟦X⟧) + PowerSeries.X ^ (2 * n + 1)) ^ 2) *
      (∏' n : ℕ,
        ((1 : ℚ⟦X⟧) + PowerSeries.X ^ (2 * (n + 1))) ^ 2) =
      jacobiAllPlusSquareProduct := by
  rw [jacobiAllPlusSquareProduct]
  let f : ℕ → ℚ⟦X⟧ := fun n =>
    ((1 : ℚ⟦X⟧) + PowerSeries.X ^ (n + 1)) ^ 2
  have he : (fun k => f (2 * k)) = fun n =>
      ((1 : ℚ⟦X⟧) + PowerSeries.X ^ (2 * n + 1)) ^ 2 := by
    funext n
    rfl
  have ho : (fun k => f (2 * k + 1)) = fun n =>
      ((1 : ℚ⟦X⟧) + PowerSeries.X ^ (2 * (n + 1))) ^ 2 := by
    funext n
    simp only [f]
    congr 3
  have hEven : Multipliable (fun k => f (2 * k)) := by
    rw [he]
    exact multipliable_jacobi_odd_add.pow 2
  have hOdd : Multipliable (fun k => f (2 * k + 1)) := by
    rw [ho]
    exact multipliable_jacobi_even_add.pow 2
  have h := tprod_even_mul_odd (f := f) hEven hOdd
  rw [he, ho] at h
  exact h

/-- The product combining one even-minus factor and two even-plus factors
exists coefficientwise. -/
theorem multipliable_jacobi_triangular_factor :
    Multipliable (fun n : ℕ =>
      ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) *
        (1 + PowerSeries.X ^ (2 * (n + 1))) ^ 2) :=
  multipliable_jacobi_even_sub.mul (multipliable_jacobi_even_add.pow 2)

/-- Split the combined triangular-number product into its two standard
factors. -/
theorem tprod_jacobi_triangular_factor :
    (∏' n : ℕ,
      ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) *
        (1 + PowerSeries.X ^ (2 * (n + 1))) ^ 2) =
      (∏' n : ℕ, ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1)))) *
        (∏' n : ℕ, ((1 : ℚ⟦X⟧) + PowerSeries.X ^ (2 * (n + 1)))) ^ 2 := by
  calc
    _ = (∏' n : ℕ, ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1)))) *
        (∏' n : ℕ, ((1 : ℚ⟦X⟧) + PowerSeries.X ^ (2 * (n + 1))) ^ 2) :=
      by simpa using
        multipliable_jacobi_even_sub.tprod_mul (multipliable_jacobi_even_add.pow 2)
    _ = _ := congrArg
      (fun z => (∏' n : ℕ,
        ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1)))) * z)
      (multipliable_jacobi_even_add.tprod_pow 2)

/-- The second Jacobi product, whose coefficients enumerate twice the
triangular numbers. -/
noncomputable def jacobiTriangularProduct : ℚ⟦X⟧ :=
  ∏' n : ℕ,
    ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) *
      (1 + PowerSeries.X ^ (2 * (n + 1))) ^ 2

@[simp] theorem constantCoeff_jacobiTriangularProduct :
    PowerSeries.constantCoeff jacobiTriangularProduct = 1 := by
  rw [jacobiTriangularProduct]
  calc
    PowerSeries.constantCoeff
        (∏' n : ℕ,
          ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) *
            (1 + PowerSeries.X ^ (2 * (n + 1))) ^ 2) =
        ∏' n : ℕ,
          PowerSeries.constantCoeff
            (((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) *
              (1 + PowerSeries.X ^ (2 * (n + 1))) ^ 2) :=
      multipliable_jacobi_triangular_factor.map_tprod
        (PowerSeries.constantCoeff (R := ℚ))
        (PowerSeries.WithPiTopology.continuous_constantCoeff ℚ)
    _ = 1 := by simp

theorem isUnit_jacobiTriangularProduct :
    IsUnit jacobiTriangularProduct := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp

/-- Product algebra for the two Jacobi products: their common even-minus
factor squares, while their odd/even plus factors merge into all positive
exponents. -/
theorem jacobiThetaProduct_mul_jacobiTriangularProduct :
    jacobiThetaProduct * jacobiTriangularProduct =
      jacobiEvenMinusSquareProduct * jacobiAllPlusSquareProduct := by
  rw [jacobiThetaProduct, jacobiTriangularProduct,
    jacobiEvenMinusSquareProduct]
  rw [← multipliable_jacobi_theta_factor.tprod_mul
    multipliable_jacobi_triangular_factor]
  calc
    (∏' n : ℕ,
        (((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) *
          (1 + PowerSeries.X ^ (2 * n + 1)) ^ 2) *
        (((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) *
          (1 + PowerSeries.X ^ (2 * (n + 1))) ^ 2)) =
      ∏' n : ℕ,
        (((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) ^ 2 *
          (((1 : ℚ⟦X⟧) + PowerSeries.X ^ (2 * n + 1)) ^ 2 *
            ((1 : ℚ⟦X⟧) + PowerSeries.X ^ (2 * (n + 1))) ^ 2)) :=
      tprod_congr fun n => by ring
    _ = (∏' n : ℕ,
          ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) ^ 2) *
        (∏' n : ℕ,
          ((1 : ℚ⟦X⟧) + PowerSeries.X ^ (2 * n + 1)) ^ 2 *
            ((1 : ℚ⟦X⟧) + PowerSeries.X ^ (2 * (n + 1))) ^ 2) :=
      multipliable_jacobiEvenMinusSquareFactor.tprod_mul
        ((multipliable_jacobi_odd_add.pow 2).mul
          (multipliable_jacobi_even_add.pow 2))
    _ = (∏' n : ℕ,
          ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) ^ 2) *
        ((∏' n : ℕ,
            ((1 : ℚ⟦X⟧) + PowerSeries.X ^ (2 * n + 1)) ^ 2) *
          (∏' n : ℕ,
            ((1 : ℚ⟦X⟧) + PowerSeries.X ^ (2 * (n + 1))) ^ 2)) := by
      rw [(multipliable_jacobi_odd_add.pow 2).tprod_mul
        (multipliable_jacobi_even_add.pow 2)]
    _ = _ := by rw [tprod_jacobi_odd_even_add_square]

/-- Sambale's product simplification for `βγ`: after the even/odd split,
the two Jacobi products become Euler's square product times the square of
the full plus-square product. -/
theorem jacobiThetaProduct_mul_jacobiTriangularProduct_eq_eulerSquare :
    jacobiThetaProduct * jacobiTriangularProduct =
      jacobiEulerSquareProduct * jacobiAllPlusSquareProduct ^ 2 := by
  rw [jacobiThetaProduct_mul_jacobiTriangularProduct,
    jacobiEvenMinusSquareProduct_eq_eulerSquare_mul_allPlusSquare]
  ring

/-- Product-side closure used in Jacobi's four-square proof: the fourth
power of the alternating theta product times `βγ` is Euler's sixth-power
product. No series identity is assumed here. -/
theorem jacobiAlternatingThetaProduct_pow_four_mul_theta_triangular :
    jacobiAlternatingThetaProduct ^ 4 *
        (jacobiThetaProduct * jacobiTriangularProduct) =
      jacobiEulerSixProduct := by
  rw [jacobiThetaProduct_mul_jacobiTriangularProduct_eq_eulerSquare,
    jacobiEulerSixProduct_eq_squareProduct_cubed]
  calc
    jacobiAlternatingThetaProduct ^ 4 *
        (jacobiEulerSquareProduct * jacobiAllPlusSquareProduct ^ 2) =
      jacobiEulerSquareProduct *
        (jacobiAlternatingThetaProduct ^ 2 *
          jacobiAllPlusSquareProduct) ^ 2 := by ring
    _ = jacobiEulerSquareProduct * jacobiEulerSquareProduct ^ 2 := by
      rw [jacobiAlternatingThetaProduct_sq_mul_allPlusSquare]
    _ = jacobiEulerSquareProduct ^ 3 := by ring

end QEC.Coding.TannerLiftedProduct
