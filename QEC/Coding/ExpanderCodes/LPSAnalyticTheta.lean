import QEC.Coding.ExpanderCodes.LPSTraceTheta
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# Analytic realization of the LPS formal theta series

The formal theta coefficient counts signed integral square roots.  This
module begins the bridge to Mathlib's analytic Jacobi theta function by
establishing absolute convergence of its coefficient series in the open
unit disc.  Modular transformation laws and coefficient estimates require
additional work.
-/

namespace QEC.Coding.TannerLiftedProduct

open scoped UpperHalfPlane Manifold

/-- A uniformly bounded natural coefficient sequence has a convergent
complex generating series in the open unit disc. -/
theorem summable_norm_theta_coeff_mul_pow_of_le_two
    (S : PowerSeries ℕ)
    (hCoeff : ∀ n : ℕ, PowerSeries.coeff n S ≤ 2)
    (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ =>
      ‖((PowerSeries.coeff n S : ℕ) : ℂ) * z ^ n‖) := by
  have hGeom : Summable (fun n : ℕ => (‖z‖ : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by simpa using hz)
  apply (hGeom.mul_left 2).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  simpa only [norm_mul, norm_pow, Complex.norm_natCast] using
    mul_le_mul_of_nonneg_right
      (show ((PowerSeries.coeff n S : ℕ) : ℝ) ≤ 2 by exact_mod_cast hCoeff n)
      (pow_nonneg (norm_nonneg z) _)

/-- The formal integer theta series converges absolutely on the open unit
disc. -/
theorem summable_norm_coeff_integerThetaSeries_mul_pow
    (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ =>
      ‖((PowerSeries.coeff n integerThetaSeries : ℕ) : ℂ) * z ^ n‖) := by
  apply summable_norm_theta_coeff_mul_pow_of_le_two integerThetaSeries _ z hz
  intro n
  rw [coeff_integerThetaSeries_eq_ite]
  split_ifs <;> omega

/-- The scaled theta series has the same uniform coefficient bound and
therefore converges throughout the open unit disc. -/
theorem summable_norm_coeff_scaledIntegerThetaSeries_mul_pow
    (m : ℕ) (hm : 0 < m) (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ =>
      ‖((PowerSeries.coeff n (scaledIntegerThetaSeries m) : ℕ) : ℂ) * z ^ n‖) := by
  apply summable_norm_theta_coeff_mul_pow_of_le_two (scaledIntegerThetaSeries m) _ z hz
  intro n
  rw [coeff_scaledIntegerThetaSeries]
  by_cases hdiv : m ^ 2 ∣ n
  · rw [scaledIntegerSquareRoots_eq_of_dvd hm hdiv, card_integerSquareRoots]
    split_ifs <;> omega
  · rw [scaledIntegerSquareRoots_eq_empty_of_not_dvd hm hdiv]
    simp

/-- The theta nome `exp(πiτ)` is inside the open unit disc whenever
`τ` lies in the upper half-plane. -/
theorem norm_exp_pi_I_mul_lt_one (τ : ℂ) (hτ : 0 < τ.im) :
    ‖Complex.exp (Real.pi * Complex.I * τ)‖ < 1 := by
  rw [Complex.norm_exp]
  have hRe : (Real.pi * Complex.I * τ).re = -Real.pi * τ.im := by
    simp [Complex.mul_re]
  rw [hRe]
  exact Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos
    (neg_lt_zero.mpr Real.pi_pos) hτ)

/-- Mathlib's analytic Jacobi theta summand is absolutely summable in the
upper half-plane, in the exact exponent convention of the formal series. -/
theorem summable_exp_integer_square
    (τ : ℂ) (hτ : 0 < τ.im) :
    Summable (fun z : ℤ =>
      Complex.exp (Real.pi * Complex.I * (z : ℂ) ^ 2 * τ)) := by
  simpa [jacobiTheta₂_term] using
    (hasSum_jacobiTheta₂_term 0 hτ).summable

/-- The fibre of the map `z ↦ |z|²` is exactly the finite set used by the
formal theta coefficient. -/
theorem natAbs_sq_eq_iff_mem_integerSquareRoots
    (n : ℕ) (z : ℤ) :
    z.natAbs ^ 2 = n ↔ z ∈ integerSquareRoots n := by
  rw [mem_integerSquareRoots_iff]
  constructor
  · intro h
    have h' := congrArg (fun x : ℕ => (x : ℤ)) h
    simpa only [Nat.cast_pow, Int.natCast_natAbs, sq_abs] using h'
  · intro h
    apply Nat.cast_injective (R := ℤ)
    simpa only [Nat.cast_pow, Int.natCast_natAbs, sq_abs] using h

noncomputable instance integerSquareFibreFintype (n : ℕ) :
    Fintype {z : ℤ // z.natAbs ^ 2 = n} :=
  Fintype.ofEquiv {z : ℤ // z ∈ integerSquareRoots n}
    (Equiv.subtypeEquivRight
      (natAbs_sq_eq_iff_mem_integerSquareRoots n)).symm

/-- The analytic Jacobi theta function is the convergent evaluation of the
formal integer theta coefficient sequence at `exp(πiτ)`. -/
theorem tsum_coeff_integerThetaSeries_eq_jacobiTheta
    (τ : ℂ) (hτ : 0 < τ.im) :
    (∑' n : ℕ,
      ((PowerSeries.coeff n integerThetaSeries : ℕ) : ℂ) *
        Complex.exp (Real.pi * Complex.I * τ) ^ n) = jacobiTheta τ := by
  let q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
  have hFiber := (summable_exp_integer_square τ hτ).hasSum.tsum_fiberwise
    (fun z : ℤ => z.natAbs ^ 2)
  change HasSum (fun n : ℕ =>
    ∑' z : {z : ℤ | z.natAbs ^ 2 = n},
      Complex.exp (Real.pi * Complex.I * (z.1 : ℂ) ^ 2 * τ))
    (∑' z : ℤ, Complex.exp (Real.pi * Complex.I * (z : ℂ) ^ 2 * τ)) at hFiber
  have hTerm (n : ℕ) :
      (∑' z : {z : ℤ | z.natAbs ^ 2 = n},
        Complex.exp (Real.pi * Complex.I * (z.1 : ℂ) ^ 2 * τ)) =
      ((PowerSeries.coeff n integerThetaSeries : ℕ) : ℂ) * q ^ n := by
    letI : Fintype {z : ℤ | z.natAbs ^ 2 = n} := integerSquareFibreFintype n
    have hExp (z : {z : ℤ | z.natAbs ^ 2 = n}) :
        Complex.exp (Real.pi * Complex.I * (z.1 : ℂ) ^ 2 * τ) = q ^ n := by
      have hs : ((z.1.natAbs ^ 2 : ℕ) : ℂ) = (z.1 : ℂ) ^ 2 := by
        have hsInt : ((z.1.natAbs ^ 2 : ℕ) : ℤ) = z.1 ^ 2 := by
          simp [sq_abs]
        calc
          ((z.1.natAbs ^ 2 : ℕ) : ℂ) =
              (((z.1.natAbs ^ 2 : ℕ) : ℤ) : ℂ) := by norm_cast
          _ = ((z.1 ^ 2 : ℤ) : ℂ) :=
            congrArg (fun x : ℤ => (x : ℂ)) hsInt
          _ = (z.1 : ℂ) ^ 2 := by norm_cast
      calc
        Complex.exp (Real.pi * Complex.I * (z.1 : ℂ) ^ 2 * τ) =
            Complex.exp (((z.1.natAbs ^ 2 : ℕ) : ℂ) *
              (Real.pi * Complex.I * τ)) := by
          congr 1
          rw [hs]
          ring
        _ = Complex.exp ((n : ℂ) * (Real.pi * Complex.I * τ)) := by
          rw [z.2]
        _ = q ^ n := by simpa [q] using
          (Complex.exp_nat_mul (Real.pi * Complex.I * τ) n)
    rw [tsum_fintype]
    simp_rw [hExp]
    have hCard : Fintype.card {z : ℤ | z.natAbs ^ 2 = n} =
        (integerSquareRoots n).card := by
      calc
        Fintype.card {z : ℤ | z.natAbs ^ 2 = n} =
            Fintype.card {z : ℤ // z ∈ integerSquareRoots n} :=
          Fintype.card_congr
            (Equiv.subtypeEquivRight
              (natAbs_sq_eq_iff_mem_integerSquareRoots n))
        _ = (integerSquareRoots n).card := Fintype.card_coe _
    simp [hCard, coeff_integerThetaSeries]
  have hEq := hFiber.tsum_eq
  simp_rw [hTerm] at hEq
  simpa [jacobiTheta, q] using hEq

/-- The finite fibre for the scaled square `m²z²` is the coefficient set
of the scaled formal theta series. -/
theorem scaledNatAbs_sq_eq_iff_mem_scaledIntegerSquareRoots
    (m n : ℕ) (hm : 0 < m) (z : ℤ) :
    m ^ 2 * z.natAbs ^ 2 = n ↔ z ∈ scaledIntegerSquareRoots m n := by
  rw [mem_scaledIntegerSquareRoots_iff hm]
  constructor
  · intro h
    have h' := congrArg (fun x : ℕ => (x : ℤ)) h
    simpa only [Nat.cast_mul, Nat.cast_pow, Int.natCast_natAbs, sq_abs] using h'
  · intro h
    apply Nat.cast_injective (R := ℤ)
    simpa only [Nat.cast_mul, Nat.cast_pow, Int.natCast_natAbs, sq_abs] using h

@[instance_reducible] private noncomputable def scaledIntegerSquareFibreFintype
    (m n : ℕ) (hm : 0 < m) :
    Fintype {z : ℤ // m ^ 2 * z.natAbs ^ 2 = n} :=
  Fintype.ofEquiv {z : ℤ // z ∈ scaledIntegerSquareRoots m n}
    (Equiv.subtypeEquivRight
      (scaledNatAbs_sq_eq_iff_mem_scaledIntegerSquareRoots m n hm)).symm

/-- The scaled formal theta coefficients evaluate to the Jacobi theta
function at the correspondingly scaled upper-half-plane argument. -/
theorem tsum_coeff_scaledIntegerThetaSeries_eq_jacobiTheta
    (m : ℕ) (hm : 0 < m) (τ : ℂ) (hτ : 0 < τ.im) :
    (∑' n : ℕ,
      ((PowerSeries.coeff n (scaledIntegerThetaSeries m) : ℕ) : ℂ) *
        Complex.exp (Real.pi * Complex.I * τ) ^ n) =
      jacobiTheta ((m ^ 2 : ℕ) * τ) := by
  let q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
  have hScaledIm : 0 < (((m ^ 2 : ℕ) : ℂ) * τ).im := by
    rw [Complex.mul_im]
    simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    exact mul_pos (by exact_mod_cast pow_pos hm 2) hτ
  have hSummable : Summable (fun z : ℤ =>
      Complex.exp (Real.pi * Complex.I *
        (((m : ℂ) ^ 2) * (z : ℂ) ^ 2) * τ)) := by
    convert summable_exp_integer_square (((m ^ 2 : ℕ) : ℂ) * τ) hScaledIm using 1
    ext z
    congr 1
    push_cast
    ring
  have hFiber := hSummable.hasSum.tsum_fiberwise
    (fun z : ℤ => m ^ 2 * z.natAbs ^ 2)
  change HasSum (fun n : ℕ =>
    ∑' z : {z : ℤ | m ^ 2 * z.natAbs ^ 2 = n},
      Complex.exp (Real.pi * Complex.I *
        ((m : ℂ) ^ 2 * (z.1 : ℂ) ^ 2) * τ))
    (∑' z : ℤ,
      Complex.exp (Real.pi * Complex.I *
        ((m : ℂ) ^ 2 * (z : ℂ) ^ 2) * τ)) at hFiber
  have hTerm (n : ℕ) :
      (∑' z : {z : ℤ | m ^ 2 * z.natAbs ^ 2 = n},
        Complex.exp (Real.pi * Complex.I *
          ((m : ℂ) ^ 2 * (z.1 : ℂ) ^ 2) * τ)) =
      ((PowerSeries.coeff n (scaledIntegerThetaSeries m) : ℕ) : ℂ) * q ^ n := by
    letI : Fintype {z : ℤ | m ^ 2 * z.natAbs ^ 2 = n} :=
      scaledIntegerSquareFibreFintype m n hm
    have hExp (z : {z : ℤ | m ^ 2 * z.natAbs ^ 2 = n}) :
        Complex.exp (Real.pi * Complex.I *
          ((m : ℂ) ^ 2 * (z.1 : ℂ) ^ 2) * τ) = q ^ n := by
      have hsInt : ((z.1.natAbs ^ 2 : ℕ) : ℤ) = z.1 ^ 2 := by
        simp [sq_abs]
      have hsComplex : ((z.1.natAbs ^ 2 : ℕ) : ℂ) = (z.1 : ℂ) ^ 2 := by
        calc
          ((z.1.natAbs ^ 2 : ℕ) : ℂ) =
              (((z.1.natAbs ^ 2 : ℕ) : ℤ) : ℂ) := by norm_cast
          _ = ((z.1 ^ 2 : ℤ) : ℂ) := congrArg (fun x : ℤ => (x : ℂ)) hsInt
          _ = (z.1 : ℂ) ^ 2 := by norm_cast
      have hs : ((m ^ 2 * z.1.natAbs ^ 2 : ℕ) : ℂ) =
          (m : ℂ) ^ 2 * (z.1 : ℂ) ^ 2 := by
        calc
          ((m ^ 2 * z.1.natAbs ^ 2 : ℕ) : ℂ) =
              (m : ℂ) ^ 2 * ((z.1.natAbs ^ 2 : ℕ) : ℂ) := by norm_cast
          _ = (m : ℂ) ^ 2 * (z.1 : ℂ) ^ 2 := by rw [hsComplex]
      calc
        Complex.exp (Real.pi * Complex.I *
            ((m : ℂ) ^ 2 * (z.1 : ℂ) ^ 2) * τ) =
            Complex.exp (((m ^ 2 * z.1.natAbs ^ 2 : ℕ) : ℂ) *
              (Real.pi * Complex.I * τ)) := by
          congr 1
          rw [hs]
          ring
        _ = Complex.exp ((n : ℂ) * (Real.pi * Complex.I * τ)) := by
          rw [z.2]
        _ = q ^ n := by simpa [q] using
          (Complex.exp_nat_mul (Real.pi * Complex.I * τ) n)
    rw [tsum_fintype]
    simp_rw [hExp]
    have hCard : Fintype.card {z : ℤ | m ^ 2 * z.natAbs ^ 2 = n} =
        (scaledIntegerSquareRoots m n).card := by
      calc
        Fintype.card {z : ℤ | m ^ 2 * z.natAbs ^ 2 = n} =
            Fintype.card {z : ℤ // z ∈ scaledIntegerSquareRoots m n} :=
          Fintype.card_congr
            (Equiv.subtypeEquivRight
              (scaledNatAbs_sq_eq_iff_mem_scaledIntegerSquareRoots m n hm))
        _ = (scaledIntegerSquareRoots m n).card := Fintype.card_coe _
    simp [hCard, coeff_scaledIntegerThetaSeries]
  have hEq := hFiber.tsum_eq
  simp_rw [hTerm] at hEq
  have hAnalytic :
      (∑' z : ℤ,
        Complex.exp (Real.pi * Complex.I *
          ((m : ℂ) ^ 2 * (z : ℂ) ^ 2) * τ)) =
      jacobiTheta ((m ^ 2 : ℕ) * τ) := by
    unfold jacobiTheta
    apply tsum_congr
    intro z
    congr 1
    push_cast
    ring
  rw [hAnalytic] at hEq
  simpa [q] using hEq

/-- Coefficientwise Cauchy product after complex evaluation. -/
theorem coeff_mul_mul_pow_eq_antidiagonal_sum
    (S T : PowerSeries ℕ) (z : ℂ) (n : ℕ) :
    ((PowerSeries.coeff n (S * T) : ℕ) : ℂ) * z ^ n =
      ∑ kl ∈ Finset.antidiagonal n,
        (((PowerSeries.coeff kl.1 S : ℕ) : ℂ) * z ^ kl.1) *
          (((PowerSeries.coeff kl.2 T : ℕ) : ℂ) * z ^ kl.2) := by
  rw [PowerSeries.coeff_mul]
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro kl hkl
  have hAdd : kl.1 + kl.2 = n := Finset.mem_antidiagonal.mp hkl
  rw [← hAdd, pow_add]
  ring

/-- Absolute convergence is stable under multiplying two natural-coefficient
formal power series at a given complex argument. -/
theorem summable_norm_coeff_mul_mul_pow
    (S T : PowerSeries ℕ) (z : ℂ)
    (hS : Summable (fun n : ℕ =>
      ‖((PowerSeries.coeff n S : ℕ) : ℂ) * z ^ n‖))
    (hT : Summable (fun n : ℕ =>
      ‖((PowerSeries.coeff n T : ℕ) : ℂ) * z ^ n‖)) :
    Summable (fun n : ℕ =>
      ‖((PowerSeries.coeff n (S * T) : ℕ) : ℂ) * z ^ n‖) := by
  have hConv := summable_norm_sum_mul_antidiagonal_of_summable_norm hS hT
  simpa only [← coeff_mul_mul_pow_eq_antidiagonal_sum S T z] using hConv

/-- Evaluation of a product of absolutely convergent natural-coefficient
formal series agrees with the product of evaluations. -/
theorem tsum_coeff_mul_mul_pow
    (S T : PowerSeries ℕ) (z : ℂ)
    (hS : Summable (fun n : ℕ =>
      ‖((PowerSeries.coeff n S : ℕ) : ℂ) * z ^ n‖))
    (hT : Summable (fun n : ℕ =>
      ‖((PowerSeries.coeff n T : ℕ) : ℂ) * z ^ n‖)) :
    (∑' n : ℕ, ((PowerSeries.coeff n (S * T) : ℕ) : ℂ) * z ^ n) =
      (∑' n : ℕ, ((PowerSeries.coeff n S : ℕ) : ℂ) * z ^ n) *
        (∑' n : ℕ, ((PowerSeries.coeff n T : ℕ) : ℂ) * z ^ n) := by
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hS hT]
  exact tsum_congr (coeff_mul_mul_pow_eq_antidiagonal_sum S T z)

/-- The LPS trace theta coefficients evaluate to the analytic product of
one ordinary Jacobi theta function and three scaled ones.  This is the
formal-to-analytic bridge needed before modular transformation and Fourier
coefficient estimates can be applied to the exact trace formula. -/
theorem tsum_coeff_lpsTraceThetaSeries_eq_jacobiTheta_product
    (r : ℕ) (hr : 0 < r) (τ : ℂ) (hτ : 0 < τ.im) :
    (∑' n : ℕ,
      ((PowerSeries.coeff n (lpsTraceThetaSeries r) : ℕ) : ℂ) *
        Complex.exp (Real.pi * Complex.I * τ) ^ n) =
      jacobiTheta τ *
        (jacobiTheta (((2 * r) ^ 2 : ℕ) * τ)) ^ 3 := by
  let z : ℂ := Complex.exp (Real.pi * Complex.I * τ)
  let S : PowerSeries ℕ := scaledIntegerThetaSeries (2 * r)
  have hm : 0 < 2 * r := by omega
  have hz : ‖z‖ < 1 := norm_exp_pi_I_mul_lt_one τ hτ
  have hU := summable_norm_coeff_integerThetaSeries_mul_pow z hz
  have hS := summable_norm_coeff_scaledIntegerThetaSeries_mul_pow
    (2 * r) hm z hz
  have hS2 := summable_norm_coeff_mul_mul_pow S S z hS hS
  have hPow : S ^ 3 = (S * S) * S := by ring
  have hS3 : Summable (fun n : ℕ =>
      ‖((PowerSeries.coeff n (S ^ 3) : ℕ) : ℂ) * z ^ n‖) := by
    rw [hPow]
    exact summable_norm_coeff_mul_mul_pow (S * S) S z hS2 hS
  have hEvalS3 :
      (∑' n : ℕ,
        ((PowerSeries.coeff n (S ^ 3) : ℕ) : ℂ) * z ^ n) =
      (∑' n : ℕ,
        ((PowerSeries.coeff n S : ℕ) : ℂ) * z ^ n) ^ 3 := by
    rw [hPow, tsum_coeff_mul_mul_pow (S * S) S z hS2 hS,
      tsum_coeff_mul_mul_pow S S z hS hS]
    ring
  rw [lpsTraceThetaSeries_eq_integerTheta_mul_scaled_pow_three hr]
  change (∑' n : ℕ,
    ((PowerSeries.coeff n (integerThetaSeries * S ^ 3) : ℕ) : ℂ) * z ^ n) = _
  rw [tsum_coeff_mul_mul_pow integerThetaSeries (S ^ 3) z hU hS3,
    hEvalS3]
  rw [show (∑' n : ℕ,
      ((PowerSeries.coeff n integerThetaSeries : ℕ) : ℂ) * z ^ n) =
      jacobiTheta τ by
      simpa [z] using tsum_coeff_integerThetaSeries_eq_jacobiTheta τ hτ]
  rw [show (∑' n : ℕ,
      ((PowerSeries.coeff n S : ℕ) : ℂ) * z ^ n) =
      jacobiTheta (((2 * r) ^ 2 : ℕ) * τ) by
      simpa [S, z] using
        tsum_coeff_scaledIntegerThetaSeries_eq_jacobiTheta (2 * r) hm τ hτ]

/-- The analytic theta product attached to the LPS trace form. -/
noncomputable def lpsAnalyticThetaProduct (r : ℕ) (τ : ℂ) : ℂ :=
  jacobiTheta τ * (jacobiTheta (((2 * r) ^ 2 : ℕ) * τ)) ^ 3

/-- The coefficient series evaluates to the named analytic product. -/
theorem tsum_coeff_lpsTraceThetaSeries_eq_lpsAnalyticThetaProduct
    (r : ℕ) (hr : 0 < r) (τ : ℂ) (hτ : 0 < τ.im) :
    (∑' n : ℕ,
      ((PowerSeries.coeff n (lpsTraceThetaSeries r) : ℕ) : ℂ) *
        Complex.exp (Real.pi * Complex.I * τ) ^ n) =
      lpsAnalyticThetaProduct r τ := by
  exact tsum_coeff_lpsTraceThetaSeries_eq_jacobiTheta_product r hr τ hτ

/-- The LPS theta product is invariant under translation by two.  This is
the first transformation law needed for its modular-form interpretation. -/
theorem lpsAnalyticThetaProduct_two_add (r : ℕ) (τ : ℂ) :
    lpsAnalyticThetaProduct r (2 + τ) = lpsAnalyticThetaProduct r τ := by
  let m : ℕ := (2 * r) ^ 2
  have hPeriod : Function.Periodic jacobiTheta (2 : ℂ) := by
    intro z
    simpa only [add_comm] using jacobiTheta_two_add z
  have hScaled : jacobiTheta ((m : ℂ) * ((2 : ℂ) + τ)) =
      jacobiTheta ((m : ℂ) * τ) := by
    have hShift : (m : ℂ) * ((2 : ℂ) + τ) =
        (m : ℂ) * τ + (m : ℂ) * 2 := by ring
    rw [hShift]
    simpa only [Nat.cast_mul] using (hPeriod.nat_mul m) ((m : ℂ) * τ)
  unfold lpsAnalyticThetaProduct
  rw [jacobiTheta_two_add, show (((2 * r) ^ 2 : ℕ) : ℂ) = (m : ℂ) from rfl,
    hScaled]

/-- The LPS theta product is holomorphic at every point of the upper
half-plane.  No modular-form or Fourier-coefficient bound is asserted. -/
theorem differentiableAt_lpsAnalyticThetaProduct
    (r : ℕ) (hr : 0 < r) {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ (lpsAnalyticThetaProduct r) τ := by
  let m : ℕ := (2 * r) ^ 2
  have hm : 0 < (((m : ℕ) : ℂ) * τ).im := by
    rw [Complex.mul_im]
    simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    have hr : 0 < m := by
      dsimp [m]
      exact pow_pos (Nat.mul_pos (by omega) hr) 2
    exact mul_pos (Nat.cast_pos.mpr hr) hτ
  have hScaled : DifferentiableAt ℂ
      (fun z : ℂ => jacobiTheta ((m : ℂ) * z)) τ := by
    exact (differentiableAt_jacobiTheta hm).comp τ
      (differentiableAt_id.const_mul _)
  unfold lpsAnalyticThetaProduct
  exact (differentiableAt_jacobiTheta hτ).mul (hScaled.pow 3)

/-- The LPS theta product in the standard modular-form coordinate
`q = exp (2πiz)`.  Our `jacobiTheta` uses `exp (πiτ)`, so `τ = 2z`. -/
noncomputable def lpsStandardTheta (r : ℕ) (z : ℂ) : ℂ :=
  lpsAnalyticThetaProduct r (2 * z)

/-- The formal trace-theta coefficient at `n` is exactly the coefficient
of `exp (2πiz)^n` in the standard analytic coordinate. -/
theorem tsum_coeff_lpsTraceThetaSeries_eq_lpsStandardTheta
    (r : ℕ) (hr : 0 < r) (z : ℂ) (hz : 0 < z.im) :
    (∑' n : ℕ,
      ((PowerSeries.coeff n (lpsTraceThetaSeries r) : ℕ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * z) ^ n) =
      lpsStandardTheta r z := by
  have hUpper : 0 < ((2 : ℂ) * z).im := by
    rw [Complex.mul_im]
    simpa using (mul_pos (by norm_num : (0 : ℝ) < 2) hz)
  have hExp : Complex.exp (Real.pi * Complex.I * ((2 : ℂ) * z)) =
      Complex.exp (2 * Real.pi * Complex.I * z) := by
    congr 1
    ring
  simpa only [lpsStandardTheta, hExp] using
    tsum_coeff_lpsTraceThetaSeries_eq_lpsAnalyticThetaProduct
      r hr (2 * z) hUpper

/-- Translation by one is the period law in the standard modular-form
coordinate. -/
theorem lpsStandardTheta_add_one (r : ℕ) (z : ℂ) :
    lpsStandardTheta r (z + 1) = lpsStandardTheta r z := by
  unfold lpsStandardTheta
  rw [show (2 : ℂ) * (z + 1) = 2 + 2 * z by ring,
    lpsAnalyticThetaProduct_two_add]

/-- The normalized theta product is holomorphic in the upper half-plane. -/
theorem differentiableAt_lpsStandardTheta
    (r : ℕ) (hr : 0 < r) {z : ℂ} (hz : 0 < z.im) :
    DifferentiableAt ℂ (lpsStandardTheta r) z := by
  have hUpper : 0 < ((2 : ℂ) * z).im := by
    rw [Complex.mul_im]
    simpa using (mul_pos (by norm_num : (0 : ℝ) < 2) hz)
  unfold lpsStandardTheta
  exact (differentiableAt_lpsAnalyticThetaProduct r hr hUpper).comp z
    (differentiableAt_id.const_mul _)

/-- The LPS trace-theta coefficient series converges absolutely at every
point of the open unit disc. -/
theorem summable_norm_coeff_lpsTraceThetaSeries_mul_pow
    (r : ℕ) (hr : 0 < r) (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ =>
      ‖((PowerSeries.coeff n (lpsTraceThetaSeries r) : ℕ) : ℂ) * z ^ n‖) := by
  let S : PowerSeries ℕ := scaledIntegerThetaSeries (2 * r)
  have hm : 0 < 2 * r := by omega
  have hU := summable_norm_coeff_integerThetaSeries_mul_pow z hz
  have hS := summable_norm_coeff_scaledIntegerThetaSeries_mul_pow
    (2 * r) hm z hz
  have hS2 := summable_norm_coeff_mul_mul_pow S S z hS hS
  have hPow : S ^ 3 = (S * S) * S := by ring
  have hS3 : Summable (fun n : ℕ =>
      ‖((PowerSeries.coeff n (S ^ 3) : ℕ) : ℂ) * z ^ n‖) := by
    rw [hPow]
    exact summable_norm_coeff_mul_mul_pow (S * S) S z hS2 hS
  rw [lpsTraceThetaSeries_eq_integerTheta_mul_scaled_pow_three hr]
  change Summable (fun n : ℕ =>
    ‖((PowerSeries.coeff n (integerThetaSeries * S ^ 3) : ℕ) : ℂ) * z ^ n‖)
  exact summable_norm_coeff_mul_mul_pow integerThetaSeries (S ^ 3) z hU hS3

/-- The standard theta product is represented by its exact formal
coefficients in Mathlib's period-one `qParam` convention. -/
theorem hasSum_lpsStandardTheta_coeff
    (r : ℕ) (hr : 0 < r) (z : ℍ) :
    HasSum (fun n : ℕ =>
      ((PowerSeries.coeff n (lpsTraceThetaSeries r) : ℕ) : ℂ) *
        Function.Periodic.qParam 1 (z : ℂ) ^ n)
      (lpsStandardTheta r z) := by
  have hz : ‖Function.Periodic.qParam 1 (z : ℂ)‖ < 1 :=
    Function.Periodic.norm_qParam_lt_one (by norm_num) z.2
  have hSummable :=
    (summable_norm_coeff_lpsTraceThetaSeries_mul_pow r hr _ hz).of_norm
  have hEq : (∑' n : ℕ,
      ((PowerSeries.coeff n (lpsTraceThetaSeries r) : ℕ) : ℂ) *
        Function.Periodic.qParam 1 (z : ℂ) ^ n) =
      lpsStandardTheta r z := by
    simpa [Function.Periodic.qParam] using
      tsum_coeff_lpsTraceThetaSeries_eq_lpsStandardTheta r hr z z.2
  simpa only [hEq] using hSummable.hasSum

private theorem lpsStandardTheta_periodic_comp_ofComplex (r : ℕ) :
    Function.Periodic
      ((fun z : ℍ => lpsStandardTheta r z) ∘ UpperHalfPlane.ofComplex) 1 := by
  intro z
  by_cases hz : 0 < z.im
  · have hz1 : 0 < (z + 1).im := by simpa using hz
    simp only [Function.comp_apply,
      UpperHalfPlane.ofComplex_apply_of_im_pos hz,
      UpperHalfPlane.ofComplex_apply_of_im_pos hz1]
    exact lpsStandardTheta_add_one r z
  · have hz0 : z.im ≤ 0 := le_of_not_gt hz
    have hz1 : (z + 1).im ≤ 0 := by simpa using hz0
    simp only [Function.comp_apply,
      UpperHalfPlane.ofComplex_apply_of_im_nonpos hz0,
      UpperHalfPlane.ofComplex_apply_of_im_nonpos hz1]

private theorem mdifferentiable_lpsStandardTheta
    (r : ℕ) (hr : 0 < r) :
    MDiff (fun z : ℍ => lpsStandardTheta r z) := by
  intro z
  exact (differentiableAt_lpsStandardTheta r hr z.2).mdifferentiableAt.comp
    z z.mdifferentiable_coe

private theorem hasSum_lpsStandardTheta_coeff_smul
    (r : ℕ) (hr : 0 < r) (z : ℍ) :
    HasSum (fun m : ℕ =>
      ((PowerSeries.coeff m (lpsTraceThetaSeries r) : ℕ) : ℂ) •
        Function.Periodic.qParam 1 (z : ℂ) ^ m)
      (lpsStandardTheta r z) := by
  simpa only [smul_eq_mul] using hasSum_lpsStandardTheta_coeff r hr z

private theorem boundedAtImInfty_lpsStandardTheta
    (r : ℕ) (hr : 0 < r) :
    UpperHalfPlane.IsBoundedAtImInfty
      (fun z : ℍ => lpsStandardTheta r z) := by
  apply UpperHalfPlane.isBoundedAtImInfty_of_hasSum_qExpansion
    (by norm_num : (0 : ℝ) < 1)
  exact hasSum_lpsStandardTheta_coeff_smul r hr

private theorem analyticAt_cuspFunction_lpsStandardTheta
    (r : ℕ) (hr : 0 < r) :
    AnalyticAt ℂ
      (UpperHalfPlane.cuspFunction 1
        (fun z : ℍ => lpsStandardTheta r z)) 0 := by
  exact UpperHalfPlane.analyticAt_cuspFunction_zero
    (by norm_num : (0 : ℝ) < 1)
    (lpsStandardTheta_periodic_comp_ofComplex r)
    (mdifferentiable_lpsStandardTheta r hr)
    (boundedAtImInfty_lpsStandardTheta r hr)

private noncomputable def lpsStandardThetaContinuousMap
    (r : ℕ) (hr : 0 < r) : C(ℍ, ℂ) :=
  ⟨fun z => lpsStandardTheta r z,
    (mdifferentiable_lpsStandardTheta r hr).continuous⟩

/-- Mathlib's analytic `qExpansion` of the normalized LPS theta product has
the coefficients of the already-formalized four-variable trace theta series.
No modular-form transformation law is assumed or concluded. -/
theorem coeff_qExpansion_lpsStandardTheta
    (r : ℕ) (hr : 0 < r) (n : ℕ) :
    PowerSeries.coeff n
        (UpperHalfPlane.qExpansion 1
          (fun z : ℍ => lpsStandardTheta r z)) =
      ((PowerSeries.coeff n (lpsTraceThetaSeries r) : ℕ) : ℂ) := by
  symm
  exact UpperHalfPlane.qExpansion_coeff_unique
    (lpsStandardThetaContinuousMap r hr)
    (by norm_num : (0 : ℝ) < 1)
    (analyticAt_cuspFunction_lpsStandardTheta r hr)
    (hasSum_lpsStandardTheta_coeff_smul r hr) n

end QEC.Coding.TannerLiftedProduct
