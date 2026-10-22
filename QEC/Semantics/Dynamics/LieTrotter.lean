import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Lie--Trotter product formula in a complex Banach algebra

This file supplies the two-term bounded-generator product formula used by the
finite-dimensional Lindblad construction.  The proof is elementary: a
telescoping identity controls powers, while differentiability of the two
one-step evolutions at zero gives the required little-o local error.
-/

namespace QEC.Semantics

open Filter
open scoped Topology

noncomputable section

variable {A : Type*} [NormedRing A] [NormOneClass A]
  [NormedAlgebra Complex A] [CompleteSpace A]

/-- The norm of a Banach-algebra exponential is bounded by the scalar
exponential of the norm. -/
theorem norm_normedSpace_exp_le (x : A) :
    ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ := by
  rw [← (NormedSpace.exp_series_hasSum_exp' (𝕂 := Complex) x).tsum_eq]
  calc
    ‖∑' n : Nat, ((Nat.factorial n : Complex)⁻¹ • x ^ n)‖ ≤
        ∑' n : Nat, ‖((Nat.factorial n : Complex)⁻¹ • x ^ n)‖ :=
      norm_tsum_le_tsum_norm (by
        simpa using NormedSpace.norm_expSeries_summable' (𝕂 := Complex) x)
    _ ≤ ∑' n : Nat, ‖x‖ ^ n / Nat.factorial n := by
      exact (NormedSpace.norm_expSeries_summable' (𝕂 := Complex) x).tsum_le_tsum
        (fun n => by
          rw [norm_smul]
          calc
            ‖(Nat.factorial n : Complex)⁻¹‖ * ‖x ^ n‖ ≤
                ‖(Nat.factorial n : Complex)⁻¹‖ * ‖x‖ ^ n :=
              mul_le_mul_of_nonneg_left (norm_pow_le x n) (norm_nonneg _)
            _ = ‖x‖ ^ n / Nat.factorial n := by
              simp [div_eq_mul_inv, mul_comm])
        (Real.summable_pow_div_factorial ‖x‖)
    _ = Real.exp ‖x‖ := by
      simpa [Real.exp_eq_exp_ℝ] using
        (NormedSpace.expSeries_div_hasSum_exp ‖x‖).tsum_eq

/-- A noncommutative telescoping expansion for the difference of two powers. -/
theorem pow_sub_pow_eq_sum (x y : A) (n : Nat) :
    x ^ n - y ^ n =
      ∑ k ∈ Finset.range n, x ^ k * (x - y) * y ^ (n - 1 - k) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      calc
        x ^ n * x - y ^ n * y =
            x ^ n * (x - y) + (x ^ n - y ^ n) * y := by noncomm_ring
        _ = x ^ n * (x - y) +
            (∑ k ∈ Finset.range n, x ^ k * (x - y) * y ^ (n - 1 - k)) * y := by
              rw [ih]
        _ = ∑ k ∈ Finset.range (n + 1),
            x ^ k * (x - y) * y ^ (n + 1 - 1 - k) := by
              rw [Finset.sum_mul, Finset.sum_range_succ]
              simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
              rw [add_comm]
              congr 1
              apply Finset.sum_congr rfl
              intro k hk
              have hkn : k < n := Finset.mem_range.mp hk
              rw [mul_assoc (x ^ k * (x - y)), ← pow_succ]
              congr 2
              omega

/-- Norm estimate associated with `pow_sub_pow_eq_sum`. -/
theorem norm_pow_sub_pow_le (x y : A) (n : Nat) :
    ‖x ^ n - y ^ n‖ ≤
      ∑ k ∈ Finset.range n,
        ‖x‖ ^ k * ‖x - y‖ * ‖y‖ ^ (n - 1 - k) := by
  rw [pow_sub_pow_eq_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _hk => ?_)
  calc
    ‖x ^ k * (x - y) * y ^ (n - 1 - k)‖ ≤
        ‖x ^ k * (x - y)‖ * ‖y ^ (n - 1 - k)‖ := norm_mul_le _ _
    _ ≤ (‖x ^ k‖ * ‖x - y‖) * ‖y ^ (n - 1 - k)‖ := by
      gcongr
      exact norm_mul_le _ _
    _ ≤ (‖x‖ ^ k * ‖x - y‖) * ‖y‖ ^ (n - 1 - k) := by
      gcongr
      · exact norm_pow_le x k
      · exact norm_pow_le y (n - 1 - k)
    _ = ‖x‖ ^ k * ‖x - y‖ * ‖y‖ ^ (n - 1 - k) := rfl

/-- One Lie--Trotter time slice. -/
noncomputable def lieTrotterStep (x y : A) (z : Complex) : A :=
  NormedSpace.exp (z • x) * NormedSpace.exp (z • y)

theorem hasDerivAt_lieTrotterStep_zero (x y : A) :
    HasDerivAt (lieTrotterStep x y) (x + y) (0 : Complex) := by
  change HasDerivAt
    ((fun z : Complex => NormedSpace.exp (z • x)) *
      (fun z : Complex => NormedSpace.exp (z • y))) (x + y) (0 : Complex)
  simpa only [zero_smul, NormedSpace.exp_zero, mul_one, one_mul] using
    (hasDerivAt_exp_smul_const x (0 : Complex)).mul
      (hasDerivAt_exp_smul_const y (0 : Complex))

/-- The one-step Trotter defect is little-o of the step size. -/
theorem tendsto_lieTrotter_localError (x y : A) :
    Tendsto
      (fun n : Nat => (n : Real) *
        ‖NormedSpace.exp (((n : Complex)⁻¹) • (x + y)) -
          lieTrotterStep x y ((n : Complex)⁻¹)‖)
      atTop (nhds 0) := by
  let reference : Complex → A := fun z => NormedSpace.exp (z • (x + y))
  have href : HasDerivAt reference (x + y) (0 : Complex) := by
    simpa [reference] using
      hasDerivAt_exp_smul_const (x + y) (0 : Complex)
  have hdefect := href.sub (hasDerivAt_lieTrotterStep_zero x y)
  have hquotient := (hasDerivAt_iff_tendsto.mp hdefect).comp
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := Complex))
  refine hquotient.congr' ?_
  filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  simp [reference, lieTrotterStep, norm_inv]

private theorem norm_referenceStep_pow_le (x y : A) {n k : Nat}
    (hn : 0 < n) (hk : k ≤ n) :
    ‖NormedSpace.exp (((n : Complex)⁻¹) • (x + y))‖ ^ k ≤
      Real.exp (‖x‖ + ‖y‖) := by
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hkR : (k : Real) ≤ n := by exact_mod_cast hk
  calc
    ‖NormedSpace.exp (((n : Complex)⁻¹) • (x + y))‖ ^ k ≤
        (Real.exp ‖((n : Complex)⁻¹ • (x + y))‖) ^ k := by
      gcongr
      exact norm_normedSpace_exp_le _
    _ ≤ (Real.exp (((n : Real)⁻¹) * (‖x‖ + ‖y‖))) ^ k := by
      gcongr
      rw [norm_smul, norm_inv, RCLike.norm_natCast]
      gcongr
      exact norm_add_le x y
    _ = Real.exp ((k : Real) * (((n : Real)⁻¹) * (‖x‖ + ‖y‖))) := by
      rw [Real.exp_nat_mul]
    _ ≤ Real.exp (‖x‖ + ‖y‖) := by
      apply Real.exp_le_exp.mpr
      have hratio : (k : Real) * (n : Real)⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv, div_le_one hnR]
        exact hkR
      calc
        (k : Real) * ((n : Real)⁻¹ * (‖x‖ + ‖y‖)) =
            ((k : Real) * (n : Real)⁻¹) * (‖x‖ + ‖y‖) := by ring
        _ ≤ 1 * (‖x‖ + ‖y‖) := by
          gcongr
        _ = ‖x‖ + ‖y‖ := one_mul _

private theorem norm_lieTrotterStep_pow_le (x y : A) {n k : Nat}
    (hn : 0 < n) (hk : k ≤ n) :
    ‖lieTrotterStep x y ((n : Complex)⁻¹)‖ ^ k ≤
      Real.exp (‖x‖ + ‖y‖) := by
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hkR : (k : Real) ≤ n := by exact_mod_cast hk
  have hstep : ‖lieTrotterStep x y ((n : Complex)⁻¹)‖ ≤
      Real.exp (((n : Real)⁻¹) * (‖x‖ + ‖y‖)) := by
    calc
      ‖lieTrotterStep x y ((n : Complex)⁻¹)‖ ≤
          ‖NormedSpace.exp (((n : Complex)⁻¹) • x)‖ *
            ‖NormedSpace.exp (((n : Complex)⁻¹) • y)‖ := by
        exact norm_mul_le _ _
      _ ≤ Real.exp ‖((n : Complex)⁻¹) • x‖ *
            Real.exp ‖((n : Complex)⁻¹) • y‖ := by
        gcongr <;> exact norm_normedSpace_exp_le _
      _ = Real.exp (((n : Real)⁻¹) * (‖x‖ + ‖y‖)) := by
        rw [← Real.exp_add]
        congr 1
        simp [norm_smul, norm_inv]
        ring
  calc
    ‖lieTrotterStep x y ((n : Complex)⁻¹)‖ ^ k ≤
        (Real.exp (((n : Real)⁻¹) * (‖x‖ + ‖y‖))) ^ k := by
      gcongr
    _ = Real.exp ((k : Real) * (((n : Real)⁻¹) * (‖x‖ + ‖y‖))) := by
      rw [Real.exp_nat_mul]
    _ ≤ Real.exp (‖x‖ + ‖y‖) := by
      apply Real.exp_le_exp.mpr
      have hratio : (k : Real) * (n : Real)⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv, div_le_one hnR]
        exact hkR
      calc
        (k : Real) * ((n : Real)⁻¹ * (‖x‖ + ‖y‖)) =
            ((k : Real) * (n : Real)⁻¹) * (‖x‖ + ‖y‖) := by ring
        _ ≤ 1 * (‖x‖ + ‖y‖) := by gcongr
        _ = ‖x‖ + ‖y‖ := one_mul _

private theorem norm_lieTrotter_power_defect_le (x y : A) {n : Nat}
    (hn : 0 < n) :
    ‖NormedSpace.exp (((n : Complex)⁻¹) • (x + y)) ^ n -
        (lieTrotterStep x y ((n : Complex)⁻¹)) ^ n‖ ≤
      (Real.exp (‖x‖ + ‖y‖) * Real.exp (‖x‖ + ‖y‖)) *
        ((n : Real) *
          ‖NormedSpace.exp (((n : Complex)⁻¹) • (x + y)) -
            lieTrotterStep x y ((n : Complex)⁻¹)‖) := by
  let u := NormedSpace.exp (((n : Complex)⁻¹) • (x + y))
  let v := lieTrotterStep x y ((n : Complex)⁻¹)
  let C := Real.exp (‖x‖ + ‖y‖)
  calc
    ‖u ^ n - v ^ n‖ ≤
        ∑ k ∈ Finset.range n,
          ‖u‖ ^ k * ‖u - v‖ * ‖v‖ ^ (n - 1 - k) :=
      norm_pow_sub_pow_le u v n
    _ ≤ ∑ k ∈ Finset.range n, C * ‖u - v‖ * C := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn : k < n := Finset.mem_range.mp hk
      have htail : n - 1 - k ≤ n :=
        (Nat.sub_le (n - 1) k).trans (Nat.sub_le n 1)
      dsimp only [u, v, C]
      gcongr
      · exact norm_referenceStep_pow_le x y hn hkn.le
      · exact norm_lieTrotterStep_pow_le x y hn htail
    _ = C * C * ((n : Real) * ‖u - v‖) := by
      simp [C]
      ring
    _ = (Real.exp (‖x‖ + ‖y‖) * Real.exp (‖x‖ + ‖y‖)) *
        ((n : Real) *
          ‖NormedSpace.exp (((n : Complex)⁻¹) • (x + y)) -
            lieTrotterStep x y ((n : Complex)⁻¹)‖) := by rfl

private theorem normedSpace_exp_inv_nat_smul_pow (x : A) {n : Nat}
    (hn : 0 < n) :
    (NormedSpace.exp (((n : Complex)⁻¹) • x)) ^ n =
      NormedSpace.exp x := by
  have exp_nsmul_complex (m : Nat) (z : A) :
      NormedSpace.exp (m • z) = NormedSpace.exp z ^ m := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [succ_nsmul, pow_succ,
          NormedSpace.exp_add_of_commute_of_mem_ball
            ((Commute.refl z).smul_left m)
            ((NormedSpace.expSeries_radius_eq_top Complex A).symm ▸
              edist_lt_top _ _)
            ((NormedSpace.expSeries_radius_eq_top Complex A).symm ▸
              edist_lt_top _ _), ih]
  rw [← exp_nsmul_complex]
  congr 1
  rw [← Nat.cast_smul_eq_nsmul Complex, smul_smul]
  have hnC : (n : Complex) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  rw [mul_inv_cancel₀ hnC, one_smul]

/-- The two-term Lie--Trotter product formula for bounded generators in a
complex Banach algebra. -/
theorem tendsto_lieTrotter (x y : A) :
    Tendsto
      (fun n : Nat => (lieTrotterStep x y ((n : Complex)⁻¹)) ^ n)
      atTop (nhds (NormedSpace.exp (x + y))) := by
  let u : Nat → A := fun n => NormedSpace.exp (((n : Complex)⁻¹) • (x + y))
  let v : Nat → A := fun n => lieTrotterStep x y ((n : Complex)⁻¹)
  let C : Real := Real.exp (‖x‖ + ‖y‖) * Real.exp (‖x‖ + ‖y‖)
  let localError : Nat → Real := fun n => (n : Real) * ‖u n - v n‖
  have hlocal : Tendsto localError atTop (nhds 0) := by
    simpa [localError, u, v] using tendsto_lieTrotter_localError x y
  have hmajorant : Tendsto (fun n => C * localError n) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hlocal)
  have hbound : ∀ᶠ n in atTop, ‖u n ^ n - v n ^ n‖ ≤ C * localError n := by
    filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    exact norm_lieTrotter_power_defect_le x y hn
  have hdefect : Tendsto (fun n => u n ^ n - v n ^ n) atTop (nhds 0) :=
    squeeze_zero_norm' hbound hmajorant
  have href : Tendsto (fun n => u n ^ n) atTop
      (nhds (NormedSpace.exp (x + y))) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    exact (normedSpace_exp_inv_nat_smul_pow (x + y) hn).symm
  have hresult := href.sub hdefect
  convert hresult using 1 <;> simp [u, v]

end

end QEC.Semantics
