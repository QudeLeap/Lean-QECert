import QEC.Distillation.LowOverheadProtocol.Sublogarithmic.ParameterSequence
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Finite binomial-tail estimates for the HH18 construction

This module collects the elementary finite bounds that underlie the
asymptotic punctured-Reed--Muller estimates used by the HH18 construction.
-/

namespace QEC.Distillation.HH18.HH18BinomialTailAsymptotics

open Coding.PuncturedReedMuller
open Filter Topology

/-- The first summand of a nonempty binomial tail lower-bounds the tail. -/
theorem choose_succ_le_tail (n w : Nat) (h : w + 1 ≤ n) :
    Nat.choose n (w + 1) ≤ binomialTail n w := by
  unfold binomialTail
  exact Finset.single_le_sum (fun i _ => Nat.zero_le _) (by simp [h])

/-- Every binomial tail is bounded by the full binomial row. -/
theorem binomialTail_le_two_pow (n w : Nat) : binomialTail n w ≤ 2 ^ n := by
  unfold binomialTail
  calc
    ∑ i ∈ Finset.Icc (w + 1) n, Nat.choose n i ≤
        ∑ i ∈ Finset.range (n + 1), Nat.choose n i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Finset.mem_Icc.mp hi).2)
      · intro _ _ _
        exact Nat.zero_le _
    _ = 2 ^ n := Nat.sum_range_choose n

/-- The logarithm of `n!`, normalized by `n`, has its Stirling leading term.

This is the factorial component needed to turn the finite HH18 binomial sums
into proportional entropy exponents. -/
theorem tendsto_log_factorial_div_sub_log_add_one : Tendsto
    (fun n : Nat => Real.log (n.factorial : ℝ) / n - Real.log n + 1)
    atTop (𝓝 0) := by
  have hlog_two_div : Tendsto
      (fun n : Nat => Real.log (2 * n) / (2 * n)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
        (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
  have hlog_two : Tendsto
      (fun n : Nat => Real.log (2 * n) / n) atTop (𝓝 0) := by
    have hlog_two_scaled : Tendsto
        (fun n : Nat => 2 * (Real.log (2 * n) / (2 * n))) atTop (𝓝 0) := by
      simpa using hlog_two_div.const_mul (2 : ℝ)
    refine Tendsto.congr' (Eventually.of_forall fun n => ?_) hlog_two_scaled
    by_cases hn : (n : ℝ) = 0
    · simp [hn]
    field_simp [hn]
  have hlog_stirling : Tendsto
      (fun n : Nat => Real.log (Stirling.stirlingSeq n)) atTop
        (𝓝 (Real.log (Real.sqrt Real.pi))) := by
    exact (Real.continuousAt_log (by positivity)).tendsto.comp
      Stirling.tendsto_stirlingSeq_sqrt_pi
  have hlog_stirling_div : Tendsto
      (fun n : Nat => Real.log (Stirling.stirlingSeq n) / n) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      hlog_stirling.mul (tendsto_inv_atTop_nhds_zero_nat : Tendsto
        (fun n : Nat => (n : ℝ)⁻¹) atTop (𝓝 0))
  have hmain : Tendsto
      (fun n : Nat => (1 / 2 : ℝ) * (Real.log (2 * n) / n) +
        Real.log (Stirling.stirlingSeq n) / n) atTop (𝓝 0) := by
    simpa using hlog_two.const_mul (1 / 2 : ℝ) |>.add
      hlog_stirling_div
  refine hmain.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  rw [Stirling.log_stirlingSeq_formula]
  rw [Real.log_div (by positivity) (by positivity), Real.log_exp]
  field_simp
  ring

/-- Stirling's normalized log-factorial limit along a positive integral ray. -/
theorem tendsto_log_factorial_mul_div_sub (a : Nat) (ha : 0 < a) : Tendsto
    (fun j : Nat => Real.log ((a * j).factorial : ℝ) / j - a * Real.log j)
    atTop (𝓝 (a * Real.log a - a)) := by
  have hmul : Tendsto (fun j : Nat => a * j) atTop atTop := by
    rw [tendsto_atTop]
    intro bound
    refine eventually_atTop.2 ⟨bound, fun j hj => ?_⟩
    calc
      bound ≤ a * bound := Nat.le_mul_of_pos_left bound ha
      _ ≤ a * j := Nat.mul_le_mul_left a hj
  have hbase := tendsto_log_factorial_div_sub_log_add_one.comp hmul
  have hscaled : Tendsto
      (fun j : Nat => (a : ℝ) *
        (Real.log ((a * j).factorial : ℝ) / (a * j) - Real.log (a * j) + 1))
      atTop (𝓝 0) := by
    simpa using hbase.const_mul (a : ℝ)
  have hsource : Tendsto
      (fun j : Nat => (a : ℝ) *
        (Real.log ((a * j).factorial : ℝ) / (a * j) - Real.log (a * j) + 1) +
          ((a : ℝ) * Real.log a - a))
      atTop (𝓝 ((a : ℝ) * Real.log a - a)) := by
    simpa using hscaled.add (tendsto_const_nhds (x := (a : ℝ) * Real.log a - a))
  refine Tendsto.congr' (eventually_atTop.2 ⟨1, fun j hj => ?_⟩) hsource
  have haR : (a : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt ha
  have hjR : (j : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hj
  rw [Real.log_mul (by positivity) (by positivity)]
  field_simp
  ring

end QEC.Distillation.HH18.HH18BinomialTailAsymptotics
