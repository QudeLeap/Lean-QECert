import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Schedule.DyadicSlack
import QEC.Distillation.LowOverheadProtocol.Parameterized.PathYield

/-!
# Parameterized HH18 retry-pool success budget

This internal quantitative layer fixes the small-noise domain used by the
physical retry tree.  It combines the actual dyadic shortage factor, the
literal number of logical-path pools, and the already-proved distance-power
error envelope.  The resulting finite sum is a derived union-bound budget;
it does not assume independence between sibling pools or attach a success
probability to an accounting record.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Parameterized

open Coding
open Coding.ReedMuller Coding.PuncturedReedMuller
open scoped BigOperators

attribute [local instance 100] Fintype.ofFinite

/-- The source-derived pooling domain.  Its factor `64 * k` pays for every
logical-path pool and the increasing dyadic retry denominator. -/
def decodedRetryPoolInitialPoolingDomain (w r m : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : Prop :=
  routedDepthIterationScale w r m * epsilon.1 <=
    1 / (64 * (logicalOutputCount m w : Real))

/-- The pooling domain is strictly stronger than the existing quarter-domain
used to construct every path-indexed successor rate. -/
theorem decodedRetryPoolInitialPoolingDomain_implies_routedDepthInitialSmallDomain
    {w r m : Nat} (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon) :
    routedDepthInitialSmallDomain w r m epsilon := by
  have hk : (1 : Real) <= logicalOutputCount m w := by
    exact_mod_cast Nat.succ_le_iff.mpr (routedDepthLogicalOutputCount_pos m w)
  have hkpos : 0 < (logicalOutputCount m w : Real) := lt_of_lt_of_le zero_lt_one hk
  have hden : 0 < (64 : Real) * logicalOutputCount m w := mul_pos (by norm_num) hkpos
  have hquarter :
      1 / ((64 : Real) * logicalOutputCount m w) <= 1 / 4 := by
    apply (div_le_iff₀ hden).2
    nlinarith
  exact hpool.trans hquarter

/-- The distance-power envelope is nonnegative at every finite stage. -/
theorem decodedRetryPoolErrorEnvelope_nonneg (w r m : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (stage : Nat) :
    0 <= routedDepthErrorEnvelope w r m epsilon stage := by
  induction stage with
  | zero => exact epsilon.property.1
  | succ stage ih =>
      simp only [routedDepthErrorEnvelope]
      exact mul_nonneg (pow_nonneg (routedDepthIterationScale_pos w r m).le _)
        (pow_nonneg ih _)

/-- The strong pooling threshold persists for the exact distance-power
envelope, not merely for the actual path rates that it bounds. -/
theorem decodedRetryPoolErrorEnvelope_scaled_poolingDomain
    {w r m : Nat} (h : Admissible w r m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon)
    (stage : Nat) :
    routedDepthIterationScale w r m *
        routedDepthErrorEnvelope w r m epsilon stage <=
      1 / (64 * (logicalOutputCount m w : Real)) := by
  rw [routedDepthErrorEnvelope_closed_form h epsilon]
  have hkpos : 0 < (logicalOutputCount m w : Real) := by
    exact_mod_cast routedDepthLogicalOutputCount_pos m w
  have hden : 0 < (64 : Real) * logicalOutputCount m w := mul_pos (by norm_num) hkpos
  have hthresholdNonneg :
      0 <= 1 / ((64 : Real) * logicalOutputCount m w) := (one_div_pos.mpr hden).le
  have hthresholdLeOne :
      1 / ((64 : Real) * logicalOutputCount m w) <= 1 := by
    apply (div_le_iff₀ hden).2
    have hk : (1 : Real) <= logicalOutputCount m w := by
      exact_mod_cast Nat.succ_le_iff.mpr (routedDepthLogicalOutputCount_pos m w)
    nlinarith
  have hbase : 0 <= routedDepthIterationScale w r m * epsilon.1 :=
    mul_nonneg (routedDepthIterationScale_pos w r m).le epsilon.property.1
  have hdistance : 2 <= codeDistance r w := codeDistance_two_le h
  have hpower : 1 <= codeDistance r w ^ stage :=
    one_le_pow₀ (by omega : 1 <= codeDistance r w)
  calc
    (routedDepthIterationScale w r m * epsilon.1) ^ (codeDistance r w ^ stage) <=
        (1 / ((64 : Real) * logicalOutputCount m w)) ^
          (codeDistance r w ^ stage) :=
      pow_le_pow_left₀ hbase hpool _
    _ <= (1 / ((64 : Real) * logicalOutputCount m w)) ^ 1 :=
      pow_le_pow_of_le_one hthresholdNonneg hthresholdLeOne hpower
    _ = 1 / (64 * (logicalOutputCount m w : Real)) := by ring

/-- In the pooling domain the envelope contracts fast enough to pay for four
times the number of logical branches at every successor stage. -/
theorem decodedRetryPoolErrorEnvelope_succ_le_div_four_mul_logicalOutputCount
    {w r m : Nat} (h : Admissible w r m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon)
    (stage : Nat) :
    routedDepthErrorEnvelope w r m epsilon (stage + 1) <=
      routedDepthErrorEnvelope w r m epsilon stage /
        (4 * (logicalOutputCount m w : Real)) := by
  have hdistance : 2 <= codeDistance r w := codeDistance_two_le h
  have hpred : 1 <= codeDistance r w - 1 := by omega
  have henvelopeNonneg : 0 <= routedDepthErrorEnvelope w r m epsilon stage :=
    decodedRetryPoolErrorEnvelope_nonneg w r m epsilon stage
  have hkpos : 0 < (logicalOutputCount m w : Real) := by
    exact_mod_cast routedDepthLogicalOutputCount_pos m w
  have hden64 : 0 < (64 : Real) * logicalOutputCount m w := mul_pos (by norm_num) hkpos
  have hden4 : 0 < (4 : Real) * logicalOutputCount m w := mul_pos (by norm_num) hkpos
  have hthresholdNonneg :
      0 <= 1 / ((64 : Real) * logicalOutputCount m w) := (one_div_pos.mpr hden64).le
  have hthresholdLeOne :
      1 / ((64 : Real) * logicalOutputCount m w) <= 1 := by
    apply (div_le_iff₀ hden64).2
    have hk : (1 : Real) <= logicalOutputCount m w := by
      exact_mod_cast Nat.succ_le_iff.mpr (routedDepthLogicalOutputCount_pos m w)
    nlinarith
  have hpower :
      (routedDepthIterationScale w r m *
          routedDepthErrorEnvelope w r m epsilon stage) ^
          (codeDistance r w - 1) <=
        1 / ((4 : Real) * logicalOutputCount m w) := by
    calc
      (routedDepthIterationScale w r m *
          routedDepthErrorEnvelope w r m epsilon stage) ^
          (codeDistance r w - 1) <=
          (1 / ((64 : Real) * logicalOutputCount m w)) ^
            (codeDistance r w - 1) :=
        pow_le_pow_left₀
          (mul_nonneg (routedDepthIterationScale_pos w r m).le henvelopeNonneg)
          (decodedRetryPoolErrorEnvelope_scaled_poolingDomain h epsilon hpool stage) _
      _ <= (1 / ((64 : Real) * logicalOutputCount m w)) ^ 1 :=
        pow_le_pow_of_le_one hthresholdNonneg hthresholdLeOne hpred
      _ <= 1 / ((4 : Real) * logicalOutputCount m w) := by
        have hdivision :
            1 / ((64 : Real) * logicalOutputCount m w) <=
              1 / ((4 : Real) * logicalOutputCount m w) := by
          apply (div_le_div_iff₀ hden64 hden4).2
          nlinarith
        simpa using hdivision
  have hfactor :
      routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
          routedDepthErrorEnvelope w r m epsilon stage ^ codeDistance r w =
        routedDepthErrorEnvelope w r m epsilon stage *
          (routedDepthIterationScale w r m *
            routedDepthErrorEnvelope w r m epsilon stage) ^
              (codeDistance r w - 1) := by
    rw [mul_pow]
    have hsub : codeDistance r w - 1 + 1 = codeDistance r w :=
      Nat.sub_add_cancel (by omega)
    calc
      routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
          routedDepthErrorEnvelope w r m epsilon stage ^ codeDistance r w =
          routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
            routedDepthErrorEnvelope w r m epsilon stage ^
              (codeDistance r w - 1 + 1) := by rw [hsub]
      _ = routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
            (routedDepthErrorEnvelope w r m epsilon stage ^
              (codeDistance r w - 1) *
                routedDepthErrorEnvelope w r m epsilon stage) := by rw [pow_succ]
      _ = routedDepthErrorEnvelope w r m epsilon stage *
            (routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
              routedDepthErrorEnvelope w r m epsilon stage ^
                (codeDistance r w - 1)) := by ring
  calc
    routedDepthErrorEnvelope w r m epsilon (stage + 1) =
        routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
          routedDepthErrorEnvelope w r m epsilon stage ^ codeDistance r w := rfl
    _ = routedDepthErrorEnvelope w r m epsilon stage *
          (routedDepthIterationScale w r m *
            routedDepthErrorEnvelope w r m epsilon stage) ^
              (codeDistance r w - 1) := hfactor
    _ <= routedDepthErrorEnvelope w r m epsilon stage *
          (1 / ((4 : Real) * logicalOutputCount m w)) :=
      mul_le_mul_of_nonneg_left hpower henvelopeNonneg
    _ = routedDepthErrorEnvelope w r m epsilon stage /
        (4 * (logicalOutputCount m w : Real)) := by ring

/-- The literal union-bound contribution of every retry pool at one stage:
`k^stage` pools, dyadic denominator `2^(stage+3)`, `n` physical inputs per
trial, and the actual distance-power rate envelope. -/
noncomputable def decodedRetryPoolStageAggregateShortageBudget
    (w r m : Nat) (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (stage : Nat) : Real :=
  (logicalOutputCount m w : Real) ^ stage *
    decodedRetryPoolDyadicDenominator stage *
    physicalInputCount m w *
    routedDepthErrorEnvelope w r m epsilon stage

theorem decodedRetryPoolStageAggregateShortageBudget_nonneg
    (w r m : Nat) (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (stage : Nat) :
    0 <= decodedRetryPoolStageAggregateShortageBudget w r m epsilon stage := by
  unfold decodedRetryPoolStageAggregateShortageBudget
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _))
    (decodedRetryPoolErrorEnvelope_nonneg w r m epsilon stage)

/-- The initial aggregate shortage budget is at most one sixteenth. -/
theorem decodedRetryPoolStageAggregateShortageBudget_zero_le_one_sixteenth
    {w r m : Nat} (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon) :
    decodedRetryPoolStageAggregateShortageBudget w r m epsilon 0 <= 1 / 16 := by
  have hk : (1 : Real) <= logicalOutputCount m w := by
    exact_mod_cast Nat.succ_le_iff.mpr (routedDepthLogicalOutputCount_pos m w)
  have hkpos : 0 < (logicalOutputCount m w : Real) := lt_of_lt_of_le zero_lt_one hk
  have hden : 0 < (64 : Real) * logicalOutputCount m w := mul_pos (by norm_num) hkpos
  have hthreshold :
      1 / ((64 : Real) * logicalOutputCount m w) <= 1 / 64 := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have hcountScale := two_mul_routedDepthPhysicalInputCount_le_iterationScale w r m
  have hscaled :
      (2 * (physicalInputCount m w : Real)) * epsilon.1 <=
        routedDepthIterationScale w r m * epsilon.1 :=
    mul_le_mul_of_nonneg_right hcountScale epsilon.property.1
  have hcountEpsilon :
      (physicalInputCount m w : Real) * epsilon.1 <= 1 / 128 := by
    nlinarith [hscaled, hpool.trans hthreshold]
  change (logicalOutputCount m w : Real) ^ 0 *
      decodedRetryPoolDyadicDenominator 0 * physicalInputCount m w * epsilon.1 <= 1 / 16
  norm_num [decodedRetryPoolDyadicDenominator]
  nlinarith

/-- After paying for twice as many dyadic slots and all new logical branches,
the aggregate stage budget still contracts by a factor of two. -/
theorem decodedRetryPoolStageAggregateShortageBudget_succ_le_half
    {w r m : Nat} (h : Admissible w r m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon)
    (stage : Nat) :
    decodedRetryPoolStageAggregateShortageBudget w r m epsilon (stage + 1) <=
      decodedRetryPoolStageAggregateShortageBudget w r m epsilon stage / 2 := by
  have hkpos : 0 < (logicalOutputCount m w : Real) := by
    exact_mod_cast routedDepthLogicalOutputCount_pos m w
  have hcoefficient :
      0 <= (logicalOutputCount m w : Real) ^ (stage + 1) *
        decodedRetryPoolDyadicDenominator (stage + 1) *
        physicalInputCount m w := by positivity
  have henv :=
    decodedRetryPoolErrorEnvelope_succ_le_div_four_mul_logicalOutputCount
      h epsilon hpool stage
  have hdyadic :
      (decodedRetryPoolDyadicDenominator (stage + 1) : Real) =
        2 * decodedRetryPoolDyadicDenominator stage := by
    change ((2 ^ (stage + 4) : Nat) : Real) = 2 * ((2 ^ (stage + 3) : Nat) : Real)
    rw [show stage + 4 = (stage + 3) + 1 by omega, pow_succ]
    push_cast
    ring
  unfold decodedRetryPoolStageAggregateShortageBudget
  calc
    (logicalOutputCount m w : Real) ^ (stage + 1) *
          decodedRetryPoolDyadicDenominator (stage + 1) *
          physicalInputCount m w *
          routedDepthErrorEnvelope w r m epsilon (stage + 1) <=
        ((logicalOutputCount m w : Real) ^ (stage + 1) *
          decodedRetryPoolDyadicDenominator (stage + 1) *
          physicalInputCount m w) *
          (routedDepthErrorEnvelope w r m epsilon stage /
            (4 * (logicalOutputCount m w : Real))) :=
      mul_le_mul_of_nonneg_left henv hcoefficient
    _ = ((logicalOutputCount m w : Real) ^ stage *
          decodedRetryPoolDyadicDenominator stage *
          physicalInputCount m w *
          routedDepthErrorEnvelope w r m epsilon stage) / 2 := by
      rw [pow_succ, hdyadic]
      field_simp [ne_of_gt hkpos]
      ring

/-- The finite sum of all literal stage/pool shortage budgets is uniformly
bounded by one quarter.  This is the numerical union-bound budget later
consumed by the actual physical history proof. -/
theorem decodedRetryPoolStageAggregateShortageBudget_sum_le_one_quarter
    {w r m : Nat} (h : Admissible w r m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon)
    (depth : Nat) :
    (∑ stage : Fin depth,
      decodedRetryPoolStageAggregateShortageBudget w r m epsilon stage.1) <= 1 / 4 := by
  have htail :
      (∑ stage : Fin depth,
          decodedRetryPoolStageAggregateShortageBudget w r m epsilon stage.1) +
        2 * decodedRetryPoolStageAggregateShortageBudget w r m epsilon depth <=
          2 * decodedRetryPoolStageAggregateShortageBudget w r m epsilon 0 := by
    induction depth with
    | zero => simp
    | succ depth ih =>
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last]
        have hnext := decodedRetryPoolStageAggregateShortageBudget_succ_le_half
          h epsilon hpool depth
        nlinarith
  have hsum :
      (∑ stage : Fin depth,
        decodedRetryPoolStageAggregateShortageBudget w r m epsilon stage.1) <=
        2 * decodedRetryPoolStageAggregateShortageBudget w r m epsilon 0 := by
    have hnonneg := decodedRetryPoolStageAggregateShortageBudget_nonneg
      w r m epsilon depth
    nlinarith
  have hzero :=
    decodedRetryPoolStageAggregateShortageBudget_zero_le_one_sixteenth epsilon hpool
  nlinarith

end HH18Parameterized
end Distillation
end QEC
