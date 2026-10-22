import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Physical.ScheduleBridge

/-!
# Parameterized HH18 exact retry-pool batching

The actual backward retry schedule uses a ceiling at every stage.  This module
chooses a finite terminal batch containing each dyadic divisibility factor,
proves that every ceiling is then exact, and computes the literal physical
root and terminal carrier sizes.  A telescoping natural-number estimate bounds
the accumulated retry factor by `4/3`, uniformly in the protocol depth.
-/

noncomputable section

namespace QEC.Distillation.HH18Parameterized

open Coding
open Coding.ReedMuller Coding.PuncturedReedMuller

/-- A terminal batch containing every dyadic divisibility factor below the
chosen depth. -/
def decodedRetryPoolExactBatchTerminalRequest : Nat → Nat
  | 0 => 1
  | z + 1 =>
      (decodedRetryPoolDyadicDenominator z - 1) *
        decodedRetryPoolExactBatchTerminalRequest z

/-- The product of the corresponding dyadic attempt denominators. -/
def decodedRetryPoolExactBatchDenominatorProduct : Nat → Nat
  | 0 => 1
  | z + 1 =>
      decodedRetryPoolDyadicDenominator z *
        decodedRetryPoolExactBatchDenominatorProduct z

private theorem decodedRetryPoolDyadicDenominator_sub_one_pos' (stage : Nat) :
    0 < decodedRetryPoolDyadicDenominator stage - 1 := by
  unfold decodedRetryPoolDyadicDenominator
  have hpow : 1 < 2 ^ (stage + 3) := by
    exact one_lt_pow₀ (by norm_num) (by omega)
  omega

/-- A request divisible by the stage slack makes the compiled ceiling exact. -/
theorem decodedRetryPoolDyadicAttempts_slack_multiple
    (stage multiple : Nat) :
    decodedRetryPoolDyadicAttempts stage
        ((decodedRetryPoolDyadicDenominator stage - 1) * multiple) =
      decodedRetryPoolDyadicDenominator stage * multiple := by
  unfold decodedRetryPoolDyadicAttempts decodedRetryPoolCeilDiv
  let denominator := decodedRetryPoolDyadicDenominator stage - 1
  have hdenominator : 0 < denominator := by
    simpa [denominator] using decodedRetryPoolDyadicDenominator_sub_one_pos' stage
  change
    ((decodedRetryPoolDyadicDenominator stage * (denominator * multiple) +
          denominator - 1) /
        denominator) =
      decodedRetryPoolDyadicDenominator stage * multiple
  have hnumerator :
      decodedRetryPoolDyadicDenominator stage * (denominator * multiple) =
        denominator * (decodedRetryPoolDyadicDenominator stage * multiple) := by
    ring
  rw [hnumerator]
  change
    ((denominator * (decodedRetryPoolDyadicDenominator stage * multiple) +
          denominator - 1) /
        denominator) =
      decodedRetryPoolDyadicDenominator stage * multiple
  change
    (denominator * (decodedRetryPoolDyadicDenominator stage * multiple)) ⌈/⌉
        denominator =
      decodedRetryPoolDyadicDenominator stage * multiple
  exact smul_ceilDiv hdenominator _

/-- Removing the highest exact batching factor turns a successor-depth
backward schedule into the preceding-depth schedule with its physical and
dyadic multipliers carried into the terminal request. -/
theorem decodedRetryPoolExactBatch_backwardRequired_succ
    (m w z multiple distance : Nat) :
    decodedRetryPoolBackwardRequiredAtDistance m w (z + 1)
        (multiple * decodedRetryPoolExactBatchTerminalRequest (z + 1))
        (distance + 1) =
      decodedRetryPoolBackwardRequiredAtDistance m w z
        ((physicalInputCount m w * decodedRetryPoolDyadicDenominator z * multiple) *
          decodedRetryPoolExactBatchTerminalRequest z)
        distance := by
  induction distance with
  | zero =>
      change physicalInputCount m w *
          decodedRetryPoolDyadicAttempts z
            (multiple * decodedRetryPoolExactBatchTerminalRequest (z + 1)) =
        (physicalInputCount m w * decodedRetryPoolDyadicDenominator z * multiple) *
          decodedRetryPoolExactBatchTerminalRequest z
      rw [decodedRetryPoolExactBatchTerminalRequest]
      have hrequest :
          multiple *
              ((decodedRetryPoolDyadicDenominator z - 1) *
                decodedRetryPoolExactBatchTerminalRequest z) =
            (decodedRetryPoolDyadicDenominator z - 1) *
              (multiple * decodedRetryPoolExactBatchTerminalRequest z) := by
        ring
      rw [hrequest, decodedRetryPoolDyadicAttempts_slack_multiple]
      ring
  | succ distance ih =>
      conv_lhs => rw [decodedRetryPoolBackwardRequiredAtDistance]
      conv_rhs => rw [decodedRetryPoolBackwardRequiredAtDistance]
      have hstage :
          z + 1 - (distance + 1 + 1) = z - (distance + 1) := by
        omega
      rw [hstage, ih]

/-- At positive depth, an exact terminal batch makes the root attempt count
equal to the base physical growth times the product of dyadic denominators. -/
theorem decodedRetryPoolExactBatch_root_attempts
    (m w z multiple : Nat) :
    decodedRetryPoolBackwardAttempts m w (z + 1)
        (multiple * decodedRetryPoolExactBatchTerminalRequest (z + 1))
        ⟨0, Nat.succ_pos z⟩ =
      multiple * physicalInputCount m w ^ z *
        decodedRetryPoolExactBatchDenominatorProduct (z + 1) := by
  induction z generalizing multiple with
  | zero =>
      change decodedRetryPoolDyadicAttempts 0
          (multiple * decodedRetryPoolExactBatchTerminalRequest 1) =
        multiple * physicalInputCount m w ^ 0 *
          decodedRetryPoolExactBatchDenominatorProduct 1
      rw [decodedRetryPoolExactBatchTerminalRequest]
      have hrequest :
          multiple *
              ((decodedRetryPoolDyadicDenominator 0 - 1) *
                decodedRetryPoolExactBatchTerminalRequest 0) =
            (decodedRetryPoolDyadicDenominator 0 - 1) * multiple := by
        simp [decodedRetryPoolExactBatchTerminalRequest, Nat.mul_comm]
      rw [hrequest, decodedRetryPoolDyadicAttempts_slack_multiple]
      simp [decodedRetryPoolExactBatchDenominatorProduct, Nat.mul_comm]
  | succ z ih =>
      change decodedRetryPoolDyadicAttempts 0
          (decodedRetryPoolBackwardRequiredAtDistance m w (z + 2)
            (multiple * decodedRetryPoolExactBatchTerminalRequest (z + 2))
            (z + 1)) =
        multiple * physicalInputCount m w ^ (z + 1) *
          decodedRetryPoolExactBatchDenominatorProduct (z + 2)
      rw [decodedRetryPoolExactBatch_backwardRequired_succ
        m w (z + 1) multiple z]
      change decodedRetryPoolBackwardAttempts m w (z + 1)
          (((physicalInputCount m w * decodedRetryPoolDyadicDenominator (z + 1) *
              multiple) * decodedRetryPoolExactBatchTerminalRequest (z + 1)))
          ⟨0, Nat.succ_pos z⟩ =
        multiple * physicalInputCount m w ^ (z + 1) *
          decodedRetryPoolExactBatchDenominatorProduct (z + 2)
      rw [ih]
      rw [show decodedRetryPoolExactBatchDenominatorProduct (z + 2) =
        decodedRetryPoolDyadicDenominator (z + 1) *
          decodedRetryPoolExactBatchDenominatorProduct (z + 1) by rfl, pow_succ]
      ring

/-- The literal physical root carrier for the exact batch has cardinality
`n ^ z` times the exact dyadic-denominator product. -/
theorem decodedRetryPoolExactBatch_rootInputSlots_card
    (m w z : Nat) :
    Fintype.card
        (decodedRetryPoolPhysicalProtocolRootInputSlots m w (z + 1)
          (decodedRetryPoolExactBatchTerminalRequest (z + 1)) (Nat.succ_pos z)) =
      physicalInputCount m w ^ (z + 1) *
        decodedRetryPoolExactBatchDenominatorProduct (z + 1) := by
  rw [decodedRetryPoolPhysicalProtocolRootInputSlots_card]
  have hattempts := decodedRetryPoolExactBatch_root_attempts m w z 1
  simp only [one_mul] at hattempts
  rw [hattempts, pow_succ]
  ring

/-- The literal terminal carrier for the exact batch has cardinality equal to
the terminal batch factor times `k ^ z`. -/
theorem decodedRetryPoolExactBatch_terminalOutputSlots_card
    (m w z : Nat) :
    Fintype.card
        (decodedRetryPoolPhysicalProtocolTerminalOutputSlots m w z
          (decodedRetryPoolExactBatchTerminalRequest z)) =
      decodedRetryPoolExactBatchTerminalRequest z *
        logicalOutputCount m w ^ z :=
  decodedRetryPoolPhysicalProtocolTerminalOutputSlots_card m w z
    (decodedRetryPoolExactBatchTerminalRequest z)

/-- A telescoping integer invariant for the accumulated dyadic retry factor. -/
theorem decodedRetryPoolExactBatch_dyadic_telescope (z : Nat) :
    3 * 2 ^ z * decodedRetryPoolExactBatchDenominatorProduct z ≤
      (2 ^ (z + 2) - 1) * decodedRetryPoolExactBatchTerminalRequest z := by
  induction z with
  | zero =>
      norm_num [decodedRetryPoolExactBatchDenominatorProduct,
        decodedRetryPoolExactBatchTerminalRequest]
  | succ z ih =>
      have hpowOne : 2 ^ (z + 1) = 2 * 2 ^ z := by
        rw [pow_succ]
        ring
      have hpowTwo : 2 ^ (z + 2) = 4 * 2 ^ z := by
        rw [pow_add]
        norm_num
        ring
      have hpowThree : 2 ^ (z + 3) = 8 * 2 ^ z := by
        rw [pow_add]
        norm_num
        ring
      have hdenominator :
          decodedRetryPoolDyadicDenominator z = 8 * 2 ^ z := by
        unfold decodedRetryPoolDyadicDenominator
        exact hpowThree
      rw [hpowTwo] at ih
      let t := 2 ^ z
      let denominator := decodedRetryPoolDyadicDenominator z
      let a := 4 * t - 1
      have ht : 1 ≤ t := by
        have htpos : 0 < t := by
          dsimp [t]
          positivity
        omega
      have hdenominatorA : denominator = 2 * a + 2 := by
        dsimp [denominator, a, t]
        rw [hdenominator]
        omega
      have hnextA : 8 * t - 1 = 2 * a + 1 := by
        dsimp [a]
        omega
      have hcoefficient :
          2 * denominator * a ≤
            (8 * t - 1) * (denominator - 1) := by
        rw [hdenominatorA, hnextA]
        have hsub : 2 * a + 2 - 1 = 2 * a + 1 := by omega
        rw [hsub]
        nlinarith
      have hscaled := Nat.mul_le_mul_left (2 * denominator) ih
      rw [decodedRetryPoolExactBatchDenominatorProduct,
        decodedRetryPoolExactBatchTerminalRequest]
      change 3 * 2 ^ (z + 1) *
          (denominator * decodedRetryPoolExactBatchDenominatorProduct z) ≤
        (2 ^ (z + 3) - 1) *
          ((denominator - 1) * decodedRetryPoolExactBatchTerminalRequest z)
      calc
        3 * 2 ^ (z + 1) *
              (denominator * decodedRetryPoolExactBatchDenominatorProduct z) =
            (2 * denominator) *
              (3 * t * decodedRetryPoolExactBatchDenominatorProduct z) := by
                rw [hpowOne]
                dsimp [t]
                ring
        _ ≤ (2 * denominator) *
              (a * decodedRetryPoolExactBatchTerminalRequest z) := by
                simpa [a, t] using hscaled
        _ = (2 * denominator * a) *
              decodedRetryPoolExactBatchTerminalRequest z := by ring
        _ ≤ ((8 * t - 1) * (denominator - 1)) *
              decodedRetryPoolExactBatchTerminalRequest z :=
            Nat.mul_le_mul_right _ hcoefficient
        _ = (2 ^ (z + 3) - 1) *
              ((denominator - 1) * decodedRetryPoolExactBatchTerminalRequest z) := by
            rw [hpowThree]
            ring

/-- The exact terminal request is always a nonempty finite batch. -/
theorem decodedRetryPoolExactBatchTerminalRequest_pos (z : Nat) :
    0 < decodedRetryPoolExactBatchTerminalRequest z := by
  induction z with
  | zero => simp [decodedRetryPoolExactBatchTerminalRequest]
  | succ z ih =>
      rw [decodedRetryPoolExactBatchTerminalRequest]
      exact mul_pos (decodedRetryPoolDyadicDenominator_sub_one_pos' z) ih

/-- The exact dyadic-denominator product is always positive. -/
theorem decodedRetryPoolExactBatchDenominatorProduct_pos (z : Nat) :
    0 < decodedRetryPoolExactBatchDenominatorProduct z := by
  induction z with
  | zero => simp [decodedRetryPoolExactBatchDenominatorProduct]
  | succ z ih =>
      rw [decodedRetryPoolExactBatchDenominatorProduct]
      exact mul_pos (by unfold decodedRetryPoolDyadicDenominator; positivity) ih

/-- The accumulated exact retry multiplier is uniformly at most `4/3` in
cross-multiplied natural-number form. -/
theorem decodedRetryPoolExactBatch_retryFactor_four_thirds (z : Nat) :
    3 * decodedRetryPoolExactBatchDenominatorProduct z ≤
      4 * decodedRetryPoolExactBatchTerminalRequest z := by
  have htelescope := decodedRetryPoolExactBatch_dyadic_telescope z
  have hpowTwo : 2 ^ (z + 2) = 4 * 2 ^ z := by
    rw [pow_add]
    norm_num
    ring
  rw [hpowTwo] at htelescope
  have hcoefficient : 4 * 2 ^ z - 1 ≤ 4 * 2 ^ z := Nat.sub_le _ _
  have hscaledRight := Nat.mul_le_mul_right
    (decodedRetryPoolExactBatchTerminalRequest z) hcoefficient
  have hcombined := htelescope.trans hscaledRight
  have hfactor :
      2 ^ z * (3 * decodedRetryPoolExactBatchDenominatorProduct z) ≤
        2 ^ z * (4 * decodedRetryPoolExactBatchTerminalRequest z) := by
    simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hcombined
  exact Nat.le_of_mul_le_mul_left hfactor (by positivity)

/-- For the exact divisible terminal batch, the literal physical root carrier
has at most a `4/3` retry factor over the `n^z/k^z` input/output ratio. -/
theorem decodedRetryPoolExactBatch_physicalCost_four_thirds
    (m w z : Nat) :
    3 * logicalOutputCount m w ^ (z + 1) *
        Fintype.card
          (decodedRetryPoolPhysicalProtocolRootInputSlots m w (z + 1)
            (decodedRetryPoolExactBatchTerminalRequest (z + 1)) (Nat.succ_pos z)) ≤
      4 * physicalInputCount m w ^ (z + 1) *
        Fintype.card
          (decodedRetryPoolPhysicalProtocolTerminalOutputSlots m w (z + 1)
            (decodedRetryPoolExactBatchTerminalRequest (z + 1))) := by
  rw [decodedRetryPoolExactBatch_rootInputSlots_card,
    decodedRetryPoolExactBatch_terminalOutputSlots_card]
  have hfactor := decodedRetryPoolExactBatch_retryFactor_four_thirds (z + 1)
  have hscaled := Nat.mul_le_mul_left
    (physicalInputCount m w ^ (z + 1) * logicalOutputCount m w ^ (z + 1)) hfactor
  convert hscaled using 1 <;> ring

end QEC.Distillation.HH18Parameterized
