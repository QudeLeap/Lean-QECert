import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Schedule.ExactBatching
import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Physical.AcceptedError

/-!
# Exact finite-slot cost of the physical HH18 retry protocol

For each positive protocol depth, the exact divisible terminal request names a
single genuine physical run.  This layer derives its finite input and output
slot types, success yield, and successful-output cost from that same run.  The
cost bound combines the exact physical retry count with the run's proved
three-quarters success probability; it stores no independent cost conclusion.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Parameterized

open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.FiniteInstrument

attribute [local instance 100] Fintype.ofFinite

/-- Literal raw-resource slots of the exact physical batch at depth `depth+1`. -/
abbrev decodedRetryPoolPhysicalExactBatchInputSlots
    (m w depth : Nat) :=
  decodedRetryPoolPhysicalProtocolRootInputSlots m w (depth + 1)
    (decodedRetryPoolExactBatchTerminalRequest (depth + 1))
    (Nat.succ_pos depth)

/-- Literal terminal-qubit coordinates of that same exact physical batch. -/
abbrev decodedRetryPoolPhysicalExactBatchOutputSlots
    (m w depth : Nat) :=
  decodedRetryPoolPhysicalProtocolOutputCoordinate m w (depth + 1)
    (decodedRetryPoolExactBatchTerminalRequest (depth + 1))
    (Nat.succ_pos depth)

/-- The genuine exact-batch physical run, with no detached schedule shell. -/
noncomputable abbrev decodedRetryPoolPhysicalExactBatchRun
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :=
  decodedRetryPoolPhysicalProtocolRun h hdegree epsilon (depth + 1)
    (decodedRetryPoolExactBatchTerminalRequest (depth + 1))
    (Nat.succ_pos depth) rhoUnit

/-- Expected-yield factor derived from the genuine run's Born success mass. -/
noncomputable def decodedRetryPoolPhysicalExactBatchYield
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) : NNReal :=
  ⟨(decodedRetryPoolPhysicalExactBatchRun
      h hdegree epsilon depth rhoUnit).successProbability,
    (decodedRetryPoolPhysicalExactBatchRun
      h hdegree epsilon depth rhoUnit).success_nonneg⟩

/-- The derived yield is definitionally the actual run success probability. -/
theorem decodedRetryPoolPhysicalExactBatchYield_eq_runSuccess
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    (decodedRetryPoolPhysicalExactBatchYield
        h hdegree epsilon depth rhoUnit : Real) =
      (decodedRetryPoolPhysicalExactBatchRun
        h hdegree epsilon depth rhoUnit).successProbability :=
  rfl

/-- The literal input-slot cardinality is the resource count stored by the
same genuine run. -/
theorem decodedRetryPoolPhysicalExactBatchInputSlots_card_eq_run_resourceCount
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    Fintype.card (decodedRetryPoolPhysicalExactBatchInputSlots m w depth) =
      (decodedRetryPoolPhysicalExactBatchRun
        h hdegree epsilon depth rhoUnit).resourceCount := by
  rw [decodedRetryPoolPhysicalProtocolRootInputSlots_card,
    decodedRetryPoolPhysicalProtocolRun_resourceCount]

/-- The literal output-coordinate carrier has the exact batch factor times
`k^(depth+1)` terminal qubits. -/
theorem decodedRetryPoolPhysicalExactBatchOutputSlots_card
    (m w depth : Nat) :
    Fintype.card (decodedRetryPoolPhysicalExactBatchOutputSlots m w depth) =
      decodedRetryPoolExactBatchTerminalRequest (depth + 1) *
        logicalOutputCount m w ^ (depth + 1) :=
  decodedRetryPoolPhysicalProtocolOutputCoordinate_card m w (depth + 1)
    (decodedRetryPoolExactBatchTerminalRequest (depth + 1))
    (Nat.succ_pos depth)

/-- The actual exact-batch input/output slot ratio has only the uniform
`4/3` retry overhead beyond `(n/k)^(depth+1)`. -/
theorem decodedRetryPoolPhysicalExactBatchInputOutputRatio_le_four_thirds
    (m w depth : Nat) :
    DependentBatch.typedInputOutputRatio
        (decodedRetryPoolPhysicalExactBatchInputSlots m w depth)
        (decodedRetryPoolPhysicalExactBatchOutputSlots m w depth) <=
      (4 / 3 : Real) *
        ((physicalInputCount m w : Real) / logicalOutputCount m w) ^
          (depth + 1) := by
  let InputSlots := decodedRetryPoolPhysicalExactBatchInputSlots m w depth
  let OutputSlots := decodedRetryPoolPhysicalExactBatchOutputSlots m w depth
  have houtputCard :
      Fintype.card OutputSlots =
        Fintype.card
          (decodedRetryPoolPhysicalProtocolTerminalOutputSlots m w (depth + 1)
            (decodedRetryPoolExactBatchTerminalRequest (depth + 1))) := by
    dsimp only [OutputSlots]
    rw [decodedRetryPoolPhysicalExactBatchOutputSlots_card,
      decodedRetryPoolExactBatch_terminalOutputSlots_card]
  have hcrossNat := decodedRetryPoolExactBatch_physicalCost_four_thirds
    m w depth
  change 3 * logicalOutputCount m w ^ (depth + 1) *
      Fintype.card InputSlots <=
    4 * physicalInputCount m w ^ (depth + 1) *
      Fintype.card
        (decodedRetryPoolPhysicalProtocolTerminalOutputSlots m w (depth + 1)
          (decodedRetryPoolExactBatchTerminalRequest (depth + 1))) at hcrossNat
  rw [← houtputCard] at hcrossNat
  have hcross :
      (3 : Real) * (logicalOutputCount m w : Real) ^ (depth + 1) *
          Fintype.card InputSlots <=
        4 * (physicalInputCount m w : Real) ^ (depth + 1) *
          Fintype.card OutputSlots := by
    exact_mod_cast hcrossNat
  have hk : 0 < (logicalOutputCount m w : Real) := by
    exact_mod_cast routedDepthLogicalOutputCount_pos m w
  have hq : 0 < decodedRetryPoolExactBatchTerminalRequest (depth + 1) :=
    decodedRetryPoolExactBatchTerminalRequest_pos (depth + 1)
  have houtputNat : 0 < Fintype.card OutputSlots := by
    dsimp only [OutputSlots]
    rw [decodedRetryPoolPhysicalExactBatchOutputSlots_card]
    exact mul_pos hq (pow_pos (routedDepthLogicalOutputCount_pos m w) _)
  have houtput : 0 < (Fintype.card OutputSlots : Real) := by
    exact_mod_cast houtputNat
  unfold DependentBatch.typedInputOutputRatio
  rw [div_pow]
  calc
    (Fintype.card InputSlots : Real) / Fintype.card OutputSlots <=
        ((4 / 3 : Real) * (physicalInputCount m w : Real) ^ (depth + 1)) /
          (logicalOutputCount m w : Real) ^ (depth + 1) := by
      apply (div_le_div_iff₀ houtput (pow_pos hk _)).2
      nlinarith [hcross]
    _ = (4 / 3 : Real) *
        ((physicalInputCount m w : Real) ^ (depth + 1) /
          (logicalOutputCount m w : Real) ^ (depth + 1)) := by ring

/-- Successful-output cost derived from the exact slots and actual run yield. -/
noncomputable def decodedRetryPoolPhysicalExactBatchTypedSuccessfulOutputCost
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) : Real :=
  DependentBatch.typedSuccessfulOutputCost
    (decodedRetryPoolPhysicalExactBatchInputSlots m w depth)
    (decodedRetryPoolPhysicalExactBatchOutputSlots m w depth)
    (decodedRetryPoolPhysicalExactBatchYield
      h hdegree epsilon depth rhoUnit)

/-- The physical retry factor and actual success lower bound together give a
uniform `16/9` successful-output-cost factor. -/
theorem decodedRetryPoolPhysicalExactBatchTypedSuccessfulOutputCost_le_sixteen_ninths
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon)
    (depth : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    decodedRetryPoolPhysicalExactBatchTypedSuccessfulOutputCost
        h hdegree epsilon depth rhoUnit <=
      (16 / 9 : Real) *
        ((physicalInputCount m w : Real) / logicalOutputCount m w) ^
          (depth + 1) := by
  let ratio := DependentBatch.typedInputOutputRatio
    (decodedRetryPoolPhysicalExactBatchInputSlots m w depth)
    (decodedRetryPoolPhysicalExactBatchOutputSlots m w depth)
  let yieldFactor := decodedRetryPoolPhysicalExactBatchYield
    h hdegree epsilon depth rhoUnit
  have hratio : ratio <= (4 / 3 : Real) *
      ((physicalInputCount m w : Real) / logicalOutputCount m w) ^
        (depth + 1) :=
    decodedRetryPoolPhysicalExactBatchInputOutputRatio_le_four_thirds
      m w depth
  have hratioNonneg : 0 <= ratio := by
    dsimp only [ratio]
    unfold DependentBatch.typedInputOutputRatio
    positivity
  have hyield : (3 / 4 : Real) <= (yieldFactor : Real) := by
    dsimp only [yieldFactor]
    exact decodedRetryPoolPhysicalProtocolRun_success_three_quarters_le
      h hdegree epsilon hpool (depth + 1)
        (decodedRetryPoolExactBatchTerminalRequest (depth + 1))
        (Nat.succ_pos depth) rhoUnit
  unfold decodedRetryPoolPhysicalExactBatchTypedSuccessfulOutputCost
    DependentBatch.typedSuccessfulOutputCost
  change ratio / (yieldFactor : Real) <= _
  calc
    ratio / (yieldFactor : Real) <= ratio / (3 / 4 : Real) :=
      div_le_div_of_nonneg_left hratioNonneg (by norm_num) hyield
    _ <= ((4 / 3 : Real) *
          ((physicalInputCount m w : Real) / logicalOutputCount m w) ^
            (depth + 1)) / (3 / 4 : Real) := by
      exact div_le_div_of_nonneg_right hratio (by norm_num)
    _ = (16 / 9 : Real) *
        ((physicalInputCount m w : Real) / logicalOutputCount m w) ^
          (depth + 1) := by ring

end HH18Parameterized
end Distillation
end QEC
