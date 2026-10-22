import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Physical.Accounting
import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Successor.RecordRouting
import QEC.Distillation.LowOverheadProtocol.Parameterized.Schedule

/-!
# Parameterized HH18 physical retry-pool schedule bridge

The arbitrary-depth physical chain and the routed asymptotic schedule both
use `decodedInstrument`.  This module proves that connection explicitly:
every routed stage success is the accepted Born weight of that instrument,
the pooled yield is the finite average of products of those physical weights,
and an attained error path retains the same stage weights.  It then exports
the already-derived dependent physical-overhead predicate through that proved
connection, without a fixed-register family shell or stored conclusions.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Parameterized

open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open scoped BigOperators

attribute [local instance 100] Fintype.ofFinite

/-- The finite physical slots consumed by the actual root retry pool. -/
abbrev decodedRetryPoolPhysicalProtocolRootInputSlots
    (m w z q : Nat) (hz : 0 < z) :=
  decodedRetryPoolBackwardRootRawCarrier m w z q hz

/-- The finite logical slots delivered by the actual terminal retry pool. -/
abbrev decodedRetryPoolPhysicalProtocolTerminalOutputSlots
    (m w z q : Nat) :=
  decodedRetryPoolBackwardTerminalGoodCarrier m w z q

/-- The actual root carrier has one physical block for every derived root
retry attempt. -/
theorem decodedRetryPoolPhysicalProtocolRootInputSlots_card
    (m w z q : Nat) (hz : 0 < z) :
    Fintype.card (decodedRetryPoolPhysicalProtocolRootInputSlots m w z q hz) =
      physicalInputCount m w *
        decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩ :=
  decodedRetryPoolBackwardRootRawCarrier_card m w z q hz

/-- The actual terminal carrier has the requested batch factor times exactly
`k ^ z` logical output slots. -/
theorem decodedRetryPoolPhysicalProtocolTerminalOutputSlots_card
    (m w z q : Nat) :
    Fintype.card (decodedRetryPoolPhysicalProtocolTerminalOutputSlots m w z q) =
      q * logicalOutputCount m w ^ z :=
  decodedRetryPoolBackwardTerminalGoodCarrier_card m w z q

/-- A fixed accepted output port of the actual parent retry pool supplies the
literal tensor-product input consumed by the next retry pool on the appended
routed path.  This is a marginal statement for one selected port; it does not
assume that distinct sibling ports are independent. -/
theorem routedDepthPathAcceptedPortSuccessorInputChannel_mapDensity
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    {depth : Nat} (path : routedDepthOutputSlots m w depth)
    (port : LogicalSite m w)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    (decodedRetryPoolAcceptedPortSuccessorInputChannel
      m w z q stage hstage port).mapDensity
        (decodedRetryPoolAcceptedProductDensity h hdegree
          (routedDepthPathRate h hdegree epsilon hsmall depth path)
          rhoUnit
          (decodedRetryPoolBackwardSchedule m w z q stage)) =
      tensorPowerProductInput
        (prepareMeasuredResources m w
          (noisyResources m w
            (routedDepthPathRate h hdegree epsilon hsmall (depth + 1)
              (routedDepthOutputPathAppend m w depth path port))))
        rhoUnit
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩) := by
  rw [routedDepthPathRate_append_eq_nextInputRate]
  exact decodedRetryPoolAcceptedPortSuccessorInputChannel_mapDensity
    h hdegree
    (routedDepthPathRate h hdegree epsilon hsmall depth path)
    z q stage hstage port
    (routedDepthPathNextHalf h hdegree epsilon hsmall path port) rhoUnit

/-- The observed history mass on that actual successor input is the tensor
product of the one-level accepted/rejected Born weights at the appended path
rate. -/
theorem
    routedDepthPathAcceptedPortSuccessorBornWeight_eq_tensorPowerBornProduct
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    {depth : Nat} (path : routedDepthOutputSlots m w depth)
    (port : LogicalSite m w)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (history : tensorPowerHistory DistillationOutcome
      (decodedRetryPoolBackwardAttempts m w z q
        ⟨stage.1 + 1, hstage⟩)) :
    decodedRetryPoolAcceptedPortSuccessorBornWeight h hdegree
        (routedDepthPathRate h hdegree epsilon hsmall depth path)
        z q stage hstage port
        (routedDepthPathNextHalf h hdegree epsilon hsmall path port)
        rhoUnit history =
      tensorPowerBornProduct (decodedInstrument h hdegree)
        (prepareMeasuredResources m w
          (noisyResources m w
            (routedDepthPathRate h hdegree epsilon hsmall (depth + 1)
              (routedDepthOutputPathAppend m w depth path port))))
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩) history := by
  rw [routedDepthPathRate_append_eq_nextInputRate]
  exact
    decodedRetryPoolAcceptedPortSuccessorBornWeight_eq_tensorPowerBornProduct
      h hdegree
      (routedDepthPathRate h hdegree epsilon hsmall depth path)
      z q stage hstage port
      (routedDepthPathNextHalf h hdegree epsilon hsmall path port)
      rhoUnit history

/-- When the observed successor history is large enough and has positive
mass, normalizing its actual branch yields the accepted-product density at
the appended path rate. -/
theorem
    routedDepthPathAcceptedPortSuccessorConditionalDensity_eq_acceptedProduct
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    {depth : Nat} (path : routedDepthOutputSlots m w depth)
    (port : LogicalSite m w)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (history : tensorPowerHistory DistillationOutcome
      (decodedRetryPoolBackwardAttempts m w z q
        ⟨stage.1 + 1, hstage⟩))
    (henough :
      decodedRetryPoolBackwardSchedule m w z q
          ⟨stage.1 + 1, hstage⟩ ≤
        (tensorPowerAcceptedIndices decodedRetryPoolAccepts
          (decodedRetryPoolBackwardAttempts m w z q
            ⟨stage.1 + 1, hstage⟩) history).card)
    (hpositive : 0 <
      decodedRetryPoolAcceptedPortSuccessorBornWeight h hdegree
        (routedDepthPathRate h hdegree epsilon hsmall depth path)
        z q stage hstage port
        (routedDepthPathNextHalf h hdegree epsilon hsmall path port)
        rhoUnit history) :
    (decodedRetryPoolInstrument h hdegree
      (decodedRetryPoolBackwardAttempts m w z q
        ⟨stage.1 + 1, hstage⟩)
      (decodedRetryPoolBackwardSchedule m w z q
        ⟨stage.1 + 1, hstage⟩)).conditionalDensity
        ⟨history, PUnit.unit⟩
        ((decodedRetryPoolAcceptedPortSuccessorInputChannel
          m w z q stage hstage port).mapDensity
            (decodedRetryPoolAcceptedProductDensity h hdegree
              (routedDepthPathRate h hdegree epsilon hsmall depth path)
              rhoUnit
              (decodedRetryPoolBackwardSchedule m w z q stage)))
        hpositive =
      decodedRetryPoolAcceptedProductDensity h hdegree
        (routedDepthPathRate h hdegree epsilon hsmall (depth + 1)
          (routedDepthOutputPathAppend m w depth path port))
        rhoUnit
        (decodedRetryPoolBackwardSchedule m w z q
          ⟨stage.1 + 1, hstage⟩) := by
  rw [routedDepthPathRate_append_eq_nextInputRate]
  exact
    decodedRetryPoolAcceptedPortSuccessorConditionalDensity_eq_acceptedProduct
      h hdegree
      (routedDepthPathRate h hdegree epsilon hsmall depth path)
      z q stage hstage port
      (routedDepthPathNextHalf h hdegree epsilon hsmall path port)
      rhoUnit history henough hpositive

/-- Every routed-stage success probability is exactly the accepted Born
weight of the decoded finite instrument used by each physical retry pool. -/
theorem routedDepthPathStageRun_successProbability_eq_decodedInstrument_bornWeight
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) (stage : Fin depth) :
    (routedDepthPathStageRun h hdegree epsilon hsmall depth path stage).successProbability =
      (decodedInstrument h hdegree).bornWeight .accepted
        (prepareMeasuredResources m w
          (noisyResources m w
            (routedDepthPathRate h hdegree epsilon hsmall stage.1
              (routedDepthPathStagePath m w depth path stage)))) := by
  unfold routedDepthPathStageRun
  rw [routedDepthPathActualRun_eq_resourceDecodedRun]
  change endpointWeight h hdegree
      (noisyResources m w
        (routedDepthPathRate h hdegree epsilon hsmall stage.1
          (routedDepthPathStagePath m w depth path stage))) .accepted = _
  rw [decodedInstrument_bornWeight_prepareMeasuredResources]

/-- A path yield is literally the product of accepted decoded-instrument Born
weights along that physical routed path. -/
theorem routedDepthPathYieldFactor_eq_decodedInstrument_bornWeight_product
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) :
    (routedDepthPathYieldFactor h hdegree epsilon hsmall depth path : ℝ) =
      ∏ stage : Fin depth,
        (decodedInstrument h hdegree).bornWeight .accepted
          (prepareMeasuredResources m w
            (noisyResources m w
              (routedDepthPathRate h hdegree epsilon hsmall stage.1
                (routedDepthPathStagePath m w depth path stage)))) := by
  rw [routedDepthPathYieldFactor_eq_actualStageSuccessProduct]
  apply Finset.prod_congr rfl
  intro stage _
  exact routedDepthPathStageRun_successProbability_eq_decodedInstrument_bornWeight
    h hdegree epsilon hsmall depth path stage

/-- The schedule yield is the normalized finite sum of physical accepted Born
weight products, one for every actual routed logical output path. -/
theorem routedDepthScheduleExpectedYield_eq_decodedInstrument_bornWeight_average
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    (routedDepthScheduleExpectedYield h hdegree epsilon hsmall depth : ℝ) =
      (∑ path : routedDepthOutputSlots m w depth,
        ∏ stage : Fin depth,
          (decodedInstrument h hdegree).bornWeight .accepted
            (prepareMeasuredResources m w
              (noisyResources m w
                (routedDepthPathRate h hdegree epsilon hsmall stage.1
                  (routedDepthPathStagePath m w depth path stage))))) /
        Fintype.card (routedDepthOutputSlots m w depth) := by
  rw [routedDepthPooledYield_eq_sum_div_card]
  apply congrArg (fun numerator : ℝ => numerator /
    Fintype.card (routedDepthOutputSlots m w depth))
  apply Finset.sum_congr rfl
  intro path _
  exact routedDepthPathYieldFactor_eq_decodedInstrument_bornWeight_product
    h hdegree epsilon hsmall depth path

/-- The reached finite error maximum is attained on a physical routed path,
and every stage of that same path exposes its decoded-instrument Born weight. -/
theorem routedDepthScheduleActualOutputError_exists_path_with_decodedInstrument_weights
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    ∃ path : routedDepthOutputSlots m w depth,
      routedDepthScheduleActualOutputError h hdegree epsilon hsmall depth =
          (routedDepthPathRate h hdegree epsilon hsmall depth path).1 ∧
        ∀ stage : Fin depth,
          (routedDepthPathStageRun h hdegree epsilon hsmall depth path stage).successProbability =
            (decodedInstrument h hdegree).bornWeight .accepted
              (prepareMeasuredResources m w
                (noisyResources m w
                  (routedDepthPathRate h hdegree epsilon hsmall stage.1
                    (routedDepthPathStagePath m w depth path stage)))) := by
  obtain ⟨path, hpath⟩ :=
    routedDepthScheduleActualOutputError_exists_path h hdegree epsilon hsmall depth
  refine ⟨path, hpath, ?_⟩
  intro stage
  exact routedDepthPathStageRun_successProbability_eq_decodedInstrument_bornWeight
    h hdegree epsilon hsmall depth path stage

/-- The proved physical schedule adapter for downstream asymptotics.  Its
yield and reached error are connected above to the same decoded finite
instrument that builds the arbitrary-depth retry-pool protocol. -/
theorem decodedRetryPoolPhysicalProtocol_physicalPolylogarithmicExpectedYieldOverhead
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon) :
    DependentBatch.physicalPolylogarithmicExpectedYieldOverhead
      (routedDepthScheduleInputSlots m w)
      (routedDepthScheduleOutputSlots m w)
      (routedDepthScheduleTargetError w r m epsilon)
      (routedDepthScheduleActualOutputError h hdegree epsilon hsmall)
      (routedDepthScheduleExpectedYield h hdegree epsilon hsmall)
      (routedDepthScheduleGamma w r m)
      (routedDepthScheduleCostCoefficient h epsilon) :=
  routedDepthSchedule_physicalPolylogarithmicExpectedYieldOverhead
    h hdegree epsilon hepsilon hsmall

end HH18Parameterized
end Distillation
end QEC
