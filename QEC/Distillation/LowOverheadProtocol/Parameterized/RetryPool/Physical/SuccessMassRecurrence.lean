import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Physical.BornMass
import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Successor.BranchProduct
import QEC.Semantics.Instruments.Tensor.MarginalBornMass
import QEC.Semantics.Instruments.TensorPower.BranchOperator
/-!
# Born-mass recurrence for physical HH18 routing success

This layer records the literal successful-prefix mass of the recursive
physical retry protocol.  At each successor stage it partitions that mass
into histories whose new pools all route successfully and histories whose
prefix was good but whose new stage fails.  The identity is a finite Born-mass
partition; it assumes no independence between sibling pools.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Parameterized

open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.FiniteInstrument
open scoped BigOperators

attribute [local instance 100] Fintype.ofFinite

local instance instPhysicalSuccessMassRecurrenceClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

private theorem sum_sigma_punit_filter_fst
    {alpha : Type*} [Fintype alpha] (predicate : alpha -> Prop)
    [DecidablePred predicate] (weight : (Sigma fun _ : alpha => PUnit) -> Real) :
    (∑ outcome ∈ Finset.univ.filter (fun outcome => predicate outcome.1),
      weight outcome) =
      ∑ value ∈ Finset.univ.filter predicate, weight ⟨value, PUnit.unit⟩ := by
  classical
  rw [Finset.sum_filter, Fintype.sum_sigma, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro value _
  simp

/-- The observed failure mass of one retry-pool outcome is exactly its
existing shortage mass. -/
theorem decodedRetryPoolOutcomeFailureMass_eq_shortageMass
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (attempts required : Nat)
    (rho : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) attempts)) :
    (∑ outcome ∈ Finset.univ.filter
        (fun outcome : Sigma fun _ : tensorPowerHistory DistillationOutcome attempts =>
          PUnit => decodedRetryPoolOutcomeEnough attempts required outcome ≠ true),
      (decodedRetryPoolInstrument h hdegree attempts required).bornWeight outcome rho) =
      decodedRetryPoolShortageMass h hdegree attempts required rho := by
  classical
  unfold decodedRetryPoolShortageMass decodedRetryPoolOutcomeEnough
  rw [Finset.sum_filter, Fintype.sum_sigma, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro history _
  by_cases hshort :
      (tensorPowerAcceptedIndices decodedRetryPoolAccepts attempts history).card < required
  · simp [hshort]
  · have henough :
        required ≤
          (tensorPowerAcceptedIndices decodedRetryPoolAccepts attempts history).card := by
      omega
    simp [hshort, henough]

/-- On a genuine accepted-parent product, failure of at least one actual
successor retry pool is bounded by the sum of the true per-port shortage
masses.  The routed successor input may be correlated across ports; this is
the finite-instrument union bound on its actual marginals. -/
theorem decodedRetryPoolSuccessorStageFailureMass_le_portShortageSum
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (hhalf : ∀ port : LogicalSite m w,
      selectedLogicalPortRawError h hdegree epsilon port ≤ 1 / 2)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    (∑ outcome ∈ Finset.univ.filter
        (fun outcome : decodedRetryPoolSuccessorStageOutcome
            m w z q stage hstage =>
          decodedRetryPoolSuccessorStageRoutingGood
            m w z q stage hstage outcome ≠ true),
      (decodedRetryPoolSuccessorStageInstrument
        h hdegree z q stage hstage).bornWeight outcome
          (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
            (decodedRetryPoolBackwardSchedule m w z q stage))) ≤
      ∑ port : LogicalSite m w,
        decodedRetryPoolShortageMass h hdegree
          (decodedRetryPoolBackwardAttempts m w z q
            ⟨stage.1 + 1, hstage⟩)
          (decodedRetryPoolBackwardSchedule m w z q
            ⟨stage.1 + 1, hstage⟩)
          (tensorPowerProductInput
            (prepareMeasuredResources m w
              (noisyResources m w
                (selectedLogicalPortNextInputRate
                  h hdegree epsilon port (hhalf port))))
            rhoUnit
            (decodedRetryPoolBackwardAttempts m w z q
              ⟨stage.1 + 1, hstage⟩)) := by
  classical
  let nextPool := decodedRetryPoolInstrument h hdegree
    (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
    (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩)
  let source := decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
    (decodedRetryPoolBackwardSchedule m w z q stage)
  let joint := (decodedRetryPoolSuccessorNestedInputChannel
    m w z q stage hstage).mapDensity source
  have hunion := tensorPower_bornWeight_any_coordinate_failure_le
    nextPool
    (decodedRetryPoolInstrument_complete h hdegree
      (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
      (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩))
    (fun poolOutcome =>
      decodedRetryPoolOutcomeEnough
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩)
        poolOutcome ≠ true)
    (logicalOutputCount m w) joint
  have hleft :
      (∑ outcome ∈ Finset.univ.filter
          (fun outcome : decodedRetryPoolSuccessorStageOutcome
              m w z q stage hstage =>
            decodedRetryPoolSuccessorStageRoutingGood
              m w z q stage hstage outcome ≠ true),
        (decodedRetryPoolSuccessorStageInstrument
          h hdegree z q stage hstage).bornWeight outcome source) =
        ∑ history ∈ Finset.univ.filter
          (fun history : tensorPowerHistory
              (Sigma fun _ : tensorPowerHistory DistillationOutcome
                (decodedRetryPoolBackwardAttempts m w z q
                  ⟨stage.1 + 1, hstage⟩) => PUnit)
              (logicalOutputCount m w) =>
            ∃ branch : Fin (logicalOutputCount m w),
              decodedRetryPoolOutcomeEnough
                (decodedRetryPoolBackwardAttempts m w z q
                  ⟨stage.1 + 1, hstage⟩)
                (decodedRetryPoolBackwardSchedule m w z q
                  ⟨stage.1 + 1, hstage⟩)
                (tensorPowerHistoryAt _ (logicalOutputCount m w) history branch) ≠ true),
          (nextPool.tensorPower (logicalOutputCount m w)).bornWeight history joint := by
    rw [Finset.sum_filter, Fintype.sum_sigma, Finset.sum_filter]
    simp only [Fintype.sum_unique]
    apply Finset.sum_congr rfl
    intro history _
    have hevent := tensorPowerHistoryAll_ne_true_iff_exists
      (decodedRetryPoolOutcomeEnough
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩))
      (logicalOutputCount m w) history
    by_cases hfailure :
        tensorPowerHistoryAll
          (decodedRetryPoolOutcomeEnough
            (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
          (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩))
          (logicalOutputCount m w) history ≠ true
    · have hstageFailure :
          decodedRetryPoolSuccessorStageRoutingGood
              m w z q stage hstage ⟨PUnit.unit, history⟩ ≠ true := by
        exact hfailure
      rw [if_pos hstageFailure, if_pos (hevent.1 hfailure)]
      exact toFiniteInstrument_bindDependent_bornWeight
        (decodedRetryPoolSuccessorNestedInputChannel m w z q stage hstage)
        (nextPool.tensorPower (logicalOutputCount m w)) history source
    · have hstageGood : ¬
          decodedRetryPoolSuccessorStageRoutingGood
              m w z q stage hstage ⟨PUnit.unit, history⟩ ≠ true := by
        exact hfailure
      rw [if_neg hstageGood, if_neg]
      intro hexists
      exact hfailure (hevent.2 hexists)
  rw [hleft]
  refine hunion.trans_eq ?_
  apply Fintype.sum_equiv (decodedRetryPoolLogicalSiteFinEquiv m w).symm
  intro branch
  rw [decodedRetryPoolOutcomeFailureMass_eq_shortageMass]
  rw [show tensorPowerInputMarginal (logicalOutputCount m w) joint branch =
      tensorPowerProductInput
        (prepareMeasuredResources m w
          (noisyResources m w
            (selectedLogicalPortNextInputRate h hdegree epsilon
              ((decodedRetryPoolLogicalSiteFinEquiv m w).symm branch)
              (hhalf ((decodedRetryPoolLogicalSiteFinEquiv m w).symm branch)))))
        rhoUnit
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩) by
    simpa [source, joint] using
      decodedRetryPoolSuccessorNestedInputChannel_inputMarginal_acceptedProduct
        h hdegree epsilon z q stage hstage
          ((decodedRetryPoolLogicalSiteFinEquiv m w).symm branch)
          (hhalf ((decodedRetryPoolLogicalSiteFinEquiv m w).symm branch)) rhoUnit]

/-- The actual Born mass of the physical protocol prefix histories for which
every routing requirement through `stage` succeeds. -/
noncomputable def decodedRetryPoolProtocolSuccessfulRoutingMassAux
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) (stage : Nat) (hstage : stage < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier m w z q hz)) : Real :=
  ∑ outcome ∈ Finset.univ.filter
      (fun outcome : decodedRetryPoolProtocolOutcomeAux m w z q stage hstage =>
        decodedRetryPoolProtocolSuccessfulRoutingAux
          m w z q stage hstage outcome = true),
    (decodedRetryPoolProtocolInstrumentAux
      h hdegree z q hz stage hstage).bornWeight outcome rho

/-- The literal mass lost at one successor step: the predecessor prefix is
successful, but at least one actual pool of the appended physical stage is
short of its requested accepted blocks. -/
noncomputable def decodedRetryPoolProtocolStageRoutingFailureMass
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) (stage : Nat) (hstage : stage + 1 < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier m w z q hz)) : Real :=
  ∑ nextOutcome ∈ Finset.univ.filter
      (fun nextOutcome : decodedRetryPoolProtocolOutcomeAux
          m w z q (stage + 1) hstage =>
        decodedRetryPoolProtocolSuccessfulRoutingAux
            m w z q stage (by omega) nextOutcome.1 = true ∧
          nestedTensorHistoryAll
              (decodedRetryPoolSuccessorStageRoutingGood
                m w z q ⟨stage, by omega⟩ hstage)
              (logicalOutputCount m w) stage nextOutcome.2 ≠ true),
    (decodedRetryPoolProtocolInstrumentAux
      h hdegree z q hz (stage + 1) hstage).bornWeight nextOutcome rho

/-- The actual independent noisy-resource input consumed by the root retry
pool of the physical schedule. -/
noncomputable def decodedRetryPoolPhysicalProtocolNoisyRootInput
    (m w z q : Nat) (hz : 0 < z)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (rhoUnit : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    DensityOperator (decodedRetryPoolProtocolRootInputCarrier m w z q hz) :=
  tensorPowerProductInput
    (prepareMeasuredResources m w (noisyResources m w epsilon)) rhoUnit
    (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩)

/-- At the root, successful routing is exactly the actual decoded retry-pool
enough-history event. -/
theorem decodedRetryPoolProtocolSuccessfulRoutingMassAux_zero_eq_enoughMass
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier m w z q hz)) :
    decodedRetryPoolProtocolSuccessfulRoutingMassAux
        h hdegree z q hz 0 hz rho =
      decodedRetryPoolEnoughMass h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨0, hz⟩) rho := by
  classical
  unfold decodedRetryPoolProtocolSuccessfulRoutingMassAux
    decodedRetryPoolEnoughMass
  simp only [decodedRetryPoolProtocolSuccessfulRoutingAux_zero,
    decodedRetryPoolOutcomeEnough, decide_eq_true_eq]
  exact sum_sigma_punit_filter_fst
    (fun history =>
      decodedRetryPoolBackwardSchedule m w z q ⟨0, hz⟩ <=
        (tensorPowerAcceptedIndices decodedRetryPoolAccepts
          (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩) history).card)
    (fun outcome =>
      (decodedRetryPoolInstrument h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨0, hz⟩)).bornWeight
          outcome rho)

/-- The physical root's good-routing mass satisfies the exact stage-zero
dyadic shortage bound on the genuine noisy product input. -/
theorem decodedRetryPoolProtocolSuccessfulRoutingMassAux_zero_lower_bound
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (rhoUnit : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    1 - decodedRetryPoolStageAggregateShortageBudget w r m epsilon 0 <=
      decodedRetryPoolProtocolSuccessfulRoutingMassAux
        h hdegree z q hz 0 hz
          (decodedRetryPoolPhysicalProtocolNoisyRootInput
            m w z q hz epsilon rhoUnit) := by
  rw [decodedRetryPoolProtocolSuccessfulRoutingMassAux_zero_eq_enoughMass]
  simpa [decodedRetryPoolPhysicalProtocolNoisyRootInput,
    decodedRetryPoolBackwardAttempts,
    decodedRetryPoolStageAggregateShortageBudget,
    decodedRetryPoolDyadicDenominator, routedDepthErrorEnvelope] using
    (decodedRetryPoolDyadicEnoughMass_noisyResources_lower_bound
      h hdegree epsilon rhoUnit 0
        (decodedRetryPoolBackwardSchedule m w z q ⟨0, hz⟩))

theorem decodedRetryPoolProtocolSuccessfulRoutingMassAux_nonneg
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) (stage : Nat) (hstage : stage < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier m w z q hz)) :
    0 <= decodedRetryPoolProtocolSuccessfulRoutingMassAux
      h hdegree z q hz stage hstage rho := by
  unfold decodedRetryPoolProtocolSuccessfulRoutingMassAux
  exact Finset.sum_nonneg fun outcome _ =>
    (decodedRetryPoolProtocolInstrumentAux
      h hdegree z q hz stage hstage).bornWeight_nonneg outcome rho

theorem decodedRetryPoolProtocolStageRoutingFailureMass_nonneg
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) (stage : Nat) (hstage : stage + 1 < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier m w z q hz)) :
    0 <= decodedRetryPoolProtocolStageRoutingFailureMass
      h hdegree z q hz stage hstage rho := by
  unfold decodedRetryPoolProtocolStageRoutingFailureMass
  exact Finset.sum_nonneg fun outcome _ =>
    (decodedRetryPoolProtocolInstrumentAux
      h hdegree z q hz (stage + 1) hstage).bornWeight_nonneg outcome rho

/-- Appending one complete physical stage partitions every good-prefix Born
mass into newly successful histories and the literal new-stage failure mass. -/
theorem decodedRetryPoolProtocolSuccessfulRoutingMassAux_succ_add_failure
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) (stage : Nat) (hstage : stage + 1 < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier m w z q hz)) :
    decodedRetryPoolProtocolSuccessfulRoutingMassAux
        h hdegree z q hz (stage + 1) hstage rho +
      decodedRetryPoolProtocolStageRoutingFailureMass
        h hdegree z q hz stage hstage rho =
      decodedRetryPoolProtocolSuccessfulRoutingMassAux
        h hdegree z q hz stage (by omega) rho := by
  let currentGood : decodedRetryPoolProtocolOutcomeAux
      m w z q (stage + 1) hstage -> Prop := fun nextOutcome =>
    nestedTensorHistoryAll
        (decodedRetryPoolSuccessorStageRoutingGood
          m w z q ⟨stage, by omega⟩ hstage)
        (logicalOutputCount m w) stage nextOutcome.2 = true
  have hpartition := Finset.sum_filter_add_sum_filter_not
    (s := (Finset.univ : Finset
      (decodedRetryPoolProtocolOutcomeAux m w z q (stage + 1) hstage)).filter
        (fun nextOutcome =>
          decodedRetryPoolProtocolSuccessfulRoutingAux
            m w z q stage (by omega) nextOutcome.1 = true))
    (p := currentGood)
    (f := fun nextOutcome =>
      (decodedRetryPoolProtocolInstrumentAux
        h hdegree z q hz (stage + 1) hstage).bornWeight nextOutcome rho)
  calc
    decodedRetryPoolProtocolSuccessfulRoutingMassAux
          h hdegree z q hz (stage + 1) hstage rho +
        decodedRetryPoolProtocolStageRoutingFailureMass
          h hdegree z q hz stage hstage rho =
        ∑ nextOutcome ∈ Finset.univ.filter
            (fun nextOutcome : decodedRetryPoolProtocolOutcomeAux
                m w z q (stage + 1) hstage =>
              decodedRetryPoolProtocolSuccessfulRoutingAux
                m w z q stage (by omega) nextOutcome.1 = true),
          (decodedRetryPoolProtocolInstrumentAux
            h hdegree z q hz (stage + 1) hstage).bornWeight nextOutcome rho := by
      simpa only [decodedRetryPoolProtocolSuccessfulRoutingMassAux,
        decodedRetryPoolProtocolStageRoutingFailureMass,
        decodedRetryPoolProtocolSuccessfulRoutingAux_succ,
        Bool.and_eq_true, Finset.filter_filter, currentGood] using hpartition
    _ = decodedRetryPoolProtocolSuccessfulRoutingMassAux
          h hdegree z q hz stage (by omega) rho := by
      exact decodedRetryPoolProtocolInstrumentAux_bornWeight_good_prefix_succ_sum
        h hdegree z q hz stage hstage rho

/-- The public terminal success mass is exactly the successful-prefix mass at
the last bounded physical stage. -/
theorem decodedRetryPoolPhysicalProtocolSuccessMass_eq_aux
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier m w z q hz)) :
    decodedRetryPoolPhysicalProtocolSuccessMass h hdegree z q hz rho =
      decodedRetryPoolProtocolSuccessfulRoutingMassAux
        h hdegree z q hz (z - 1) (by omega) rho := by
  rw [decodedRetryPoolPhysicalProtocolSuccessMass_eq_sum]
  rfl

end HH18Parameterized
end Distillation
end QEC
