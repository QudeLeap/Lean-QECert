import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Paths.NestedPathRouting
import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Successor.SelectedEnoughBranch

/-!
# One routed-path success event in the physical retry tree

This layer projects the global successful-routing event onto one literal
logical-port path.  At every stage it reads the actual visible retry-pool
history selected by that path; it does not introduce an independent branch
model or a detached success assumption.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Parameterized

open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.FiniteInstrument

attribute [local instance 100] Fintype.ofFinite

/-- Successful routing along one literal path through a bounded physical
protocol outcome. -/
def decodedRetryPoolProtocolPathSuccessfulRoutingAux
    (m w z q : Nat) : (stage : Nat) -> (hstage : stage < z) ->
      routedDepthOutputSlots m w stage ->
      decodedRetryPoolProtocolOutcomeAux m w z q stage hstage -> Bool
  | 0, hzero, _, outcome =>
      decodedRetryPoolOutcomeEnough
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hzero⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨0, hzero⟩) outcome
  | stage + 1, hstage, path, outcome =>
      let priorPath := routedDepthOutputPathInit m w stage path
      let port := routedDepthOutputPathLast m w stage path
      let nestedPath :=
        (decodedRetryPoolNestedPathEquiv m w stage).symm priorPath
      let successorOutcome :=
        nestedTensorHistoryAt
          (decodedRetryPoolSuccessorStageOutcome
            m w z q ⟨stage, by omega⟩ hstage)
          (logicalOutputCount m w) stage outcome.2 nestedPath
      decodedRetryPoolProtocolPathSuccessfulRoutingAux
          m w z q stage (by omega) priorPath outcome.1 &&
        decodedRetryPoolSuccessorStageSelectedPoolEnough
          m w z q ⟨stage, by omega⟩ hstage port successorOutcome

@[simp] theorem decodedRetryPoolProtocolPathSuccessfulRoutingAux_zero
    (m w z q : Nat) (hz : 0 < z)
    (path : routedDepthOutputSlots m w 0)
    (outcome : decodedRetryPoolProtocolOutcomeAux m w z q 0 hz) :
    decodedRetryPoolProtocolPathSuccessfulRoutingAux
        m w z q 0 hz path outcome =
      decodedRetryPoolOutcomeEnough
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨0, hz⟩) outcome :=
  rfl

@[simp] theorem decodedRetryPoolProtocolPathSuccessfulRoutingAux_succ
    (m w z q stage : Nat) (hstage : stage + 1 < z)
    (path : routedDepthOutputSlots m w (stage + 1))
    (outcome : decodedRetryPoolProtocolOutcomeAux m w z q (stage + 1) hstage) :
    decodedRetryPoolProtocolPathSuccessfulRoutingAux
        m w z q (stage + 1) hstage path outcome =
      (decodedRetryPoolProtocolPathSuccessfulRoutingAux
          m w z q stage (by omega)
            (routedDepthOutputPathInit m w stage path) outcome.1 &&
        decodedRetryPoolSuccessorStageSelectedPoolEnough
          m w z q ⟨stage, by omega⟩ hstage
            (routedDepthOutputPathLast m w stage path)
            (nestedTensorHistoryAt
              (decodedRetryPoolSuccessorStageOutcome
                m w z q ⟨stage, by omega⟩ hstage)
              (logicalOutputCount m w) stage outcome.2
              ((decodedRetryPoolNestedPathEquiv m w stage).symm
                (routedDepthOutputPathInit m w stage path)))) :=
  rfl

/-- Global successful routing implies successful routing on every actual
logical-port path. -/
theorem decodedRetryPoolProtocolSuccessfulRoutingAux_implies_path
    (m w z q stage : Nat) (hstage : stage < z)
    (outcome : decodedRetryPoolProtocolOutcomeAux m w z q stage hstage)
    (hglobal : decodedRetryPoolProtocolSuccessfulRoutingAux
      m w z q stage hstage outcome = true)
    (path : routedDepthOutputSlots m w stage) :
    decodedRetryPoolProtocolPathSuccessfulRoutingAux
        m w z q stage hstage path outcome = true := by
  induction stage with
  | zero =>
      simpa using hglobal
  | succ stage ih =>
      rw [decodedRetryPoolProtocolSuccessfulRoutingAux_succ,
        Bool.and_eq_true] at hglobal
      rw [decodedRetryPoolProtocolPathSuccessfulRoutingAux_succ,
        Bool.and_eq_true]
      constructor
      · exact ih (by omega) outcome.1 hglobal.1
          (routedDepthOutputPathInit m w stage path)
      · let priorPath := routedDepthOutputPathInit m w stage path
        let nestedPath :=
          (decodedRetryPoolNestedPathEquiv m w stage).symm priorPath
        have hstageGood :=
          (nestedTensorHistoryAll_eq_true_iff
            (decodedRetryPoolSuccessorStageRoutingGood
              m w z q ⟨stage, by omega⟩ hstage)
            (logicalOutputCount m w) stage outcome.2).1 hglobal.2 nestedPath
        have hportGood :=
          (tensorPowerHistoryAll_eq_true_iff
            (decodedRetryPoolOutcomeEnough
              (decodedRetryPoolBackwardAttempts m w z q
                ⟨stage + 1, hstage⟩)
              (decodedRetryPoolBackwardSchedule m w z q
                ⟨stage + 1, hstage⟩))
            (logicalOutputCount m w)
            (nestedTensorHistoryAt
              (decodedRetryPoolSuccessorStageOutcome
                m w z q ⟨stage, by omega⟩ hstage)
              (logicalOutputCount m w) stage outcome.2 nestedPath).2).1
            hstageGood
            (decodedRetryPoolLogicalSiteFinEquiv m w
              (routedDepthOutputPathLast m w stage path))
        simpa [decodedRetryPoolSuccessorStageSelectedPoolEnough,
          priorPath, nestedPath] using hportGood

end HH18Parameterized
end Distillation
end QEC
