import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Successor.NestedSuccessorStage

/-!
# Parameterized HH18 arbitrary-depth physical retry-pool protocol

This module composes the actual root decoded retry pool with every physical
successor stage of a positive finite schedule.  Raw Kraus indices and visible
observations grow recursively with the schedule, while the output Hilbert
carrier grows by literal nested tensor powers.  Completeness and normalized
Born mass are derived for the resulting finite instrument; no branch-product
state or detached success-probability hypothesis is introduced.
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

/-- The complete raw history through a bounded natural-number stage. -/
def decodedRetryPoolProtocolRawIndexAux {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) : (stage : Nat) -> stage < z -> Type
  | 0, hzero =>
      decodedRetryPoolRawIndex h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hzero⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨0, hzero⟩)
  | stage + 1, hstage =>
      let previous : Fin z := ⟨stage, by omega⟩
      decodedRetryPoolProtocolRawIndexAux h hdegree z q stage (by omega) ×
        nestedTensorHistory
          (decodedRetryPoolSuccessorStageRawIndex
            h hdegree z q previous hstage)
          (logicalOutputCount m w) stage

/-- The complete visible observation history through a bounded stage. -/
def decodedRetryPoolProtocolOutcomeAux
    (m w z q : Nat) : (stage : Nat) -> stage < z -> Type
  | 0, hzero =>
      Sigma fun _ : tensorPowerHistory DistillationOutcome
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hzero⟩) => PUnit
  | stage + 1, hstage =>
      let previous : Fin z := ⟨stage, by omega⟩
      Sigma fun _ : decodedRetryPoolProtocolOutcomeAux m w z q stage (by omega) =>
        nestedTensorHistory
          (decodedRetryPoolSuccessorStageOutcome m w z q previous hstage)
          (logicalOutputCount m w) stage

/-- Every recursively accumulated raw protocol history is finite. -/
instance decodedRetryPoolProtocolRawIndexAuxFintype {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) : (stage : Nat) -> (hstage : stage < z) ->
    Fintype (decodedRetryPoolProtocolRawIndexAux h hdegree z q stage hstage)
  | 0, hzero => by
      simp only [decodedRetryPoolProtocolRawIndexAux]
      infer_instance
  | stage + 1, hstage => by
      let previousProof : stage < z := by omega
      letI : Fintype
          (decodedRetryPoolProtocolRawIndexAux
            h hdegree z q stage previousProof) :=
        decodedRetryPoolProtocolRawIndexAuxFintype
          h hdegree z q stage previousProof
      change Fintype
        (decodedRetryPoolProtocolRawIndexAux h hdegree z q stage previousProof ×
          nestedTensorHistory
            (decodedRetryPoolSuccessorStageRawIndex
              h hdegree z q ⟨stage, previousProof⟩ hstage)
            (logicalOutputCount m w) stage)
      infer_instance

/-- Every recursively accumulated visible protocol history is finite. -/
instance decodedRetryPoolProtocolOutcomeAuxFintype
    (m w z q : Nat) : (stage : Nat) -> (hstage : stage < z) ->
    Fintype (decodedRetryPoolProtocolOutcomeAux m w z q stage hstage)
  | 0, hzero => by
      simp only [decodedRetryPoolProtocolOutcomeAux]
      infer_instance
  | stage + 1, hstage => by
      letI := decodedRetryPoolProtocolOutcomeAuxFintype
        m w z q stage (by omega)
      simp only [decodedRetryPoolProtocolOutcomeAux]
      infer_instance

/-- The raw protocol history ending at a `Fin z` stage. -/
abbrev decodedRetryPoolProtocolRawIndexToStage {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (stage : Fin z) :=
  decodedRetryPoolProtocolRawIndexAux h hdegree z q stage.1 stage.2

/-- The visible protocol history ending at a `Fin z` stage. -/
abbrev decodedRetryPoolProtocolOutcomeToStage
    (m w z q : Nat) (stage : Fin z) :=
  decodedRetryPoolProtocolOutcomeAux m w z q stage.1 stage.2

/-- The actual tensor power of root physical blocks consumed by the schedule. -/
abbrev decodedRetryPoolProtocolRootInputCarrier
    (m w z q : Nat) (hz : 0 < z) :=
  tensorPowerCarrier (PhysicalRegister m w)
    (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩)

/-- The literal nested selected-output carrier after a bounded stage. -/
abbrev decodedRetryPoolProtocolOutputCarrierAux
    (m w z q stage : Nat) (hstage : stage < z) :=
  nestedTensorCarrier
    (QubitRegister
      (Fin (decodedRetryPoolBackwardSchedule m w z q ⟨stage, hstage⟩) ×
        LogicalSite m w))
    (logicalOutputCount m w) stage

/-- The explicitly typed physical successor instrument between consecutive
natural-number stages. -/
noncomputable def decodedRetryPoolProtocolSuccessorInstrumentAux {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q stage : Nat) (hstage : stage + 1 < z) :
    FiniteInstrument
      (nestedTensorHistory
        (decodedRetryPoolSuccessorStageRawIndex
          h hdegree z q ⟨stage, by omega⟩ hstage)
        (logicalOutputCount m w) stage)
      (nestedTensorHistory
        (decodedRetryPoolSuccessorStageOutcome
          m w z q ⟨stage, by omega⟩ hstage)
        (logicalOutputCount m w) stage)
      (decodedRetryPoolProtocolOutputCarrierAux m w z q stage (by omega))
      (decodedRetryPoolProtocolOutputCarrierAux m w z q (stage + 1) hstage) :=
  decodedRetryPoolNestedSuccessorStageInstrument
    h hdegree z q ⟨stage, by omega⟩ hstage

/-- The actual root pool followed by every physical successor instrument up
to the supplied bounded stage. -/
noncomputable def decodedRetryPoolProtocolInstrumentAux {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) : (stage : Nat) -> (hstage : stage < z) ->
    FiniteInstrument
      (decodedRetryPoolProtocolRawIndexAux h hdegree z q stage hstage)
      (decodedRetryPoolProtocolOutcomeAux m w z q stage hstage)
      (decodedRetryPoolProtocolRootInputCarrier m w z q hz)
      (decodedRetryPoolProtocolOutputCarrierAux m w z q stage hstage)
  | 0, hzero =>
      decodedRetryPoolInstrument h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hzero⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨0, hzero⟩)
  | stage + 1, hstage =>
      let previousProof : stage < z := by omega
      (decodedRetryPoolProtocolInstrumentAux
        h hdegree z q hz stage previousProof).bind
        (fun _ => decodedRetryPoolProtocolSuccessorInstrumentAux
          h hdegree z q stage hstage)

/-- One protocol successor is literally the preceding physical prefix bound
to the actual nested successor-stage instrument. -/
theorem decodedRetryPoolProtocolInstrumentAux_succ {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) (stage : Nat) (hstage : stage + 1 < z) :
    decodedRetryPoolProtocolInstrumentAux
        h hdegree z q hz (stage + 1) hstage =
      (decodedRetryPoolProtocolInstrumentAux
        h hdegree z q hz stage (by omega)).bind
        (fun _ => decodedRetryPoolProtocolSuccessorInstrumentAux
          h hdegree z q stage hstage) := by
  rfl

/-- A successor observation retains the entire previous history and appends
the actual nested successor-stage observation. -/
theorem decodedRetryPoolProtocolInstrumentAux_observe_succ {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) (stage : Nat) (hstage : stage + 1 < z)
    (firstIndex : decodedRetryPoolProtocolRawIndexAux
      h hdegree z q stage (by omega))
    (secondIndex : nestedTensorHistory
      (decodedRetryPoolSuccessorStageRawIndex
        h hdegree z q ⟨stage, by omega⟩ hstage)
      (logicalOutputCount m w) stage) :
    (decodedRetryPoolProtocolInstrumentAux
      h hdegree z q hz (stage + 1) hstage).observe
        (firstIndex, secondIndex) =
      ⟨(decodedRetryPoolProtocolInstrumentAux
          h hdegree z q hz stage (by omega)).observe firstIndex,
        (decodedRetryPoolProtocolSuccessorInstrumentAux
          h hdegree z q stage hstage).observe secondIndex⟩ := by
  rfl

/-- The physical protocol prefix is complete at every bounded stage. -/
theorem decodedRetryPoolProtocolInstrumentAux_complete {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) : (stage : Nat) -> (hstage : stage < z) ->
    (decodedRetryPoolProtocolInstrumentAux
      h hdegree z q hz stage hstage).kraus.Complete
  | 0, hzero =>
      decodedRetryPoolInstrument_complete h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hzero⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨0, hzero⟩)
  | stage + 1, hstage => by
      let previousProof : stage < z := by omega
      exact FiniteInstrument.bind_complete
        (decodedRetryPoolProtocolInstrumentAux
          h hdegree z q hz stage previousProof)
        (fun _ => decodedRetryPoolProtocolSuccessorInstrumentAux
          h hdegree z q stage hstage)
        (decodedRetryPoolProtocolInstrumentAux_complete
          h hdegree z q hz stage previousProof)
        (fun _ => decodedRetryPoolNestedSuccessorStageInstrument_complete
          h hdegree z q ⟨stage, previousProof⟩ hstage)

/-- The physical protocol prefix indexed by a `Fin z` stage. -/
noncomputable def decodedRetryPoolProtocolInstrumentToStage {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) (stage : Fin z) :
    FiniteInstrument
      (decodedRetryPoolProtocolRawIndexToStage h hdegree z q stage)
      (decodedRetryPoolProtocolOutcomeToStage m w z q stage)
      (decodedRetryPoolProtocolRootInputCarrier m w z q hz)
      (decodedRetryPoolProtocolOutputCarrierAux m w z q stage.1 stage.2) :=
  decodedRetryPoolProtocolInstrumentAux h hdegree z q hz stage.1 stage.2

/-- Every `Fin z`-indexed physical protocol prefix is complete. -/
theorem decodedRetryPoolProtocolInstrumentToStage_complete {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) (stage : Fin z) :
    (decodedRetryPoolProtocolInstrumentToStage
      h hdegree z q hz stage).kraus.Complete :=
  decodedRetryPoolProtocolInstrumentAux_complete
    h hdegree z q hz stage.1 stage.2

/-- The last stage of a positive finite schedule. -/
abbrev decodedRetryPoolProtocolTerminalStage (z : Nat) (hz : 0 < z) : Fin z :=
  ⟨z - 1, by omega⟩

/-- The full raw Kraus history of the positive-depth physical protocol. -/
abbrev decodedRetryPoolPhysicalProtocolRawIndex {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) :=
  decodedRetryPoolProtocolRawIndexToStage h hdegree z q
    (decodedRetryPoolProtocolTerminalStage z hz)

/-- The full visible observation history of the physical protocol. -/
abbrev decodedRetryPoolPhysicalProtocolOutcome
    (m w z q : Nat) (hz : 0 < z) :=
  decodedRetryPoolProtocolOutcomeToStage m w z q
    (decodedRetryPoolProtocolTerminalStage z hz)

/-- The literal nested terminal selected-output carrier. -/
abbrev decodedRetryPoolPhysicalProtocolOutputCarrier
    (m w z q : Nat) (hz : 0 < z) :=
  decodedRetryPoolProtocolOutputCarrierAux m w z q (z - 1) (by omega)

/-- The complete arbitrary-positive-depth physical HH18 retry-pool protocol. -/
noncomputable def decodedRetryPoolPhysicalProtocolInstrument {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) :
    FiniteInstrument
      (decodedRetryPoolPhysicalProtocolRawIndex h hdegree z q hz)
      (decodedRetryPoolPhysicalProtocolOutcome m w z q hz)
      (decodedRetryPoolProtocolRootInputCarrier m w z q hz)
      (decodedRetryPoolPhysicalProtocolOutputCarrier m w z q hz) :=
  decodedRetryPoolProtocolInstrumentToStage h hdegree z q hz
    (decodedRetryPoolProtocolTerminalStage z hz)

/-- The full physical protocol finite instrument is complete. -/
theorem decodedRetryPoolPhysicalProtocolInstrument_complete {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) :
    (decodedRetryPoolPhysicalProtocolInstrument
      h hdegree z q hz).kraus.Complete :=
  decodedRetryPoolProtocolInstrumentToStage_complete h hdegree z q hz
    (decodedRetryPoolProtocolTerminalStage z hz)

/-- Every root input density has normalized total observed Born mass under the
full physical protocol. -/
theorem decodedRetryPoolPhysicalProtocolInstrument_sum_bornWeight_eq_one
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier m w z q hz)) :
    ∑ outcome,
        (decodedRetryPoolPhysicalProtocolInstrument
          h hdegree z q hz).bornWeight outcome rho = 1 :=
  (decodedRetryPoolPhysicalProtocolInstrument h hdegree z q hz).sum_bornWeight_eq_one
    (decodedRetryPoolPhysicalProtocolInstrument_complete h hdegree z q hz) rho

/-- The terminal physical retry pool requests exactly the prescribed `q`
selected blocks. -/
theorem decodedRetryPoolPhysicalProtocol_terminal_required
    (m w z q : Nat) (hz : 0 < z) :
    decodedRetryPoolBackwardSchedule m w z q
      (decodedRetryPoolProtocolTerminalStage z hz) = q :=
  decodedRetryPoolBackwardSchedule_terminal m w z q hz

end HH18Parameterized
end Distillation
end QEC
