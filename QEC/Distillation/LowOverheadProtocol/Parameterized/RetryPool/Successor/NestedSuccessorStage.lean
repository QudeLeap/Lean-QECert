import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Schedule.StageTransition
import QEC.Semantics.Instruments.NestedTensor.Power
/-!
# Parameterized HH18 nested physical successor stages

This internal physical layer starts from the selected logical register of one
retry-pool stage, applies the constructed successor routing/regrouping channel,
and runs the actual next retry pool on every logical branch.  Tensoring that
whole stage at its path depth realizes a growing arbitrary-depth physical tree
without assuming that the input density factors across branches.
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

/-- The actual chosen channel branch followed by every next-pool raw history. -/
abbrev decodedRetryPoolSuccessorStageRawIndex {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :=
  Sigma fun _ : Fin
      ((decodedRetryPoolSuccessorNestedInputChannel m w z q stage hstage).chosenKrausCount) =>
    tensorPowerHistory
      (decodedRetryPoolRawIndex h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩))
      (logicalOutputCount m w)

/-- The visible routing outcome followed by every next-pool observation. -/
abbrev decodedRetryPoolSuccessorStageOutcome
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :=
  Sigma fun _ : PUnit =>
    tensorPowerHistory
      (Sigma fun _ : tensorPowerHistory DistillationOutcome
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩) => PUnit)
      (logicalOutputCount m w)

/-- Route one selected stage output into the successor inputs and run the
actual next-stage decoded pool on every logical branch. -/
noncomputable def decodedRetryPoolSuccessorStageInstrument {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :
    FiniteInstrument
      (decodedRetryPoolSuccessorStageRawIndex h hdegree z q stage hstage)
      (decodedRetryPoolSuccessorStageOutcome m w z q stage hstage)
      (QubitRegister (decodedRetryPoolSuccessorSourceSlots m w z q stage))
      (tensorPowerCarrier
        (QubitRegister
          (Fin (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩) ×
            LogicalSite m w))
        (logicalOutputCount m w)) :=
  (QuantumChannel.toFiniteInstrument
      (decodedRetryPoolSuccessorNestedInputChannel m w z q stage hstage)).bindDependent
    (fun _ =>
      (decodedRetryPoolInstrument h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩)).tensorPower
          (logicalOutputCount m w))

/-- The one-path successor stage retains the unit channel observation and all
actual next-pool observations. -/
theorem decodedRetryPoolSuccessorStageInstrument_observe {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (firstIndex : Fin
      ((decodedRetryPoolSuccessorNestedInputChannel m w z q stage hstage).chosenKrausCount))
    (secondHistory : tensorPowerHistory
      (decodedRetryPoolRawIndex h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩))
      (logicalOutputCount m w)) :
    (decodedRetryPoolSuccessorStageInstrument h hdegree z q stage hstage).observe
        ⟨firstIndex, secondHistory⟩ =
      ⟨PUnit.unit,
        ((decodedRetryPoolInstrument h hdegree
          (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
          (decodedRetryPoolBackwardSchedule m w z q
            ⟨stage.1 + 1, hstage⟩)).tensorPower
              (logicalOutputCount m w)).observe secondHistory⟩ := by
  exact FiniteInstrument.bindDependent_observe
    (QuantumChannel.toFiniteInstrument
      (decodedRetryPoolSuccessorNestedInputChannel m w z q stage hstage))
    (fun _ =>
      (decodedRetryPoolInstrument h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩)).tensorPower
          (logicalOutputCount m w))
    firstIndex secondHistory

/-- The physical routing channel and all actual next pools form a complete
finite instrument. -/
theorem decodedRetryPoolSuccessorStageInstrument_complete {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :
    (decodedRetryPoolSuccessorStageInstrument h hdegree z q stage hstage).kraus.Complete := by
  exact FiniteInstrument.bindDependent_complete
    (QuantumChannel.toFiniteInstrument
      (decodedRetryPoolSuccessorNestedInputChannel m w z q stage hstage))
    (fun _ =>
      (decodedRetryPoolInstrument h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩)).tensorPower
          (logicalOutputCount m w))
    (QuantumChannel.toFiniteInstrument_complete
      (decodedRetryPoolSuccessorNestedInputChannel m w z q stage hstage))
    (fun _ =>
      (decodedRetryPoolInstrument h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩)).tensorPower_complete
          (decodedRetryPoolInstrument_complete h hdegree
            (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
            (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩))
          (logicalOutputCount m w))

/-- Lift the complete successor stage over every current logical path.  Its
literal output carrier is the next path depth by construction. -/
noncomputable def decodedRetryPoolNestedSuccessorStageInstrument {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :
    FiniteInstrument
      (nestedTensorHistory
        (decodedRetryPoolSuccessorStageRawIndex h hdegree z q stage hstage)
        (logicalOutputCount m w) stage.1)
      (nestedTensorHistory
        (decodedRetryPoolSuccessorStageOutcome m w z q stage hstage)
        (logicalOutputCount m w) stage.1)
      (nestedTensorCarrier
        (QubitRegister (decodedRetryPoolSuccessorSourceSlots m w z q stage))
        (logicalOutputCount m w) stage.1)
      (nestedTensorCarrier
        (QubitRegister
          (Fin (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩) ×
            LogicalSite m w))
        (logicalOutputCount m w) (stage.1 + 1)) :=
  nestedTensorPower
    (decodedRetryPoolSuccessorStageInstrument h hdegree z q stage hstage)
    (logicalOutputCount m w) stage.1

/-- Every depth-indexed physical successor stage is complete. -/
theorem decodedRetryPoolNestedSuccessorStageInstrument_complete {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :
    (decodedRetryPoolNestedSuccessorStageInstrument
      h hdegree z q stage hstage).kraus.Complete := by
  exact nestedTensorPower_complete
    (decodedRetryPoolSuccessorStageInstrument h hdegree z q stage hstage)
    (decodedRetryPoolSuccessorStageInstrument_complete h hdegree z q stage hstage)
    (logicalOutputCount m w) stage.1

/-- Every density input has normalized total observed mass under the complete
depth-indexed physical successor stage. -/
theorem decodedRetryPoolNestedSuccessorStageInstrument_sum_bornWeight_eq_one
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (rho : DensityOperator
      (nestedTensorCarrier
        (QubitRegister (decodedRetryPoolSuccessorSourceSlots m w z q stage))
        (logicalOutputCount m w) stage.1)) :
    ∑ outcome,
        (decodedRetryPoolNestedSuccessorStageInstrument
          h hdegree z q stage hstage).bornWeight outcome rho = 1 := by
  exact nestedTensorPower_sum_bornWeight_eq_one
    (decodedRetryPoolSuccessorStageInstrument h hdegree z q stage hstage)
    (decodedRetryPoolSuccessorStageInstrument_complete h hdegree z q stage hstage)
    (logicalOutputCount m w) stage.1 rho

end HH18Parameterized
end Distillation
end QEC
