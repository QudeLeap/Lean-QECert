import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Physical.Protocol
import QEC.Semantics.Instruments.NestedTensor.PowerBasis
/-!
# Parameterized HH18 physical retry-pool accounting

This module identifies the literal input and output carriers of the complete
physical retry-pool finite instrument with the exact coordinate carriers of
the compiled backward schedule.  Both identifications are basis-preserving
unitary transports.  Thus the root physical cost and terminal `q * k ^ z`
output count describe the actual protocol carriers, rather than detached
metadata or caller-supplied conclusions.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Parameterized

open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument

attribute [local instance 100] Fintype.ofFinite

/-- The flattened finite slots of the literal terminal nested output carrier. -/
abbrev decodedRetryPoolPhysicalProtocolTerminalNestedSlots
    (m w z q : Nat) (hz : 0 < z) :=
  nestedTensorQubitSlots
    (Fin (decodedRetryPoolBackwardSchedule m w z q
      (decodedRetryPoolProtocolTerminalStage z hz)) × LogicalSite m w)
    (logicalOutputCount m w) (z - 1)

/-- The literal terminal nested carrier has exactly `q * k ^ z` qubit slots. -/
theorem decodedRetryPoolPhysicalProtocolTerminalNestedSlots_card
    (m w z q : Nat) (hz : 0 < z) :
    Fintype.card
        (decodedRetryPoolPhysicalProtocolTerminalNestedSlots m w z q hz) =
      q * logicalOutputCount m w ^ z := by
  rw [nestedTensorQubitSlots_card]
  rw [decodedRetryPoolPhysicalProtocol_terminal_required]
  simp only [Fintype.card_prod, Fintype.card_fin]
  change (q * logicalOutputCount m w) * logicalOutputCount m w ^ (z - 1) =
    q * logicalOutputCount m w ^ z
  have hzSucc : z - 1 + 1 = z := by omega
  calc
    (q * logicalOutputCount m w) * logicalOutputCount m w ^ (z - 1) =
        q * (logicalOutputCount m w ^ (z - 1) * logicalOutputCount m w) := by
      ac_rfl
    _ = q * logicalOutputCount m w ^ (z - 1 + 1) := by
      rw [pow_succ]
    _ = q * logicalOutputCount m w ^ z := by rw [hzSucc]

/-- The flattened physical terminal slots have the same cardinality as the
backward schedule's exact good-output carrier. -/
theorem decodedRetryPoolPhysicalProtocolTerminalNestedSlots_card_eq
    (m w z q : Nat) (hz : 0 < z) :
    Fintype.card
        (decodedRetryPoolPhysicalProtocolTerminalNestedSlots m w z q hz) =
      Fintype.card (decodedRetryPoolBackwardTerminalGoodCarrier m w z q) := by
  rw [decodedRetryPoolPhysicalProtocolTerminalNestedSlots_card,
    decodedRetryPoolBackwardTerminalGoodCarrier_card]

/-- The actual flattened terminal coordinates are finitely equivalent to the
backward schedule's `q` selected blocks with one logical coordinate at every
stage. -/
noncomputable def decodedRetryPoolPhysicalProtocolTerminalSlotEquiv
    (m w z q : Nat) (hz : 0 < z) :
    decodedRetryPoolPhysicalProtocolTerminalNestedSlots m w z q hz ≃
      decodedRetryPoolBackwardTerminalGoodCarrier m w z q :=
  Fintype.equivOfCardEq
    (decodedRetryPoolPhysicalProtocolTerminalNestedSlots_card_eq m w z q hz)

/-- Reindex bitstrings along a finite physical slot equivalence. -/
noncomputable def decodedRetryPoolPhysicalProtocolBitstringEquivOfSlotEquiv
    {alpha beta : Type*} (equiv : alpha ≃ beta) :
    Qubit.Bitstring alpha ≃ Qubit.Bitstring beta where
  toFun := fun bits target => bits (equiv.symm target)
  invFun := fun bits source => bits (equiv source)
  left_inv := by
    intro bits
    funext source
    simp
  right_inv := by
    intro bits
    funext target
    simp

/-- The exact computational-basis label equivalence from the terminal nested
history to the backward schedule's good-output carrier. -/
noncomputable def decodedRetryPoolPhysicalProtocolTerminalLabelEquiv
    (m w z q : Nat) (hz : 0 < z) :
    nestedTensorHistory
        (Qubit.Bitstring
          (Fin (decodedRetryPoolBackwardSchedule m w z q
            (decodedRetryPoolProtocolTerminalStage z hz)) × LogicalSite m w))
        (logicalOutputCount m w) (z - 1) ≃
      Qubit.Bitstring (decodedRetryPoolBackwardTerminalGoodCarrier m w z q) :=
  (nestedTensorQubitBitstringEquiv
    (Fin (decodedRetryPoolBackwardSchedule m w z q
      (decodedRetryPoolProtocolTerminalStage z hz)) × LogicalSite m w)
    (logicalOutputCount m w) (z - 1)).trans
    (decodedRetryPoolPhysicalProtocolBitstringEquivOfSlotEquiv
      (decodedRetryPoolPhysicalProtocolTerminalSlotEquiv m w z q hz))

/-- The actual root tensor-power input is unitarily identified with one
physical-site coordinate for every derived root retry attempt. -/
noncomputable def decodedRetryPoolPhysicalProtocolRootInputTransport
    (m w z q : Nat) (hz : 0 < z) :
    UnitaryTransport
      (decodedRetryPoolProtocolRootInputCarrier m w z q hz)
      (QubitRegister (decodedRetryPoolBackwardRootRawCarrier m w z q hz)) :=
  tensorPowerQubitRegisterTransport (PhysicalSite m w)
    (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩)

/-- The root transport acts by the exact tensor-history/physical-coordinate
reindex on every computational basis vector. -/
@[simp] theorem decodedRetryPoolPhysicalProtocolRootInputTransport_apply_basis
    (m w z q : Nat) (hz : 0 < z)
    (history : tensorPowerHistory (Qubit.Bitstring (PhysicalSite m w))
      (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩)) :
    decodedRetryPoolPhysicalProtocolRootInputTransport m w z q hz
      (tensorPowerBasis
        (EuclideanSpace.basisFun (Qubit.Bitstring (PhysicalSite m w)) Complex)
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩) history) =
      EuclideanSpace.basisFun
        (Qubit.Bitstring (decodedRetryPoolBackwardRootRawCarrier m w z q hz)) Complex
        (tensorPowerQubitBitstringEquiv (PhysicalSite m w)
          (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩) history) := by
  exact tensorPowerQubitRegisterTransport_apply_basis
    (PhysicalSite m w)
    (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩) history

/-- The literal terminal nested output carrier is unitarily identified with
the exact `q`-block, depth-`z` logical output carrier. -/
noncomputable def decodedRetryPoolPhysicalProtocolTerminalRegisterTransport
    (m w z q : Nat) (hz : 0 < z) :
    UnitaryTransport
      (decodedRetryPoolPhysicalProtocolOutputCarrier m w z q hz)
      (QubitRegister (decodedRetryPoolBackwardTerminalGoodCarrier m w z q)) := by
  let sourceBasis := nestedTensorBasis
    (EuclideanSpace.basisFun
      (Qubit.Bitstring
        (Fin (decodedRetryPoolBackwardSchedule m w z q
          (decodedRetryPoolProtocolTerminalStage z hz)) × LogicalSite m w))
      Complex)
    (logicalOutputCount m w) (z - 1)
  let targetBasis := EuclideanSpace.basisFun
    (Qubit.Bitstring (decodedRetryPoolBackwardTerminalGoodCarrier m w z q)) Complex
  let transport := sourceBasis.equiv targetBasis
    (decodedRetryPoolPhysicalProtocolTerminalLabelEquiv m w z q hz)
  exact
    { toLinearEquiv := transport.toLinearEquiv
      map_inner := transport.inner_map_map }

/-- The terminal transport maps every physical nested computational basis
vector to the exact good-output carrier label. -/
@[simp] theorem decodedRetryPoolPhysicalProtocolTerminalRegisterTransport_apply_basis
    (m w z q : Nat) (hz : 0 < z)
    (history : nestedTensorHistory
      (Qubit.Bitstring
        (Fin (decodedRetryPoolBackwardSchedule m w z q
          (decodedRetryPoolProtocolTerminalStage z hz)) × LogicalSite m w))
      (logicalOutputCount m w) (z - 1)) :
    decodedRetryPoolPhysicalProtocolTerminalRegisterTransport m w z q hz
      (nestedTensorBasis
        (EuclideanSpace.basisFun
          (Qubit.Bitstring
            (Fin (decodedRetryPoolBackwardSchedule m w z q
              (decodedRetryPoolProtocolTerminalStage z hz)) × LogicalSite m w))
          Complex)
        (logicalOutputCount m w) (z - 1) history) =
      EuclideanSpace.basisFun
        (Qubit.Bitstring (decodedRetryPoolBackwardTerminalGoodCarrier m w z q)) Complex
        (decodedRetryPoolPhysicalProtocolTerminalLabelEquiv m w z q hz history) := by
  dsimp [decodedRetryPoolPhysicalProtocolTerminalRegisterTransport]
  rw [OrthonormalBasis.equiv_apply_basis]

end HH18Parameterized
end Distillation
end QEC
