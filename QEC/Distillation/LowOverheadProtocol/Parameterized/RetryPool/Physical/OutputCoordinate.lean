import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Physical.Run
import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Physical.Accounting
import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Records.AcceptedPortRecordProduct

/-!
# Literal terminal coordinates of the physical HH18 retry protocol

The complete retry protocol returns a recursively nested register.  This
layer names one of its actual terminal qubits by a routed predecessor path,
one selected terminal block, and one logical port.  It then constructs the
physical CPTP marginal to that qubit and its genuine negative-A measurement.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Parameterized

open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit

attribute [local instance 100] Fintype.ofFinite

/-- One literal terminal qubit of the nested physical retry-protocol output. -/
abbrev decodedRetryPoolPhysicalProtocolOutputCoordinate
    (m w z q : Nat) (hz : 0 < z) :=
  routedDepthOutputSlots m w (z - 1) ×
    (Fin (decodedRetryPoolBackwardSchedule m w z q
      (decodedRetryPoolProtocolTerminalStage z hz)) × LogicalSite m w)

/-- The literal terminal-coordinate carrier has the actual output count
`q * k^z`. -/
theorem decodedRetryPoolPhysicalProtocolOutputCoordinate_card
    (m w z q : Nat) (hz : 0 < z) :
    Fintype.card
        (decodedRetryPoolPhysicalProtocolOutputCoordinate m w z q hz) =
      q * logicalOutputCount m w ^ z := by
  simp only [decodedRetryPoolPhysicalProtocolOutputCoordinate,
    Fintype.card_prod, Fintype.card_fin, routedDepthOutputSlots_card]
  rw [decodedRetryPoolPhysicalProtocol_terminal_required]
  have hzSucc : z - 1 + 1 = z := by omega
  calc
    logicalOutputCount m w ^ (z - 1) *
        (q * Fintype.card (LogicalSite m w)) =
      q * (logicalOutputCount m w ^ (z - 1) * logicalOutputCount m w) := by
        simp only [show Fintype.card (LogicalSite m w) =
          logicalOutputCount m w by rfl]
        ring
    _ = q * logicalOutputCount m w ^ (z - 1 + 1) := by rw [pow_succ]
    _ = q * logicalOutputCount m w ^ z := by rw [hzSucc]

/-- Retain one block and then one logical port from an accepted-product
register. -/
noncomputable def decodedRetryPoolAcceptedProductCoordinateChannel
    (m w required : Nat) (block : Fin required) (port : LogicalSite m w) :
    QuantumChannel
      (QubitRegister (Fin required × LogicalSite m w)) QubitSpace :=
  QuantumChannel.comp
    (decodedRetryPoolQubitRegisterCoordinateChannel (LogicalSite m w) port)
    (tensorPowerRegisterTrialChannel (LogicalSite m w) required block)

/-- On the genuine accepted product, a named block/port coordinate is the
actual selected-port accepted output at that product's physical rate. -/
theorem decodedRetryPoolAcceptedProductCoordinateChannel_mapDensity
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (required : Nat) (block : Fin required) (port : LogicalSite m w) :
    (decodedRetryPoolAcceptedProductCoordinateChannel
      m w required block port).mapDensity
        (decodedRetryPoolAcceptedProductDensity
          h hdegree epsilon rhoUnit required) =
      selectedLogicalPortTransportedAcceptedOutput
        h hdegree epsilon port := by
  rw [decodedRetryPoolAcceptedProductCoordinateChannel,
    QuantumChannel.comp_mapDensity]
  rw [decodedRetryPoolAcceptedProductDensity]
  rw [tensorPowerRegisterProductDensity]
  rw [tensorPowerRegisterTrialChannel_mapDensity_transport]
  rw [tensorPowerInputMarginal_productInput]
  exact decodedRetryPoolQubitRegisterCoordinateChannel_mapDensity_eq_selectedLogicalPort
    m w port
      (resourceDecodedRun h hdegree (noisyResources m w epsilon)).acceptedOutput

/-- The physical CPTP marginal from the complete nested terminal carrier to
one literal routed-path/block/port qubit. -/
noncomputable def decodedRetryPoolPhysicalProtocolTerminalCoordinateChannel
    (m w z q : Nat) (hz : 0 < z)
    (coordinate :
      decodedRetryPoolPhysicalProtocolOutputCoordinate m w z q hz) :
    QuantumChannel
      (decodedRetryPoolPhysicalProtocolOutputCarrier m w z q hz) QubitSpace :=
  QuantumChannel.comp
    (decodedRetryPoolAcceptedProductCoordinateChannel m w
      (decodedRetryPoolBackwardSchedule m w z q
        (decodedRetryPoolProtocolTerminalStage z hz))
      coordinate.2.1 coordinate.2.2)
    (nestedTensorCoordinateOperator
      (QubitRegister
        (Fin (decodedRetryPoolBackwardSchedule m w z q
          (decodedRetryPoolProtocolTerminalStage z hz)) × LogicalSite m w))
      (logicalOutputCount m w) (z - 1)
      ((decodedRetryPoolNestedPathEquiv m w (z - 1)).symm coordinate.1))

/-- Evaluating the terminal block/port part of the physical coordinate on a
genuine accepted product returns the selected one-level accepted output. -/
theorem decodedRetryPoolPhysicalProtocolTerminalCoordinateChannel_mapDensity_acceptedProduct
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (coordinate :
      decodedRetryPoolPhysicalProtocolOutputCoordinate m w z q hz) :
    (decodedRetryPoolAcceptedProductCoordinateChannel m w
      (decodedRetryPoolBackwardSchedule m w z q
        (decodedRetryPoolProtocolTerminalStage z hz))
      coordinate.2.1 coordinate.2.2).mapDensity
        (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
          (decodedRetryPoolBackwardSchedule m w z q
            (decodedRetryPoolProtocolTerminalStage z hz))) =
      selectedLogicalPortTransportedAcceptedOutput
        h hdegree epsilon coordinate.2.2 :=
  decodedRetryPoolAcceptedProductCoordinateChannel_mapDensity
    h hdegree epsilon rhoUnit _ coordinate.2.1 coordinate.2.2

/-- The literal negative-A error probability at one actual terminal output
coordinate of an arbitrary physical output density. -/
noncomputable def decodedRetryPoolPhysicalProtocolCoordinateRawError
    (m w z q : Nat) (hz : 0 < z)
    (coordinate :
      decodedRetryPoolPhysicalProtocolOutputCoordinate m w z q hz)
    (rho : DensityOperator
      (decodedRetryPoolPhysicalProtocolOutputCarrier m w z q hz)) : Real :=
  aBasisInstrument.bornWeight .negative
    ((decodedRetryPoolPhysicalProtocolTerminalCoordinateChannel
      m w z q hz coordinate).mapDensity rho)

theorem decodedRetryPoolPhysicalProtocolCoordinateRawError_nonneg
    (m w z q : Nat) (hz : 0 < z)
    (coordinate :
      decodedRetryPoolPhysicalProtocolOutputCoordinate m w z q hz)
    (rho : DensityOperator
      (decodedRetryPoolPhysicalProtocolOutputCarrier m w z q hz)) :
    0 <= decodedRetryPoolPhysicalProtocolCoordinateRawError
      m w z q hz coordinate rho :=
  aBasisInstrument.bornWeight_nonneg .negative _

end HH18Parameterized
end Distillation
end QEC
