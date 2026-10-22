import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Successor.Preparation
import QEC.Semantics.Instruments.Registers.ChannelProduct
/-!
# Parameterized HH18 decoded retry-pool successor measurement

The compiled successor preparation produces genuine noisy inverse-`T`
resource qubits.  The decoded retry pool, however, consumes the classical
physical-error record obtained by the resource measurement.  This layer
performs that missing physical step: it rotates the resource back to the
established A basis and transports the already-dephased outcome basis to the
computational record basis.  The dephasing remains part of the preceding
physical preparation, so the complete channel records a measurement outcome
rather than coherently relabelling an arbitrary input.
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

/-- The one-qubit computational record with the same actual A-basis error
parameter. -/
noncomputable def decodedRetryPoolOneQubitRecordDensity
    (parameter : ErrorParameter) : DensityOperator QubitSpace :=
  aBasisTransport.symm.conjDensity (diagonalAResource parameter)

/-- Complete one-qubit successor-to-record channel.  It first uses the
compiled A-dephasing/inverse-phase resource handoff, rotates that resource
back to the A basis, and finally records the dephased outcome in the
computational basis. -/
noncomputable def decodedRetryPoolSuccessorOneQubitRecordChannel :
    QuantumChannel QubitSpace QubitSpace :=
  QuantumChannel.comp
    (QuantumChannel.unitaryConj aBasisTransport.symm)
    (QuantumChannel.comp
      (QuantumChannel.unitaryConj
        (OneQubitMagic.phaseShiftTransport (Real.pi / 2)))
      decodedRetryPoolSuccessorOneQubitPreparation)

/-- The inverse-phase resource handoff followed by the forward resource
rotation cancels exactly, leaving the genuine A-dephasing and outcome-record
transport. -/
theorem decodedRetryPoolSuccessorOneQubitRecordChannel_mapDensity
    (rho : DensityOperator QubitSpace) :
    decodedRetryPoolSuccessorOneQubitRecordChannel.mapDensity rho =
      aBasisTransport.symm.conjDensity (aBasisDephasing.mapDensity rho) := by
  rw [decodedRetryPoolSuccessorOneQubitRecordChannel,
    QuantumChannel.comp_mapDensity, QuantumChannel.comp_mapDensity,
    decodedRetryPoolSuccessorOneQubitPreparation_mapDensity]
  apply DensityOperator.ext_toOperator
  simp only [QuantumChannel.mapDensity_toOperator,
    QuantumChannel.unitaryConj_apply,
    UnitaryTransport.conjDensity_toOperator]
  rw [UnitaryTransport.conjOperator_symm_conjOperator]

/-- The record density is the literal computational-basis mixture with the
actual clean and error weights. -/
theorem decodedRetryPoolOneQubitRecordDensity_toOperator
    (parameter : ErrorParameter) :
    (decodedRetryPoolOneQubitRecordDensity parameter).toOperator =
      (parameter.cleanWeight : Complex) •
          (InnerProductSpace.rankOne Complex
            (EuclideanSpace.basisFun (Fin 2) Complex 0)
            (EuclideanSpace.basisFun (Fin 2) Complex 0)).toLinearMap +
        (parameter.rate : Complex) •
          (InnerProductSpace.rankOne Complex
            (EuclideanSpace.basisFun (Fin 2) Complex 1)
            (EuclideanSpace.basisFun (Fin 2) Complex 1)).toLinearMap := by
  rw [decodedRetryPoolOneQubitRecordDensity,
    UnitaryTransport.conjDensity_toOperator,
    diagonalAResource_toOperator]
  change aBasisTransport.symm.conjOperator
      ((parameter.cleanWeight : Complex) • aZeroDensity.toOperator +
        (parameter.rate : Complex) • aOneDensity.toOperator) = _
  rw [← aBasisTransport.symm.conjOperatorLinearMap_apply, map_add,
    map_smul, map_smul]
  simp only [UnitaryTransport.conjOperatorLinearMap_apply]
  rw [aZeroDensity_rankOne, aOneDensity_rankOne,
    QuditSubsystem.conjOperator_rankOne,
    QuditSubsystem.conjOperator_rankOne]
  have hzero :
      aBasisTransport.symm aZeroState =
        EuclideanSpace.basisFun (Fin 2) Complex 0 := by
    rw [← aBasisTransport_basis_zero]
    simp only [UnitaryTransport.symm_toLinearEquiv,
      LinearEquiv.symm_apply_apply]
  have hone :
      aBasisTransport.symm aOneState =
        EuclideanSpace.basisFun (Fin 2) Complex 1 := by
    rw [← aBasisTransport_basis_one]
    simp only [UnitaryTransport.symm_toLinearEquiv,
      LinearEquiv.symm_apply_apply]
  rw [hzero, hone]

/-- On an actual accepted logical output, the complete physical successor
channel produces the computational record at its measured error parameter. -/
theorem decodedRetryPoolSuccessorOneQubitRecordChannel_selectedOutput
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w) :
    decodedRetryPoolSuccessorOneQubitRecordChannel.mapDensity
        (selectedLogicalPortTransportedAcceptedOutput h hdegree epsilon port) =
      decodedRetryPoolOneQubitRecordDensity
        (selectedLogicalPortRawParameter h hdegree epsilon port) := by
  rw [decodedRetryPoolSuccessorOneQubitRecordChannel_mapDensity]
  change aBasisTransport.symm.conjDensity
      (selectedLogicalPortDephasedOutput h hdegree epsilon port) = _
  rw [selectedLogicalPortDephasedOutput_eq_diagonalAResource]
  rfl

/-- Apply the complete successor-to-record channel independently at every
selected output site.  It acts on the full register and remains valid for
correlated accepted logical blocks. -/
noncomputable def decodedRetryPoolSuccessorRecordPreparationChannel
    (m w z q : Nat) (stage : Fin z) :
    QuantumChannel
      (QubitRegister (decodedRetryPoolSuccessorSourceSlots m w z q stage))
      (QubitRegister (decodedRetryPoolSuccessorSourceSlots m w z q stage)) :=
  tensorPowerRegisterSitewiseChannel
    (decodedRetryPoolQubitRegisterSitewiseChannel
      decodedRetryPoolSuccessorOneQubitRecordChannel
      (LogicalSite m w))
    (decodedRetryPoolBackwardSchedule m w z q stage)

/-- On a genuine product of accepted parent blocks, the physical record
preparation remains a genuine product of the corresponding blockwise record
densities.  The channel itself is defined on arbitrary, possibly correlated,
source registers; only this evaluation theorem uses the accepted-product
shape. -/
theorem decodedRetryPoolSuccessorRecordPreparationChannel_mapDensity_product
    (m w z q : Nat) (stage : Fin z)
    (rho : DensityOperator (LogicalRegister m w))
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (LogicalRegister m w) 0)) :
    (decodedRetryPoolSuccessorRecordPreparationChannel m w z q stage).mapDensity
        (tensorPowerRegisterProductDensity (LogicalSite m w) rho rhoUnit
          (decodedRetryPoolBackwardSchedule m w z q stage)) =
      tensorPowerRegisterProductDensity (LogicalSite m w)
        ((decodedRetryPoolQubitRegisterSitewiseChannel
          decodedRetryPoolSuccessorOneQubitRecordChannel
          (LogicalSite m w)).mapDensity rho)
        rhoUnit (decodedRetryPoolBackwardSchedule m w z q stage) := by
  simpa [decodedRetryPoolSuccessorRecordPreparationChannel] using
    (tensorPowerRegisterSitewiseChannel_mapDensity_product
      (decodedRetryPoolQubitRegisterSitewiseChannel
        decodedRetryPoolSuccessorOneQubitRecordChannel
        (LogicalSite m w))
      rho rhoUnit (decodedRetryPoolBackwardSchedule m w z q stage))

end HH18Parameterized
end Distillation
end QEC
