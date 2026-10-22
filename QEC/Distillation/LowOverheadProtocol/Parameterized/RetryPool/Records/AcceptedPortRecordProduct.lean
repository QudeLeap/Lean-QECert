import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Records.AcceptedProduct
import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Successor.Measurement
import QEC.Semantics.Instruments.TensorPower.ChannelProduct
/-!
# Parameterized HH18 accepted-port record products

An enough retry-pool history leaves a genuine product of accepted parent
blocks.  For one fixed logical port, this module partially traces that port
from each distinct parent block, applies the complete physical successor
record channel, and proves that the resulting records form the corresponding
tensor product.  No independence between different ports of one accepted
block is assumed.
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

/-- The physical marginal channel selecting one actual logical port from a
whole accepted logical block. -/
noncomputable def decodedRetryPoolSelectedPortChannel
    (m w : Nat) (port : LogicalSite m w) :
    QuantumChannel (LogicalRegister m w) QubitSpace :=
  QuantumChannel.comp
    (QuantumChannel.unitaryConj (selectedLogicalPortTransport m w port))
    (selectedLogicalPortSubsystem m w port).selectedPartialTraceFromRegister

/-- The selected-port channel returns the already-defined physical marginal
of the genuine accepted block. -/
theorem decodedRetryPoolSelectedPortChannel_mapDensity_acceptedOutput
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w) :
    (decodedRetryPoolSelectedPortChannel m w port).mapDensity
        (resourceDecodedRun h hdegree
          (noisyResources m w epsilon)).acceptedOutput =
      selectedLogicalPortTransportedAcceptedOutput
        h hdegree epsilon port := by
  rfl

/-- Select one actual logical port from a whole accepted block and apply the
complete successor measurement-record channel to that physical marginal. -/
noncomputable def decodedRetryPoolSelectedPortRecordChannel
    (m w : Nat) (port : LogicalSite m w) :
    QuantumChannel (LogicalRegister m w) QubitSpace :=
  QuantumChannel.comp
    decodedRetryPoolSuccessorOneQubitRecordChannel
    (decodedRetryPoolSelectedPortChannel m w port)

/-- On the genuine normalized accepted output, the selected-port channel
produces its literal computational clean/error record. -/
theorem decodedRetryPoolSelectedPortRecordChannel_mapDensity_acceptedOutput
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w) :
    (decodedRetryPoolSelectedPortRecordChannel m w port).mapDensity
        (resourceDecodedRun h hdegree
          (noisyResources m w epsilon)).acceptedOutput =
      decodedRetryPoolOneQubitRecordDensity
        (selectedLogicalPortRawParameter h hdegree epsilon port) := by
  rw [decodedRetryPoolSelectedPortRecordChannel,
    QuantumChannel.comp_mapDensity,
    decodedRetryPoolSelectedPortChannel_mapDensity_acceptedOutput]
  exact decodedRetryPoolSuccessorOneQubitRecordChannel_selectedOutput
    h hdegree epsilon port

/-- Undo the accepted-product flattening and apply the physical selected-port
record channel independently to each distinct accepted parent block. -/
noncomputable def decodedRetryPoolSelectedPortRecordChannelTensorPower
    (m w : Nat) (port : LogicalSite m w) (required : Nat) :
    QuantumChannel
      (tensorPowerCarrier (LogicalRegister m w) required)
      (tensorPowerCarrier QubitSpace required) :=
  let channel := decodedRetryPoolSelectedPortRecordChannel m w port
  ((channel.toFiniteInstrument).tensorPower required).kraus.toQuantumChannel
    ((channel.toFiniteInstrument).tensorPower_complete
      channel.toFiniteInstrument_complete required)

/-- Undo the accepted-product flattening and apply the physical selected-port
record channel independently to each distinct accepted parent block. -/
noncomputable def decodedRetryPoolAcceptedPortRecordProductChannel
    (m w : Nat) (port : LogicalSite m w) (required : Nat) :
    QuantumChannel
      (QubitRegister (Fin required × LogicalSite m w))
      (tensorPowerCarrier QubitSpace required) :=
  QuantumChannel.comp
    (decodedRetryPoolSelectedPortRecordChannelTensorPower m w port required)
    (QuantumChannel.unitaryConj
      (tensorPowerQubitRegisterTransport (LogicalSite m w) required).symm)

/-- The fixed-port physical channel maps the genuine product of distinct
accepted blocks to the tensor product of their actual measurement records. -/
theorem decodedRetryPoolAcceptedPortRecordProductChannel_mapDensity
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (port : LogicalSite m w) (required : Nat) :
    (decodedRetryPoolAcceptedPortRecordProductChannel m w port required).mapDensity
        (decodedRetryPoolAcceptedProductDensity
          h hdegree epsilon rhoUnit required) =
      tensorPowerProductInput
        (decodedRetryPoolOneQubitRecordDensity
          (selectedLogicalPortRawParameter h hdegree epsilon port))
        rhoUnit required := by
  apply DensityOperator.ext_toOperator
  simp only [decodedRetryPoolAcceptedPortRecordProductChannel,
    decodedRetryPoolAcceptedProductDensity,
    tensorPowerRegisterProductDensity,
    QuantumChannel.mapDensity_toOperator, QuantumChannel.comp_apply,
    QuantumChannel.unitaryConj_apply,
    UnitaryTransport.conjDensity_toOperator]
  rw [UnitaryTransport.symm_conjOperator_conjOperator]
  have hproduct := quantumChannelTensorPower_mapDensity_productInput
    (decodedRetryPoolSelectedPortRecordChannel m w port)
    (resourceDecodedRun h hdegree
      (noisyResources m w epsilon)).acceptedOutput
    rhoUnit rhoUnit rfl required
  rw [decodedRetryPoolSelectedPortRecordChannel_mapDensity_acceptedOutput
    h hdegree epsilon port] at hproduct
  exact hproduct

end HH18Parameterized
end Distillation
end QEC
