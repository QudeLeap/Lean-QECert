import QEC.Semantics.Instruments.TensorPower.ChannelProduct
import QEC.Semantics.Instruments.Registers.ProductDensity
/-!
# Sitewise channels on flattened register product densities

This module transports the recursively tensorized chosen-Kraus channel to the
ordinary trial/coordinate register.  On an actual product of independent
register blocks, its density output is the corresponding product of the
one-block channel output.
-/

universe u

namespace QEC
namespace Semantics

noncomputable section

namespace FiniteInstrument

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Apply one channel independently to every flattened register trial. -/
noncomputable def tensorPowerRegisterSitewiseChannel
    (channel : QuantumChannel (Qubit.QubitRegister ι) (Qubit.QubitRegister ι))
    (attempts : Nat) :
    QuantumChannel (Qubit.QubitRegister (Fin attempts × ι))
      (Qubit.QubitRegister (Fin attempts × ι)) :=
  QuantumChannel.comp
    (QuantumChannel.unitaryConj (tensorPowerQubitRegisterTransport ι attempts))
    (QuantumChannel.comp
      (((channel.toFiniteInstrument).tensorPower attempts).kraus.toQuantumChannel
        ((channel.toFiniteInstrument).tensorPower_complete
          channel.toFiniteInstrument_complete attempts))
      (QuantumChannel.unitaryConj
        (tensorPowerQubitRegisterTransport ι attempts).symm))

/-- The flattened sitewise channel maps a genuine block-product density to
the block-product of the one-block channel outputs. -/
theorem tensorPowerRegisterSitewiseChannel_mapDensity_product
    (channel : QuantumChannel (Qubit.QubitRegister ι) (Qubit.QubitRegister ι))
    (rho : DensityOperator (Qubit.QubitRegister ι))
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (Qubit.QubitRegister ι) 0))
    (attempts : Nat) :
    (tensorPowerRegisterSitewiseChannel channel attempts).mapDensity
        (tensorPowerRegisterProductDensity ι rho rhoUnit attempts) =
      tensorPowerRegisterProductDensity ι (channel.mapDensity rho) rhoUnit attempts := by
  apply DensityOperator.ext_toOperator
  simp only [tensorPowerRegisterSitewiseChannel,
    tensorPowerRegisterProductDensity,
    QuantumChannel.mapDensity_toOperator, QuantumChannel.comp_apply,
    QuantumChannel.unitaryConj_apply,
    UnitaryTransport.conjDensity_toOperator]
  rw [UnitaryTransport.symm_conjOperator_conjOperator]
  have hproduct := quantumChannelTensorPower_mapDensity_productInput
    channel rho rhoUnit rhoUnit rfl attempts
  exact congrArg
    (tensorPowerQubitRegisterTransport ι attempts).conjOperator hproduct

end FiniteInstrument

end
end Semantics
end QEC
