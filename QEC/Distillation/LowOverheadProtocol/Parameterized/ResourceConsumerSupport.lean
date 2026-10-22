import QEC.Semantics.Entropy.Purification
/-!
# Parameterized HH18 resource-consumer support

This module contains the finite-support linearity bridge used by the physical
resource consumer.  It deliberately has no protocol-specific support
instantiation.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Parameterized

open Semantics
open scoped BigOperators

universe u

/-- A quantum channel sends an explicitly supported finite mixture to the
corresponding mixture of its pointwise images. -/
theorem quantumChannel_apply_input_of_explicit_support
    {ι H K : Type u} (support : Finset ι)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (channel : QuantumChannel H K) (input : Operator H) (weight : ι → Complex)
    (inputState : ι → DensityOperator H) (outputState : ι → DensityOperator K)
    (hinput : input = support.sum (fun i => weight i • (inputState i).toOperator))
    (hpointwise : ∀ i, channel (inputState i).toOperator = (outputState i).toOperator) :
    channel input = support.sum (fun i => weight i • (outputState i).toOperator) := by
  rw [hinput]
  change channel.toLinearMap
    (support.sum (fun i => weight i • (inputState i).toOperator)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [map_smul, hpointwise i]

end HH18Parameterized
end Distillation
end QEC
