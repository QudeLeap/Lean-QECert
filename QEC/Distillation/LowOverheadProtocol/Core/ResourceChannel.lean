import QEC.Distillation.LowOverheadProtocol.Core.ResourceDiagonal

/-!
# HH18 physical resource channel

This layer applies the weighted finite word mixture through the exact diagonal
resource-channel bridge.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Protocol

open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators

universe u

local instance instChannelClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

private theorem quantumChannel_apply_input_of_explicit_support
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

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 262144 in
/-- The resource consumer maps the actual finite measured-resource distribution
to the corresponding physical sitewise-injection branch mixture. -/
theorem resourceConsumerChannel_prepares_branchMixture
    (inputs : ResourceInput resourceCount QubitSpace) :
    resourceConsumerChannel (prepareMeasuredResources inputs).toOperator =
      physicalErrorWords.sum (fun error =>
        (measuredErrorWordProbability inputs error : Complex) •
          (DensityOperator.pureDensity (errorBranchState error)
            (errorBranchState_normSq error)).toOperator) := by
  exact quantumChannel_apply_input_of_explicit_support
    physicalErrorWords resourceConsumerChannel
    (prepareMeasuredResources inputs).toOperator
    (fun error => (measuredErrorWordProbability inputs error : Complex))
    errorWordBasisDensity
    (fun error => DensityOperator.pureDensity (errorBranchState error)
      (errorBranchState_normSq error))
    (prepareMeasuredResources_toOperator inputs)
    resourceConsumerChannel_errorWordBasisDensity

end HH18Protocol
end Distillation
end QEC
