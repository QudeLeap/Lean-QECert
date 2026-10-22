import QEC.Distillation.LowOverheadProtocol.Core.ResourceChannel

/-!
# HH18 physical resource consumer

This layer exposes the physical resource channel's public syndrome-input
surface and its exact physical-branch bridge.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Protocol

open Semantics
open Semantics.Qubit

/-- The physical state entering the HH18 stabilizer instrument, obtained by
measuring and consuming the supplied resource family. -/
noncomputable def resourcePreSyndromeState
    (inputs : ResourceInput resourceCount QubitSpace) : DensityOperator PhysicalRegister :=
  resourceConsumerChannel.mapDensity (prepareMeasuredResources inputs)

/-- The pure physical branch density is exactly the syndrome-decoding branch
operator for the same measured error word. -/
theorem errorBranchDensity_to_errorBranchOperator
    (error : PhysicalErrorWord) :
    (DensityOperator.pureDensity (errorBranchState error)
      (errorBranchState_normSq error)).toOperator =
      HH18SyndromeDecoding.errorBranchOperator error := by
  rw [DensityOperator.pureDensity_toOperator]
  rfl

end HH18Protocol
end Distillation
end QEC
