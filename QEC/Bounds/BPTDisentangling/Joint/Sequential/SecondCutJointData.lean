import QEC.Bounds.BPTDisentangling.Joint.Sequential.BlockData

/-!
# BPT simultaneous-sector second-cut block data

The named result keeps the large physical block equality out of downstream
declaration signatures while preserving the literal simultaneous compression.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

set_option maxHeartbeats 800000 in
/-- The concrete simultaneous-sector second-cut block and its normalized witness. -/
def SecondCutActualJointActiveBlock
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nB nC : Nat} [NeZero nB] [NeZero nC]
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UB : Semantics.UnitaryTransport (bcomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WB.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nB)))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC)))
    (Qsecond : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)))) : Prop :=
  ∃ phi : Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex),
    ‖phi‖ = 1 ∧
    (M.secondCutJointActiveBlockTransport region bcomponent ccomponent WB WC UB UC).conjOperator
        (M.secondCutJointCompression region
          (bcomponent.1.restrictScalars Complex) (ccomponent.1.restrictScalars Complex)) =
      (unitaryLTensor (Semantics.CompositeSystem (M.fourFactorA region)
        (WB.restrictScalars Complex))
        (tensorAssociatorUnitary (isotypicLiftedMultiplicity.{0} nB)
          (WC.restrictScalars Complex)
          (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
            (M.fourFactorD region))).symm).conjOperator
        (TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap
          (M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond))

end BPTCommutingProjectorModel

end Bounds
end QEC
