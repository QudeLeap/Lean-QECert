import QEC.Bounds.BPTSeparatedUnion.Separation
import QEC.Bounds.GeometricLocalityTradeoff.Entropy
noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- The final #388 output embedding in its exact two-transport normal form. -/
theorem finalAssemblyOutputEmbedding_eq_twoTransport
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
        (isotypicLiftedMultiplicity.{0} nC))) :
    M.finalAssemblyOutputEmbedding region bcomponent ccomponent WB WC UB UC =
      (M.fourFactorTransport region).toLinearEquiv.toLinearMap.comp
        ((M.regionSubsystem region).registerFactorization.symm.toLinearEquiv.toLinearMap.comp
          (TensorProduct.map
            (M.activeSelectedEmbedding region bcomponent WB UB).toLinearMap
            (M.activeComplementEmbedding region ccomponent WC UC).toLinearMap)) := by
  exact (M.finalAssemblyInputEmbedding_eq_outputEmbedding
    region bcomponent ccomponent WB WC UB UC).symm.trans
    (M.finalAssemblyInputEmbedding_eq_twoTransport
      region bcomponent ccomponent WB WC UB UC).symm

end BPTCommutingProjectorModel
end Bounds
end QEC
