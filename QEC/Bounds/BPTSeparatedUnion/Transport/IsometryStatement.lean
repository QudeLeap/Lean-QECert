import QEC.Bounds.BPTSeparatedUnion.Transport.CompressionExteriorCoordinates

/-!
# Final-output isometry statement

The retained output embedding's exact isometry equation is named independently
from its transport-factor proof.  The source-facing realization retains the
original theorem statement.
-/

noncomputable section

namespace QEC
namespace Bounds

open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

set_option maxHeartbeats 500000 in
set_option synthInstance.maxHeartbeats 120000 in
def FinalAssemblyOutputEmbeddingIsometry
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
        (isotypicLiftedMultiplicity.{0} nC))) : Prop :=
  let Eout := M.finalAssemblyOutputEmbedding region bcomponent ccomponent WB WC UB UC
  (LinearMap.adjoint Eout).comp Eout =
    (1 : Semantics.Operator
      (M.FinalAssemblyCompressionDomain region nB nC WB WC))

end BPTCommutingProjectorModel
end Bounds
end QEC
