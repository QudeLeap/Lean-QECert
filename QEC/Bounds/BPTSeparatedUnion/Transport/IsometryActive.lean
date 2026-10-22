import QEC.Bounds.BPTSeparatedUnion.Transport.IsometryStatement

/-!
# Active-coordinate isometry

The active selected and complement embeddings form an isometric tensor product
on the named final-assembly compression domain.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.modifyEnv fun env =>
    Lean.LibrarySuggestions.nameDenyListExt.addEntry env
      "finalAssemblyCompressionActiveEmbedding_adjoint_comp_self"

set_option maxHeartbeats 900000 in
set_option synthInstance.maxHeartbeats 180000 in
theorem finalAssemblyCompressionActiveEmbedding_adjoint_comp_self
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
    let J := M.finalAssemblyCompressionActiveEmbedding
      region bcomponent ccomponent WB WC UB UC
    (LinearMap.adjoint J).comp J =
      (1 : Semantics.Operator (M.FinalAssemblyCompressionDomain region nB nC WB WC)) := by
  dsimp only [finalAssemblyCompressionActiveEmbedding]
  let S := M.regionSubsystem region
  let eSel := M.activeSelectedEmbeddingCore region bcomponent WB UB
  let eComp := M.activeComplementEmbeddingCore region ccomponent WC UC
  simpa only [TensorProduct.toLinearMap_mapIsometry] using
    (@linearIsometry_adjoint_comp_self
      (M.FinalAssemblyCompressionDomain region nB nC WB WC)
      (Semantics.CompositeSystem S.selectedSystem S.complementSystem)
      inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance
      (TensorProduct.mapIsometry eSel eComp))

end BPTCommutingProjectorModel
end Bounds
end QEC
