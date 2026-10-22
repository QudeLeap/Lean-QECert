import QEC.Bounds.BPTSeparatedUnion.Assembly.LeftCompression
import QEC.Bounds.BPTSeparatedUnion.Transport.IsometryRealization

/-! # Isometry of the reassociated final-output embedding -/

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
      "finalAssemblyReassociatedEmbedding_adjoint_comp_self"

set_option maxHeartbeats 500000 in
theorem finalAssemblyReassociatedEmbedding_adjoint_comp_self
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
    let S := Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex)
    let N := isotypicLiftedMultiplicity.{0} nB
    let X := WC.restrictScalars Complex
    let D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
      (M.fourFactorD region)
    let E := M.finalAssemblyOutputEmbedding region bcomponent ccomponent WB WC UB UC
    let O := tensorAssociatorUnitary (Semantics.CompositeSystem S N) X D
    let Enew := E.comp O.toLinearEquiv.toLinearMap
    (LinearMap.adjoint Enew).comp Enew =
      (1 : Semantics.Operator
        (Semantics.CompositeSystem (Semantics.CompositeSystem (Semantics.CompositeSystem S N) X) D)) := by
  dsimp only
  let S := Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex)
  let N := isotypicLiftedMultiplicity.{0} nB
  let X := WC.restrictScalars Complex
  let D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
    (M.fourFactorD region)
  let E := M.finalAssemblyOutputEmbedding region bcomponent ccomponent WB WC UB UC
  let O := tensorAssociatorUnitary (Semantics.CompositeSystem S N) X D
  let Enew := E.comp O.toLinearEquiv.toLinearMap
  have hE := M.finalAssemblyOutputEmbedding_adjoint_comp_self
    region bcomponent ccomponent WB WC UB UC
  apply precomposed_embedding_isometry_of_eq O E Enew
  · rfl
  · exact hE

end BPTCommutingProjectorModel
end Bounds
end QEC
