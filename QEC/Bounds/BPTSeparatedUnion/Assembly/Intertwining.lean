import QEC.Bounds.BPTSeparatedUnion.Assembly.IntertwiningCore

/-!
# Final-assembly boundary-unitary intertwining

The explicit coordinate calculation is transferred to the retained final-output
embedding without changing the theorem statement.
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
      "finalAssemblyReassociatedEmbedding_intertwines_boundaryUnitary"

set_option maxHeartbeats 1800000 in
set_option maxRecDepth 2000 in
theorem finalAssemblyReassociatedEmbedding_intertwines_boundaryUnitary
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
    (U : Semantics.UnitaryTransport
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (WC.restrictScalars Complex))
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (WC.restrictScalars Complex))) :
    let pB := bcomponent.1.restrictScalars Complex
    let pC := ccomponent.1.restrictScalars Complex
    let S := Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex)
    let N := isotypicLiftedMultiplicity.{0} nB
    let X := WC.restrictScalars Complex
    let D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
      (M.fourFactorD region)
    let E := M.finalAssemblyOutputEmbedding region bcomponent ccomponent WB WC UB UC
    let outerAssociator := tensorAssociatorUnitary (Semantics.CompositeSystem S N) X D
    let Enew := E.comp outerAssociator.toLinearEquiv.toLinearMap
    let leftUnitary := conjugateUnitaryTransport
      (tensorAssociatorUnitary S N X) (unitaryLTensor S U)
    let leftUnitaryExtended := unitaryRTensor leftUnitary D
    let V4 := fourFactorBCUnitaryTransport (A := M.fourFactorA region)
      (D := M.fourFactorD region) (activeSectorPhysicalUnitary pB pC UB UC U)
    V4.toLinearEquiv.toLinearMap.comp Enew =
      Enew.comp leftUnitaryExtended.toLinearEquiv.toLinearMap := by
  dsimp only
  let S := Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex)
  let N := isotypicLiftedMultiplicity.{0} nB
  let X := WC.restrictScalars Complex
  let D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
    (M.fourFactorD region)
  let O := tensorAssociatorUnitary (Semantics.CompositeSystem S N) X D
  have hOutput := M.finalAssemblyOutputEmbedding_eq_jointCoordinates
    region bcomponent ccomponent WB WC UB UC
  have hEnew := congrArg (fun embedding => embedding.comp O.toLinearEquiv.toLinearMap) hOutput
  have hCore := M.finalAssemblyJointCoordinates_intertwines_boundaryUnitary
    region bcomponent ccomponent WB WC UB UC U
  exact linearMap_intertwining_of_eq _ _ _ _ hEnew hCore

end BPTCommutingProjectorModel
end Bounds
end QEC
