import QEC.Bounds.BPTSeparatedUnion.Assembly.RegionCompression
import QEC.Bounds.BPTDisentangling.SeparatedUnionBridge

/-!
# Left compression in reassociated final-assembly coordinates

This module transports a region-local operator through the retained boundary
unitary and compresses it to the left tensor factor of the final assembly.
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
      "finalAssembly_leftCompression_after_boundaryUnitary"

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 2000 in
theorem finalAssembly_leftCompression_after_boundaryUnitary
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
        (WC.restrictScalars Complex)))
    (A : Semantics.Operator (M.regionSubsystem region).selectedSystem) :
    let pB := bcomponent.1.restrictScalars Complex
    let pC := ccomponent.1.restrictScalars Complex
    let Uglobal := M.activeSectorBoundaryGlobalUnitary region pB pC UB UC U
    let F := M.fourFactorTransport region
    let S := Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex)
    let N := isotypicLiftedMultiplicity.{0} nB
    let X := WC.restrictScalars Complex
    let D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
      (M.fourFactorD region)
    let E := M.finalAssemblyOutputEmbedding region bcomponent ccomponent WB WC UB UC
    let O := tensorAssociatorUnitary (Semantics.CompositeSystem S N) X D
    let Enew := E.comp O.toLinearEquiv.toLinearMap
    let eSel := (M.activeSelectedEmbedding region bcomponent WB UB).toLinearMap
    let A0 : Semantics.Operator (Semantics.CompositeSystem S N) :=
      (LinearMap.adjoint eSel).comp (A.comp eSel)
    let leftUnitary := conjugateUnitaryTransport
      (tensorAssociatorUnitary S N X) (unitaryLTensor S U)
    let leftLocal : Semantics.Operator
        (Semantics.CompositeSystem (Semantics.CompositeSystem S N) X) :=
      leftUnitary.conjOperator (TensorProduct.map A0 (1 : Semantics.Operator X))
    (LinearMap.adjoint Enew).comp
        ((F.conjOperator
          (Uglobal.conjOperator ((M.regionSubsystem region).extendLocalToRegister A))).comp Enew) =
      TensorProduct.map leftLocal (1 : Semantics.Operator D) := by
  dsimp only
  let pB := bcomponent.1.restrictScalars Complex
  let pC := ccomponent.1.restrictScalars Complex
  let Uglobal := M.activeSectorBoundaryGlobalUnitary region pB pC UB UC U
  let F := M.fourFactorTransport region
  let S := Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex)
  let N := isotypicLiftedMultiplicity.{0} nB
  let X := WC.restrictScalars Complex
  let D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
    (M.fourFactorD region)
  let E := M.finalAssemblyOutputEmbedding region bcomponent ccomponent WB WC UB UC
  let V4 := fourFactorBCUnitaryTransport (A := M.fourFactorA region)
    (D := M.fourFactorD region) (activeSectorPhysicalUnitary pB pC UB UC U)
  let O := tensorAssociatorUnitary (Semantics.CompositeSystem S N) X D
  let Enew := E.comp O.toLinearEquiv.toLinearMap
  let leftUnitary := conjugateUnitaryTransport
    (tensorAssociatorUnitary S N X) (unitaryLTensor S U)
  let leftExtended := unitaryRTensor leftUnitary D
  let eSel := (M.activeSelectedEmbedding region bcomponent WB UB).toLinearMap
  let A0 : Semantics.Operator (Semantics.CompositeSystem S N) :=
    (LinearMap.adjoint eSel).comp (A.comp eSel)
  let leftLocal : Semantics.Operator
      (Semantics.CompositeSystem (Semantics.CompositeSystem S N) X) :=
    leftUnitary.conjOperator (TensorProduct.map A0 (1 : Semantics.Operator X))
  have hIntertwines : V4.toLinearEquiv.toLinearMap.comp Enew =
      Enew.comp leftExtended.toLinearEquiv.toLinearMap := by
    apply M.finalAssemblyReassociatedEmbedding_intertwines_boundaryUnitary
      region bcomponent ccomponent WB WC UB UC U
  calc
    (LinearMap.adjoint Enew).comp
        ((F.conjOperator
          (Uglobal.conjOperator ((M.regionSubsystem region).extendLocalToRegister A))).comp Enew) =
      (LinearMap.adjoint Enew).comp
        ((V4.conjOperator
          (F.conjOperator ((M.regionSubsystem region).extendLocalToRegister A))).comp Enew) := by
            apply embedding_compression_congr Enew
            apply M.fourFactorTransport_conj_activeSectorBoundaryGlobalUnitary_conjOperator
              region pB pC UB UC U
    _ = leftExtended.conjOperator
        ((LinearMap.adjoint Enew).comp
          ((F.conjOperator ((M.regionSubsystem region).extendLocalToRegister A)).comp Enew)) :=
          by
            apply compression_conjOperator_of_embedding_intertwines Enew V4 leftExtended
              (H := Semantics.CompositeSystem
                (Semantics.CompositeSystem (Semantics.CompositeSystem S N) X) D)
              (F.conjOperator ((M.regionSubsystem region).extendLocalToRegister A))
            exact hIntertwines
    _ = leftExtended.conjOperator
          (TensorProduct.map (TensorProduct.map A0 (1 : Semantics.Operator X))
          (1 : Semantics.Operator D)) := by
            apply unitary_conjOperator_congr leftExtended
            apply M.finalAssemblyReassociatedEmbedding_compression_regionLocal
              region bcomponent ccomponent WB WC UB UC A O
            · rfl
            · rfl
    _ = TensorProduct.map leftLocal (1 : Semantics.Operator D) := by
          apply unitaryRTensor_conj_tensorMap

end BPTCommutingProjectorModel
end Bounds
end QEC
