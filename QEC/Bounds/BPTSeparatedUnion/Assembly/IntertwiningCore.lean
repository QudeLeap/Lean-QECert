import QEC.Bounds.BPTSeparatedUnion.Assembly.IntertwiningAlgebra
import QEC.Bounds.BPTDisentangling.SeparatedUnionBridge

/-!
# Boundary-unitary intertwining in explicit final-assembly coordinates
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
      "finalAssemblyJointCoordinates_intertwines_boundaryUnitary"

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 2000 in
theorem finalAssemblyJointCoordinates_intertwines_boundaryUnitary
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
    let J := fourFactorJointBCSectorEmbedding (A := M.fourFactorA region)
      (D := M.fourFactorD region) pB pC
    let T := M.secondCutJointActiveBlockTransport region bcomponent ccomponent WB WC UB UC
    let C := composeUnitaryTransport
      (productBlockRegrouping (A := M.fourFactorA region)
        (W := WB.restrictScalars Complex) (N := N) (X := X) (D := D)).symm
      (tensorAssociatorUnitary S (Semantics.CompositeSystem N X) D)
    let O := tensorAssociatorUnitary (Semantics.CompositeSystem S N) X D
    let Wactive := jointBCSectorActiveUnitary (A := M.fourFactorA region)
      (D := M.fourFactorD region) pB pC
      (activeSectorJointBCUnitary pB pC UB UC U)
    let Vcommon := unitaryLTensor S (unitaryRTensor U D)
    let Vraw := conjugateUnitaryTransport C Vcommon
    let leftUnitary := conjugateUnitaryTransport
      (tensorAssociatorUnitary S N X) (unitaryLTensor S U)
    let leftExtended := unitaryRTensor leftUnitary D
    let V4 := fourFactorBCUnitaryTransport (A := M.fourFactorA region)
      (D := M.fourFactorD region) (activeSectorPhysicalUnitary pB pC UB UC U)
    V4.toLinearEquiv.toLinearMap.comp
        (J.comp (T.symm.toLinearEquiv.toLinearMap.comp
          (C.toLinearEquiv.toLinearMap.comp O.toLinearEquiv.toLinearMap))) =
      (J.comp (T.symm.toLinearEquiv.toLinearMap.comp
        (C.toLinearEquiv.toLinearMap.comp O.toLinearEquiv.toLinearMap))).comp
          leftExtended.toLinearEquiv.toLinearMap := by
  dsimp only
  let pB := bcomponent.1.restrictScalars Complex
  let pC := ccomponent.1.restrictScalars Complex
  let S := Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex)
  let N := isotypicLiftedMultiplicity.{0} nB
  let X := WC.restrictScalars Complex
  let D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
    (M.fourFactorD region)
  let J := fourFactorJointBCSectorEmbedding (A := M.fourFactorA region)
    (D := M.fourFactorD region) pB pC
  let T := M.secondCutJointActiveBlockTransport region bcomponent ccomponent WB WC UB UC
  let R := productBlockRegrouping (A := M.fourFactorA region)
    (W := WB.restrictScalars Complex) (N := N) (X := X) (D := D)
  let commonAssociator := tensorAssociatorUnitary S (Semantics.CompositeSystem N X) D
  let C := composeUnitaryTransport R.symm commonAssociator
  let O := tensorAssociatorUnitary (Semantics.CompositeSystem S N) X D
  let Vcommon := unitaryLTensor S (unitaryRTensor U D)
  let Vraw := conjugateUnitaryTransport C Vcommon
  let Wactive := jointBCSectorActiveUnitary (A := M.fourFactorA region)
    (D := M.fourFactorD region) pB pC
    (activeSectorJointBCUnitary pB pC UB UC U)
  let V4 := fourFactorBCUnitaryTransport (A := M.fourFactorA region)
    (D := M.fourFactorD region) (activeSectorPhysicalUnitary pB pC UB UC U)
  let leftUnitary := conjugateUnitaryTransport
    (tensorAssociatorUnitary S N X) (unitaryLTensor S U)
  let leftExtended := unitaryRTensor leftUnitary D
  have hV4J :=
    fourFactorBCUnitaryTransport_activeSector_intertwines_jointBCSectorEmbedding
      (A := M.fourFactorA region) (D := M.fourFactorD region) pB pC UB UC U
  have hTforward := secondCutActiveCoordinateTransport_intertwines
    (A := M.fourFactorA region) (B := M.fourFactorB region)
    (C := M.fourFactorC region) (D := M.fourFactorD region)
    (W := WB.restrictScalars Complex) (N := isotypicLiftedMultiplicity.{0} nB)
    (X := WC.restrictScalars Complex) (N2 := isotypicLiftedMultiplicity.{0} nC)
    UB UC U
  have hTback := unitary_intertwining_symm T Wactive Vcommon hTforward
  have hCoordinates := conjugateUnitaryTransport_intertwines C Vcommon
  have hRegroup := finalAssembly_regrouping_intertwines
    (A := M.fourFactorA region) (W := WB.restrictScalars Complex)
    (N := N) (X := X) (D := D) U
  exact linearMap_intertwining_four_stage _ _ _ _ _ _ _ _ _
    hV4J hTback hCoordinates.symm hRegroup

end BPTCommutingProjectorModel
end Bounds
end QEC
