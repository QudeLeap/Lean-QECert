import QEC.Bounds.BPTSeparatedUnion.Assembly.SelectedTensorCompression
import QEC.Bounds.BPTSeparatedUnion.Transport.Coordinates
import QEC.Bounds.BPTSeparatedUnion.Transport.SelectedTensorCore

/-! # Region-local compression in the retained final-output coordinates -/

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
      "finalAssemblyOutputEmbedding_compression_regionLocal"

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000 in
theorem finalAssemblyOutputEmbedding_compression_regionLocal
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
    (A : Semantics.Operator (M.regionSubsystem region).selectedSystem) :
    let F := M.fourFactorTransport region
    let S := Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex)
    let N := isotypicLiftedMultiplicity.{0} nB
    let X := WC.restrictScalars Complex
    let D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
      (M.fourFactorD region)
    let E := M.finalAssemblyOutputEmbedding region bcomponent ccomponent WB WC UB UC
    let eSel := (M.activeSelectedEmbedding region bcomponent WB UB).toLinearMap
    let A0 : Semantics.Operator (Semantics.CompositeSystem S N) :=
      (LinearMap.adjoint eSel).comp (A.comp eSel)
    (LinearMap.adjoint E).comp
        ((F.conjOperator ((M.regionSubsystem region).extendLocalToRegister A)).comp E) =
      TensorProduct.map A0 (1 : Semantics.Operator (Semantics.CompositeSystem X D)) := by
  dsimp only
  let F := M.fourFactorTransport region
  let S := Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex)
  let N := isotypicLiftedMultiplicity.{0} nB
  let X := WC.restrictScalars Complex
  let D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
    (M.fourFactorD region)
  let E := M.finalAssemblyOutputEmbedding region bcomponent ccomponent WB WC UB UC
  let eSel := (M.activeSelectedEmbedding region bcomponent WB UB).toLinearMap
  let eComp := (M.activeComplementEmbedding region ccomponent WC UC).toLinearMap
  let J := TensorProduct.map eSel eComp
  let R := M.regionSubsystem region
  let A0 : Semantics.Operator (Semantics.CompositeSystem S N) :=
    (LinearMap.adjoint eSel).comp (A.comp eSel)
  have hCoordinates := M.finalAssemblyOutputEmbedding_eq_twoTransport
    region bcomponent ccomponent WB WC UB UC
  calc
    (LinearMap.adjoint E).comp ((F.conjOperator (R.extendLocalToRegister A)).comp E) =
      (LinearMap.adjoint J).comp
        ((R.registerFactorization.conjOperator (R.extendLocalToRegister A)).comp J) := by
          apply compression_conj_after_transportPair_of_eq
            F R.registerFactorization J E (R.extendLocalToRegister A)
          exact hCoordinates
    _ = TensorProduct.map A0
        (1 : Semantics.Operator (Semantics.CompositeSystem X D)) := by
          apply M.finalAssemblySelectedTensor_compression_regionLocal
            region bcomponent ccomponent WB WC UB UC A J
          rfl

end BPTCommutingProjectorModel
end Bounds
end QEC
