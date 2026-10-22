import QEC.Bounds.BPTSeparatedUnion.Assembly.Intertwining
import QEC.Bounds.BPTSeparatedUnion.Transport.SelectedTensorBridge

/-! # Selected/complement tensor compression for the final assembly -/

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
      "finalAssemblySelectedTensor_compression_regionLocal"

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000 in
theorem finalAssemblySelectedTensor_compression_regionLocal
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
    let S := Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex)
    let N := isotypicLiftedMultiplicity.{0} nB
    let X := WC.restrictScalars Complex
    let D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
      (M.fourFactorD region)
    let eSel := (M.activeSelectedEmbedding region bcomponent WB UB).toLinearMap
    let eComp := (M.activeComplementEmbedding region ccomponent WC UC).toLinearMap
    let H := Semantics.CompositeSystem S N
    let K := Semantics.CompositeSystem X D
    let R := M.regionSubsystem region
    let A0 : Semantics.Operator H :=
      (LinearMap.adjoint eSel).comp (A.comp eSel)
    ∀ (J : Semantics.CompositeSystem H K →ₗ[Complex] R.factorizedSystem),
      J = TensorProduct.map eSel eComp →
      (LinearMap.adjoint J).comp
          ((R.registerFactorization.conjOperator (R.extendLocalToRegister A)).comp J) =
        TensorProduct.map A0 (1 : Semantics.Operator K) := by
  dsimp only
  intro J hJ
  let S := Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex)
  let N := isotypicLiftedMultiplicity.{0} nB
  let X := WC.restrictScalars Complex
  let D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
    (M.fourFactorD region)
  let H := Semantics.CompositeSystem S N
  let K := Semantics.CompositeSystem X D
  let eSel := (M.activeSelectedEmbedding region bcomponent WB UB).toLinearMap
  let eComp := (M.activeComplementEmbedding region ccomponent WC UC).toLinearMap
  let R := M.regionSubsystem region
  have hComplementIsometry : (LinearMap.adjoint eComp).comp eComp =
      (1 : Semantics.Operator K) := by
    exact M.activeComplementEmbedding_adjoint_comp_self region ccomponent WC UC
  apply registerFactorizedTensor_compression_left_of_embedding
    L.localDimension R eSel eComp J
  · exact hJ
  · exact hComplementIsometry

end BPTCommutingProjectorModel
end Bounds
end QEC
