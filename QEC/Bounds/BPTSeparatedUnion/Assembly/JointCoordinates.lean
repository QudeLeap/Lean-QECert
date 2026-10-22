import QEC.Bounds.BPTSeparatedUnion.Factorization
import QEC.Bounds.BPTDisentangling.Assembly.AssemblyHelpers
import QEC.Bounds.BPTDisentangling.Joint.ActiveBlockTransports
import QEC.Bounds.BPTDisentangling.Joint.Regrouping
import QEC.Bounds.BPTDisentangling.Joint.Sector

/-!
# Final-output joint-sector coordinates

The final-output embedding is exposed in the exact second-cut coordinate form
used by the boundary-unitary intertwining proof.
-/

noncomputable section

namespace QEC
namespace Bounds

open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.modifyEnv fun env =>
    Lean.LibrarySuggestions.nameDenyListExt.addEntry env
      "finalAssemblyOutputEmbedding_eq_jointCoordinates"

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 2000 in
theorem finalAssemblyOutputEmbedding_eq_jointCoordinates
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
    let J := fourFactorJointBCSectorEmbedding (A := M.fourFactorA region)
      (D := M.fourFactorD region) (bcomponent.1.restrictScalars Complex)
      (ccomponent.1.restrictScalars Complex)
    let T := M.secondCutJointActiveBlockTransport region bcomponent ccomponent WB WC UB UC
    let commonCoordinates := composeUnitaryTransport
      (productBlockRegrouping (A := M.fourFactorA region)
        (W := WB.restrictScalars Complex) (N := N) (X := X) (D := D)).symm
      (tensorAssociatorUnitary S (Semantics.CompositeSystem N X) D)
    E = J.comp
      (T.symm.toLinearEquiv.toLinearMap.comp commonCoordinates.toLinearEquiv.toLinearMap) := by
  rfl

end BPTCommutingProjectorModel
end Bounds
end QEC
