import QEC.Bounds.BPTSeparatedUnion.Assembly.Isometry
import QEC.Bounds.BPTSeparatedUnion.Transport.IntertwiningCore

/-! # Exterior-local intertwining in reassociated final-assembly coordinates -/

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
      "finalAssemblyReassociatedEmbedding_intertwines_exteriorLocal"

set_option maxHeartbeats 1000000 in
theorem finalAssemblyReassociatedEmbedding_intertwines_exteriorLocal
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
    (B : Semantics.Operator (M.regionSubsystem (M.exterior region)).selectedSystem) :
    let F := M.fourFactorTransport region
    let S := Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex)
    let N := isotypicLiftedMultiplicity.{0} nB
    let X := WC.restrictScalars Complex
    let D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
      (M.fourFactorD region)
    let E := M.finalAssemblyOutputEmbedding region bcomponent ccomponent WB WC UB UC
    let O := tensorAssociatorUnitary (Semantics.CompositeSystem S N) X D
    let Enew := E.comp O.toLinearEquiv.toLinearMap
    let rightLocal : Semantics.Operator D := TensorProduct.map
      (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} nC))
      (M.exteriorCompressionWitness region B)
    (F.conjOperator ((M.regionSubsystem (M.exterior region)).extendLocalToRegister B)).comp
        Enew = Enew.comp
          (TensorProduct.map
            (1 : Semantics.Operator (Semantics.CompositeSystem (Semantics.CompositeSystem S N) X))
            rightLocal) := by
  dsimp only
  let F := M.fourFactorTransport region
  let S := Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex)
  let N := isotypicLiftedMultiplicity.{0} nB
  let X := WC.restrictScalars Complex
  let D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
    (M.fourFactorD region)
  let E := M.finalAssemblyOutputEmbedding region bcomponent ccomponent WB WC UB UC
  let O := tensorAssociatorUnitary (Semantics.CompositeSystem S N) X D
  let Enew := E.comp O.toLinearEquiv.toLinearMap
  let Z := M.exteriorCompressionWitness region B
  let rightLocal : Semantics.Operator D :=
    TensorProduct.map (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} nC)) Z
  have hE := M.finalAssemblyOutputEmbedding_intertwines_exteriorLocal_at_witness
    region bcomponent ccomponent WB WC UB UC B
  apply intertwining_precompose_associator_right_of_eq
    (H := Semantics.CompositeSystem S N) (K := X) (J := D)
    (T := M.fourFactorSystem region)
    O (by rfl) E Enew (by rfl)
    (F.conjOperator ((M.regionSubsystem (M.exterior region)).extendLocalToRegister B))
    rightLocal hE

end BPTCommutingProjectorModel
end Bounds
end QEC
