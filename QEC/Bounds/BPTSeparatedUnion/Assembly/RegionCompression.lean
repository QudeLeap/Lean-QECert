import QEC.Bounds.BPTSeparatedUnion.Assembly.AssociatorRightOne

/-! # Region-local compression in reassociated final-assembly coordinates -/

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
      "finalAssemblyReassociatedEmbedding_compression_regionLocal"

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
set_option maxRecDepth 2000 in
theorem finalAssemblyReassociatedEmbedding_compression_regionLocal
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
    ∀ (O : Semantics.UnitaryTransport
        (Semantics.CompositeSystem
          (Semantics.CompositeSystem (Semantics.CompositeSystem S N) X) D)
        (Semantics.CompositeSystem (Semantics.CompositeSystem S N)
          (Semantics.CompositeSystem X D))),
      O = tensorAssociatorUnitary (Semantics.CompositeSystem S N) X D →
      ∀ (Enew : Semantics.CompositeSystem
          (Semantics.CompositeSystem (Semantics.CompositeSystem S N) X) D →ₗ[Complex]
        M.fourFactorSystem region),
        Enew = E.comp O.toLinearEquiv.toLinearMap →
        (LinearMap.adjoint Enew).comp
            ((F.conjOperator ((M.regionSubsystem region).extendLocalToRegister A)).comp Enew) =
          TensorProduct.map (TensorProduct.map A0 (1 : Semantics.Operator X))
            (1 : Semantics.Operator D) := by
  dsimp only
  intro O hO Enew hEnew
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
  have hRaw := M.finalAssemblyOutputEmbedding_compression_regionLocal
    region bcomponent ccomponent WB WC UB UC A
  calc
    (LinearMap.adjoint Enew).comp
        ((F.conjOperator ((M.regionSubsystem region).extendLocalToRegister A)).comp Enew) =
      O.symm.conjOperator
        ((LinearMap.adjoint E).comp
          ((F.conjOperator ((M.regionSubsystem region).extendLocalToRegister A)).comp E)) := by
            apply compression_precompose_unitary_of_eq O E Enew
            exact hEnew
    _ = O.symm.conjOperator
        (TensorProduct.map A0 (1 : Semantics.Operator (Semantics.CompositeSystem X D))) := by
          apply congrArg O.symm.conjOperator
          exact hRaw
    _ = TensorProduct.map (TensorProduct.map A0 (1 : Semantics.Operator X))
        (1 : Semantics.Operator D) := by
          subst O
          apply M.finalAssemblyAssociator_symm_conj_leftMap_right_one
            (nB := nB) (nC := nC) region WB WC

end BPTCommutingProjectorModel
end Bounds
end QEC
