import QEC.Bounds.BPTSeparatedUnion.Assembly.AssociatorSpecialization

/-! # Right-identity form of the cached final-assembly associator -/

noncomputable section

namespace QEC
namespace Bounds

open scoped TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.modifyEnv fun env =>
    Lean.LibrarySuggestions.nameDenyListExt.addEntry env
      "finalAssemblyAssociator_symm_conj_leftMap_right_one"

set_option maxHeartbeats 1000000 in
theorem finalAssemblyAssociator_symm_conj_leftMap_right_one
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    {nB nC : Nat} [NeZero nB] [NeZero nC]
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region)) :
    let H := Semantics.CompositeSystem
      (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
      (isotypicLiftedMultiplicity.{0} nB)
    let X := WC.restrictScalars Complex
    let D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
      (M.fourFactorD region)
    ∀ (A0 : Semantics.Operator H),
      (tensorAssociatorUnitary H X D).symm.conjOperator
          (TensorProduct.map A0 (1 : Semantics.Operator (Semantics.CompositeSystem X D))) =
        TensorProduct.map (TensorProduct.map A0 (1 : Semantics.Operator X))
          (1 : Semantics.Operator D) := by
  dsimp only
  intro A0
  let X := WC.restrictScalars Complex
  let D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
    (M.fourFactorD region)
  have hOne : TensorProduct.map (1 : Semantics.Operator X) (1 : Semantics.Operator D) =
      (1 : Semantics.Operator (Semantics.CompositeSystem X D)) := TensorProduct.map_one
  have hAssoc := M.finalAssemblyAssociator_symm_conj_tensorMap
    (nB := nB) (nC := nC) region WB WC A0
  exact (congrArg
    (fun Q => (tensorAssociatorUnitary
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
        (isotypicLiftedMultiplicity.{0} nB)) X D).symm.conjOperator
        (TensorProduct.map A0 Q)) hOne).symm.trans hAssoc

end BPTCommutingProjectorModel
end Bounds
end QEC
