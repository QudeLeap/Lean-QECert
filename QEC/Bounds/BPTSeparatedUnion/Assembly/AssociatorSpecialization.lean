import QEC.Bounds.BPTSeparatedUnion.Assembly.CompressionAlgebra

/-! # Cached BPT specialization of the final-assembly associator algebra -/

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
      "finalAssemblyAssociator_symm_conj_tensorMap"

set_option maxHeartbeats 1000000 in
theorem finalAssemblyAssociator_symm_conj_tensorMap
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
          (TensorProduct.map A0
            (TensorProduct.map (1 : Semantics.Operator X) (1 : Semantics.Operator D))) =
        TensorProduct.map (TensorProduct.map A0 (1 : Semantics.Operator X))
          (1 : Semantics.Operator D) := by
  dsimp only
  intro A0
  apply tensorAssociatorUnitary_symm_conj_tensorMap

end BPTCommutingProjectorModel
end Bounds
end QEC
