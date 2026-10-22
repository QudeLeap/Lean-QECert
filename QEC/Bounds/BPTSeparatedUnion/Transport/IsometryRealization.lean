import QEC.Bounds.BPTSeparatedUnion.Transport.IsometryCore

/-!
# Final-output isometry realization

The source-facing theorem retains the original final-output embedding equation.
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
      "finalAssemblyOutputEmbedding_adjoint_comp_self"

-- The retained final #388 output embedding is isometric.
set_option maxHeartbeats 900000 in
theorem finalAssemblyOutputEmbedding_adjoint_comp_self
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
    let Eout := M.finalAssemblyOutputEmbedding region bcomponent ccomponent WB WC UB UC
    (LinearMap.adjoint Eout).comp Eout =
      (1 : Semantics.Operator
        (Semantics.CompositeSystem
          (Semantics.CompositeSystem
            (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
            (isotypicLiftedMultiplicity.{0} nB))
          (Semantics.CompositeSystem (WC.restrictScalars Complex)
            (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
              (M.fourFactorD region))))) := by
  exact M.finalAssemblyOutputEmbedding_adjoint_comp_self_core
    region bcomponent ccomponent WB WC UB UC

end BPTCommutingProjectorModel
end Bounds
end QEC
