import QEC.Bounds.BPTSeparatedUnion.Transport.IsometryActive

/-!
# Coordinate-transport isometry

The register factorization transport preserves the active-coordinate isometry.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

private theorem coordinateEmbedding_unitary_gram
    {S H K : Type u}
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport H K) (J : S →ₗ[Complex] H) :
    (LinearMap.adjoint (U.toLinearEquiv.toLinearMap.comp J)).comp
        (U.toLinearEquiv.toLinearMap.comp J) = (LinearMap.adjoint J).comp J := by
  have h := compression_conjOperator_comp_unitary U J (1 : Semantics.Operator H)
  rw [U.conjOperator_one] at h
  simpa only [Module.End.one_eq_id, LinearMap.id_comp] using h

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.modifyEnv fun env =>
    Lean.LibrarySuggestions.nameDenyListExt.addEntry env
      "finalAssemblyCompressionCoordinateEmbedding_adjoint_comp_self"

set_option maxHeartbeats 900000 in
set_option synthInstance.maxHeartbeats 180000 in
theorem finalAssemblyCompressionCoordinateEmbedding_adjoint_comp_self
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
    let J := M.finalAssemblyCompressionCoordinateEmbedding
      region bcomponent ccomponent WB WC UB UC
    (LinearMap.adjoint J).comp J =
      (1 : Semantics.Operator (M.FinalAssemblyCompressionDomain region nB nC WB WC)) := by
  dsimp only [finalAssemblyCompressionCoordinateEmbedding]
  calc
    (LinearMap.adjoint
        ((M.regionSubsystem region).registerFactorization.symm.toLinearEquiv.toLinearMap.comp
          (M.finalAssemblyCompressionActiveEmbedding region bcomponent ccomponent WB WC UB UC))).comp
        ((M.regionSubsystem region).registerFactorization.symm.toLinearEquiv.toLinearMap.comp
          (M.finalAssemblyCompressionActiveEmbedding region bcomponent ccomponent WB WC UB UC)) =
      (LinearMap.adjoint
        (M.finalAssemblyCompressionActiveEmbedding region bcomponent ccomponent WB WC UB UC)).comp
        (M.finalAssemblyCompressionActiveEmbedding region bcomponent ccomponent WB WC UB UC) := by
          exact coordinateEmbedding_unitary_gram
            (M.regionSubsystem region).registerFactorization.symm
            (M.finalAssemblyCompressionActiveEmbedding region bcomponent ccomponent WB WC UB UC)
    _ = _ := M.finalAssemblyCompressionActiveEmbedding_adjoint_comp_self
      region bcomponent ccomponent WB WC UB UC

end BPTCommutingProjectorModel
end Bounds
end QEC
