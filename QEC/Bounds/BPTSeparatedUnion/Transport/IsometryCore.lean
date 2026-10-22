import QEC.Bounds.BPTSeparatedUnion.Transport.IsometryCoordinates

/-!
# Final-output isometry core

The final-output embedding is a composition of two unitary transports and the
tensor product of the active selected and complement embeddings.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

private theorem adjoint_unitary_comp_comp_self
    {S H K : Type u}
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport H K) (J : S →ₗ[Complex] H) :
    (LinearMap.adjoint (U.toLinearEquiv.toLinearMap.comp J)).comp
        (U.toLinearEquiv.toLinearMap.comp J) =
      (LinearMap.adjoint J).comp J := by
  rw [LinearMap.adjoint_comp, U.adjoint_toLinearMap]
  ext x
  simp only [LinearMap.comp_apply]
  congr 1
  exact U.toLinearEquiv.symm_apply_apply (J x)

-- This dependent tensor-isometry calculation is too large to be an automated premise.
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.modifyEnv fun env =>
    Lean.LibrarySuggestions.nameDenyListExt.addEntry env
      "finalAssemblyOutputEmbedding_adjoint_comp_self_core"

set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem finalAssemblyOutputEmbedding_adjoint_comp_self_core
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
    M.FinalAssemblyOutputEmbeddingIsometry region bcomponent ccomponent WB WC UB UC := by
  unfold FinalAssemblyOutputEmbeddingIsometry
  dsimp only
  let F := M.fourFactorTransport region
  let J := M.finalAssemblyCompressionCoordinateEmbedding
    region bcomponent ccomponent WB WC UB UC
  have hF' :
      (LinearMap.adjoint (F.toLinearEquiv.toLinearMap.comp J)).comp
          (F.toLinearEquiv.toLinearMap.comp J) =
        (LinearMap.adjoint J).comp J :=
    adjoint_unitary_comp_comp_self F J
  have hOutput := M.finalAssemblyOutputEmbedding_eq_compressionCoordinateEmbedding
    region bcomponent ccomponent WB WC UB UC
  have hRewrite := congrArg
    (α := M.FinalAssemblyCompressionDomain region nB nC WB WC →ₗ[Complex]
      M.fourFactorSystem region)
    (β := Semantics.Operator (M.FinalAssemblyCompressionDomain region nB nC WB WC))
    (a₁ := M.finalAssemblyOutputEmbedding region bcomponent ccomponent WB WC UB UC)
    (a₂ := F.toLinearEquiv.toLinearMap.comp J)
    (fun E : M.FinalAssemblyCompressionDomain region nB nC WB WC →ₗ[Complex]
        M.fourFactorSystem region =>
      show Semantics.Operator (M.FinalAssemblyCompressionDomain region nB nC WB WC) from
        (LinearMap.adjoint E : M.fourFactorSystem region →ₗ[Complex]
          M.FinalAssemblyCompressionDomain region nB nC WB WC).comp E)
    hOutput
  exact hRewrite.trans (hF'.trans
    (M.finalAssemblyCompressionCoordinateEmbedding_adjoint_comp_self
      region bcomponent ccomponent WB WC UB UC))

end BPTCommutingProjectorModel
end Bounds
end QEC
