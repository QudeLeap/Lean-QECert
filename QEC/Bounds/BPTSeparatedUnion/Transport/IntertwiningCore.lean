import QEC.Bounds.BPTSeparatedUnion.Transport.IntertwiningTransportCore

/-!
# Final-output exterior intertwining core

The canonical exterior witness supplies a complement action.  This module moves
that action through the active-coordinate embedding before transport restores
the final-output coordinates.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

-- This final-output coordinate calculation is too large to be an automated premise.
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.modifyEnv fun env =>
    Lean.LibrarySuggestions.nameDenyListExt.addEntry env
      "finalAssemblyOutputEmbedding_intertwines_exteriorLocal_at_witness"

set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem finalAssemblyOutputEmbedding_intertwines_exteriorLocal_at_witness
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
    (P : Semantics.Operator (M.regionSubsystem (M.exterior region)).selectedSystem) :
    M.FinalAssemblyOutputEmbeddingIntertwiningAt
      region bcomponent ccomponent WB WC UB UC P
        (M.exteriorCompressionWitness region P) := by
  unfold FinalAssemblyOutputEmbeddingIntertwiningAt
  dsimp only
  let S := M.regionSubsystem region
  let Q := M.exteriorCompressionComplementAction region P
  let J := M.finalAssemblyCompressionActiveEmbedding
    region bcomponent ccomponent WB WC UB UC
  let R := S.registerFactorization
  let F := M.fourFactorTransport region
  let E := M.finalAssemblyOutputEmbedding region bcomponent ccomponent WB WC UB UC
  let Daction := M.finalAssemblyCompressionActiveResult region nB nC WB WC
    (M.exteriorCompressionWitness region P)
  have hE : E = F.toLinearEquiv.toLinearMap.comp
      (R.symm.toLinearEquiv.toLinearMap.comp J) := by
    exact M.finalAssemblyOutputEmbedding_eq_compressionCoordinateEmbedding
      region bcomponent ccomponent WB WC UB UC
  have hRexternal : R.conjOperator
      ((M.regionSubsystem (M.exterior region)).extendLocalToRegister P) =
      TensorProduct.map (1 : Semantics.Operator S.selectedSystem) Q := by
    simpa only [S, R, Q] using M.exteriorCompressionWitness_spec region P
  have hJ : (TensorProduct.map (1 : Semantics.Operator S.selectedSystem) Q).comp J =
      J.comp Daction := by
    simpa only [S, Q, J, Daction] using
      M.finalAssemblyCompressionActiveEmbedding_intertwines_exteriorCompression
        region bcomponent ccomponent WB WC UB UC P
  exact intertwining_after_transportPair_of_eq F R J E
    ((M.regionSubsystem (M.exterior region)).extendLocalToRegister P)
    (TensorProduct.map (1 : Semantics.Operator S.selectedSystem) Q)
    Daction hE hRexternal hJ

end BPTCommutingProjectorModel
end Bounds
end QEC
