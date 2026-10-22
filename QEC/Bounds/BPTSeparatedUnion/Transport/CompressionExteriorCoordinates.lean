import QEC.Bounds.BPTSeparatedUnion.Transport.FourFactor
import QEC.Bounds.BPTDisentangling.Assembly.AssemblyHelpers

/-!
# Exterior-compression coordinate embeddings

Named core-coordinate embeddings keep the two transport cancellations from
re-elaborating the full final-assembly endpoint.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

/-- The four-factor active domain compressed by the final assembly embedding. -/
abbrev FinalAssemblyCompressionDomain
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (nB nC : Nat)
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region)) : Type :=
  Semantics.CompositeSystem
    (Semantics.CompositeSystem
      (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
      (isotypicLiftedMultiplicity.{0} nB))
    (Semantics.CompositeSystem (WC.restrictScalars Complex)
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
        (M.fourFactorD region)))

-- These coordinate declarations are too large to be useful as automated premises.
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.modifyEnv fun env =>
    let env := Lean.LibrarySuggestions.nameDenyListExt.addEntry env
      "finalAssemblyCompressionActiveEmbedding"
    let env := Lean.LibrarySuggestions.nameDenyListExt.addEntry env
      "finalAssemblyCompressionCoordinateEmbedding"
    let env := Lean.LibrarySuggestions.nameDenyListExt.addEntry env
      "finalAssemblyInputEmbedding_eq_compressionCoordinateEmbedding"
    Lean.LibrarySuggestions.nameDenyListExt.addEntry env
      "finalAssemblyOutputEmbedding_eq_compressionCoordinateEmbedding"

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
def finalAssemblyCompressionActiveEmbedding
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
        (isotypicLiftedMultiplicity.{0} nC))) :=
  (show
    M.FinalAssemblyCompressionDomain region nB nC WB WC →ₗ[Complex]
      (Semantics.CompositeSystem
        (M.regionSubsystem region).selectedSystem
        (M.regionSubsystem region).complementSystem) from
    TensorProduct.map
      (M.activeSelectedEmbeddingCore region bcomponent WB UB).toLinearMap
      (M.activeComplementEmbeddingCore region ccomponent WC UC).toLinearMap)

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
def finalAssemblyCompressionCoordinateEmbedding
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
        (isotypicLiftedMultiplicity.{0} nC))) :=
  (M.regionSubsystem region).registerFactorization.symm.toLinearEquiv.toLinearMap.comp
    (M.finalAssemblyCompressionActiveEmbedding region bcomponent ccomponent WB WC UB UC)

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem finalAssemblyInputEmbedding_eq_compressionCoordinateEmbedding
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
    M.finalAssemblyInputEmbedding region bcomponent ccomponent WB WC UB UC =
      (M.fourFactorTransport region).toLinearEquiv.toLinearMap.comp
        (M.finalAssemblyCompressionCoordinateEmbedding
          region bcomponent ccomponent WB WC UB UC) := by
  rfl

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem finalAssemblyOutputEmbedding_eq_compressionCoordinateEmbedding
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
    M.finalAssemblyOutputEmbedding region bcomponent ccomponent WB WC UB UC =
      (M.fourFactorTransport region).toLinearEquiv.toLinearMap.comp
        (M.finalAssemblyCompressionCoordinateEmbedding
          region bcomponent ccomponent WB WC UB UC) := by
  exact (M.finalAssemblyInputEmbedding_eq_outputEmbedding
    region bcomponent ccomponent WB WC UB UC).symm.trans
    (M.finalAssemblyInputEmbedding_eq_compressionCoordinateEmbedding
      region bcomponent ccomponent WB WC UB UC)

end BPTCommutingProjectorModel
end Bounds
end QEC
