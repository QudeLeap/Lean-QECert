import QEC.Bounds.BPTSeparatedUnion.Transport.CompressionExteriorWitness
import QEC.Bounds.BPTSeparatedUnion.Transport.CompressionExteriorCoordinates

/-!
# Final-output exterior intertwining statement

The exact final-output range invariance is named before its coordinate proof is
assembled.  The public realization keeps the original theorem statement.
-/

noncomputable section

namespace QEC
namespace Bounds

open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

set_option maxHeartbeats 500000 in
set_option synthInstance.maxHeartbeats 120000 in
def FinalAssemblyOutputEmbeddingIntertwiningAt
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
    (P : Semantics.Operator (M.regionSubsystem (M.exterior region)).selectedSystem)
    (Z : Semantics.Operator (M.fourFactorD region)) : Prop :=
  let Eout := M.finalAssemblyOutputEmbedding region bcomponent ccomponent WB WC UB UC
  let Daction : Semantics.Operator
      (M.FinalAssemblyCompressionDomain region nB nC WB WC) :=
    TensorProduct.map
      (1 : Semantics.Operator
        (Semantics.CompositeSystem
          (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
          (isotypicLiftedMultiplicity.{0} nB)))
      (TensorProduct.map (1 : Semantics.Operator (WC.restrictScalars Complex))
        (TensorProduct.map
          (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} nC)) Z))
  ((M.fourFactorTransport region).conjOperator
      ((M.regionSubsystem (M.exterior region)).extendLocalToRegister P)).comp Eout =
    Eout.comp Daction

set_option maxHeartbeats 350000 in
def FinalAssemblyOutputEmbeddingIntertwining
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
    (P : Semantics.Operator (M.regionSubsystem (M.exterior region)).selectedSystem) : Prop :=
  ∃ Z : Semantics.Operator (M.fourFactorD region),
    M.FinalAssemblyOutputEmbeddingIntertwiningAt
      region bcomponent ccomponent WB WC UB UC P Z

end BPTCommutingProjectorModel
end Bounds
end QEC
