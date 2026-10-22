import QEC.Bounds.BPTSeparatedUnion.Transport.ExteriorAction
import QEC.Bounds.BPTSeparatedUnion.Transport.CompressionExteriorCoordinates

/-!
# Exterior-compression active statement

The active-coordinate existential is named independently from its realization
so the large dependent equality is compiled only once.
-/

noncomputable section

namespace QEC
namespace Bounds

open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- The four-factor operator produced after compressing the exterior action. -/
noncomputable def finalAssemblyCompressionActiveResult
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (nB nC : Nat)
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (Z : Semantics.Operator (M.fourFactorD region)) :
    Semantics.Operator (M.FinalAssemblyCompressionDomain region nB nC WB WC) :=
  TensorProduct.map (1 : Semantics.Operator
    (Semantics.CompositeSystem
      (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
      (isotypicLiftedMultiplicity.{0} nB)))
    (TensorProduct.map (1 : Semantics.Operator (WC.restrictScalars Complex))
      (TensorProduct.map
        (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} nC)) Z))

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.modifyEnv fun env =>
    Lean.LibrarySuggestions.nameDenyListExt.addEntry env
      "finalAssemblyCompressionActiveResult_eq_tensorMap"

set_option maxHeartbeats 800000 in
theorem finalAssemblyCompressionActiveResult_eq_tensorMap
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (nB nC : Nat)
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (Z : Semantics.Operator (M.fourFactorD region)) :
    M.finalAssemblyCompressionActiveResult region nB nC WB WC Z =
      (show Semantics.Operator (M.FinalAssemblyCompressionDomain region nB nC WB WC) from
        TensorProduct.map (1 : Semantics.Operator
          (Semantics.CompositeSystem
            (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
            (isotypicLiftedMultiplicity.{0} nB)))
          (TensorProduct.map (1 : Semantics.Operator (WC.restrictScalars Complex))
            (TensorProduct.map
              (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} nC)) Z))) := by
  rfl

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
def FinalAssemblyCompressionActiveAt
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
  let J := M.finalAssemblyCompressionActiveEmbedding
    region bcomponent ccomponent WB WC UB UC
  (LinearMap.adjoint J).comp
      ((((M.regionSubsystem region).registerFactorization.conjOperator
        ((M.regionSubsystem (M.exterior region)).extendLocalToRegister P)).comp
        J)) =
      M.finalAssemblyCompressionActiveResult region nB nC WB WC Z

set_option maxHeartbeats 300000 in
def FinalAssemblyCompressionActiveStatement
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
    M.FinalAssemblyCompressionActiveAt
      region bcomponent ccomponent WB WC UB UC P Z

end BPTCommutingProjectorModel
end Bounds
end QEC
