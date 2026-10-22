import QEC.Bounds.BPTSeparatedUnion.Assembly.Core
import QEC.Bounds.BPTSeparatedUnion.Separation

/-! # Final-assembly factorization on an actually separated right region -/

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
      "sourceFactorization_of_finalAssemblyWitness_on_actualSeparatedRight"

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 2000 in
theorem sourceFactorization_of_finalAssemblyWitness_on_actualSeparatedRight
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hseparated : M.ActualProjectorSeparated left right)
    (hdisjoint : Disjoint left right)
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal left))
      (M.fourFactorB left))
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC left))
      (M.fourFactorC left))
    {nB nC : Nat} [NeZero nB] [NeZero nC]
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal left))
      (M.fourFactorB left))
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC left))
      (M.fourFactorC left))
    (UB : Semantics.UnitaryTransport (bcomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WB.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nB)))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC)))
    (P_D : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
        (M.fourFactorD left)))
    (phi : Semantics.CompositeSystem (M.fourFactorA left) (WB.restrictScalars Complex))
    (n0 : isotypicLiftedMultiplicity.{0} nB)
    (c0 : WC.restrictScalars Complex)
    (U : Semantics.UnitaryTransport
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (WC.restrictScalars Complex))
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (WC.restrictScalars Complex)))
    (hphi : ‖phi‖ = 1) (hn0 : ‖n0‖ = 1) (hc0 : ‖c0‖ = 1)
    (htransport :
      let pB := bcomponent.1.restrictScalars Complex
      let pC := ccomponent.1.restrictScalars Complex
      let Uglobal := M.activeSectorBoundaryGlobalUnitary left pB pC UB UC U
      let Eout := M.finalAssemblyOutputEmbedding left bcomponent ccomponent WB WC UB UC
      let Pproduct : Semantics.Operator
          (Semantics.CompositeSystem
            (Semantics.CompositeSystem
              (Semantics.CompositeSystem (M.fourFactorA left) (WB.restrictScalars Complex))
              (isotypicLiftedMultiplicity.{0} nB))
            (Semantics.CompositeSystem (WC.restrictScalars Complex)
              (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
                (M.fourFactorD left)))) :=
        rankOneTensorOperator
          (phi ⊗ₜ[Complex] n0 : Semantics.CompositeSystem
            (Semantics.CompositeSystem (M.fourFactorA left) (WB.restrictScalars Complex))
            (isotypicLiftedMultiplicity.{0} nB))
          (rankOneTensorOperator c0 P_D)
      (M.fourFactorTransport left).conjOperator
          (Uglobal.conjOperator M.fullCodeProjector) =
        Eout.comp (Pproduct.comp (LinearMap.adjoint Eout))) :
    ∀ (A : Semantics.Operator (M.regionSubsystem left).selectedSystem)
      (B : Semantics.Operator (M.regionSubsystem right).selectedSystem),
      ∃ coefficient : Complex,
        M.fullCodeProjector * (M.regionSubsystem left).extendLocalToRegister A *
            (M.regionSubsystem right).extendLocalToRegister B * M.fullCodeProjector =
          coefficient •
            (M.fullCodeProjector * (M.regionSubsystem right).extendLocalToRegister B *
              M.fullCodeProjector) := by
  let pB := bcomponent.1.restrictScalars Complex
  let pC := ccomponent.1.restrictScalars Complex
  let Uglobal := M.activeSectorBoundaryGlobalUnitary left pB pC UB UC U
  have hRightExterior : right ⊆ M.exterior left :=
    M.subset_exterior_of_actualProjectorSeparated left right hseparated hdisjoint
  have hboundaryRight : Disjoint (M.boundary left) right :=
    M.boundary_disjoint_of_actualProjectorSeparated left right hseparated
  have hUsupported : M.UnitarySupportedOn (M.boundary left) Uglobal := by
    simpa [Uglobal, pB, pC] using
      (M.activeSectorBoundaryGlobalUnitary_supported left pB pC UB UC U)
  intro localLeft localRight
  let localRightGlobal := (M.regionSubsystem right).extendLocalToRegister localRight
  have hRightSupported :
      (M.regionSubsystem right).OperatorSupportedOnRegister localRightGlobal := by
    exact (M.regionSubsystem right).extendLocalToRegister_operatorSupportedOn localRight
  have hRightExteriorSupported :
      (M.regionSubsystem (M.exterior left)).OperatorSupportedOnRegister localRightGlobal := by
    apply operatorSupportedOnRegister_of_subset (M.regionSubsystem right)
      (M.regionSubsystem (M.exterior left))
    · simpa [BPTCommutingProjectorModel.regionSubsystem] using hRightExterior
    · exact hRightSupported
  rcases hRightExteriorSupported with ⟨exteriorRight, hexteriorRight⟩
  have hRightFixed : Uglobal.conjOperator localRightGlobal = localRightGlobal :=
    M.unitary_conjOperator_eq_of_disjoint_region_support
      (M.boundary left) right hboundaryRight Uglobal hUsupported hRightSupported
  have hExteriorRightFixed : Uglobal.conjOperator
      ((M.regionSubsystem (M.exterior left)).extendLocalToRegister exteriorRight) =
      (M.regionSubsystem (M.exterior left)).extendLocalToRegister exteriorRight := by
    rw [hexteriorRight]
    exact hRightFixed
  rcases M.sourceFactorization_of_finalAssemblyWitness left bcomponent ccomponent WB WC UB UC
      P_D phi n0 c0 U hphi hn0 hc0 htransport localLeft exteriorRight
      hExteriorRightFixed with ⟨localCoefficient, hlocalFactor⟩
  refine ⟨localCoefficient, ?_⟩
  rw [hexteriorRight] at hlocalFactor
  simpa [localRightGlobal] using hlocalFactor

end BPTCommutingProjectorModel
end Bounds
end QEC
