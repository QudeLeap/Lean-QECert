import QEC.Bounds.BPTSeparatedUnion.Assembly.RightIntertwining

/-! # Final-assembly projector in reassociated rank-one coordinates -/

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
      "finalAssemblyReassociatedProjector_eq"

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000 in
theorem finalAssemblyReassociatedProjector_eq
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
    (P_D : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
        (M.fourFactorD region)))
    (phi : Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
    (n0 : isotypicLiftedMultiplicity.{0} nB)
    (c0 : WC.restrictScalars Complex)
    (U : Semantics.UnitaryTransport
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (WC.restrictScalars Complex))
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (WC.restrictScalars Complex)))
    (htransport :
      let pB := bcomponent.1.restrictScalars Complex
      let pC := ccomponent.1.restrictScalars Complex
      let Uglobal := M.activeSectorBoundaryGlobalUnitary region pB pC UB UC U
      let Eout := M.finalAssemblyOutputEmbedding region bcomponent ccomponent WB WC UB UC
      let Pproduct : Semantics.Operator
          (Semantics.CompositeSystem
            (Semantics.CompositeSystem
              (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
              (isotypicLiftedMultiplicity.{0} nB))
            (Semantics.CompositeSystem (WC.restrictScalars Complex)
              (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
                (M.fourFactorD region)))) :=
        rankOneTensorOperator
          (phi ⊗ₜ[Complex] n0 : Semantics.CompositeSystem
            (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
            (isotypicLiftedMultiplicity.{0} nB))
          (rankOneTensorOperator c0 P_D)
      (M.fourFactorTransport region).conjOperator
          (Uglobal.conjOperator M.fullCodeProjector) =
        Eout.comp (Pproduct.comp (LinearMap.adjoint Eout))) :
    let pB := bcomponent.1.restrictScalars Complex
    let pC := ccomponent.1.restrictScalars Complex
    let Uglobal := M.activeSectorBoundaryGlobalUnitary region pB pC UB UC U
    let F := M.fourFactorTransport region
    let S := Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex)
    let N := isotypicLiftedMultiplicity.{0} nB
    let X := WC.restrictScalars Complex
    let D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
      (M.fourFactorD region)
    let E := M.finalAssemblyOutputEmbedding region bcomponent ccomponent WB WC UB UC
    let O := tensorAssociatorUnitary (Semantics.CompositeSystem S N) X D
    let Enew := E.comp O.toLinearEquiv.toLinearMap
    let psi : Semantics.CompositeSystem (Semantics.CompositeSystem S N) X :=
      (phi ⊗ₜ[Complex] n0) ⊗ₜ[Complex] c0
    Enew.comp ((rankOneTensorOperator psi P_D).comp (LinearMap.adjoint Enew)) =
      F.conjOperator (Uglobal.conjOperator M.fullCodeProjector) := by
  dsimp only
  let pB := bcomponent.1.restrictScalars Complex
  let pC := ccomponent.1.restrictScalars Complex
  let Uglobal := M.activeSectorBoundaryGlobalUnitary region pB pC UB UC U
  let F := M.fourFactorTransport region
  let S := Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex)
  let N := isotypicLiftedMultiplicity.{0} nB
  let X := WC.restrictScalars Complex
  let D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
    (M.fourFactorD region)
  let E := M.finalAssemblyOutputEmbedding region bcomponent ccomponent WB WC UB UC
  let O := tensorAssociatorUnitary (Semantics.CompositeSystem S N) X D
  let Enew := E.comp O.toLinearEquiv.toLinearMap
  let phiN : Semantics.CompositeSystem S N := phi ⊗ₜ[Complex] n0
  let psi : Semantics.CompositeSystem (Semantics.CompositeSystem S N) X :=
    phiN ⊗ₜ[Complex] c0
  have hLift : Enew.comp
      ((rankOneTensorOperator psi P_D).comp (LinearMap.adjoint Enew)) =
      E.comp
        ((rankOneTensorOperator phiN (rankOneTensorOperator c0 P_D)).comp
          (LinearMap.adjoint E)) := by
    exact reassociated_rankOne_isometric_lift E phiN c0 P_D
  have hOutput : F.conjOperator (Uglobal.conjOperator M.fullCodeProjector) =
      E.comp
        ((rankOneTensorOperator phiN (rankOneTensorOperator c0 P_D)).comp
          (LinearMap.adjoint E)) := by
    change F.conjOperator (Uglobal.conjOperator M.fullCodeProjector) =
      E.comp
        ((rankOneTensorOperator phiN (rankOneTensorOperator c0 P_D)).comp
          (LinearMap.adjoint E)) at htransport
    exact htransport
  exact hLift.trans hOutput.symm

end BPTCommutingProjectorModel
end Bounds
end QEC
