import QEC.Bounds.BPTSeparatedUnion.Assembly.ProjectorLift
import QEC.Bounds.BPTDisentangling.SeparatedUnionBridge
import QEC.Bounds.BPTSeparatedUnion.Transport.CompressionExteriorWitness

/-! # Source-coordinate factorization for the final-assembly witness -/

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
      "finalAssemblySourceFactorization"

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 2000 in
theorem finalAssemblySourceFactorization
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
    (hphi : ‖phi‖ = 1) (hn0 : ‖n0‖ = 1) (hc0 : ‖c0‖ = 1)
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
        Eout.comp (Pproduct.comp (LinearMap.adjoint Eout)))
    (A : Semantics.Operator (M.regionSubsystem region).selectedSystem)
    (B : Semantics.Operator (M.regionSubsystem (M.exterior region)).selectedSystem) :
    let pB := bcomponent.1.restrictScalars Complex
    let pC := ccomponent.1.restrictScalars Complex
    let Uglobal := M.activeSectorBoundaryGlobalUnitary region pB pC UB UC U
    let F := M.fourFactorTransport region
    let S := Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex)
    let N := isotypicLiftedMultiplicity.{0} nB
    let X := WC.restrictScalars Complex
    let leftUnitary := conjugateUnitaryTransport
      (tensorAssociatorUnitary S N X) (unitaryLTensor S U)
    let eSel := (M.activeSelectedEmbedding region bcomponent WB UB).toLinearMap
    let A0 : Semantics.Operator (Semantics.CompositeSystem S N) :=
      (LinearMap.adjoint eSel).comp (A.comp eSel)
    let leftLocal : Semantics.Operator
        (Semantics.CompositeSystem (Semantics.CompositeSystem S N) X) :=
      leftUnitary.conjOperator (TensorProduct.map A0 (1 : Semantics.Operator X))
    let psi : Semantics.CompositeSystem (Semantics.CompositeSystem S N) X :=
      (phi ⊗ₜ[Complex] n0) ⊗ₜ[Complex] c0
    SourceFactorization
      (F.conjOperator (Uglobal.conjOperator M.fullCodeProjector))
      (F.conjOperator
        (Uglobal.conjOperator ((M.regionSubsystem region).extendLocalToRegister A)))
      (F.conjOperator ((M.regionSubsystem (M.exterior region)).extendLocalToRegister B))
      (inner Complex psi (leftLocal psi)) := by
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
  let leftUnitary := conjugateUnitaryTransport
    (tensorAssociatorUnitary S N X) (unitaryLTensor S U)
  let eSel := (M.activeSelectedEmbedding region bcomponent WB UB).toLinearMap
  let A0 : Semantics.Operator (Semantics.CompositeSystem S N) :=
    (LinearMap.adjoint eSel).comp (A.comp eSel)
  let leftLocal : Semantics.Operator
      (Semantics.CompositeSystem (Semantics.CompositeSystem S N) X) :=
    leftUnitary.conjOperator (TensorProduct.map A0 (1 : Semantics.Operator X))
  let rightLocal : Semantics.Operator D :=
    TensorProduct.map (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} nC))
      (M.exteriorCompressionWitness region B)
  let psi : Semantics.CompositeSystem (Semantics.CompositeSystem S N) X :=
    (phi ⊗ₜ[Complex] n0) ⊗ₜ[Complex] c0
  let projector : Semantics.Operator (M.fourFactorSystem region) :=
    F.conjOperator (Uglobal.conjOperator M.fullCodeProjector)
  let leftAmbient : Semantics.Operator (M.fourFactorSystem region) :=
    F.conjOperator
      (Uglobal.conjOperator ((M.regionSubsystem region).extendLocalToRegister A))
  let rightAmbient : Semantics.Operator (M.fourFactorSystem region) :=
    F.conjOperator ((M.regionSubsystem (M.exterior region)).extendLocalToRegister B)
  let liftedProjector : Semantics.Operator (M.fourFactorSystem region) :=
    Enew.comp ((rankOneTensorOperator psi P_D).comp (LinearMap.adjoint Enew))
  let coefficient := inner Complex psi (leftLocal psi)
  have hpsi : ‖psi‖ = 1 := by
    rw [TensorProduct.norm_tmul, TensorProduct.norm_tmul]
    simp [hphi, hn0, hc0]
  have hProjector : liftedProjector = projector := by
    apply M.finalAssemblyReassociatedProjector_eq
    exact htransport
  have hRaw : SourceFactorization liftedProjector leftAmbient rightAmbient coefficient := by
    change liftedProjector * leftAmbient * rightAmbient * liftedProjector =
      coefficient • (liftedProjector * rightAmbient * liftedProjector)
    apply sourceFactorization_of_rankOneLift Enew psi hpsi P_D
    · exact M.finalAssemblyReassociatedEmbedding_adjoint_comp_self
        region bcomponent ccomponent WB WC UB UC
    · exact M.finalAssembly_leftCompression_after_boundaryUnitary
        region bcomponent ccomponent WB WC UB UC U A
    · exact M.finalAssemblyReassociatedEmbedding_intertwines_exteriorLocal
        region bcomponent ccomponent WB WC UB UC B
  exact source_factorization_projector_congr
    liftedProjector projector leftAmbient rightAmbient coefficient hProjector hRaw

end BPTCommutingProjectorModel
end Bounds
end QEC
