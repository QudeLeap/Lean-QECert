import QEC.Bounds.BPTDisentangling.Assembly.AssemblyHelpers

/-!
# BPT final factorization assembly

The expensive conversion from the final four-factor operator factorization to
the physical `Disentangled` witness lives in its own build artifact.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 800000 in
/--
An exact final output factorization yields the physical disentangling witness.
This is the cached terminal assembly step of the BPT proof.
-/
theorem disentangled_of_finalAssemblyFactorization
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
    (hP_D : P_D.IsSymmetricProjection)
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
    M.Disentangled region := by
  let pB := bcomponent.1.restrictScalars Complex
  let pC := ccomponent.1.restrictScalars Complex
  let eSel := M.activeSelectedEmbedding region bcomponent WB UB
  let eComp := M.activeComplementEmbedding region ccomponent WC UC
  let phiRegion := eSel (phi ⊗ₜ[Complex] n0)
  let Pbase :=
    @rankOneTensorOperator
      (WC.restrictScalars Complex)
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
        (M.fourFactorD region))
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      c0 P_D
  let complementProjector : Semantics.Operator
      (M.regionSubsystem region).complementSystem :=
    M.activeComplementProjector region ccomponent WC UC Pbase
  let Uglobal := M.activeSectorBoundaryGlobalUnitary region pB pC UB UC U
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
      Pbase
  let F := M.fourFactorTransport region
  let Eout := M.finalAssemblyOutputEmbedding
    region bcomponent ccomponent WB WC UB UC
  let Eleft := M.finalAssemblyInputEmbedding
    region bcomponent ccomponent WB WC UB UC
  have hphiRegion : ‖phiRegion‖ = 1 := by
    dsimp [phiRegion]
    rw [eSel.norm_map, TensorProduct.norm_tmul]
    simp [hphi, hn0]
  have hPbase := @rankOneTensorOperator_isSymmetricProjection
    (WC.restrictScalars Complex)
    (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
      (M.fourFactorD region))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    c0 hc0 P_D hP_D
  have heSel : (LinearMap.adjoint eSel.toLinearMap).comp eSel.toLinearMap =
      (1 : Semantics.Operator
        (Semantics.CompositeSystem
          (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
          (isotypicLiftedMultiplicity.{0} nB))) := by
    exact @linearIsometry_adjoint_comp_self
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
        (isotypicLiftedMultiplicity.{0} nB))
      (M.regionSubsystem region).selectedSystem
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      eSel
  have hComplementProjector :=
    M.activeComplementProjector_isSymmetricProjection
      region ccomponent WC UC Pbase hPbase
  have hTensorLift : TensorProduct.map
      (InnerProductSpace.rankOne Complex phiRegion phiRegion).toLinearMap
      complementProjector =
        (TensorProduct.map eSel.toLinearMap eComp.toLinearMap).comp
          (Pproduct.comp
            (LinearMap.adjoint (TensorProduct.map eSel.toLinearMap eComp.toLinearMap))) := by
    have hLift := tensorMap_rankOne_isometric_lift
      eSel.toLinearMap heSel eComp.toLinearMap (phi ⊗ₜ[Complex] n0) Pbase
    simpa only [phiRegion, complementProjector, activeComplementProjector,
      Pproduct, rankOneTensorOperator, eComp, LinearIsometry.coe_toLinearMap] using hLift
  have hCoordinates : Eleft = Eout := by
    simpa only [Eleft, Eout] using
      (M.finalAssemblyInputEmbedding_eq_outputEmbedding
        region bcomponent ccomponent WB WC UB UC)
  have hTargetLift : F.conjOperator
      (M.pureFactorTensorComplementProjector region phiRegion complementProjector) =
      Eleft.comp (Pproduct.comp (LinearMap.adjoint Eleft)) := by
    exact two_unitary_conj_isometric_lift_of_factorization
      (M.regionSubsystem region).registerFactorization.symm
      (M.fourFactorTransport region)
      (TensorProduct.map eSel.toLinearMap eComp.toLinearMap) Pproduct
      (TensorProduct.map
        (InnerProductSpace.rankOne Complex phiRegion phiRegion).toLinearMap
        complementProjector)
      (M.finalAssemblyInputEmbedding region bcomponent ccomponent WB WC UB UC)
      hTensorLift
      (M.finalAssemblyInputEmbedding_eq_twoTransport
        region bcomponent ccomponent WB WC UB UC)
  have hOutputFactorization : F.conjOperator
      (Uglobal.conjOperator M.fullCodeProjector) =
      Eout.comp (Pproduct.comp (LinearMap.adjoint Eout)) := by
    simpa only [pB, pC, Uglobal, Eout, Pproduct, Pbase, F] using htransport
  refine ⟨Uglobal, phiRegion, complementProjector,
    M.activeSectorBoundaryGlobalUnitary_supported region pB pC UB UC U,
    hphiRegion, hComplementProjector, ?_⟩
  exact eq_of_common_isometric_factorization_under_unitary
    F (Uglobal.conjOperator M.fullCodeProjector)
    (M.pureFactorTensorComplementProjector region phiRegion complementProjector)
    Pproduct Eout Eleft hOutputFactorization hCoordinates hTargetLift

end BPTCommutingProjectorModel

end Bounds
end QEC
