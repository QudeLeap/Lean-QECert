import QEC.Bounds.BPTDisentangling.Assembly.AssemblyTransportCore

/-!
# BPT final transport witness realization

This module turns fixed active-sector data into the final output-factorization
witness. Reusable coordinate transport lemmas live in
`FinalAssemblyTransportBasic`, while the witness interface lives in
`FinalAssemblyTransportCore`, so this expensive realization has its own build
artifact.
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
theorem finalAssemblyTransportWitness_of_fixedActiveData
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
    (Qsecond : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))
    (hfixed : M.FixedActiveDataProductRankOneTensor
      region bcomponent ccomponent WB WC UB UC P_D Qsecond) :
    FinalAssemblyTransportWitness M region bcomponent ccomponent WB WC UB UC P_D := by

  cases hfixed with
  | intro hcore _hCactive _hBactive hReconstruction =>
    cases hcore with
    | intro phi eta psi n0 c0 U hphi hP_D hP_D0 heta hPeta hpsi hn0 hc0 hU hJoint hproduct =>
      cases hReconstruction with
      | intro hReconstruct =>
          let pB := bcomponent.1.restrictScalars Complex
          let pC := ccomponent.1.restrictScalars Complex
          let Uglobal := M.activeSectorBoundaryGlobalUnitary region pB pC UB UC U
          let Pbase :=
            @rankOneTensorOperator
              (WC.restrictScalars Complex)
              (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
                (M.fourFactorD region))
              inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
              c0 P_D
          let F := M.fourFactorTransport region
          let J := fourFactorJointBCSectorEmbedding (A := M.fourFactorA region)
            (D := M.fourFactorD region) pB pC
          let Jright := jointBCSectorEmbeddingRight (A := M.fourFactorA region)
            (D := M.fourFactorD region) pB pC
          let P4 := F.conjOperator M.fullCodeProjector
          let Cblock := (LinearMap.adjoint J).comp (P4.comp J)
          let T := M.secondCutJointActiveBlockTransport region bcomponent ccomponent WB WC UB UC
          let R := productBlockRegrouping (A := M.fourFactorA region)
            (W := WB.restrictScalars Complex) (N := isotypicLiftedMultiplicity.{0} nB)
            (X := WC.restrictScalars Complex)
            (D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
              (M.fourFactorD region))
          let Apre := (tensorAssociatorUnitary
            (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
            (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
              (WC.restrictScalars Complex))
            (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
              (M.fourFactorD region))).symm
          let Wactive := jointBCSectorActiveUnitary (A := M.fourFactorA region)
            (D := M.fourFactorD region) pB pC
            (activeSectorJointBCUnitary pB pC UB UC U)
          let Vcommon := unitaryLTensor
            (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
            (unitaryRTensor U
              (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
                (M.fourFactorD region)))
          let V4 := fourFactorBCUnitaryTransport (A := M.fourFactorA region)
            (D := M.fourFactorD region) (activeSectorPhysicalUnitary pB pC UB UC U)
          let Qprime := M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond
          let Tpre := unitaryLTensor
            (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
            (tensorAssociatorUnitary (isotypicLiftedMultiplicity.{0} nB)
              (WC.restrictScalars Complex)
              (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
                (M.fourFactorD region))).symm
          let Pproduct : Semantics.Operator
              (Semantics.CompositeSystem
                (Semantics.CompositeSystem
                  (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
                  (isotypicLiftedMultiplicity.{0} nB))
                (Semantics.CompositeSystem (WC.restrictScalars Complex)
                  (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
                    (M.fourFactorD region)))) :=
            rankOneTensorOperator (phi ⊗ₜ[Complex] n0) Pbase
          have hReconstruct' : P4 = J.comp (Cblock.comp (LinearMap.adjoint J)) := by
            simpa [P4, J, Cblock, F] using hReconstruct
          have hCblock : Cblock = (LinearMap.adjoint Jright).comp
              ((M.secondCutCodeLift region).comp Jright) := by
            simpa [Cblock, J, Jright, P4, F] using
              (M.fourFactorJointBCSectorCompression_eq_secondCutCompression region pB pC)
          have hJoint' : T.conjOperator Cblock = Tpre.conjOperator
              (rankOneTensorOperator phi Qprime) := by
            calc
              T.conjOperator Cblock = T.conjOperator
                  ((LinearMap.adjoint Jright).comp ((M.secondCutCodeLift region).comp Jright)) :=
                congrArg T.conjOperator hCblock
              _ = Tpre.conjOperator
                  (rankOneTensorOperator phi Qprime) := by
                exact hJoint
          have hV4Intertwines : V4.toLinearEquiv.toLinearMap.comp J =
              J.comp Wactive.toLinearEquiv.toLinearMap := by
            simpa [V4, J, Wactive] using
              (fourFactorBCUnitaryTransport_activeSector_intertwines_jointBCSectorEmbedding
                (A := M.fourFactorA region) (D := M.fourFactorD region) pB pC UB UC U)
          have hV4Compression : V4.conjOperator P4 =
              J.comp ((Wactive.conjOperator Cblock).comp (LinearMap.adjoint J)) := by
            calc
              V4.conjOperator P4 = V4.conjOperator
                  (J.comp (Cblock.comp (LinearMap.adjoint J))) :=
                congrArg V4.conjOperator hReconstruct'
              _ = J.comp ((Wactive.conjOperator Cblock).comp (LinearMap.adjoint J)) :=
                unitaryTransport_conj_embedding_compression_of_intertwines
                  J V4 Wactive hV4Intertwines Cblock
          have hTConj :=
            M.secondCutJointActiveBlockTransport_intertwines_activeSectorUnitary
              region bcomponent ccomponent WB WC UB UC U
          have hActiveTransport : T.conjOperator (Wactive.conjOperator Cblock) =
              Vcommon.conjOperator (T.conjOperator Cblock) :=
            transport_conjOperator_conjOperator_of_conj_toLinearMap_eq
              T Wactive Vcommon hTConj Cblock
          have hVproduct :=
            M.finalActiveProductOperator_of_joint_product region WB WC U P_D Qprime
              (T.conjOperator Cblock) phi n0 c0 hJoint' hproduct
          have hRegroup : R.conjOperator
              (Apre.conjOperator
                (M.finalActiveProductOperator region WB WC phi n0 c0 P_D)) =
              Pproduct := by
            have hAssoc : Apre.conjOperator
                (M.finalActiveProductOperator region WB WC phi n0 c0 P_D) =
                TensorProduct.map
                  (TensorProduct.map
                    (InnerProductSpace.rankOne Complex phi phi).toLinearMap
                    (InnerProductSpace.rankOne Complex
                      (n0 ⊗ₜ[Complex] c0 : Semantics.CompositeSystem
                        (isotypicLiftedMultiplicity.{0} nB) (WC.restrictScalars Complex))
                      (n0 ⊗ₜ[Complex] c0 : Semantics.CompositeSystem
                        (isotypicLiftedMultiplicity.{0} nB)
                        (WC.restrictScalars Complex))).toLinearMap)
                  P_D := by
              dsimp only [Apre, finalActiveProductOperator]
              exact tensorAssociatorUnitary_symm_conj_tensorMap
                (H := Semantics.CompositeSystem
                  (M.fourFactorA region) (WB.restrictScalars Complex))
                (K := Semantics.CompositeSystem
                  (isotypicLiftedMultiplicity.{0} nB) (WC.restrictScalars Complex))
                (J := Semantics.CompositeSystem
                  (isotypicLiftedMultiplicity.{0} nC) (M.fourFactorD region))
                (InnerProductSpace.rankOne Complex phi phi).toLinearMap
                (InnerProductSpace.rankOne Complex
                  (n0 ⊗ₜ[Complex] c0 : Semantics.CompositeSystem
                    (isotypicLiftedMultiplicity.{0} nB) (WC.restrictScalars Complex))
                  (n0 ⊗ₜ[Complex] c0 : Semantics.CompositeSystem
                    (isotypicLiftedMultiplicity.{0} nB)
                    (WC.restrictScalars Complex))).toLinearMap
                P_D
            calc
              R.conjOperator
                  (Apre.conjOperator
                    (M.finalActiveProductOperator region WB WC phi n0 c0 P_D)) =
                  R.conjOperator
                    (TensorProduct.map
                      (TensorProduct.map
                        (InnerProductSpace.rankOne Complex phi phi).toLinearMap
                        (InnerProductSpace.rankOne Complex
                          (n0 ⊗ₜ[Complex] c0 : Semantics.CompositeSystem
                            (isotypicLiftedMultiplicity.{0} nB)
                            (WC.restrictScalars Complex))
                          (n0 ⊗ₜ[Complex] c0 : Semantics.CompositeSystem
                            (isotypicLiftedMultiplicity.{0} nB)
                            (WC.restrictScalars Complex))).toLinearMap)
                      P_D) := congrArg R.conjOperator hAssoc
              _ = Pproduct := by
                simpa only [R, Pproduct, Pbase, rankOneTensorOperator] using
                  (conjOperator_productBlockRegrouping phi n0 c0 P_D)
          have hBeforeRegroup : M.finalActiveProductOperator region WB WC phi n0 c0 P_D =
              Apre.symm.conjOperator (R.symm.conjOperator Pproduct) := by
            have hRegroupBack : Apre.conjOperator
                (M.finalActiveProductOperator region WB WC phi n0 c0 P_D) =
                R.symm.conjOperator Pproduct := by
              calc
                Apre.conjOperator
                    (M.finalActiveProductOperator region WB WC phi n0 c0 P_D) =
                    R.symm.conjOperator (R.conjOperator (Apre.conjOperator
                      (M.finalActiveProductOperator region WB WC phi n0 c0 P_D))) :=
                  (R.symm_conjOperator_conjOperator _).symm
                _ = R.symm.conjOperator Pproduct :=
                  congrArg R.symm.conjOperator hRegroup
            calc
              M.finalActiveProductOperator region WB WC phi n0 c0 P_D =
                  Apre.symm.conjOperator (Apre.conjOperator
                    (M.finalActiveProductOperator region WB WC phi n0 c0 P_D)) :=
                (Apre.symm_conjOperator_conjOperator _).symm
              _ = Apre.symm.conjOperator (R.symm.conjOperator Pproduct) :=
                congrArg Apre.symm.conjOperator hRegroupBack
          have hActiveProduct : Wactive.conjOperator Cblock =
              T.symm.conjOperator
                (Apre.symm.conjOperator (R.symm.conjOperator Pproduct)) := by
            exact conjOperator_eq_symm_conjOperator_of_transport
              T Wactive Vcommon Cblock
              (M.finalActiveProductOperator region WB WC phi n0 c0 P_D)
              (Apre.symm.conjOperator (R.symm.conjOperator Pproduct))
              hActiveTransport hVproduct hBeforeRegroup
          let Eout := M.finalAssemblyOutputEmbedding
            region bcomponent ccomponent WB WC UB UC
          have hOutputLift : J.comp
              ((T.symm.conjOperator
                (Apre.symm.conjOperator (R.symm.conjOperator Pproduct))).comp
                (LinearMap.adjoint J)) =
              Eout.comp (Pproduct.comp (LinearMap.adjoint Eout)) := by
            exact
              (embedding_comp_three_conjOperators R.symm Apre.symm T.symm J Pproduct)
          have hPhysicalTransport : F.conjOperator
              (Uglobal.conjOperator M.fullCodeProjector) = V4.conjOperator P4 := by
            simpa [F, Uglobal, V4, P4] using
              (M.fourFactorTransport_conj_activeSectorBoundaryGlobalUnitary_conj_fullCodeProjector
                region pB pC UB UC U)
          refine ⟨phi, n0, c0, U, hphi, hn0, hc0, hP_D, ?_⟩
          exact
            calc
              F.conjOperator (Uglobal.conjOperator M.fullCodeProjector) = V4.conjOperator P4 :=
                hPhysicalTransport
              _ = J.comp ((Wactive.conjOperator Cblock).comp (LinearMap.adjoint J)) :=
                hV4Compression
              _ = J.comp
                  ((T.symm.conjOperator
                    (Apre.symm.conjOperator (R.symm.conjOperator Pproduct))).comp
                    (LinearMap.adjoint J)) :=
                congrArg (fun X => J.comp (X.comp (LinearMap.adjoint J))) hActiveProduct
              _ = Eout.comp (Pproduct.comp (LinearMap.adjoint Eout)) := hOutputLift

end BPTCommutingProjectorModel

end Bounds
end QEC
