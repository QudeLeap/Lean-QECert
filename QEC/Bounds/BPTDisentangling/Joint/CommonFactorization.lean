import QEC.Bounds.BPTDisentangling.Joint.Sequential.Blocks
import QEC.Bounds.BPTDisentangling.Joint.Sequential.Factorization
import QEC.Bounds.BPTDisentangling.Joint.CommonFactorizationData
import QEC.Bounds.BPTDisentangling.Joint.CommonFactorizationNonzeroData

/-!
# BPT common active-block factorization

Internal proof layer for the finite-dimensional BPT Disentangling Lemma.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

-- Internal cache bridges are intentionally excluded from automated premise indexing.
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.modifyEnv fun env =>
    let env := Lean.LibrarySuggestions.nameDenyListExt.addEntry env
      "exists_actual_commonFactorization_and_jointSecondCutBlock_of_fixed_active_data"
    Lean.LibrarySuggestions.nameDenyListExt.addEntry env
      "exists_actual_commonFactorization_of_nonzero_code"

set_option maxHeartbeats 1400000 in
/--
For fixed BPT sector data, the common-factor equation and the actual
simultaneous-sector second-cut block use one and the same normalized `phi`.
This is the witness-preserving coordinate-data node for D5; it does not merge
independent existential sector choices.
-/
theorem exists_actual_commonFactorization_and_jointSecondCutBlock_of_fixed_active_data
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥) (hM : M.RegionErasureRecoverable region)
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
    (Pfirst : Semantics.Operator
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
        (WC.restrictScalars Complex)))
    (P_D : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
        (M.fourFactorD region)))
    (Pleft : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex)))
    (Qsecond : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))) )
    (hBactive : M.secondCutCodeLift region * M.secondCutSectorLift region bcomponent =
      M.secondCutCodeLift region)
    (hCleft :
      (unitaryLTensor
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)) UC).conjOperator
          (overlapProjectorOnIsotypicComponent (M.firstCutProjectorMC region) ccomponent) =
        rightTensorExtensionAfterLeft
          (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
          (WC.restrictScalars Complex) (isotypicLiftedMultiplicity.{0} nC) Pfirst)
    (hCright :
      (unitaryRTensor UC (M.fourFactorD region)).conjOperator
          (overlapRightProjectorOnIsotypicComponent
            (M.firstCutProjectorMC region) (M.fourFactorProjectorCDLocal region) ccomponent) =
        leftTensorExtensionBeforeRight (WC.restrictScalars Complex)
          (isotypicLiftedMultiplicity.{0} nC) (M.fourFactorD region) P_D)
    (hBleft :
      (unitaryLTensor (M.fourFactorA region) UB).conjOperator
          (overlapProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) bcomponent) =
        rightTensorExtensionAfterLeft (M.fourFactorA region)
          (WB.restrictScalars Complex) (isotypicLiftedMultiplicity.{0} nB) Pleft)
    (hBright :
      (unitaryRTensor UB
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))).conjOperator
          (overlapRightProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) (M.secondCutProjectorBbarM region)
            bcomponent) =
        leftTensorExtensionBeforeRight (WB.restrictScalars Complex)
          (isotypicLiftedMultiplicity.{0} nB)
          (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) Qsecond) :
    ActualCommonFactorizationAndJointSecondCutBlock M region bcomponent ccomponent
      WB WC UB UC Pfirst P_D Qsecond := by
  unfold ActualCommonFactorizationAndJointSecondCutBlock
  have hjointResult := M.secondCut_actual_joint_active_block_of_region_recoverable
    region hcode hM bcomponent ccomponent WB WC UB UC Pleft Qsecond hBactive hBleft hBright
  let phi := Classical.choose hjointResult
  have hphi : ‖phi‖ = 1 := (Classical.choose_spec hjointResult).1
  have hjoint := (Classical.choose_spec hjointResult).2
  have hsecond := map_eq_of_eq_of_map_eq
    (M.secondCutJointActiveBlockTransport region bcomponent ccomponent WB WC UB UC).conjOperator
    (M.jointBCSectorCompressionRight_eq_sequentialSecondCutCompression region
      (bcomponent.1.restrictScalars Complex) (ccomponent.1.restrictScalars Complex)).symm
    hjoint
  have hfirst := M.firstCut_actual_sequential_active_block
    region bcomponent ccomponent WB WC UB UC Pfirst P_D hCleft hCright
  have htransport : composeUnitaryTransport
      (tensorAssociatorUnitary
        (Semantics.CompositeSystem (M.fourFactorA region)
          (bcomponent.1.restrictScalars Complex))
        (ccomponent.1.restrictScalars Complex) (M.fourFactorD region))
      (M.secondCutJointActiveBlockTransport region bcomponent ccomponent WB WC UB UC) =
      M.firstCutJointActiveBlockTransport region bcomponent ccomponent WB WC UB UC := by
    simpa [secondCutJointActiveBlockTransport, firstCutJointActiveBlockTransport] using
      sequential_isotypicSectorBlockTransportLeft_coherence UB UC
  have hsequential := M.sequentialJointBCSectorCompression_secondCut_eq_firstCut
    region (bcomponent.1.restrictScalars Complex) (ccomponent.1.restrictScalars Complex)
  have hcommon := commonFactorization_of_transport_equivalent_blocks
    (tensorAssociatorUnitary
      (Semantics.CompositeSystem (M.fourFactorA region)
        (bcomponent.1.restrictScalars Complex))
      (ccomponent.1.restrictScalars Complex) (M.fourFactorD region))
    (M.secondCutJointActiveBlockTransport region bcomponent ccomponent WB WC UB UC)
    (M.firstCutJointActiveBlockTransport region bcomponent ccomponent WB WC UB UC)
    (M.sequentialSecondCutJointCompression region
      (bcomponent.1.restrictScalars Complex) (ccomponent.1.restrictScalars Complex))
    (M.sequentialFirstCutJointCompression region
      (bcomponent.1.restrictScalars Complex) (ccomponent.1.restrictScalars Complex))
    phi hphi
    (M.firstCutPleftOnSecondCutActiveSector region bcomponent WB UB
      (WC.restrictScalars Complex) Pfirst)
    (M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond)
    P_D hsequential htransport hsecond hfirst
  exact ⟨phi, hphi, hjoint, hcommon⟩

set_option maxHeartbeats 4000000 in
/--
The source common factor is obtained from the two physical BV03 blocks, not
from caller-supplied sequential equalities.  The first-cut complement block
`P_D` remains an unconstrained projection throughout this assembly.
-/
theorem exists_actual_commonFactorization_of_nonzero_code
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (hM : M.RegionErasureRecoverable region)
    (hC : M.RegionErasureRecoverable (M.externalBoundary region)) :
    ActualCommonFactorizationOfNonzeroCode M region := by
  unfold ActualCommonFactorizationOfNonzeroCode
  have hCselection := M.firstCut_active_sector_tensor_blocks_of_nonzero_code region hcode hC
  let ccomponent := Classical.choose hCselection
  have hcactive := (Classical.choose_spec hCselection).1
  have hCblocks := (Classical.choose_spec hCselection).2.2
  have hBselection := M.secondCut_active_sector_tensor_blocks_of_nonzero_code region hcode hM
  let bcomponent := Classical.choose hBselection
  have hbactive := (Classical.choose_spec hBselection).1
  have hBblocks := (Classical.choose_spec hBselection).2.2
  rcases hCblocks with ⟨nC, hnC, WC, _, _, UC, Pfirst, P_D, hCleft, hCright⟩
  letI : NeZero nC := hnC
  rcases hBblocks with ⟨nB, hnB, WB, _, _, UB, Pleft, Qsecond, hBleft, hBright⟩
  letI : NeZero nB := hnB
  rcases M.exists_actual_commonFactorization_and_jointSecondCutBlock_of_fixed_active_data
    region hcode hM bcomponent ccomponent WB WC UB UC Pfirst P_D Pleft Qsecond
      hbactive hCleft hCright hBleft hBright with
    ⟨phi, hphi, _, hcommon⟩
  exact ⟨ccomponent, bcomponent, hcactive, hbactive, nC, hnC, WC, UC, Pfirst, P_D,
    hCleft, hCright, nB, hnB, WB, UB, Pleft, Qsecond, phi, hBleft, hBright, hphi,
    hcommon⟩


end BPTCommutingProjectorModel

end Bounds
end QEC
