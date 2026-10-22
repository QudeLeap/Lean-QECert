import QEC.Bounds.BPTDisentangling.Joint.Sequential.SecondCutActive
import QEC.Bounds.BPTDisentangling.Joint.Sequential.SecondCutEquality
import QEC.Bounds.BPTDisentangling.Joint.Sequential.SecondCutJointData

/-!
# BPT joint-sector second-cut block

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

-- Internal cache bridge; do not index its large dependent type as an automated premise.
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.modifyEnv fun env =>
    Lean.LibrarySuggestions.nameDenyListExt.addEntry env
      "secondCut_actual_joint_active_block_of_region_recoverable"

set_option maxHeartbeats 800000 in
/--
The same physical B-first active block, now expressed through the simultaneous
joint `B,C` embedding.  It is obtained by rewriting the sequential block, so
the returned `phi` is the very same witness used by the common factorization.
-/
theorem secondCut_actual_joint_active_block_of_region_recoverable
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
    (Pleft : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex)))
    (Qsecond : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))) )
    (hactive : M.secondCutCodeLift region * M.secondCutSectorLift region bcomponent =
      M.secondCutCodeLift region)
    (hleft :
      (unitaryLTensor (M.fourFactorA region) UB).conjOperator
          (overlapProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) bcomponent) =
        rightTensorExtensionAfterLeft (M.fourFactorA region)
          (WB.restrictScalars Complex) (isotypicLiftedMultiplicity.{0} nB) Pleft)
    (hright :
      (unitaryRTensor UB
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))).conjOperator
          (overlapRightProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) (M.secondCutProjectorBbarM region)
            bcomponent) =
        leftTensorExtensionBeforeRight (WB.restrictScalars Complex)
          (isotypicLiftedMultiplicity.{0} nB)
          (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) Qsecond) :
    SecondCutActualJointActiveBlock M region bcomponent ccomponent WB WC UB UC Qsecond := by
  unfold SecondCutActualJointActiveBlock
  have hsequentialResult := M.secondCut_actual_sequential_active_block_of_region_recoverable
    region hcode hM bcomponent ccomponent WB WC UB UC
      Pleft Qsecond ⟨hactive, hleft, hright⟩
  let phi := Classical.choose hsequentialResult
  have hphi : ‖phi‖ = 1 := (Classical.choose_spec hsequentialResult).1
  have hsequential := (Classical.choose_spec hsequentialResult).2
  refine ⟨phi, hphi, ?_⟩
  exact map_eq_of_eq_of_map_eq
    (M.secondCutJointActiveBlockTransport region bcomponent ccomponent WB WC UB UC).conjOperator
    (M.jointBCSectorCompressionRight_eq_sequentialSecondCutCompression region
      (bcomponent.1.restrictScalars Complex) (ccomponent.1.restrictScalars Complex))
    hsequential


end BPTCommutingProjectorModel

end Bounds
end QEC
