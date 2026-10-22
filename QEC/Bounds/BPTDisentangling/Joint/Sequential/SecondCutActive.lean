import QEC.Bounds.BPTDisentangling.Joint.Sequential.BlockData
import QEC.Bounds.BPTDisentangling.ScalarCompression.LeftRankOneProductWitnessNorm
import QEC.Bounds.BPTDisentangling.ScalarCompression.SelectedB

/-!
# BPT physical second-cut sequential block

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
      "secondCut_actual_sequential_active_block_of_region_recoverable"

set_option maxHeartbeats 800000 in
/--
The concrete B-first sequential block for the BPT code.  The source
rank-one `Pi_AB'` equation is obtained from `hM`, then its literal active
`C` subtype compression is transported by the proved right-factor
naturality square.  This supplies the actual `hsecond` input to the common
factorization step.
-/
theorem secondCut_actual_sequential_active_block_of_region_recoverable
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
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))
    (hsource : SecondCutActiveBlockConditions M region bcomponent WB UB Pleft Qsecond) :
    SecondCutActualSequentialActiveBlock M region bcomponent ccomponent WB WC UB UC Qsecond := by
  unfold SecondCutActualSequentialActiveBlock
  let hproduct := M.secondCut_compressed_overlap_rankOne_block_product_of_region_recoverable
    region hcode hM bcomponent WB UB Pleft Qsecond hsource
  let phi := SecondCutRankOneBlockProduct.witness (n := nB) hproduct
  have hphi : ‖phi‖ = 1 :=
    SecondCutRankOneBlockProduct.witness_norm (n := nB) hproduct
  have hblock := (Classical.choose_spec hproduct).2
  refine ⟨phi, hphi, ?_⟩
  dsimp only
  have hblock' :
      (isotypicSectorBlockTransportLeft (M.fourFactorA region)
        (bcomponent.1.restrictScalars Complex) (WB.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nB)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) UB).conjOperator
          (M.secondCutSelectedBCompression region
            (bcomponent.1.restrictScalars Complex)) =
        TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap Qsecond := by
    exact hblock
  exact sequential_secondCut_named_block
    (A := M.fourFactorA region)
    (H := bcomponent.1.restrictScalars Complex)
    (W := WB.restrictScalars Complex)
    (N := isotypicLiftedMultiplicity.{0} nB)
    (C := ccomponent.1.restrictScalars Complex)
    (C' := M.fourFactorC region)
    (X := WC.restrictScalars Complex)
    (N2 := isotypicLiftedMultiplicity.{0} nC)
    (D := M.fourFactorD region)
    UB UC (ccomponent.1.restrictScalars Complex).subtype
    (M.secondCutSelectedBCompression region (bcomponent.1.restrictScalars Complex))
    (InnerProductSpace.rankOne Complex phi phi).toLinearMap Qsecond
    (M.sequentialSecondCutJointCompression region
      (bcomponent.1.restrictScalars Complex) (ccomponent.1.restrictScalars Complex))
    (M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond)
    (M.secondCutJointActiveBlockTransport region bcomponent ccomponent WB WC UB UC)
    rfl rfl rfl hblock'


end BPTCommutingProjectorModel

end Bounds
end QEC
