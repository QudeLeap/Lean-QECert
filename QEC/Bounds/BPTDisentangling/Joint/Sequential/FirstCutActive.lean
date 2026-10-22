import QEC.Bounds.BPTDisentangling.Joint.Sequential.FirstCutCore
import QEC.Bounds.BPTDisentangling.FirstCutBlock
import QEC.Bounds.BPTDisentangling.Joint.ActiveBlockTransports
import QEC.Bounds.BPTDisentangling.Joint.Sequential.Factors
import QEC.Bounds.BPTDisentangling.Joint.Sequential.FirstCutActiveData

/-!
# BPT physical first-cut sequential block

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
      "firstCut_actual_sequential_active_block"

set_option maxHeartbeats 800000 in
/--
The concrete C-first sequential block for the BPT code.  The physical
first-cut BV03 product is compressed through the literal active `B` subtype
using the proved left-factor naturality square, then transported by the
actual `B` isotypic unitary.  This is the actual `hfirst` input to the common
factorization step, with `P_D` retained unchanged.
-/
theorem firstCut_actual_sequential_active_block
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
    (Pfirst : Semantics.Operator
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
        (WC.restrictScalars Complex)))
    (P_D : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
        (M.fourFactorD region)))
    (hleft :
      (unitaryLTensor
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)) UC).conjOperator
          (overlapProjectorOnIsotypicComponent (M.firstCutProjectorMC region) ccomponent) =
        rightTensorExtensionAfterLeft
          (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
          (WC.restrictScalars Complex) (isotypicLiftedMultiplicity.{0} nC) Pfirst)
    (hright :
      (unitaryRTensor UC (M.fourFactorD region)).conjOperator
          (overlapRightProjectorOnIsotypicComponent
            (M.firstCutProjectorMC region) (M.fourFactorProjectorCDLocal region) ccomponent) =
        leftTensorExtensionBeforeRight (WC.restrictScalars Complex)
          (isotypicLiftedMultiplicity.{0} nC) (M.fourFactorD region) P_D) :
    FirstCutActualSequentialActiveBlock M region bcomponent ccomponent WB WC UB UC Pfirst P_D := by
  unfold FirstCutActualSequentialActiveBlock
  have hblock :
      (isotypicSectorBlockTransportLeft
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
        (ccomponent.1.restrictScalars Complex) (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC) (M.fourFactorD region) UC).conjOperator
          ((LinearMap.adjoint (tensorTripleSubtypeEmbedding
            (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
            (C := M.fourFactorD region) (ccomponent.1.restrictScalars Complex))).comp
            ((M.firstCutCodeLift region).comp
              (tensorTripleSubtypeEmbedding
                (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
                (C := M.fourFactorD region) (ccomponent.1.restrictScalars Complex)))) =
        TensorProduct.map Pfirst P_D :=
    M.firstCut_compressed_overlap_block_product region ccomponent WC UC Pfirst P_D hleft hright
  exact sequential_firstCut_named_block
      (A := M.fourFactorA region)
      (B := bcomponent.1.restrictScalars Complex)
      (B' := M.fourFactorB region)
      (H := ccomponent.1.restrictScalars Complex)
      (W := WC.restrictScalars Complex)
      (N := isotypicLiftedMultiplicity.{0} nC)
      (D := M.fourFactorD region)
      (WB := WB.restrictScalars Complex)
      (NB := isotypicLiftedMultiplicity.{0} nB)
      UC UB
      (bcomponent.1.restrictScalars Complex).subtype
      ((LinearMap.adjoint (tensorTripleSubtypeEmbedding
        (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
        (C := M.fourFactorD region) (ccomponent.1.restrictScalars Complex))).comp
        ((M.firstCutCodeLift region).comp
          (tensorTripleSubtypeEmbedding
            (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
            (C := M.fourFactorD region) (ccomponent.1.restrictScalars Complex))))
      Pfirst P_D
      (M.sequentialFirstCutJointCompression region
        (bcomponent.1.restrictScalars Complex) (ccomponent.1.restrictScalars Complex))
      (M.firstCutPleftOnSecondCutActiveSector region bcomponent WB UB
        (WC.restrictScalars Complex) Pfirst)
      (M.firstCutJointActiveBlockTransport region bcomponent ccomponent WB WC UB UC)
      rfl rfl rfl hblock


end BPTCommutingProjectorModel

end Bounds
end QEC
