import QEC.Bounds.BPTDisentangling.Joint.CommonFactorizationData

/-!
# BPT nonzero-code common-factor data

This named proposition records the complete selected-sector data and the
source common-factor equation obtained from a nonzero code projector.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

set_option maxHeartbeats 800000 in
/-- The complete active-sector common-factor package for a nonzero code. -/
def ActualCommonFactorizationOfNonzeroCode
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) : Prop :=
  ∃ (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)),
    M.firstCutCodeLift region * M.firstCutSectorLift region ccomponent =
        M.firstCutCodeLift region ∧
    M.secondCutCodeLift region * M.secondCutSectorLift region bcomponent =
        M.secondCutCodeLift region ∧
    ∃ (nC : Nat) (hnC : NeZero nC),
      letI : NeZero nC := hnC
      ∃ (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
          (M.fourFactorC region))
        (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
          (Semantics.CompositeSystem (WC.restrictScalars Complex)
            (isotypicLiftedMultiplicity.{0} nC)))
        (Pfirst : Semantics.Operator
          (Semantics.CompositeSystem
            (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
            (WC.restrictScalars Complex)))
        (P_D : Semantics.Operator
          (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
            (M.fourFactorD region))),
        (unitaryLTensor
          (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)) UC).conjOperator
            (overlapProjectorOnIsotypicComponent (M.firstCutProjectorMC region) ccomponent) =
          rightTensorExtensionAfterLeft
            (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
            (WC.restrictScalars Complex) (isotypicLiftedMultiplicity.{0} nC) Pfirst ∧
        (unitaryRTensor UC (M.fourFactorD region)).conjOperator
            (overlapRightProjectorOnIsotypicComponent
              (M.firstCutProjectorMC region) (M.fourFactorProjectorCDLocal region) ccomponent) =
          leftTensorExtensionBeforeRight (WC.restrictScalars Complex)
            (isotypicLiftedMultiplicity.{0} nC) (M.fourFactorD region) P_D ∧
        ∃ (nB : Nat) (hnB : NeZero nB),
          letI : NeZero nB := hnB
          ∃ (WB : Submodule
              (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
              (M.fourFactorB region))
            (UB : Semantics.UnitaryTransport (bcomponent.1.restrictScalars Complex)
              (Semantics.CompositeSystem (WB.restrictScalars Complex)
                (isotypicLiftedMultiplicity.{0} nB)))
            (Pleft : Semantics.Operator
              (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex)))
            (Qsecond : Semantics.Operator
              (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
                (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))
            (phi : Semantics.CompositeSystem (M.fourFactorA region)
              (WB.restrictScalars Complex)),
            (unitaryLTensor (M.fourFactorA region) UB).conjOperator
                (overlapProjectorOnIsotypicComponent
                  (M.fourFactorProjectorABLocal region) bcomponent) =
              rightTensorExtensionAfterLeft (M.fourFactorA region)
                (WB.restrictScalars Complex) (isotypicLiftedMultiplicity.{0} nB) Pleft ∧
            (unitaryRTensor UB
              (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))).conjOperator
                (overlapRightProjectorOnIsotypicComponent
                  (M.fourFactorProjectorABLocal region) (M.secondCutProjectorBbarM region)
                  bcomponent) =
              leftTensorExtensionBeforeRight (WB.restrictScalars Complex)
                (isotypicLiftedMultiplicity.{0} nB)
                (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) Qsecond ∧
            ‖phi‖ = 1 ∧
            (tensorAssociatorUnitary (isotypicLiftedMultiplicity.{0} nB)
              (WC.restrictScalars Complex)
              (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
                (M.fourFactorD region))).symm.conjOperator
                (M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond) =
              TensorProduct.map
                (leftTensorCompression phi
                  (M.firstCutPleftOnSecondCutActiveSector region bcomponent WB UB
                    (WC.restrictScalars Complex) Pfirst)) P_D

end BPTCommutingProjectorModel

end Bounds
end QEC
