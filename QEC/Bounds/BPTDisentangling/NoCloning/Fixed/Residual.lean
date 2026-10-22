import QEC.Bounds.BPTDisentangling.NoCloning.Fixed.RankOne

/-!
# BPT fixed-data residual rank-one closure

Cacheable proof layer from the two physical scalar-compression families to the
rank-one common residual factor.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

-- Internal cache boundary; do not index its large dependent type as an automated premise.
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.modifyEnv fun env =>
    Lean.LibrarySuggestions.nameDenyListExt.addEntry env
      "exists_residualRankOne_of_fixed_active_data_for_D5"

set_option maxHeartbeats 1800000 in
/-- The exact common residual factor is rank one for fixed active sector data. -/
theorem exists_residualRankOne_of_fixed_active_data_for_D5
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥) (hM : M.RegionErasureRecoverable region)
    (hC : M.RegionErasureRecoverable (M.externalBoundary region))
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
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))
    (hCactive : M.firstCutCodeLift region * M.firstCutSectorLift region ccomponent =
      M.firstCutCodeLift region)
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
    M.FixedActiveDataResidualRankOne
      region bcomponent ccomponent WB WC UB UC Pfirst P_D Qsecond := by
  have hcommonData := M.fixedActive_commonFactorizationData_for_D5
    region hcode hM bcomponent ccomponent WB WC UB UC Pfirst P_D Pleft Qsecond
      hCactive hBactive hCleft hCright hBleft hBright
  have hcompressionData := M.fixedActive_regroupedCompressionData_for_D5
    region hcode hM hC ccomponent bcomponent WC UC WB UB Pleft Qsecond
      hCactive hBactive hBleft hBright
  exact M.residualRankOne_of_common_and_compression_for_D5
    region bcomponent ccomponent WB WC UB UC Pfirst P_D Qsecond
      hcommonData hcompressionData

end BPTCommutingProjectorModel

end Bounds
end QEC
