import QEC.Bounds.BPTDisentangling.NoCloning.ProductUnitary

/-!
# BPT fixed-data residual contract

Transparent exact contract for the rank-one common residual factor.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

set_option maxHeartbeats 1800000 in
/-- Exact fixed-data statement that the common residual factor is rank one. -/
def FixedActiveDataResidualRankOne
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
    (Qsecond : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)))) : Prop :=
  ∃ (phi : Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
    (eta : Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
      (M.fourFactorD region))
    (psi : Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
      (WC.restrictScalars Complex)),
    ‖phi‖ = 1 ∧ P_D.IsSymmetricProjection ∧ P_D ≠ 0 ∧ ‖eta‖ = 1 ∧ P_D eta = eta ∧
    ‖psi‖ = 1 ∧
    (M.secondCutJointActiveBlockTransport region bcomponent ccomponent WB WC UB UC).conjOperator
        (M.secondCutJointCompression region
          (bcomponent.1.restrictScalars Complex) (ccomponent.1.restrictScalars Complex)) =
      (unitaryLTensor
        (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
        (tensorAssociatorUnitary (isotypicLiftedMultiplicity.{0} nB)
          (WC.restrictScalars Complex)
          (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
            (M.fourFactorD region))).symm).conjOperator
        (TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap
          (M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond)) ∧
    (tensorAssociatorUnitary (isotypicLiftedMultiplicity.{0} nB)
      (WC.restrictScalars Complex)
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
        (M.fourFactorD region))).symm.conjOperator
        (M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond) =
      TensorProduct.map
        (leftTensorCompression phi
          (M.firstCutPleftOnSecondCutActiveSector region bcomponent WB UB
            (WC.restrictScalars Complex) Pfirst)) P_D ∧
    leftTensorCompression phi
        (M.firstCutPleftOnSecondCutActiveSector region bcomponent WB UB
          (WC.restrictScalars Complex) Pfirst) =
      (InnerProductSpace.rankOne Complex psi psi).toLinearMap

end BPTCommutingProjectorModel

end Bounds
end QEC
