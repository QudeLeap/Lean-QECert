import QEC.Bounds.BPTDisentangling.NoCloning.Fixed.ProductCoreData
import QEC.Bounds.BPTDisentangling.NoCloning.ProductFactorization

/-!
# BPT fixed-data product core

Cacheable proof layer converting the exact rank-one residual factor into a
rank-one product factor under a unitary transport.
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
      "productCore_of_residualRankOne_for_D5"

set_option maxHeartbeats 1800000 in
/-- Convert the fixed-data rank-one residual factor into the exact product block. -/
theorem productCore_of_residualRankOne_for_D5
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
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))
    (hresidual : M.FixedActiveDataResidualRankOne
      region bcomponent ccomponent WB WC UB UC Pfirst P_D Qsecond) :
    M.FixedActiveDataProductCore
      region bcomponent ccomponent WB WC UB UC P_D Qsecond := by
  rcases hresidual with
    ⟨phi, eta, psi, hphi, hP_D, hP_D0, heta, hPeta, hpsi, hjoint,
      hcommon, hpsiRankOne⟩
  rcases exists_unitaryTransport_conj_rankOne_eq_normalized_product psi hpsi with
    ⟨n0, c0, hn0, hc0, U, hU, hconj⟩
  have hproduct :
      (unitaryRTensor U
        (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
          (M.fourFactorD region))).conjOperator
          ((tensorAssociatorUnitary (isotypicLiftedMultiplicity.{0} nB)
            (WC.restrictScalars Complex)
            (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
              (M.fourFactorD region))).symm.conjOperator
            (M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond)) =
        TensorProduct.map
          (InnerProductSpace.rankOne Complex
            (n0 ⊗ₜ[Complex] c0 : Semantics.CompositeSystem
              (isotypicLiftedMultiplicity.{0} nB) (WC.restrictScalars Complex))
            (n0 ⊗ₜ[Complex] c0 : Semantics.CompositeSystem
              (isotypicLiftedMultiplicity.{0} nB) (WC.restrictScalars Complex))).toLinearMap P_D := by
    exact unitaryRTensor_conj_of_two_step_factorization U
      ((tensorAssociatorUnitary (isotypicLiftedMultiplicity.{0} nB)
        (WC.restrictScalars Complex)
        (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
          (M.fourFactorD region))).symm.conjOperator
        (M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond))
      (leftTensorCompression phi
        (M.firstCutPleftOnSecondCutActiveSector region bcomponent WB UB
          (WC.restrictScalars Complex) Pfirst))
      (InnerProductSpace.rankOne Complex psi psi).toLinearMap
      (InnerProductSpace.rankOne Complex
        (n0 ⊗ₜ[Complex] c0 : Semantics.CompositeSystem
          (isotypicLiftedMultiplicity.{0} nB) (WC.restrictScalars Complex))
        (n0 ⊗ₜ[Complex] c0 : Semantics.CompositeSystem
          (isotypicLiftedMultiplicity.{0} nB) (WC.restrictScalars Complex))).toLinearMap
      P_D hcommon hpsiRankOne hconj
  exact ⟨phi, eta, psi, n0, c0, U, hphi, hP_D, hP_D0, heta, hPeta, hpsi,
    hn0, hc0, hU, hjoint, hproduct⟩

end BPTCommutingProjectorModel

end Bounds
end QEC
