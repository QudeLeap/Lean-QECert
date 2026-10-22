import QEC.Bounds.BPTDisentangling.NoCloning.Fixed.Compression

/-!
# BPT fixed-data rank-one residual

Cacheable no-cloning closure from the exact common-factor and physical
scalar-compression contracts to a rank-one residual factor.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

set_option maxHeartbeats 1800000

-- This internal bridge is too large to be useful as an automated premise.
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.modifyEnv fun env =>
    Lean.LibrarySuggestions.nameDenyListExt.addEntry env
      "residualRankOne_of_common_and_compression_for_D5"

theorem residualRankOne_of_common_and_compression_for_D5
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
    (hcommonData : M.FixedActiveCommonFactorizationData
      region bcomponent ccomponent WB WC UB UC Pfirst P_D Qsecond)
    (hcompressionData : M.FixedActiveRegroupedCompressionData
      region ccomponent WC UC Qsecond) :
    M.FixedActiveDataResidualRankOne
      region bcomponent ccomponent WB WC UB UC Pfirst P_D Qsecond := by
  rcases hcommonData with
    ⟨phi, eta, hphi, hP_D, hP_D0, heta, hPeta, hjoint, hcommon⟩
  rcases hcompressionData with ⟨hQprime, hQprime0, hregrouped⟩
  let N := isotypicLiftedMultiplicity.{0} nB
  let NC := isotypicLiftedMultiplicity.{0} nC
  let C' := WC.restrictScalars Complex
  let D' := Semantics.CompositeSystem NC (M.fourFactorD region)
  let Qprime : Semantics.Operator (Semantics.CompositeSystem N (Semantics.CompositeSystem C' D')) :=
    M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond
  let Theta : Semantics.Operator (Semantics.CompositeSystem N C') :=
    leftTensorCompression phi
      (M.firstCutPleftOnSecondCutActiveSector region bcomponent WB UB C' Pfirst)
  have hcommon' : (tensorAssociatorUnitary N C' D').symm.conjOperator Qprime =
      TensorProduct.map Theta P_D := by
    simpa only [Qprime, Theta, N, C', D', NC] using hcommon
  have hQprime' : Qprime.IsSymmetricProjection := by
    simpa [Qprime] using hQprime
  have hQprime0' : Qprime ≠ 0 := by
    simpa [Qprime] using hQprime0
  have hThetaRecovered : secondCutResidualTheta eta Qprime = Theta :=
    secondCutResidualTheta_eq_of_common_first_second_block
      eta heta P_D hPeta Qprime Theta hcommon'
  have hThetaProjection : @LinearMap.IsSymmetricProjection Complex
      (Semantics.CompositeSystem N C') _ _ _
      (secondCutResidualTheta (N := N) (C := C') (D := D') eta Qprime) := by
    exact secondCutResidualTheta_isSymmetricProjection_of_common_first_second_block
      (N := N) (C := C') (D := D')
      eta heta P_D hP_D hP_D0 hPeta Qprime Theta hQprime' hcommon'
  have hTheta0 : secondCutResidualTheta eta Qprime ≠ 0 :=
    secondCutResidualTheta_ne_zero_of_common_first_second_block
      eta heta P_D hPeta Qprime Theta hQprime0' hcommon'
  rw [hThetaRecovered] at hThetaProjection hTheta0
  rcases hregrouped with ⟨hinternal, hexternal⟩
  rcases secondCutResidualTheta_two_sided_scalar_compressions_for_noCloning
    eta heta P_D hP_D hPeta Qprime Theta hcommon' hinternal hexternal with
    ⟨hThetaInternal, hThetaExternal⟩
  rcases isSymmetricProjection_eq_rankOne_of_ne_zero_of_two_factor_scalar_compressions
    Theta hThetaProjection hTheta0 hThetaInternal hThetaExternal with
    ⟨psi, hpsi, hpsiRankOne⟩
  have hpsiRankOne' :
      leftTensorCompression phi
          (M.firstCutPleftOnSecondCutActiveSector region bcomponent WB UB
            (WC.restrictScalars Complex) Pfirst) =
        (InnerProductSpace.rankOne Complex psi psi).toLinearMap := by
    simpa only [Theta, C'] using hpsiRankOne
  exact ⟨phi, eta, psi, hphi, hP_D, hP_D0, heta, hPeta, hpsi, hjoint,
    hcommon, hpsiRankOne'⟩

end BPTCommutingProjectorModel

end Bounds
end QEC
