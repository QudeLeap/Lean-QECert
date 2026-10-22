import QEC.Bounds.BPTDisentangling.NoCloning.ScalarCompression.External

/-!
# BPT scalar-compression aggregate contract

Cacheable internal proof layer for the finite-dimensional BPT Disentangling Lemma.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

set_option maxHeartbeats 800000

/--
The two source no-information paths are available on the actual active
`B'' tensor C' tensor (C''D)` block.  The first-cut BV03 data, including the
arbitrary source complement factor `P_D`, is accepted unchanged; no common
factor, residual `Theta`, or scalar conclusion is supplied by the caller.
-/
theorem secondCutQrightOnFirstCutActiveSector_scalar_compressions_of_recoverable
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥) (hM : M.RegionErasureRecoverable region)
    (hC : M.RegionErasureRecoverable (M.externalBoundary region))
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    {nC nB : Nat} [NeZero nC] [NeZero nB]
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC)))
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (UB : Semantics.UnitaryTransport (bcomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WB.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nB)))
    (Pleft : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex)))
    (Qsecond : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))
    (hCactive : M.firstCutCodeLift region * M.firstCutSectorLift region ccomponent =
      M.firstCutCodeLift region)
    (hBactive : M.secondCutCodeLift region * M.secondCutSectorLift region bcomponent =
      M.secondCutCodeLift region)
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
    M.ActualActiveSectorScalarCompressions region ccomponent WC UC Qsecond := by
  rcases M.secondCutQrightOnFirstCutActiveSector_isSymmetricProjection_and_ne_zero
    region hcode hM ccomponent bcomponent WC UC WB UB Pleft Qsecond
      hCactive hBactive hBleft hBright with ⟨hprojection, hnonzero⟩
  refine ⟨⟨hprojection, hnonzero⟩, ?_, ?_⟩
  · exact M.secondCutQrightOnFirstCutActiveSector_all_internalResidual_scalar_compression_of_region_recoverable
      region hcode hM ccomponent bcomponent WC UC WB UB Pleft Qsecond
        hCactive hBactive hBleft hBright
  · exact M.secondCutQrightOnFirstCutActiveSector_all_externalResidual_scalar_compression_of_externalBoundary_recoverable
      region hcode hM hC ccomponent bcomponent WC UC WB UB Pleft Qsecond
      hCactive hBactive hBleft hBright

end BPTCommutingProjectorModel

end Bounds
end QEC
