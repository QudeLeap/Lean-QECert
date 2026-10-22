import QEC.Bounds.BPTDisentangling.NoCloning.ScalarCompression.ExternalData

/-!
# BPT physical external-residual scalar compression

Cacheable extraction of the physical zero-extension and scalar-compression
witnesses for one external probe.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

/-- Exact physical data needed to transport one external-residual probe. -/
def ExternalResidualPhysicalWitness
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nC nB : Nat} [NeZero nC] [NeZero nB]
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC)))
    (Qsecond : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))
    (Y : Semantics.Operator (WC.restrictScalars Complex)) : Prop :=
  ∃ (E : Semantics.Operator (ccomponent.1.restrictScalars Complex))
    (Ephysical : Semantics.Operator (M.fourFactorC region)) (scalar : Complex),
    M.ExternalResidualProbePullback region ccomponent WC UC Y E Ephysical ∧
    M.PhysicalExternalResidualProbeCompression region Qsecond Ephysical scalar

set_option maxHeartbeats 4000000

/-- Extract the physical witness for one `C'` probe from external-boundary recoverability. -/
theorem externalResidual_physical_witness_for_probe
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
    (Y : Semantics.Operator (WC.restrictScalars Complex))
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
    M.ExternalResidualPhysicalWitness region ccomponent WC UC Qsecond Y := by
  let H := ccomponent.1.restrictScalars Complex
  let NC := isotypicLiftedMultiplicity.{0} nC
  let E : Semantics.Operator H := UC.symm.conjOperator
    (TensorProduct.map Y (1 : Semantics.Operator NC))
  let Ephysical : Semantics.Operator (M.fourFactorC region) :=
    H.subtype.comp (E.comp (LinearMap.adjoint H.subtype))
  rcases M.secondCut_Qright_all_externalResidual_scalar_compression_of_externalBoundary_recoverable
      region hcode hM bcomponent WB UB Pleft Qsecond hBactive hBleft hBright hC Ephysical with
    ⟨scalar, hscalar⟩
  refine ⟨E, Ephysical, scalar, ⟨rfl, rfl⟩, ?_⟩
  change Qsecond *
      TensorProduct.map (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} nB))
        (TensorProduct.map Ephysical (1 : Semantics.Operator (M.fourFactorD region))) *
      Qsecond = scalar • Qsecond
  exact hscalar

end BPTCommutingProjectorModel

end Bounds
end QEC
