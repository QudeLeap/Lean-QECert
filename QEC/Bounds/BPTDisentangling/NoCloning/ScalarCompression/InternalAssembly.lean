import QEC.Bounds.BPTDisentangling.NoCloning.ScalarCompression.InternalPhysical
import QEC.Bounds.BPTDisentangling.NoCloning.ScalarCompression.InternalTransport

/-!
# BPT internal-residual scalar-compression assembly

Pure assembly of a physical family and a fixed-probe transport theorem into the
exact active-sector contract.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

set_option maxHeartbeats 4000000

/-- Transport an exact physical `B''` scalar-compression family to the active sector. -/
theorem all_internalResidual_scalar_compressions_on_actual_active_sector
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
    (hQ : Qsecond.IsSymmetricProjection)
    (hsupport :
      Qsecond.comp
          (TensorProduct.map (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} nB))
            (TensorProduct.map
              (leftIsotypicSectorProjector (M.firstCutProjectorMC region) ccomponent)
              (1 : Semantics.Operator (M.fourFactorD region)))) = Qsecond)
    (hphysical :
      ∀ X : Semantics.Operator (isotypicLiftedMultiplicity.{0} nB),
        ∃ scalar : Complex,
          M.PhysicalInternalResidualProbeCompression region Qsecond X scalar) :
    M.ActualInternalResidualScalarCompression region ccomponent WC UC Qsecond := by
  intro X
  rcases hphysical X with ⟨scalar, hscalar⟩
  refine ⟨scalar, ?_⟩
  exact M.internalResidual_scalar_compression_on_actual_active_sector
    region ccomponent WC UC Qsecond X scalar hQ hsupport hscalar

end BPTCommutingProjectorModel

end Bounds
end QEC
