import QEC.Bounds.BPTDisentangling.NoCloning.ScalarCompression.ExternalPhysical
import QEC.Bounds.BPTDisentangling.NoCloning.ScalarCompression.ExternalTransport

/-!
# BPT external-residual scalar-compression assembly

Pure assembly of physical external witnesses and fixed-probe transport into the
exact active-sector family.
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

/-- Transport an exact physical external-residual family to the active sector. -/
theorem all_externalResidual_scalar_compressions_on_actual_active_sector
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
      ∀ Y : Semantics.Operator (WC.restrictScalars Complex),
        M.ExternalResidualPhysicalWitness region ccomponent WC UC Qsecond Y) :
    M.ActualExternalResidualScalarCompression region ccomponent WC UC Qsecond := by
  intro Y
  rcases hphysical Y with ⟨E, Ephysical, scalar, hPullback, hscalar⟩
  refine ⟨scalar, ?_⟩
  exact M.externalResidual_scalar_compression_on_actual_active_sector
    region ccomponent WC UC Qsecond Y E Ephysical scalar hPullback hQ hsupport hscalar

end BPTCommutingProjectorModel

end Bounds
end QEC
