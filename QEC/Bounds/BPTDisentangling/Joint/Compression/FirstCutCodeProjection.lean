import QEC.Bounds.BPTDisentangling.Joint.Compression.FirstCutFactorNonzero

/-!
# BPT first-cut compressed code projection

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

set_option maxHeartbeats 800000 in
/-- The active first-cut code compressed to its selected `C` sector is a projection. -/
theorem firstCut_compressedCode_isSymmetricProjection
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region)) :
    let AB := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)
    let H := component.1.restrictScalars Complex
    let D := M.fourFactorD region
    let J := tensorTripleSubtypeEmbedding (A := AB) (C := D) H
    ((LinearMap.adjoint J).comp ((M.firstCutCodeLift region).comp J)).IsSymmetricProjection := by
  dsimp only
  let AB := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)
  let H := component.1.restrictScalars Complex
  let D := M.fourFactorD region
  let J := tensorTripleSubtypeEmbedding (A := AB) (C := D) H
  let R := M.firstCutCodeLift region
  have hR : R.IsSymmetricProjection := by
    have hfull : M.fullCodeProjector.IsSymmetricProjection := by
      constructor
      · exact M.fullCodeProjector_idempotent
      · exact (LinearMap.isSymmetric_iff_isSelfAdjoint M.fullCodeProjector).mpr
          M.fullCodeProjector_adjoint_eq_self
    change (M.firstCutCodeLift region).IsSymmetricProjection
    rw [← M.firstCutGlobalCoordinateTransport_conj_fullCodeProjector region]
    exact (isSymmetricProjection_conjOperator_iff
      (M.firstCutGlobalCoordinateTransport region) M.fullCodeProjector).mpr hfull
  have hself : LinearMap.adjoint (M.firstCutProjectorMC region) = M.firstCutProjectorMC region :=
    (M.firstCutProjectorMC_isSymmetricProjection region).isSymmetric.adjoint_eq
  have hover : Commute (overlapLiftLeft (C := D) (M.firstCutProjectorMC region))
      (overlapLiftRight (A := AB) (M.fourFactorProjectorCDLocal region)) :=
    M.firstCut_overlap_commute region
  have hJJ : J.comp (LinearMap.adjoint J) = M.firstCutSectorLift region component := by
    simpa only [J, AB, H, D, firstCutSectorLift] using
      (tensorTripleSubtypeEmbedding_comp_adjoint_eq_leftIsotypicSectorLift
        (M.firstCutProjectorMC region) component (C := D))
  have hcommuteSector : Commute R (M.firstCutSectorLift region component) := by
    simpa only [R, AB, D, firstCutCodeLift, firstCutSectorLift] using
      (overlap_product_commutes_leftIsotypicSectorLift
        (M.firstCutProjectorMC region) (M.fourFactorProjectorCDLocal region)
        hself hover component)
  have hcommute : Commute R (J.comp (LinearMap.adjoint J)) :=
    hJJ.symm ▸ hcommuteSector
  change ((LinearMap.adjoint J).comp (R.comp J)).IsSymmetricProjection
  exact isSymmetricProjection_of_isometric_compression_commuting
    J (LinearMap.adjoint J) R
    (adjoint_tensorTripleSubtypeEmbedding_comp_tensorTripleSubtypeEmbedding (A := AB) (C := D) H)
    rfl hR hcommute



end BPTCommutingProjectorModel

end Bounds
end QEC
