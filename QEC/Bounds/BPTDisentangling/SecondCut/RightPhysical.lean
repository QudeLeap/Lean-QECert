import QEC.Bounds.BPTDisentangling.SecondCut.TensorFactor

/-!
# BPT second-cut physical right-factor block

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
/--
The second-cut block equality makes the residual right factor nonzero and
idempotent.  Both conclusions are derived from the physical code projector,
not stored as factorization data.
-/
theorem secondCut_Qright_idempotent_and_ne_zero_of_nonzero_code
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    {n : Nat} [NeZero n]
    (W : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)) :
    let A := M.fourFactorA region
    let H := component.1.restrictScalars Complex
    let W0 := W.restrictScalars Complex
    let N := isotypicLiftedMultiplicity.{0} n
    let CD := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)
    ∀ (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W0 N))
      (Pleft : Semantics.Operator (Semantics.CompositeSystem A W0))
      (Qright : Semantics.Operator (Semantics.CompositeSystem N CD)),
      M.secondCutCodeLift region * M.secondCutSectorLift region component =
          M.secondCutCodeLift region →
      (unitaryLTensor A U).conjOperator
          (overlapProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) component) =
          rightTensorExtensionAfterLeft A W0 N Pleft →
      (unitaryRTensor U CD).conjOperator
          (overlapRightProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) (M.secondCutProjectorBbarM region) component) =
          leftTensorExtensionBeforeRight W0 N CD Qright →
      Qright * Qright = Qright ∧ Qright ≠ 0 := by
  dsimp only
  intro U Pleft Qright hactive hleft hright
  exact right_factor_idempotent_and_ne_zero_of_projection_block
    (isotypicSectorBlockTransportLeft (M.fourFactorA region)
      (component.1.restrictScalars Complex) (W.restrictScalars Complex)
      (isotypicLiftedMultiplicity.{0} n)
      (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) U)
    _ Pleft Qright
    (M.secondCutCodeLift_active_compression_ne_zero_of_nonzero_code
      region hcode component hactive)
    (M.secondCut_Pleft_isSymmetricProjection region component W U Pleft hleft)
    (M.secondCut_Pleft_ne_zero_of_nonzero_code region hcode component W U Pleft Qright
      hactive hleft hright)
    (M.secondCut_compressedCode_isSymmetricProjection region component)
    (M.secondCut_compressed_overlap_block_product
      region component W U Pleft Qright hleft hright)

end BPTCommutingProjectorModel

end Bounds
end QEC
