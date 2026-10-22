import QEC.Bounds.BPTDisentangling.Joint.Compression.FirstCutProjection

/-!
# BPT joint compression residual projection

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
The source `Pi_C''D` factor is a nonzero orthogonal projection on the active
first-cut block.  It is the concrete arbitrary `P_D` retained by the residual
no-cloning argument.
-/
theorem firstCut_Qright_isSymmetricProjection_of_nonzero_code_active_block
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {n : Nat} [NeZero n]
    (W : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region)) :
    let AB := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)
    let H := component.1.restrictScalars Complex
    let W0 := W.restrictScalars Complex
    let N := isotypicLiftedMultiplicity.{0} n
    let D := M.fourFactorD region
    ∀ (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W0 N))
      (Pleft : Semantics.Operator (Semantics.CompositeSystem AB W0))
      (Qright : Semantics.Operator (Semantics.CompositeSystem N D)),
      M.firstCutCodeLift region * M.firstCutSectorLift region component =
          M.firstCutCodeLift region →
      (unitaryLTensor AB U).conjOperator
          (overlapProjectorOnIsotypicComponent (M.firstCutProjectorMC region) component) =
          rightTensorExtensionAfterLeft AB W0 N Pleft →
      (unitaryRTensor U D).conjOperator
          (overlapRightProjectorOnIsotypicComponent
            (M.firstCutProjectorMC region) (M.fourFactorProjectorCDLocal region) component) =
          leftTensorExtensionBeforeRight W0 N D Qright →
      Qright.IsSymmetricProjection ∧ Qright ≠ 0 := by
  dsimp only
  intro U Pleft Qright hactive hleft hright
  have hblockEq := M.firstCut_compressed_overlap_block_product
    region component W U Pleft Qright hleft hright
  have hcompressedProjection :=
    M.firstCut_compressedCode_isSymmetricProjection region component
  have hblock : (TensorProduct.map Pleft Qright).IsSymmetricProjection := by
    exact isSymmetricProjection_congr
      ((isSymmetricProjection_conjOperator_iff
        (isotypicSectorBlockTransportLeft
          (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
          (component.1.restrictScalars Complex) (W.restrictScalars Complex)
          (isotypicLiftedMultiplicity.{0} n) (M.fourFactorD region) U) _).mpr
        hcompressedProjection)
      hblockEq
  have hPleft := M.firstCut_Pleft_isSymmetricProjection region component W U Pleft hleft
  have hPleft0 := M.firstCut_Pleft_ne_zero_of_nonzero_code
    region hcode component W U Pleft Qright hactive hleft hright
  constructor
  · exact right_factor_isSymmetricProjection_of_tensor_product_projection Pleft Qright
      hPleft hPleft0 hblock
  · have hRcompressed := M.firstCutCodeLift_active_compression_ne_zero_of_nonzero_code
      region hcode component hactive
    exact right_factor_ne_zero_of_nonzero_unitary_tensor_block
      (isotypicSectorBlockTransportLeft
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
        (component.1.restrictScalars Complex) (W.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} n) (M.fourFactorD region) U)
      ((LinearMap.adjoint
        (tensorTripleSubtypeEmbedding
          (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
          (C := M.fourFactorD region) (component.1.restrictScalars Complex))).comp
        ((M.firstCutCodeLift region).comp
          (tensorTripleSubtypeEmbedding
            (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
            (C := M.fourFactorD region) (component.1.restrictScalars Complex))))
      Pleft Qright hRcompressed hblockEq



end BPTCommutingProjectorModel

end Bounds
end QEC
