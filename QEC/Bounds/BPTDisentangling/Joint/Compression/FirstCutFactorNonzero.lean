import QEC.Bounds.BPTDisentangling.Joint.Compression.FirstCutCodeNonzero

/-!
# BPT first-cut factor nonzero

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
/-- A nonempty active first-cut block has a nonzero left BV03 factor. -/
theorem firstCut_Pleft_ne_zero_of_nonzero_code
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
      Pleft ≠ 0 := by
  dsimp only
  intro U Pleft Qright hactive hleft hright
  have hRcompressed := M.firstCutCodeLift_active_compression_ne_zero_of_nonzero_code
    region hcode component hactive
  have hblock := M.firstCut_compressed_overlap_block_product
    region component W U Pleft Qright hleft hright
  exact left_factor_ne_zero_of_nonzero_unitary_tensor_block
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
    Pleft Qright hRcompressed hblock



end BPTCommutingProjectorModel

end Bounds
end QEC
