import QEC.Bounds.BPTDisentangling.Sectors.Conjugation

/-!
# BPT first-cut compressed block

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
For the physical first BPT cut, compression to an externally-active `C`
isotypic sector is exactly the common-unitary tensor block product.  The
left-hand side is the literal `Pi_MC Pi_CD` code lift, rather than an
abstract overlap pair; this is the point at which the BV03 block calculation
enters the source projector proof.
-/
theorem firstCut_compressed_overlap_block_product
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
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
      (unitaryLTensor AB U).conjOperator
          (overlapProjectorOnIsotypicComponent (M.firstCutProjectorMC region) component) =
          rightTensorExtensionAfterLeft AB W0 N Pleft →
      (unitaryRTensor U D).conjOperator
          (overlapRightProjectorOnIsotypicComponent
            (M.firstCutProjectorMC region) (M.fourFactorProjectorCDLocal region) component) =
          leftTensorExtensionBeforeRight W0 N D Qright →
      (isotypicSectorBlockTransportLeft AB H W0 N D U).conjOperator
          ((LinearMap.adjoint (tensorTripleSubtypeEmbedding (A := AB) (C := D) H)).comp
            ((M.firstCutCodeLift region).comp
              (tensorTripleSubtypeEmbedding (A := AB) (C := D) H))) =
        TensorProduct.map Pleft Qright := by
  dsimp only
  intro U Pleft Qright hleft hright
  unfold firstCutCodeLift
  exact isotypicSectorBlockTransportLeft_conj_compressed_overlap_product
    (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
    (H := M.fourFactorC region) (W := W.restrictScalars Complex)
    (N := isotypicLiftedMultiplicity.{0} n) (C := M.fourFactorD region)
    (M.firstCutProjectorMC region) (M.fourFactorProjectorCDLocal region)
    (M.firstCutProjectorMC_isSymmetric region).adjoint_eq
    (M.firstCut_overlap_commute region) component U Pleft Qright hleft hright

end BPTCommutingProjectorModel

end Bounds
end QEC
