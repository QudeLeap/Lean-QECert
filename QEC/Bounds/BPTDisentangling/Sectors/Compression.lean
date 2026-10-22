import QEC.Bounds.BPTDisentangling.FirstCutBlock

/-!
# BPT second-cut compressed block

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
For the physical second BPT cut, compression to an hM-selected internal
boundary sector is exactly the common-unitary tensor block product.  This is
the literal `Pi_AB Pi_Bbar(M)` source lift, so its `Pleft` factor is the
`AB'` projector which the region no-information argument must make rank one.
-/
theorem secondCut_compressed_overlap_block_product
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
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
      (unitaryLTensor A U).conjOperator
          (overlapProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) component) =
          rightTensorExtensionAfterLeft A W0 N Pleft →
      (unitaryRTensor U CD).conjOperator
          (overlapRightProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) (M.secondCutProjectorBbarM region) component) =
          leftTensorExtensionBeforeRight W0 N CD Qright →
      (isotypicSectorBlockTransportLeft A H W0 N CD U).conjOperator
          ((LinearMap.adjoint (tensorTripleSubtypeEmbedding (A := A) (C := CD) H)).comp
            ((M.secondCutCodeLift region).comp
              (tensorTripleSubtypeEmbedding (A := A) (C := CD) H))) =
        TensorProduct.map Pleft Qright := by
  dsimp only
  intro U Pleft Qright hleft hright
  unfold secondCutCodeLift
  exact isotypicSectorBlockTransportLeft_conj_compressed_overlap_product
    (A := M.fourFactorA region) (H := M.fourFactorB region)
    (W := W.restrictScalars Complex) (N := isotypicLiftedMultiplicity.{0} n)
    (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
    (M.fourFactorProjectorABLocal region) (M.secondCutProjectorBbarM region)
    (M.secondCutProjectorAB_isSymmetric region).adjoint_eq
    (M.secondCut_overlap_commute region) component U Pleft Qright hleft hright

end BPTCommutingProjectorModel

end Bounds
end QEC
