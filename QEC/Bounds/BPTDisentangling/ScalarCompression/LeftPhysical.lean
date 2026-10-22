import QEC.Bounds.BPTDisentangling.ScalarCompression.LeftProbe

/-!
# BPT physical second-cut left scalar compression

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

set_option maxHeartbeats 12000000 in
/--
The hM no-information equation descends through the active second BV03
sector to scalar compression by every operator on `Pleft`.  The proof uses
the physical-region probe, the literal compressed code relation, and the
residual tensor-factor cancellation; it is the source's `Pi_AB'` argument.
-/
theorem secondCut_Pleft_all_scalar_compression_of_region_recoverable
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (hM : M.RegionErasureRecoverable region)
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
      ∀ X : Semantics.Operator (Semantics.CompositeSystem A W0),
        ∃ scalar : Complex, Pleft * X * Pleft = scalar • Pleft := by
  intro A H W0 N CD U Pleft Qright hactive hleft hright
  let T := isotypicSectorBlockTransportLeft A H W0 N CD U
  have hQright : Qright * Qright = Qright ∧ Qright ≠ 0 := by
    exact M.secondCut_Qright_idempotent_and_ne_zero_of_nonzero_code
      region hcode component W U Pleft Qright hactive hleft hright
  obtain ⟨hQidem, hQright0⟩ := hQright
  let J := tensorTripleSubtypeEmbedding (A := A) (C := CD) H
  have hJ : J = tensorTripleSubtypeEmbedding (A := A) (C := CD) H := rfl
  let Rcompressed : Semantics.Operator
      (Semantics.CompositeSystem (Semantics.CompositeSystem A H) CD) :=
    (LinearMap.adjoint J).comp ((M.secondCutCodeLift region).comp J)
  have hreconstruct : M.secondCutCodeLift region =
      J.comp (Rcompressed.comp (LinearMap.adjoint J)) := by
    exact M.secondCutCodeLift_eq_active_embedding_compression_of_absorption
      region component hactive
  intro X
  let Lprobe := overlapLiftLeft (C := CD)
    ((unitaryLTensor A U).symm.conjOperator
      (rightTensorExtensionAfterLeft A W0 N X))
  rcases M.secondCut_Pleft_compressed_scalar_for_left_probe
    region hM H W0 J hJ Rcompressed hreconstruct U X with ⟨scalar, hcompressedScalar⟩
  have hblock : T.conjOperator Rcompressed = TensorProduct.map Pleft Qright := by
    exact M.secondCut_compressed_overlap_block_product
      region component W U Pleft Qright hleft hright
  have hprobe : T.conjOperator Lprobe =
      TensorProduct.map X (1 : Semantics.Operator (Semantics.CompositeSystem N CD)) := by
    exact M.secondCut_Pleft_left_probe_transport region H W0 U X
  refine ⟨scalar, ?_⟩
  exact left_factor_scalar_compression_of_tensor_block
    T Pleft Qright Rcompressed Lprobe X scalar hblock hQidem hQright0
      hcompressedScalar hprobe

end BPTCommutingProjectorModel

end Bounds
end QEC
