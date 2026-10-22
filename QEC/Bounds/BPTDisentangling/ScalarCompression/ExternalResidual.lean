import QEC.Bounds.BPTDisentangling.ScalarCompression.ExternalLocal

/-!
# BPT external residual scalar compression

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

set_option maxHeartbeats 2000000 in
/--
The hC counterpart of the existing hM residual theorem: external-boundary
correctability descends to scalar compression by every literal `C` probe on
the same second-cut `Qright` block.
-/
theorem secondCut_Qright_all_externalResidual_scalar_compression_of_externalBoundary_recoverable
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
    let B := M.fourFactorB region
    let H := component.1.restrictScalars Complex
    let W0 := W.restrictScalars Complex
    let N := isotypicLiftedMultiplicity.{0} n
    let C0 := M.fourFactorC region
    let D := M.fourFactorD region
    let CD := Semantics.CompositeSystem C0 D
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
      M.RegionErasureRecoverable (M.externalBoundary region) →
    ∀ Y : Semantics.Operator C0,
      ∃ scalar : Complex,
        Qright * TensorProduct.map (1 : Semantics.Operator N)
          (TensorProduct.map Y (1 : Semantics.Operator D)) * Qright =
          scalar • Qright := by
  intro A B H W0 N C0 D CD U Pleft Qright hactive hleft hright hC
  let J := tensorTripleSubtypeEmbedding (A := A) (C := CD) H
  let Jadj := LinearMap.adjoint J
  let R := M.secondCutCodeLift region
  let Rcompressed : Semantics.Operator (Semantics.CompositeSystem (Semantics.CompositeSystem A H) CD) :=
    Jadj.comp (R.comp J)
  let T := isotypicSectorBlockTransportLeft A H W0 N CD U
  have hJadjJ : Jadj.comp J =
      (1 : Semantics.Operator (Semantics.CompositeSystem (Semantics.CompositeSystem A H) CD)) := by
    simpa [J, Jadj] using
      (adjoint_tensorTripleSubtypeEmbedding_comp_tensorTripleSubtypeEmbedding
        (A := A) (C := CD) H)
  have hself : LinearMap.adjoint (M.fourFactorProjectorABLocal region) =
      M.fourFactorProjectorABLocal region :=
    (M.secondCutProjectorAB_isSymmetricProjection region).isSymmetric.adjoint_eq
  have hover : Commute
      (overlapLiftLeft (C := CD) (M.fourFactorProjectorABLocal region))
      (overlapLiftRight (A := A) (M.secondCutProjectorBbarM region)) :=
    M.secondCut_overlap_commute region
  have hreconstruct : R = J.comp (Rcompressed.comp Jadj) := by
    dsimp [Rcompressed, R, J, Jadj]
    apply active_overlap_product_eq_isotypic_embedding_compression
      (M.fourFactorProjectorABLocal region) (M.secondCutProjectorBbarM region)
      hself hover component
    exact hactive
  rcases M.secondCut_compressed_overlap_rankOne_block_product_of_region_recoverable
    region hcode hM component W U Pleft Qright ⟨hactive, hleft, hright⟩ with
    ⟨phi, hphi, hblock⟩
  intro Y
  let Z : Semantics.Operator CD := TensorProduct.map Y (1 : Semantics.Operator D)
  let Lprobe : Semantics.Operator (Semantics.CompositeSystem
      (Semantics.CompositeSystem A B) CD) :=
    TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem A B)) Z
  let Lsub : Semantics.Operator (Semantics.CompositeSystem
      (Semantics.CompositeSystem A H) CD) :=
    TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem A H)) Z
  rcases M.secondCut_all_externalLocal_scalar_compression_of_externalBoundary_recoverable
    region hC Y with ⟨scalar, hscalar⟩
  have hprobe : Jadj.comp (Lprobe.comp J) = Lsub := by
    simpa [J, Jadj, Lprobe, Lsub] using
      (adjoint_tensorTripleSubtypeEmbedding_comp_tensorMap_right_comp_tensorTripleSubtypeEmbedding
        (A := A) (B := B) (C := CD) H Z)
  have hcompressedScalar : Rcompressed * Lsub * Rcompressed = scalar • Rcompressed :=
    compressed_scalar_of_named_isometric_reconstruction
      J R Lprobe Rcompressed Lsub scalar hJadjJ hreconstruct hprobe hscalar
  have hTprobe : T.conjOperator Lsub =
      TensorProduct.map (1 : Semantics.Operator
        (Semantics.CompositeSystem A W0))
        (TensorProduct.map (1 : Semantics.Operator N) Z) := by
    simpa [T, Lsub] using
      (isotypicSectorBlockTransportLeft_conj_tensorMap_right
        (A := A) (H := H) (W := W0) (N := N) (C := CD) U Z)
  refine ⟨scalar, ?_⟩
  simpa [Z] using
    (right_factor_scalar_compression_of_rankOne_transport
      T Rcompressed Lsub phi hphi Qright
      (TensorProduct.map (1 : Semantics.Operator N) Z) scalar
      hblock hTprobe hcompressedScalar)


end BPTCommutingProjectorModel

end Bounds
end QEC
