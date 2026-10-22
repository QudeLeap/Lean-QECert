import QEC.Bounds.BPTDisentangling.ScalarCompression.Coordinates

/-!
# BPT second-cut left-probe transport

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

set_option maxHeartbeats 300000 in
/--
Compress the physical hM no-information equation to the selected second-cut
sector for an arbitrary left-factor probe.
-/
theorem secondCut_Pleft_compressed_scalar_for_left_probe
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hM : M.RegionErasureRecoverable region)
    (H W0 : Submodule Complex (M.fourFactorB region))
    {n : Nat} [NeZero n]
    (J : Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) H)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) →ₗ[Complex]
      Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)))
    (hJ : J = tensorTripleSubtypeEmbedding (A := M.fourFactorA region)
      (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) H)
    (Rcompressed : Semantics.Operator
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) H)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))
    (hreconstruct : M.secondCutCodeLift region =
      J.comp (Rcompressed.comp (LinearMap.adjoint J)))
    (U : Semantics.UnitaryTransport H
      (Semantics.CompositeSystem W0 (isotypicLiftedMultiplicity.{0} n)))
    (X : Semantics.Operator (Semantics.CompositeSystem (M.fourFactorA region) W0)) :
    ∃ scalar : Complex,
      Rcompressed *
          overlapLiftLeft
            (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
            ((unitaryLTensor (M.fourFactorA region) U).symm.conjOperator
              (rightTensorExtensionAfterLeft (M.fourFactorA region) W0
                (isotypicLiftedMultiplicity.{0} n) X)) *
          Rcompressed =
        scalar • Rcompressed := by
    let Esub : Semantics.Operator (Semantics.CompositeSystem (M.fourFactorA region) H) :=
      (unitaryLTensor (M.fourFactorA region) U).symm.conjOperator
        (rightTensorExtensionAfterLeft (M.fourFactorA region)
          W0 (isotypicLiftedMultiplicity.{0} n) X)
    rcases M.secondCut_compressed_scalar_for_left_subtype_probe
      region hM H J hJ Rcompressed hreconstruct Esub with ⟨scalar, hscalar⟩
    exact ⟨scalar, hscalar⟩

/-- The second-cut block transport sends the selected left probe to `X tensor 1`. -/
theorem secondCut_Pleft_left_probe_transport
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (H W0 : Submodule Complex (M.fourFactorB region))
    {n : Nat} [NeZero n]
    :
    let A := M.fourFactorA region
    let N := isotypicLiftedMultiplicity.{0} n
    let CD := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)
    ∀ (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W0 N))
      (X : Semantics.Operator (Semantics.CompositeSystem A W0)),
      (isotypicSectorBlockTransportLeft A H W0 N CD U).conjOperator
          (overlapLiftLeft (C := CD)
            ((unitaryLTensor A U).symm.conjOperator
              (rightTensorExtensionAfterLeft A W0 N X))) =
        TensorProduct.map X (1 : Semantics.Operator (Semantics.CompositeSystem N CD)) := by
  dsimp only
  intro U X
  let A := M.fourFactorA region
  let B := M.fourFactorB region
  let N := isotypicLiftedMultiplicity.{0} n
  let CD := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)
  let T := isotypicSectorBlockTransportLeft A H W0 N CD U
  let Esub : Semantics.Operator (Semantics.CompositeSystem A H) :=
    (unitaryLTensor A U).symm.conjOperator
      (rightTensorExtensionAfterLeft A W0 N X)
  let Lsub := overlapLiftLeft (C := CD) Esub
  have hprobeTransport : (unitaryLTensor A U).conjOperator Esub =
      rightTensorExtensionAfterLeft A W0 N X := by
    simpa [Esub] using
      (unitaryLTensor A U).conjOperator_symm_conjOperator
        (rightTensorExtensionAfterLeft A W0 N X)
  simpa [T, Lsub, A, N, CD] using
    (isotypicSectorBlockTransportLeft_conj_overlapLiftLeft U Esub X hprobeTransport)

end BPTCommutingProjectorModel

end Bounds
end QEC
