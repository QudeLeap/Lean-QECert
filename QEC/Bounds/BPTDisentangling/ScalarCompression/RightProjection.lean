import QEC.Bounds.BPTDisentangling.ScalarCompression.LeftRankOneBlock

/-!
# BPT second-cut right projection

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

/--
When a nonzero normalized rank-one left factor tensors with an orthogonal
projection, the right factor is itself an orthogonal projection.  This turns
the second-cut residual into the concrete code projector to which the two
residual erasure arguments are applied.
-/
theorem right_factor_isSymmetricProjection_of_rankOne_tensor_projection
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (phi : H) (hphi : ‖phi‖ = 1) (Q : Semantics.Operator K)
    (hprojection :
      LinearMap.IsSymmetricProjection
        (TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap Q)) :
    LinearMap.IsSymmetricProjection Q := by
  let P : Semantics.Operator H := (InnerProductSpace.rankOne Complex phi phi).toLinearMap
  have hP : P.IsSymmetricProjection := by
    simpa [P] using
      (InnerProductSpace.isSymmetricProjection_rankOne_self (𝕜 := Complex) hphi)
  have hphi0 : phi ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hphi
    norm_num at hphi
  have hP0 : P ≠ 0 := by
    intro hzero
    have happly := congrArg (fun operator => operator phi) hzero
    have hinner : inner Complex phi phi = 1 := by
      rw [inner_self_eq_norm_sq_to_K]
      simpa [hphi]
    change inner Complex phi phi • phi = 0 at happly
    rw [hinner, one_smul] at happly
    exact hphi0 happly
  have hidempotent : Q * Q = Q := by
    exact right_factor_idempotent_of_tensor_product_projection P Q
      hP.isIdempotentElem hP0 (by simpa [P] using hprojection)
  have hselfTensor :
      LinearMap.adjoint (TensorProduct.map P Q) = TensorProduct.map P Q :=
    (LinearMap.isSymmetric_iff_isSelfAdjoint _).mp hprojection.isSymmetric
  have hself : LinearMap.adjoint Q = Q := by
    apply LinearMap.ext
    intro vector
    have hmap : TensorProduct.map P (LinearMap.adjoint Q) = TensorProduct.map P Q := by
      calc
        TensorProduct.map P (LinearMap.adjoint Q) =
            LinearMap.adjoint (TensorProduct.map P Q) := by
              rw [TensorProduct.adjoint_map, hP.isSymmetric.adjoint_eq]
        _ = TensorProduct.map P Q := hselfTensor
    have happly := congrArg (fun operator => operator (phi ⊗ₜ[Complex] vector)) hmap
    have hinner : inner Complex phi phi = 1 := by
      rw [inner_self_eq_norm_sq_to_K]
      simpa [hphi]
    have htensor : phi ⊗ₜ[Complex] (LinearMap.adjoint Q) vector =
        phi ⊗ₜ[Complex] Q vector := by
      simpa [P, InnerProductSpace.rankOne_apply, hinner, hphi] using happly
    apply ext_inner_left Complex
    intro test
    have hinnerTensor := congrArg
      (fun tensor => inner Complex (phi ⊗ₜ[Complex] test) tensor) htensor
    simpa only [TensorProduct.inner_tmul, hinner, one_mul] using hinnerTensor
  constructor
  · exact hidempotent
  · exact (LinearMap.isSymmetric_iff_isSelfAdjoint _).mpr hself

set_option maxHeartbeats 4000000 in
/--
The residual second-cut factor `Pi_B''bar(M)` is an actual orthogonal
projection once the hM-forced `Pi_AB'` rank-one block has been substituted.
This is the residual code projector used immediately in the two-cut
no-cloning closure.
-/
theorem secondCut_Qright_isSymmetricProjection_of_region_recoverable
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
    let J := tensorTripleSubtypeEmbedding (A := A) (C := CD) H
    let Rcompressed : Semantics.Operator (Semantics.CompositeSystem
        (Semantics.CompositeSystem A H) CD) :=
      (LinearMap.adjoint J).comp ((M.secondCutCodeLift region).comp J)
    ∀ (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W0 N)),
      let T := isotypicSectorBlockTransportLeft A H W0 N CD U
      ∀
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
      LinearMap.IsSymmetricProjection Qright := by
  intro A H W0 N CD J Rcompressed U T Pleft Qright hactive hleft hright
  rcases M.secondCut_compressed_overlap_rankOne_block_product_of_region_recoverable
    region hcode hM component W U Pleft Qright ⟨hactive, hleft, hright⟩ with
    ⟨phi, hphi, hblockEq⟩
  have hcompressed : LinearMap.IsSymmetricProjection Rcompressed :=
    M.secondCut_compressedCode_isSymmetricProjection region component
  have htransported : LinearMap.IsSymmetricProjection (T.conjOperator Rcompressed) :=
    (isSymmetricProjection_conjOperator_iff T Rcompressed).mpr hcompressed
  have hblock : LinearMap.IsSymmetricProjection
      (TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap Qright) :=
    (congrArg (fun operator => LinearMap.IsSymmetricProjection operator) hblockEq).mp htransported
  exact right_factor_isSymmetricProjection_of_rankOne_tensor_projection phi hphi Qright hblock

end BPTCommutingProjectorModel

end Bounds
end QEC
