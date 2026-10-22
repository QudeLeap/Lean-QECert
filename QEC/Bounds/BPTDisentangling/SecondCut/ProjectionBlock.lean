import QEC.Bounds.BPTDisentangling.SecondCut.LeftPhysical

/-!
# BPT second-cut compressed projection block algebra

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

/-- A nonzero fixed right tensor factor can be cancelled from an equality of pure tensors. -/
theorem tmul_left_eq_of_tmul_right_eq_of_ne_zero
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    {left left' : H} (right : K) (hright : right ≠ 0)
    (h : left ⊗ₜ[Complex] right = left' ⊗ₜ[Complex] right) : left = left' := by
  have happly := congrArg (LinearMap.adjoint (overlapRightEmbedding H K right)) h
  rw [adjoint_overlapRightEmbedding_apply_tmul,
    adjoint_overlapRightEmbedding_apply_tmul] at happly
  have hinner : inner Complex right right ≠ 0 := inner_self_ne_zero.mpr hright
  calc
    left = (inner Complex right right)⁻¹ • ((inner Complex right right) • left) := by
      rw [smul_smul, inv_mul_cancel₀ hinner, one_smul]
    _ = (inner Complex right right)⁻¹ • ((inner Complex right right) • left') :=
      congrArg ((inner Complex right right)⁻¹ • ·) happly
    _ = left' := by rw [smul_smul, inv_mul_cancel₀ hinner, one_smul]

/-- A nonzero fixed left tensor factor can be cancelled from an equality of pure tensors. -/
theorem tmul_right_eq_of_tmul_left_eq_of_ne_zero
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (left : H) (hleft : left ≠ 0) {right right' : K}
    (h : left ⊗ₜ[Complex] right = left ⊗ₜ[Complex] right') : right = right' := by
  have happly := congrArg (LinearMap.adjoint (overlapLeftEmbedding H K left)) h
  rw [adjoint_overlapLeftEmbedding_apply_tmul,
    adjoint_overlapLeftEmbedding_apply_tmul] at happly
  have hinner : inner Complex left left ≠ 0 := inner_self_ne_zero.mpr hleft
  calc
    right = (inner Complex left left)⁻¹ • ((inner Complex left left) • right) := by
      rw [smul_smul, inv_mul_cancel₀ hinner, one_smul]
    _ = (inner Complex left left)⁻¹ • ((inner Complex left left) • right') :=
      congrArg ((inner Complex left left)⁻¹ • ·) happly
    _ = right' := by rw [smul_smul, inv_mul_cancel₀ hinner, one_smul]

/-- The literal second-cut code lift is an orthogonal projection. -/
theorem secondCutCodeLift_isSymmetricProjection
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.secondCutCodeLift region).IsSymmetricProjection := by
  have hfull : M.fullCodeProjector.IsSymmetricProjection := by
    constructor
    · exact M.fullCodeProjector_idempotent
    · exact (LinearMap.isSymmetric_iff_isSelfAdjoint M.fullCodeProjector).mpr
        M.fullCodeProjector_adjoint_eq_self
  have htransported :
      ((M.secondCutGlobalCoordinateTransport region).conjOperator
        M.fullCodeProjector).IsSymmetricProjection :=
    (isSymmetricProjection_conjOperator_iff
      (M.secondCutGlobalCoordinateTransport region) M.fullCodeProjector).mpr hfull
  simpa only [M.secondCutGlobalCoordinateTransport_conj_fullCodeProjector region] using
    htransported

/-- The second-cut code lift commutes with compression to any selected sector. -/
theorem secondCutCodeLift_commute_sectorCompressionProjection
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)) :
    let A := M.fourFactorA region
    let H := component.1.restrictScalars Complex
    let CD := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)
    let J := tensorTripleSubtypeEmbedding (A := A) (C := CD) H
    Commute (M.secondCutCodeLift region) (J.comp (LinearMap.adjoint J)) := by
  dsimp only
  have hself : LinearMap.adjoint (M.fourFactorProjectorABLocal region) =
      M.fourFactorProjectorABLocal region :=
    (M.secondCutProjectorAB_isSymmetricProjection region).isSymmetric.adjoint_eq
  have hover : Commute
      (overlapLiftLeft
        (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
        (M.fourFactorProjectorABLocal region))
      (overlapLiftRight (A := M.fourFactorA region)
        (M.secondCutProjectorBbarM region)) :=
    M.secondCut_overlap_commute region
  rw [show
    (tensorTripleSubtypeEmbedding (A := M.fourFactorA region)
        (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
        (component.1.restrictScalars Complex)).comp
      (LinearMap.adjoint (tensorTripleSubtypeEmbedding (A := M.fourFactorA region)
        (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
        (component.1.restrictScalars Complex))) =
      M.secondCutSectorLift region component by
        simpa only [secondCutSectorLift] using
          (tensorTripleSubtypeEmbedding_comp_adjoint_eq_leftIsotypicSectorLift
            (M.fourFactorProjectorABLocal region) component
            (C := Semantics.CompositeSystem
              (M.fourFactorC region) (M.fourFactorD region)))]
  simpa only [secondCutCodeLift, secondCutSectorLift] using
    (overlap_product_commutes_leftIsotypicSectorLift
      (M.fourFactorProjectorABLocal region) (M.secondCutProjectorBbarM region)
      hself hover component)

/--
The active second-cut code compressed to its selected isotypic sector is an
orthogonal projection.  This follows from the actual full code projector and
the proved sector commutation, and is used to obtain idempotence of `Qright`.
-/
theorem secondCut_compressedCode_isSymmetricProjection
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)) :
    let A := M.fourFactorA region
    let H := component.1.restrictScalars Complex
    let CD := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)
    let J := tensorTripleSubtypeEmbedding (A := A) (C := CD) H
    ((LinearMap.adjoint J).comp ((M.secondCutCodeLift region).comp J)).IsSymmetricProjection := by
  dsimp only
  exact isSymmetricProjection_of_isometric_compression_commuting
    (tensorTripleSubtypeEmbedding (A := M.fourFactorA region)
      (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
      (component.1.restrictScalars Complex))
    (LinearMap.adjoint (tensorTripleSubtypeEmbedding (A := M.fourFactorA region)
      (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
      (component.1.restrictScalars Complex)))
    (M.secondCutCodeLift region)
    (adjoint_tensorTripleSubtypeEmbedding_comp_tensorTripleSubtypeEmbedding
      (A := M.fourFactorA region)
      (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
      (component.1.restrictScalars Complex))
    rfl (M.secondCutCodeLift_isSymmetricProjection region)
    (M.secondCutCodeLift_commute_sectorCompressionProjection region component)

/--
In a nonzero tensor-block code projection, idempotence of a nonzero left
factor forces idempotence of the right factor.  This is the minimal algebra
needed to cancel the residual block in the hM scalar-compression argument.
-/
theorem right_factor_idempotent_of_tensor_product_projection
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (P : Semantics.Operator H) (Q : Semantics.Operator K)
    (hP : P * P = P) (hP0 : P ≠ 0)
    (hPQ : (TensorProduct.map P Q).IsSymmetricProjection) : Q * Q = Q := by
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hP0
  have hEq : TensorProduct.map P (Q * Q) = TensorProduct.map P Q := by
    calc
      TensorProduct.map P (Q * Q) = TensorProduct.map (P * P) (Q * Q) := by rw [hP]
      _ = TensorProduct.map P Q * TensorProduct.map P Q := TensorProduct.map_mul _ _ _ _
      _ = TensorProduct.map P Q := hPQ.isIdempotentElem
  apply LinearMap.ext
  intro y
  apply tmul_right_eq_of_tmul_left_eq_of_ne_zero (P x) hx
  have happly := congrArg (fun operator => operator (x ⊗ₜ[Complex] y)) hEq
  simpa only [TensorProduct.map_tmul] using happly

end BPTCommutingProjectorModel

end Bounds
end QEC
