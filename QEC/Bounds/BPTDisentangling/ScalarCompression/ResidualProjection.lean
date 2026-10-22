import QEC.Bounds.BPTDisentangling.ScalarCompression.Tensor

/-!
# BPT residual projection algebra

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

/-- A nonzero orthogonal projection has a normalized fixed vector in its range. -/
theorem exists_normalized_fixed_vector_of_nonzero_isSymmetricProjection
    {D : Type u} [NormedAddCommGroup D] [InnerProductSpace Complex D]
    [Semantics.FiniteQuantumSystem D]
    (P : Semantics.Operator D) (hP : P.IsSymmetricProjection) (hP0 : P ≠ 0) :
    ∃ eta : D, ‖eta‖ = 1 ∧ P eta = eta := by
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hP0
  let v : D := P x
  have hv : v ≠ 0 := by simpa [v] using hx
  let eta : D := (‖v‖ : Complex)⁻¹ • v
  have hnormv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have heta : ‖eta‖ = 1 := by
    dsimp [eta]
    rw [norm_smul, norm_inv]
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg v)] using inv_mul_cancel₀ hnormv
  have hfixedv : P v = v := by
    dsimp [v]
    have happly := congrArg (fun operator => operator x) hP.isIdempotentElem
    simpa [Module.End.mul_eq_comp] using happly
  have hfixed : P eta = eta := by
    dsimp [eta]
    rw [LinearMap.map_smul, hfixedv]
  exact ⟨eta, heta, hfixed⟩

/--
The residual source factor `Theta_{B'' C'}` is a literal compression of the
reassociated second-cut block.  The source complement factor remains the
arbitrary projection `P_D`, rather than being replaced by a rank-one state.
-/
noncomputable def secondCutResidualTheta
    {N C D : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (eta : D) (Qright : Semantics.Operator
      (Semantics.CompositeSystem N (Semantics.CompositeSystem C D))) :
    Semantics.Operator (Semantics.CompositeSystem N C) :=
  rightTensorCompression eta
    ((tensorAssociatorUnitary N C D).symm.conjOperator Qright)

/-- The literal residual compression recovers `Theta` from `Theta tensor P_D`. -/
theorem secondCutResidualTheta_eq_of_common_first_second_block
    {N C D : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (eta : D) (heta : ‖eta‖ = 1) (P_D : Semantics.Operator D) (hPeta : P_D eta = eta)
    (Qright : Semantics.Operator (Semantics.CompositeSystem N (Semantics.CompositeSystem C D)))
    (Theta : Semantics.Operator (Semantics.CompositeSystem N C))
    (hcommon : (tensorAssociatorUnitary N C D).symm.conjOperator Qright =
      TensorProduct.map Theta P_D) :
    secondCutResidualTheta eta Qright = Theta := by
  unfold secondCutResidualTheta
  rw [hcommon, rightTensorCompression_tensorMap, hPeta, inner_self_eq_norm_sq_to_K, heta]
  norm_num

/-- The nonzero common block has a nonzero residual `Theta_{B'' C'}` factor. -/
theorem secondCutResidualTheta_ne_zero_of_common_first_second_block
    {N C D : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (eta : D) (heta : ‖eta‖ = 1) (P_D : Semantics.Operator D) (hPeta : P_D eta = eta)
    (Qright : Semantics.Operator (Semantics.CompositeSystem N (Semantics.CompositeSystem C D)))
    (Theta : Semantics.Operator (Semantics.CompositeSystem N C)) (hQright : Qright ≠ 0)
    (hcommon : (tensorAssociatorUnitary N C D).symm.conjOperator Qright =
      TensorProduct.map Theta P_D) :
    secondCutResidualTheta eta Qright ≠ 0 := by
  rw [secondCutResidualTheta_eq_of_common_first_second_block eta heta P_D hPeta Qright Theta hcommon]
  intro hTheta
  apply hQright
  calc
    Qright = (tensorAssociatorUnitary N C D).conjOperator
        ((tensorAssociatorUnitary N C D).symm.conjOperator Qright) :=
      (tensorAssociatorUnitary N C D).conjOperator_symm_conjOperator Qright |>.symm
    _ = (tensorAssociatorUnitary N C D).conjOperator (TensorProduct.map Theta P_D) := by
      rw [hcommon]
    _ = (tensorAssociatorUnitary N C D).conjOperator 0 := by
      rw [hTheta, TensorProduct.map_zero_left]
    _ = 0 := by simp [Semantics.UnitaryTransport.conjOperator]

/-- A nonzero projection factor transfers projection structure to `Theta`. -/
theorem right_factor_isSymmetricProjection_of_tensor_product_projection
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (P : Semantics.Operator H) (Q : Semantics.Operator K)
    (hP : P.IsSymmetricProjection) (hP0 : P ≠ 0)
    (hprojection : (TensorProduct.map P Q).IsSymmetricProjection) :
    Q.IsSymmetricProjection := by
  have hidempotent : Q * Q = Q :=
    right_factor_idempotent_of_tensor_product_projection P Q hP.isIdempotentElem hP0 hprojection
  have hselfTensor : LinearMap.adjoint (TensorProduct.map P Q) = TensorProduct.map P Q :=
    (LinearMap.isSymmetric_iff_isSelfAdjoint _).mp hprojection.isSymmetric
  have hself : LinearMap.adjoint Q = Q := by
    obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hP0
    apply LinearMap.ext
    intro vector
    apply tmul_right_eq_of_tmul_left_eq_of_ne_zero (P x) hx
    have hmap : TensorProduct.map P (LinearMap.adjoint Q) = TensorProduct.map P Q := by
      calc
        TensorProduct.map P (LinearMap.adjoint Q) = LinearMap.adjoint (TensorProduct.map P Q) := by
          rw [TensorProduct.adjoint_map, hP.isSymmetric.adjoint_eq]
        _ = TensorProduct.map P Q := hselfTensor
    have happly := congrArg (fun operator => operator (x ⊗ₜ[Complex] vector)) hmap
    simpa only [TensorProduct.map_tmul] using happly
  constructor
  · exact hidempotent
  · exact (LinearMap.isSymmetric_iff_isSelfAdjoint _).mpr hself

/-- The general source block `Theta tensor P_D` transfers projection structure to `Theta`. -/
theorem secondCutResidualTheta_isSymmetricProjection_of_common_first_second_block
    {N C D : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (eta : D) (heta : ‖eta‖ = 1) (P_D : Semantics.Operator D)
    (hP_D : P_D.IsSymmetricProjection) (hP_D0 : P_D ≠ 0) (hPeta : P_D eta = eta)
    (Qright : Semantics.Operator (Semantics.CompositeSystem N (Semantics.CompositeSystem C D)))
    (Theta : Semantics.Operator (Semantics.CompositeSystem N C))
    (hQright : Qright.IsSymmetricProjection)
    (hcommon : (tensorAssociatorUnitary N C D).symm.conjOperator Qright =
      TensorProduct.map Theta P_D) :
    (secondCutResidualTheta eta Qright).IsSymmetricProjection := by
  have hblock : (TensorProduct.map Theta P_D).IsSymmetricProjection := by
    rw [← hcommon]
    exact (isSymmetricProjection_conjOperator_iff (tensorAssociatorUnitary N C D).symm Qright).mpr
      hQright
  have hswapped : (TensorProduct.map P_D Theta).IsSymmetricProjection := by
    rw [← tensorSwapUnitary_conj_tensorMap]
    exact (isSymmetricProjection_conjOperator_iff
      (tensorSwapUnitary (Semantics.CompositeSystem N C) D) _).mpr hblock
  rw [secondCutResidualTheta_eq_of_common_first_second_block eta heta P_D hPeta Qright Theta hcommon]
  exact right_factor_isSymmetricProjection_of_tensor_product_projection P_D Theta hP_D hP_D0 hswapped


end BPTCommutingProjectorModel

end Bounds
end QEC
