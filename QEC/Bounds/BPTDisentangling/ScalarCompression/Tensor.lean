import QEC.Bounds.BPTDisentangling.ScalarCompression.ExternalResidual

/-!
# BPT tensor-factor compression algebra

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
Contracting a tensor block against an arbitrary right-factor vector records
the corresponding matrix coefficient on the left.  This is the concrete
operation used below to isolate the residual `Theta_{B'' C'}` block after the
first- and second-cut decompositions have been identified.
-/
theorem rightTensorCompression_tensorMap
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P : Semantics.Operator A) (Q : Semantics.Operator B) (eta : B) :
    rightTensorCompression eta (TensorProduct.map P Q) =
      (inner Complex eta (Q eta)) • P := by
  apply LinearMap.ext
  intro a
  change LinearMap.adjoint (overlapRightEmbedding A B eta)
      ((TensorProduct.map P Q) (overlapRightEmbedding A B eta a)) = _
  change LinearMap.adjoint (overlapRightEmbedding A B eta) (P a ⊗ₜ[Complex] Q eta) = _
  rw [adjoint_overlapRightEmbedding_apply_tmul]
  simp [LinearMap.smul_apply]

/-- Contracting a tensor-product operator against its left factor. -/
theorem leftTensorCompression_tensorMap
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P : Semantics.Operator A) (Q : Semantics.Operator B) (eta : A) :
    leftTensorCompression eta (TensorProduct.map P Q) =
      (inner Complex eta (P eta)) • Q := by
  apply LinearMap.ext
  intro b
  change LinearMap.adjoint (overlapLeftEmbedding A B eta)
      ((TensorProduct.map P Q) (overlapLeftEmbedding A B eta b)) = _
  change LinearMap.adjoint (overlapLeftEmbedding A B eta) (P eta ⊗ₜ[Complex] Q b) = _
  rw [adjoint_overlapLeftEmbedding_apply_tmul]
  simp [LinearMap.smul_apply]

/--
Left compression commutes with reassociating a tensor block, while preserving
the arbitrary right factor.  This is the associator-aware coefficient identity
needed to retain the BPT source projector `Pi_C''D` unchanged.
-/
theorem leftTensorCompression_tensorAssociator_conj_tensorMap
    {A W N : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    (eta : A) (P : Semantics.Operator (Semantics.CompositeSystem A W))
    (Q : Semantics.Operator N) :
    leftTensorCompression eta
      ((tensorAssociatorUnitary A W N).conjOperator (TensorProduct.map P Q)) =
      TensorProduct.map (leftTensorCompression eta P) Q := by
  unfold leftTensorCompression Semantics.UnitaryTransport.conjOperator
  change
    (LinearMap.adjoint (overlapLeftEmbedding A (Semantics.CompositeSystem W N) eta)).comp
        (((tensorAssociatorUnitary A W N).toLinearEquiv.toLinearMap.comp
          ((TensorProduct.map P Q).comp
            (tensorAssociatorUnitary A W N).toLinearEquiv.symm.toLinearMap)).comp
          (overlapLeftEmbedding A (Semantics.CompositeSystem W N) eta)) =
      TensorProduct.map
        ((LinearMap.adjoint (overlapLeftEmbedding A W eta)).comp
          (P.comp (overlapLeftEmbedding A W eta))) Q
  have hright :
      (tensorAssociatorUnitary A W N).toLinearEquiv.symm.toLinearMap.comp
        (overlapLeftEmbedding A (Semantics.CompositeSystem W N) eta) =
          TensorProduct.map (overlapLeftEmbedding A W eta) (1 : Semantics.Operator N) := by
    change (tensorAssociatorUnitary A W N).symm.toLinearEquiv.toLinearMap.comp
      (overlapLeftEmbedding A (Semantics.CompositeSystem W N) eta) = _
    exact tensorAssociatorUnitary_symm_comp_overlapLeftEmbedding A W N eta
  calc
    _ = ((LinearMap.adjoint (overlapLeftEmbedding A (Semantics.CompositeSystem W N) eta)).comp
          (tensorAssociatorUnitary A W N).toLinearEquiv.toLinearMap).comp
        ((TensorProduct.map P Q).comp
          ((tensorAssociatorUnitary A W N).toLinearEquiv.symm.toLinearMap.comp
            (overlapLeftEmbedding A (Semantics.CompositeSystem W N) eta))) := by
          simp only [LinearMap.comp_assoc]
    _ = (TensorProduct.map (LinearMap.adjoint (overlapLeftEmbedding A W eta))
          (1 : Semantics.Operator N)).comp
        ((TensorProduct.map P Q).comp
          (TensorProduct.map (overlapLeftEmbedding A W eta)
            (1 : Semantics.Operator N))) := by
          rw [adjoint_overlapLeftEmbedding_comp_tensorAssociatorUnitary A W N eta, hright]
    _ = TensorProduct.map
        ((LinearMap.adjoint (overlapLeftEmbedding A W eta)).comp
          (P.comp (overlapLeftEmbedding A W eta))) Q := by
          rw [← TensorProduct.map_comp, ← TensorProduct.map_comp]
          rfl

/--
An actual joint rank-one block can be reconstructed through the two source
associators without collapsing its arbitrary final projector.  The hypothesis
is the literal common active block, and the conclusion is the `hcommon` form
consumed by the BPT residual argument.
-/
theorem tensor_factor_eq_of_rankOne_joint_block_associator
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (phi : A) (hphi : ‖phi‖ = 1)
    (Pleft : Semantics.Operator (Semantics.CompositeSystem A (Semantics.CompositeSystem B C)))
    (Qright : Semantics.Operator (Semantics.CompositeSystem B (Semantics.CompositeSystem C D)))
    (P_D : Semantics.Operator D)
    (hjoint :
      (unitaryLTensor A (tensorAssociatorUnitary B C D).symm).conjOperator
          (TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap Qright) =
        (tensorAssociatorUnitary A (Semantics.CompositeSystem B C) D).conjOperator
          (TensorProduct.map Pleft P_D)) :
    (tensorAssociatorUnitary B C D).symm.conjOperator Qright =
      TensorProduct.map (leftTensorCompression phi Pleft) P_D := by
  have hcompressed := congrArg (leftTensorCompression phi) hjoint
  have hleftTransport :
      leftTensorCompression phi
          ((unitaryLTensor A (tensorAssociatorUnitary B C D).symm).conjOperator
            (TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap Qright)) =
        (tensorAssociatorUnitary B C D).symm.conjOperator
          (leftTensorCompression phi
            (TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap Qright)) := by
    exact
      (leftInteractionCoefficient_unitaryLTensor_conjOperator
        (tensorAssociatorUnitary B C D).symm
        (TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap Qright)
        phi phi)
  have hphiInner : inner Complex phi phi = 1 := by
    rw [inner_self_eq_norm_sq_to_K]
    simpa [hphi]
  have hrankApply :
      (InnerProductSpace.rankOne Complex phi phi).toLinearMap phi = phi := by
    simp [InnerProductSpace.rankOne_apply, hphi]
  have hrank :
      leftTensorCompression phi
          (TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap Qright) =
        Qright := by
    rw [leftTensorCompression_tensorMap, hrankApply, hphiInner, one_smul]
  calc
    (tensorAssociatorUnitary B C D).symm.conjOperator Qright =
        (tensorAssociatorUnitary B C D).symm.conjOperator
          (leftTensorCompression phi
            (TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap Qright)) := by
          rw [hrank]
    _ = leftTensorCompression phi
          ((unitaryLTensor A (tensorAssociatorUnitary B C D).symm).conjOperator
            (TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap Qright)) :=
          hleftTransport.symm
    _ = leftTensorCompression phi
          ((tensorAssociatorUnitary A (Semantics.CompositeSystem B C) D).conjOperator
            (TensorProduct.map Pleft P_D)) := hcompressed
    _ = TensorProduct.map (leftTensorCompression phi Pleft) P_D :=
          leftTensorCompression_tensorAssociator_conj_tensorMap phi Pleft P_D


end BPTCommutingProjectorModel

end Bounds
end QEC
