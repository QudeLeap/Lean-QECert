import QEC.Bounds.BPTDisentangling.ScalarCompression.ResidualProjection

/-!
# BPT residual two-sided scalar compression

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

/-- Compression is linear in the ambient block. -/
theorem rightTensorCompression_smul
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (eta : B) (scalar : Complex) (T : Semantics.Operator (Semantics.CompositeSystem A B)) :
    rightTensorCompression eta (scalar • T) = scalar • rightTensorCompression eta T := by
  apply LinearMap.ext
  intro a
  simp [rightTensorCompression, LinearMap.comp_apply]

/-- Scalar compression on `Theta tensor P_D` descends to the literal residual `Theta`. -/
theorem secondCutResidualTheta_scalar_compression_of_common_first_second_block
    {N C D : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (eta : D) (heta : ‖eta‖ = 1) (P_D : Semantics.Operator D)
    (hP_D : P_D.IsSymmetricProjection) (hPeta : P_D eta = eta)
    (Qright : Semantics.Operator (Semantics.CompositeSystem N (Semantics.CompositeSystem C D)))
    (Theta Z : Semantics.Operator (Semantics.CompositeSystem N C))
    (hcommon : (tensorAssociatorUnitary N C D).symm.conjOperator Qright =
      TensorProduct.map Theta P_D)
    (hscalar : ∃ scalar : Complex,
      (tensorAssociatorUnitary N C D).symm.conjOperator Qright *
          TensorProduct.map Z (1 : Semantics.Operator D) *
          (tensorAssociatorUnitary N C D).symm.conjOperator Qright =
        scalar • (tensorAssociatorUnitary N C D).symm.conjOperator Qright) :
    ∃ scalar : Complex, Theta * Z * Theta = scalar • Theta := by
  rcases hscalar with ⟨scalar, hscalar⟩
  have hinner : inner Complex eta (P_D eta) = 1 := by
    rw [hPeta, inner_self_eq_norm_sq_to_K, heta]
    norm_num
  have hcompress (T : Semantics.Operator (Semantics.CompositeSystem N C)) :
      rightTensorCompression eta (TensorProduct.map T P_D) = T := by
    rw [rightTensorCompression_tensorMap, hinner, one_smul]
  have hmap : TensorProduct.map (Theta * Z * Theta) P_D =
      TensorProduct.map Theta P_D * TensorProduct.map Z (1 : Semantics.Operator D) *
        TensorProduct.map Theta P_D := by
    symm
    calc
      TensorProduct.map Theta P_D * TensorProduct.map Z (1 : Semantics.Operator D) *
          TensorProduct.map Theta P_D =
          TensorProduct.map (Theta * Z) (P_D * (1 : Semantics.Operator D)) *
            TensorProduct.map Theta P_D := by rw [← TensorProduct.map_mul]
      _ = TensorProduct.map ((Theta * Z) * Theta)
          ((P_D * (1 : Semantics.Operator D)) * P_D) := by rw [← TensorProduct.map_mul]
      _ = TensorProduct.map (Theta * Z * Theta) P_D := by
        rw [mul_one, hP_D.isIdempotentElem]
  refine ⟨scalar, ?_⟩
  calc
    Theta * Z * Theta = rightTensorCompression eta (TensorProduct.map (Theta * Z * Theta) P_D) :=
      (hcompress _).symm
    _ = rightTensorCompression eta
        (TensorProduct.map Theta P_D * TensorProduct.map Z (1 : Semantics.Operator D) *
          TensorProduct.map Theta P_D) := congrArg (rightTensorCompression eta) hmap
    _ = rightTensorCompression eta
        ((tensorAssociatorUnitary N C D).symm.conjOperator Qright *
          TensorProduct.map Z (1 : Semantics.Operator D) *
          (tensorAssociatorUnitary N C D).symm.conjOperator Qright) := by rw [← hcommon]
    _ = rightTensorCompression eta
        (scalar • (tensorAssociatorUnitary N C D).symm.conjOperator Qright) :=
      congrArg (rightTensorCompression eta) hscalar
    _ = scalar • rightTensorCompression eta
        ((tensorAssociatorUnitary N C D).symm.conjOperator Qright) :=
      rightTensorCompression_smul eta scalar _
    _ = scalar • Theta := by
      rw [hcommon, rightTensorCompression_tensorMap, hinner, one_smul]

/--
The two residual erasures now act on one actual `Theta_{B'' C'}` while the
source complement projector `P_D` is retained.  This is the exact input to
the remaining two-factor no-cloning `finrank <= 1` closure.
-/
theorem secondCutResidualTheta_two_sided_scalar_compressions_for_noCloning
    {N C D : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (eta : D) (heta : ‖eta‖ = 1) (P_D : Semantics.Operator D)
    (hP_D : P_D.IsSymmetricProjection) (hPeta : P_D eta = eta)
    (Qright : Semantics.Operator (Semantics.CompositeSystem N (Semantics.CompositeSystem C D)))
    (Theta : Semantics.Operator (Semantics.CompositeSystem N C))
    (hcommon : (tensorAssociatorUnitary N C D).symm.conjOperator Qright =
      TensorProduct.map Theta P_D)
    (hinternal : ∀ X : Semantics.Operator N, ∃ scalar : Complex,
      (tensorAssociatorUnitary N C D).symm.conjOperator Qright *
          TensorProduct.map (TensorProduct.map X (1 : Semantics.Operator C))
            (1 : Semantics.Operator D) *
          (tensorAssociatorUnitary N C D).symm.conjOperator Qright =
        scalar • (tensorAssociatorUnitary N C D).symm.conjOperator Qright)
    (hexternal : ∀ Y : Semantics.Operator C, ∃ scalar : Complex,
      (tensorAssociatorUnitary N C D).symm.conjOperator Qright *
          TensorProduct.map (TensorProduct.map (1 : Semantics.Operator N) Y)
            (1 : Semantics.Operator D) *
          (tensorAssociatorUnitary N C D).symm.conjOperator Qright =
        scalar • (tensorAssociatorUnitary N C D).symm.conjOperator Qright) :
    (∀ X : Semantics.Operator N, ∃ scalar : Complex,
      Theta * TensorProduct.map X (1 : Semantics.Operator C) * Theta = scalar • Theta) ∧
    (∀ Y : Semantics.Operator C, ∃ scalar : Complex,
      Theta * TensorProduct.map (1 : Semantics.Operator N) Y * Theta = scalar • Theta) := by
  constructor
  · intro X
    exact secondCutResidualTheta_scalar_compression_of_common_first_second_block
      eta heta P_D hP_D hPeta Qright Theta (TensorProduct.map X (1 : Semantics.Operator C))
        hcommon (hinternal X)
  · intro Y
    exact secondCutResidualTheta_scalar_compression_of_common_first_second_block
      eta heta P_D hP_D hPeta Qright Theta (TensorProduct.map (1 : Semantics.Operator N) Y)
        hcommon (hexternal Y)

end BPTCommutingProjectorModel

end Bounds
end QEC
