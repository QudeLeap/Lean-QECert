import QEC.Bounds.BPTDisentangling.SecondCut.ScalarTransport

/-!
# BPT second-cut tensor-factor cancellation algebra

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
Cancel the nonzero right tensor factor after transporting a compressed scalar
equation to a literal product block.  This is the algebraic tail shared by
the second-cut `Pi_AB'` and residual-factor scalar-compression arguments.
-/
theorem left_factor_scalar_compression_of_tensor_block
    {H K S : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup S] [InnerProductSpace Complex S]
    [Semantics.FiniteQuantumSystem S]
    (T : Semantics.UnitaryTransport S (Semantics.CompositeSystem H K))
    (P : Semantics.Operator H) (Q : Semantics.Operator K)
    (R L : Semantics.Operator S) (X : Semantics.Operator H) (scalar : Complex)
    (hblock : T.conjOperator R = TensorProduct.map P Q)
    (hQidem : Q * Q = Q) (hQ0 : Q ≠ 0)
    (hscalar : R * L * R = scalar • R)
    (hprobe : T.conjOperator L =
      TensorProduct.map X (1 : Semantics.Operator K)) :
    P * X * P = scalar • P := by
  have htarget :
      TensorProduct.map P Q * TensorProduct.map X (1 : Semantics.Operator K) *
          TensorProduct.map P Q = scalar • TensorProduct.map P Q := by
    calc
      TensorProduct.map P Q * TensorProduct.map X (1 : Semantics.Operator K) *
          TensorProduct.map P Q =
          T.conjOperator R * T.conjOperator L * T.conjOperator R := by
            rw [hblock, hprobe]
      _ = T.conjOperator (R * L * R) := by
        rw [Semantics.UnitaryTransport.conjOperator_mul,
          Semantics.UnitaryTransport.conjOperator_mul]
      _ = T.conjOperator (scalar • R) := congrArg T.conjOperator hscalar
      _ = scalar • T.conjOperator R :=
        T.conjOperatorLinearMap.map_smul scalar R
      _ = scalar • TensorProduct.map P Q := by rw [hblock]
  have hcombined : TensorProduct.map (P * X * P) Q =
      TensorProduct.map (scalar • P) Q := by
    calc
      TensorProduct.map (P * X * P) Q =
          TensorProduct.map P Q * TensorProduct.map X (1 : Semantics.Operator K) *
            TensorProduct.map P Q := by
              rw [← TensorProduct.map_mul, ← TensorProduct.map_mul]
              simp only [mul_one, hQidem]
      _ = scalar • TensorProduct.map P Q := htarget
      _ = TensorProduct.map (scalar • P) Q := by
        rw [TensorProduct.map_smul_left]
  obtain ⟨qvector, hqvector⟩ := DFunLike.ne_iff.mp hQ0
  apply LinearMap.ext
  intro vector
  apply tmul_left_eq_of_tmul_right_eq_of_ne_zero (Q qvector) hqvector
  have happly := congrArg (fun operator => operator (vector ⊗ₜ[Complex] qvector)) hcombined
  simpa only [TensorProduct.map_tmul, LinearMap.smul_apply] using happly

/-- A nonzero tensor block has a nonzero right factor. -/
theorem right_factor_ne_zero_of_nonzero_unitary_tensor_block
    {S H K : Type u} [NormedAddCommGroup S] [InnerProductSpace Complex S]
    [Semantics.FiniteQuantumSystem S] [NormedAddCommGroup H]
    [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K]
    (T : Semantics.UnitaryTransport S (Semantics.CompositeSystem H K))
    (R : Semantics.Operator S) (P : Semantics.Operator H) (Q : Semantics.Operator K)
    (hR : R ≠ 0) (hblock : T.conjOperator R = TensorProduct.map P Q) : Q ≠ 0 := by
  intro hQ
  apply hR
  calc
    R = T.symm.conjOperator (T.conjOperator R) :=
      (T.symm_conjOperator_conjOperator R).symm
    _ = T.symm.conjOperator (TensorProduct.map P Q) :=
      congrArg T.symm.conjOperator hblock
    _ = T.symm.conjOperator 0 := by simp [hQ]
    _ = 0 := by simp [Semantics.UnitaryTransport.conjOperator]

/--
An actual nonzero compressed projection block supplies all algebra needed for
the right tensor factor: idempotence and nonzeroness.
-/
theorem right_factor_idempotent_and_ne_zero_of_projection_block
    {S H K : Type u} [NormedAddCommGroup S] [InnerProductSpace Complex S]
    [Semantics.FiniteQuantumSystem S] [NormedAddCommGroup H]
    [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K]
    (T : Semantics.UnitaryTransport S (Semantics.CompositeSystem H K))
    (R : Semantics.Operator S) (P : Semantics.Operator H) (Q : Semantics.Operator K)
    (hR : R ≠ 0) (hP : P.IsSymmetricProjection) (hP0 : P ≠ 0)
    (hRprojection : R.IsSymmetricProjection)
    (hblock : T.conjOperator R = TensorProduct.map P Q) :
    Q * Q = Q ∧ Q ≠ 0 := by
  have hblockProjection : (TensorProduct.map P Q).IsSymmetricProjection :=
    isSymmetricProjection_congr
      ((isSymmetricProjection_conjOperator_iff T R).mpr hRprojection) hblock
  exact ⟨right_factor_idempotent_of_tensor_product_projection P Q
      hP.isIdempotentElem hP0 hblockProjection,
    right_factor_ne_zero_of_nonzero_unitary_tensor_block T R P Q hR hblock⟩

end BPTCommutingProjectorModel

end Bounds
end QEC
