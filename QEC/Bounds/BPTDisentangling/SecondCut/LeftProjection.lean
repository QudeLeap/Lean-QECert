import QEC.Bounds.BPTDisentangling.SecondCut.Projection

/-!
# BPT second-cut left-factor projection chain

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
The second-cut BV03 left block `Pleft` is an orthogonal projection.  It is
obtained by restricting the physical `Pi_AB` projector to the hM-selected
sector and reflecting the displayed `Pleft tensor 1` block equality.
-/
theorem secondCut_Pleft_isSymmetricProjection
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
    ∀ (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W0 N))
      (Pleft : Semantics.Operator (Semantics.CompositeSystem A W0)),
      (unitaryLTensor A U).conjOperator
          (overlapProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) component) =
          rightTensorExtensionAfterLeft A W0 N Pleft →
      @LinearMap.IsSymmetricProjection Complex
        (Semantics.CompositeSystem A W0) _ _ _ Pleft := by
  dsimp only
  intro U Pleft hleft
  have hcompressed : (overlapProjectorOnIsotypicComponent
      (M.fourFactorProjectorABLocal region) component).IsSymmetricProjection :=
    overlapProjectorOnIsotypicComponent_isSymmetricProjection
      (M.fourFactorProjectorABLocal region)
      (M.secondCutProjectorAB_isSymmetricProjection region) component
  let eta := isotypicLiftedMultiplicityUnitVector.{0} n
  have heta : ‖eta‖ = 1 := norm_isotypicLiftedMultiplicityUnitVector.{0} n
  exact isSymmetricProjection_of_unitary_eq_rightTensorExtension
    U (overlapProjectorOnIsotypicComponent
      (M.fourFactorProjectorABLocal region) component) Pleft eta heta hcompressed hleft

/-- The literal second-cut source code lift is nonzero whenever the code carrier is nonzero. -/
theorem secondCutCodeLift_ne_zero_of_nonzero_code
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥) :
    M.secondCutCodeLift region ≠ 0 := by
  have hfullNonzero : M.fullCodeProjector ≠ 0 := by
    intro hzero
    apply hcode
    apply le_antisymm
    · intro vector hvector
      have hfixed : M.fullCodeProjector vector = vector :=
        M.codeSpace.projector_eq_self_of_mem hvector
      rw [hzero] at hfixed
      simpa using hfixed.symm
    · exact bot_le
  intro hzero
  apply hfullNonzero
  calc
    M.fullCodeProjector =
        (M.secondCutGlobalCoordinateTransport region).symm.conjOperator
          ((M.secondCutGlobalCoordinateTransport region).conjOperator
            M.fullCodeProjector) :=
      (M.secondCutGlobalCoordinateTransport region).symm_conjOperator_conjOperator _ |>.symm
    _ = (M.secondCutGlobalCoordinateTransport region).symm.conjOperator
          (M.secondCutCodeLift region) := by
      rw [M.secondCutGlobalCoordinateTransport_conj_fullCodeProjector]
    _ = (M.secondCutGlobalCoordinateTransport region).symm.conjOperator 0 :=
      congrArg (M.secondCutGlobalCoordinateTransport region).symm.conjOperator hzero
    _ = 0 := by simp [Semantics.UnitaryTransport.conjOperator]

/-- Nonzeroness reflects across a reconstructed isometric compression. -/
theorem compression_ne_zero_of_reconstruction
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (J : H →ₗ[Complex] K) (R : Semantics.Operator K) (hR : R ≠ 0)
    (hreconstruct : R = J.comp (((LinearMap.adjoint J).comp (R.comp J)).comp
      (LinearMap.adjoint J))) :
    ((LinearMap.adjoint J).comp (R.comp J)) ≠ 0 := by
  intro hzero
  apply hR
  calc
    R = J.comp (((LinearMap.adjoint J).comp (R.comp J)).comp (LinearMap.adjoint J)) :=
      hreconstruct
    _ = J.comp ((0 : Semantics.Operator H).comp (LinearMap.adjoint J)) := by rw [hzero]
    _ = 0 := by simp

/-- A nonzero active second-cut sector has nonzero literal code compression. -/
theorem secondCutCodeLift_active_compression_ne_zero_of_nonzero_code
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (hactive : M.secondCutCodeLift region * M.secondCutSectorLift region component =
      M.secondCutCodeLift region) :
    let A := M.fourFactorA region
    let H := component.1.restrictScalars Complex
    let CD := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)
    let J := tensorTripleSubtypeEmbedding (A := A) (C := CD) H
    ((LinearMap.adjoint J).comp ((M.secondCutCodeLift region).comp J)) ≠ 0 := by
  dsimp
  exact compression_ne_zero_of_reconstruction
    (tensorTripleSubtypeEmbedding (A := M.fourFactorA region)
      (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
      (component.1.restrictScalars Complex))
    (M.secondCutCodeLift region)
    (M.secondCutCodeLift_ne_zero_of_nonzero_code region hcode)
    (M.secondCutCodeLift_eq_active_embedding_compression_of_absorption
      region component hactive)

/-- A nonzero operator remains nonzero when its unitary block is a tensor map with nonzero left factor. -/
theorem left_factor_ne_zero_of_nonzero_unitary_tensor_block
    {X A W N C : Type u}
    [NormedAddCommGroup X] [InnerProductSpace Complex X] [Semantics.FiniteQuantumSystem X]
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (T : Semantics.UnitaryTransport X
      (Semantics.CompositeSystem (Semantics.CompositeSystem A W)
        (Semantics.CompositeSystem N C)))
    (R : Semantics.Operator X)
    (P : Semantics.Operator (Semantics.CompositeSystem A W))
    (Q : Semantics.Operator (Semantics.CompositeSystem N C))
    (hR : R ≠ 0) (hblock : T.conjOperator R = TensorProduct.map P Q) :
    P ≠ 0 := by
  intro hP
  apply hR
  calc
    R = T.symm.conjOperator (T.conjOperator R) :=
      (T.symm_conjOperator_conjOperator R).symm
    _ = T.symm.conjOperator (TensorProduct.map P Q) :=
      congrArg T.symm.conjOperator hblock
    _ = T.symm.conjOperator 0 := by simp [hP]
    _ = 0 := by simp [Semantics.UnitaryTransport.conjOperator]


end BPTCommutingProjectorModel

end Bounds
end QEC
