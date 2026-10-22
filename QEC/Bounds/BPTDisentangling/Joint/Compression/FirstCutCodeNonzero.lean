import QEC.Bounds.BPTDisentangling.Joint.Compression.FirstCutLeftProjection

/-!
# BPT first-cut code nonzero

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

/-- The literal first-cut source code lift is nonzero whenever the code carrier is nonzero. -/
theorem firstCutCodeLift_ne_zero_of_nonzero_code
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥) :
    M.firstCutCodeLift region ≠ 0 := by
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
        (M.firstCutGlobalCoordinateTransport region).symm.conjOperator
          ((M.firstCutGlobalCoordinateTransport region).conjOperator M.fullCodeProjector) :=
      (M.firstCutGlobalCoordinateTransport region).symm_conjOperator_conjOperator _ |>.symm
    _ = (M.firstCutGlobalCoordinateTransport region).symm.conjOperator
          (M.firstCutCodeLift region) := by
      rw [M.firstCutGlobalCoordinateTransport_conj_fullCodeProjector]
    _ = (M.firstCutGlobalCoordinateTransport region).symm.conjOperator 0 :=
      congrArg (M.firstCutGlobalCoordinateTransport region).symm.conjOperator hzero
    _ = 0 := by simp [Semantics.UnitaryTransport.conjOperator]

/-- A nonzero active first-cut sector has nonzero literal code compression. -/
theorem firstCutCodeLift_active_compression_ne_zero_of_nonzero_code
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (hactive : M.firstCutCodeLift region * M.firstCutSectorLift region component =
      M.firstCutCodeLift region) :
    let AB := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)
    let H := component.1.restrictScalars Complex
    let D := M.fourFactorD region
    let J := tensorTripleSubtypeEmbedding (A := AB) (C := D) H
    ((LinearMap.adjoint J).comp ((M.firstCutCodeLift region).comp J)) ≠ 0 := by
  dsimp only
  let AB := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)
  let H := component.1.restrictScalars Complex
  let D := M.fourFactorD region
  let J := tensorTripleSubtypeEmbedding (A := AB) (C := D) H
  have hself : LinearMap.adjoint (M.firstCutProjectorMC region) =
      M.firstCutProjectorMC region :=
    (M.firstCutProjectorMC_isSymmetricProjection region).isSymmetric.adjoint_eq
  have hover : Commute (overlapLiftLeft (C := D) (M.firstCutProjectorMC region))
      (overlapLiftRight (A := AB) (M.fourFactorProjectorCDLocal region)) :=
    M.firstCut_overlap_commute region
  have hreconstruct : M.firstCutCodeLift region =
      J.comp (((LinearMap.adjoint J).comp
        ((M.firstCutCodeLift region).comp J)).comp (LinearMap.adjoint J)) := by
    dsimp [J, AB, H, D]
    apply active_overlap_product_eq_isotypic_embedding_compression
      (M.firstCutProjectorMC region) (M.fourFactorProjectorCDLocal region)
      hself hover component
    simpa only [firstCutCodeLift, firstCutSectorLift] using hactive
  exact compression_ne_zero_of_reconstruction J (M.firstCutCodeLift region)
    (M.firstCutCodeLift_ne_zero_of_nonzero_code region hcode) hreconstruct



end BPTCommutingProjectorModel

end Bounds
end QEC
