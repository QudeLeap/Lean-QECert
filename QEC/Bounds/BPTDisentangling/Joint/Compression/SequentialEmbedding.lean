import QEC.Bounds.BPTDisentangling.Joint.Compression.SequentialEmbeddingCore

/-!
# BPT sequential first-cut compression

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


set_option maxHeartbeats 800000 in
/-- The factorized first-cut embedding realizes the named sequential compression block. -/
theorem firstCutFactorizedCompression_eq_sequential
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region)) :
    (LinearMap.adjoint ((M.firstCutSelectedCEmbedding region pC).comp
      (M.firstCutSelectedBAfterCEmbedding region pB pC))).comp
      ((M.firstCutCodeLift region).comp
        ((M.firstCutSelectedCEmbedding region pC).comp
          (M.firstCutSelectedBAfterCEmbedding region pB pC))) =
      M.sequentialFirstCutJointCompression region pB pC := by
  exact compression_comp_embedding
    (M.firstCutSelectedCEmbedding region pC)
    (M.firstCutSelectedBAfterCEmbedding region pB pC)
    (M.firstCutCodeLift region)

set_option maxHeartbeats 2000000 in
/-- Simultaneous first-cut compression agrees with its sequential `C`-then-`B` form. -/
theorem jointBCSectorCompressionLeft_eq_sequentialFirstCutCompression
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region)) :
    (LinearMap.adjoint
      (jointBCSectorEmbeddingLeft (A := M.fourFactorA region)
        (D := M.fourFactorD region) pB pC)).comp
      ((M.firstCutCodeLift region).comp
        (jointBCSectorEmbeddingLeft (A := M.fourFactorA region)
          (D := M.fourFactorD region) pB pC)) =
      M.sequentialFirstCutJointCompression region pB pC := by
  have hJ := M.jointBCSectorEmbeddingLeft_eq_firstCutSector_after_secondCutSector
    region pB pC
  calc
    (LinearMap.adjoint
      (jointBCSectorEmbeddingLeft (A := M.fourFactorA region)
        (D := M.fourFactorD region) pB pC)).comp
      ((M.firstCutCodeLift region).comp
        (jointBCSectorEmbeddingLeft (A := M.fourFactorA region)
          (D := M.fourFactorD region) pB pC)) =
      (LinearMap.adjoint ((M.firstCutSelectedCEmbedding region pC).comp
        (M.firstCutSelectedBAfterCEmbedding region pB pC))).comp
        ((M.firstCutCodeLift region).comp
          ((M.firstCutSelectedCEmbedding region pC).comp
            (M.firstCutSelectedBAfterCEmbedding region pB pC))) :=
        compression_congr_of_embedding_eq (M.firstCutCodeLift region) hJ
    _ = _ := M.firstCutFactorizedCompression_eq_sequential region pB pC


end BPTCommutingProjectorModel

end Bounds
end QEC
