import QEC.Bounds.BPTDisentangling.Joint.Sequential.Factors

/-!
# BPT sequential active-block compression

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
The common joint B/C block written as the two sequential compressions which
the first- and second-cut BV03 block equations act on.  This is a direct
expansion of `jointBCSectorCompression_secondCutCodeLift_eq_firstCutCodeLift`.
-/
theorem sequentialJointBCSectorCompression_secondCut_eq_firstCut
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region)) :
    let V := tensorAssociatorUnitary
      (Semantics.CompositeSystem (M.fourFactorA region) pB) pC (M.fourFactorD region)
    M.sequentialSecondCutJointCompression region pB pC =
      V.conjOperator (M.sequentialFirstCutJointCompression region pB pC) := by
  dsimp only
  let V := tensorAssociatorUnitary
    (Semantics.CompositeSystem (M.fourFactorA region) pB) pC (M.fourFactorD region)
  have hright :=
    M.jointBCSectorCompressionRight_eq_sequentialSecondCutCompression region pB pC
  have hleft :=
    M.jointBCSectorCompressionLeft_eq_sequentialFirstCutCompression region pB pC
  have hjoint := M.jointBCSectorCompression_secondCutCodeLift_eq_firstCutCodeLift
    region pB pC
  calc
    M.sequentialSecondCutJointCompression region pB pC =
        (LinearMap.adjoint (jointBCSectorEmbeddingRight
          (A := M.fourFactorA region) (D := M.fourFactorD region) pB pC)).comp
          ((M.secondCutCodeLift region).comp
            (jointBCSectorEmbeddingRight
              (A := M.fourFactorA region) (D := M.fourFactorD region) pB pC)) := hright.symm
    _ = V.conjOperator
        ((LinearMap.adjoint (jointBCSectorEmbeddingLeft
          (A := M.fourFactorA region) (D := M.fourFactorD region) pB pC)).comp
          ((M.firstCutCodeLift region).comp
            (jointBCSectorEmbeddingLeft
              (A := M.fourFactorA region) (D := M.fourFactorD region) pB pC))) := by
          simpa [V] using hjoint
    _ = V.conjOperator (M.sequentialFirstCutJointCompression region pB pC) :=
      congrArg V.conjOperator hleft

end BPTCommutingProjectorModel

end Bounds
end QEC
