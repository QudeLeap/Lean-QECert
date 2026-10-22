import QEC.Bounds.BPTDisentangling.ScalarCompression.LeftRankOneBlock

/-!
# BPT selected-B compression

Named second-cut embedding and compression shared by scalar and joint layers.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

/-- The selected `B`-sector embedding in second-cut coordinates. -/
def secondCutSelectedBEmbedding
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region)) :
    (Semantics.CompositeSystem
      (Semantics.CompositeSystem (M.fourFactorA region) pB)
      (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))) →ₗ[Complex]
    (Semantics.CompositeSystem
      (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
      (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))) :=
  tensorTripleSubtypeEmbedding (A := M.fourFactorA region)
    (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) pB

/-- The second-cut code compressed to one selected `B` sector. -/
noncomputable def secondCutSelectedBCompression
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region)) :
    Semantics.Operator (Semantics.CompositeSystem
      (Semantics.CompositeSystem (M.fourFactorA region) pB)
      (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))) :=
  (LinearMap.adjoint (M.secondCutSelectedBEmbedding region pB)).comp
    ((M.secondCutCodeLift region).comp (M.secondCutSelectedBEmbedding region pB))

end BPTCommutingProjectorModel

end Bounds
end QEC
