import QEC.Bounds.BPTDisentangling.Joint.Compression.Transport

/-!
# BPT first-cut left projection

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

/-- The active first-cut left BV03 block is an orthogonal projection. -/
theorem firstCut_Pleft_isSymmetricProjection
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {n : Nat} [NeZero n]
    (W : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region)) :
    let AB := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)
    let H := component.1.restrictScalars Complex
    let W0 := W.restrictScalars Complex
    let N := isotypicLiftedMultiplicity.{0} n
    ∀ (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W0 N))
      (Pleft : Semantics.Operator (Semantics.CompositeSystem AB W0)),
      (unitaryLTensor AB U).conjOperator
          (overlapProjectorOnIsotypicComponent (M.firstCutProjectorMC region) component) =
          rightTensorExtensionAfterLeft AB W0 N Pleft →
        @LinearMap.IsSymmetricProjection Complex
          (Semantics.CompositeSystem AB W0) _ _ _ Pleft := by
  dsimp only
  intro U Pleft hleft
  let AB := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)
  have hcompressed : (overlapProjectorOnIsotypicComponent
      (M.firstCutProjectorMC region) component).IsSymmetricProjection :=
    overlapProjectorOnIsotypicComponent_isSymmetricProjection
      (M.firstCutProjectorMC region)
      (M.firstCutProjectorMC_isSymmetricProjection region) component
  let eta := isotypicLiftedMultiplicityUnitVector.{0} n
  have heta : ‖eta‖ = 1 := norm_isotypicLiftedMultiplicityUnitVector.{0} n
  exact isSymmetricProjection_of_unitary_eq_rightTensorExtension
    U (overlapProjectorOnIsotypicComponent (M.firstCutProjectorMC region) component)
    Pleft eta heta hcompressed hleft



end BPTCommutingProjectorModel

end Bounds
end QEC
