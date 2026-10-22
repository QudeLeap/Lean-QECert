import QEC.Bounds.BPTDisentangling.ScalarCompression.LeftRankOne

/-!
# BPT second-cut left rank-one witness

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

set_option maxHeartbeats 1600000 in
/-- The selected source factor is a normalized rank-one projector. -/
theorem secondCut_Pleft_eq_rankOne_of_region_recoverable
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (hM : M.RegionErasureRecoverable region)
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
    let CD := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)
    ∀ (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W0 N))
      (Pleft : Semantics.Operator (Semantics.CompositeSystem A W0))
      (Qright : Semantics.Operator (Semantics.CompositeSystem N CD)),
      M.secondCutCodeLift region * M.secondCutSectorLift region component =
          M.secondCutCodeLift region →
      (unitaryLTensor A U).conjOperator
          (overlapProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) component) =
          rightTensorExtensionAfterLeft A W0 N Pleft →
      (unitaryRTensor U CD).conjOperator
          (overlapRightProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) (M.secondCutProjectorBbarM region) component) =
          leftTensorExtensionBeforeRight W0 N CD Qright →
      ∃ phi : Semantics.CompositeSystem A W0,
        ‖phi‖ = 1 ∧
        Pleft = (InnerProductSpace.rankOne Complex phi phi).toLinearMap := by
  intro A H W0 N CD U Pleft Qright hactive hleft hright
  exact isSymmetricProjection_eq_rankOne_of_ne_zero_of_range_finrank_le_one Pleft
    (M.secondCut_Pleft_isSymmetricProjection region component W U Pleft hleft)
    (M.secondCut_Pleft_ne_zero_of_nonzero_code
      region hcode component W U Pleft Qright hactive hleft hright)
    (M.secondCut_Pleft_range_finrank_le_one_of_region_recoverable
      region hcode hM component W U Pleft Qright hactive hleft hright)

end BPTCommutingProjectorModel

end Bounds
end QEC
