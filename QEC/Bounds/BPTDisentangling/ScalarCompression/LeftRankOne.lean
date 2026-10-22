import QEC.Bounds.BPTDisentangling.ScalarCompression.LeftPhysical
import QEC.Bounds.BPTDisentangling.ScalarCompression.RankOne

/-!
# BPT second-cut left rank-one reduction

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
/--
The hM scalar-compression bridge forces the selected source `Pi_AB'` factor
to have at most one-dimensional range.  This is the finite-dimensional
rank-one step at BPT source lines 643--647.
-/
theorem secondCut_Pleft_range_finrank_le_one_of_region_recoverable
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
      Module.finrank Complex (LinearMap.range Pleft) ≤ 1 := by
  intro A H W0 N CD U Pleft Qright hactive hleft hright
  have hscalar : ∀ X : Semantics.Operator
      (Semantics.CompositeSystem A W0),
      ∃ scalar : Complex, Pleft * X * Pleft = scalar • Pleft := by
    exact M.secondCut_Pleft_all_scalar_compression_of_region_recoverable
      region hcode hM component W U Pleft Qright hactive hleft hright
  exact finrank_range_le_one_of_all_scalar_compression
    (H := Semantics.CompositeSystem A W0)
    Pleft (M.secondCut_Pleft_isSymmetricProjection region component W U Pleft hleft) hscalar

end BPTCommutingProjectorModel

end Bounds
end QEC
