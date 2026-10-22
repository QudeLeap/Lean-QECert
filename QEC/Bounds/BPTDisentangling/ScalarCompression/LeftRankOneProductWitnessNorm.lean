import QEC.Bounds.BPTDisentangling.ScalarCompression.LeftRankOneProductWitness

/-! # BPT second-cut rank-one product witness normalization -/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

/-- The selected second-cut rank-one product witness is normalized. -/
theorem SecondCutRankOneBlockProduct.witness_norm
    {M : BPTCommutingProjectorModel L kappa} {region : Finset L.Site}
    {component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)}
    {n : Nat} [NeZero n]
    {W : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)}
    {U : Semantics.UnitaryTransport (component.1.restrictScalars Complex)
      (Semantics.CompositeSystem (W.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} n))}
    {Qright : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} n)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)))}
    (h : SecondCutRankOneBlockProduct (n := n) M region component W U Qright) :
    ‖SecondCutRankOneBlockProduct.witness (n := n) h‖ = 1 :=
  (Classical.choose_spec h).1

end BPTCommutingProjectorModel

end Bounds
end QEC
