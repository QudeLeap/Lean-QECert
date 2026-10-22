import QEC.Bounds.BPTDisentangling.NoCloning.Fixed.ProductData

/-!
# BPT actual-sector product contract

Compact exact interface between sector selection and the final physical
disentangling proof.  Intermediate first- and second-cut equations have already
been consumed when constructing the fixed-data product evidence.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

set_option maxHeartbeats 1800000 in
/-- Actual sector coordinates together with the exact fixed-data D5 evidence. -/
inductive ActualFixedActiveDataProductRankOneTensor
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) : Prop where
  | intro
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (nC : Nat) [hnC : NeZero nC]
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC)))
    (P_D : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
        (M.fourFactorD region)))
    (nB : Nat) [hnB : NeZero nB]
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (UB : Semantics.UnitaryTransport (bcomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WB.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nB)))
    (Qsecond : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))
    (evidence : M.FixedActiveDataProductRankOneTensor
      region bcomponent ccomponent WB WC UB UC P_D Qsecond) :
    ActualFixedActiveDataProductRankOneTensor M region

end BPTCommutingProjectorModel

end Bounds
end QEC
