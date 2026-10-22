import QEC.Bounds.BPTDisentangling.Joint.Sequential.SecondCutCore

/-!
# BPT joint active-block transports

Cacheable coordinate transports shared by the physical sequential blocks and
the common-factor assembly.
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
/--
The fixed-witness transport from the simultaneous active `B,C` sector in
second-cut coordinates to the common `A B' B'' C' C''D` coordinates.
-/
noncomputable def secondCutJointActiveBlockTransport
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nB nC : Nat} [NeZero nB] [NeZero nC]
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UB : Semantics.UnitaryTransport (bcomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WB.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nB)))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC))) :
    Semantics.UnitaryTransport
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region)
          (bcomponent.1.restrictScalars Complex))
        (Semantics.CompositeSystem (ccomponent.1.restrictScalars Complex)
          (M.fourFactorD region)))
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
        (Semantics.CompositeSystem
          (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
            (WC.restrictScalars Complex))
          (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
            (M.fourFactorD region)))) :=
  composeUnitaryTransport
    (isotypicSectorBlockTransportLeft (M.fourFactorA region)
      (bcomponent.1.restrictScalars Complex) (WB.restrictScalars Complex)
      (isotypicLiftedMultiplicity.{0} nB)
      (Semantics.CompositeSystem (ccomponent.1.restrictScalars Complex)
        (M.fourFactorD region)) UB)
    (composeUnitaryTransport
      (unitaryLTensor (Semantics.CompositeSystem (M.fourFactorA region)
        (WB.restrictScalars Complex))
        (unitaryLTensor (isotypicLiftedMultiplicity.{0} nB)
          (composeUnitaryTransport (unitaryRTensor UC (M.fourFactorD region))
            (tensorAssociatorUnitary (WC.restrictScalars Complex)
              (isotypicLiftedMultiplicity.{0} nC) (M.fourFactorD region)))))
      (unitaryLTensor (Semantics.CompositeSystem (M.fourFactorA region)
        (WB.restrictScalars Complex))
        (tensorAssociatorUnitary (isotypicLiftedMultiplicity.{0} nB)
          (WC.restrictScalars Complex)
          (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
            (M.fourFactorD region))).symm))

set_option maxHeartbeats 800000 in
/--
The companion fixed-witness transport from the simultaneous active sector in
first-cut coordinates to the same common coordinates.
-/
noncomputable def firstCutJointActiveBlockTransport
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nB nC : Nat} [NeZero nB] [NeZero nC]
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UB : Semantics.UnitaryTransport (bcomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WB.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nB)))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC))) :
    Semantics.UnitaryTransport
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem
          (Semantics.CompositeSystem (M.fourFactorA region)
            (bcomponent.1.restrictScalars Complex))
          (ccomponent.1.restrictScalars Complex))
        (M.fourFactorD region))
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
        (Semantics.CompositeSystem
          (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
            (WC.restrictScalars Complex))
          (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
            (M.fourFactorD region)))) :=
  composeUnitaryTransport
    (isotypicSectorBlockTransportLeft
      (Semantics.CompositeSystem (M.fourFactorA region)
        (bcomponent.1.restrictScalars Complex))
      (ccomponent.1.restrictScalars Complex) (WC.restrictScalars Complex)
      (isotypicLiftedMultiplicity.{0} nC) (M.fourFactorD region) UC)
    (composeUnitaryTransport
      (unitaryRTensor
        (isotypicSectorBlockTransportLeft (M.fourFactorA region)
          (bcomponent.1.restrictScalars Complex) (WB.restrictScalars Complex)
          (isotypicLiftedMultiplicity.{0} nB) (WC.restrictScalars Complex) UB)
        (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
          (M.fourFactorD region)))
      (tensorAssociatorUnitary
        (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
        (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
          (WC.restrictScalars Complex))
        (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
          (M.fourFactorD region))))


end BPTCommutingProjectorModel

end Bounds
end QEC
