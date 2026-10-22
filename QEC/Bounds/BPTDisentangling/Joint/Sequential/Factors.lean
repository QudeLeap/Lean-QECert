import QEC.Bounds.BPTDisentangling.Joint.Compression.Core

/-!
# BPT sequential active-block factors

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
/--
The actual first-cut left BV03 block after compression to the active second-cut
`B` sector and its isotypic coordinates.  This is the left factor paired with
the unchanged source complement block `Pi_C''D` in the common joint sector.
-/
noncomputable def firstCutPleftOnSecondCutActiveSector
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    {nB : Nat} [NeZero nB]
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (UB : Semantics.UnitaryTransport (bcomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WB.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nB)))
    (WC : Type) [NormedAddCommGroup WC] [InnerProductSpace Complex WC]
    [Semantics.FiniteQuantumSystem WC]
    (Pleft : Semantics.Operator
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)) WC)) :
    Semantics.Operator
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
        (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB) WC)) :=
  let pB := bcomponent.1.restrictScalars Complex
  let K : (Semantics.CompositeSystem (Semantics.CompositeSystem (M.fourFactorA region) pB) WC) →ₗ[Complex]
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)) WC) :=
    TensorProduct.map
      (TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region)) pB.subtype)
      (1 : Semantics.Operator WC)
  (isotypicSectorBlockTransportLeft (M.fourFactorA region) pB
    (WB.restrictScalars Complex) (isotypicLiftedMultiplicity.{0} nB) WC UB).conjOperator
      ((LinearMap.adjoint K).comp (Pleft.comp K))

set_option maxHeartbeats 800000 in
/--
The actual second-cut right BV03 block after compression to the active first-cut
`C` sector and its isotypic coordinates.  Its final factors are exactly
`B'' tensor C' tensor (C''D)`; no rank-one assumption is made on the last one.
-/
noncomputable def secondCutQrightOnFirstCutActiveSector
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nC nB : Nat} [NeZero nC] [NeZero nB]
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC)))
    (Qright : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)))) :
    Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (Semantics.CompositeSystem (WC.restrictScalars Complex)
          (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
            (M.fourFactorD region)))) :=
  let HC := ccomponent.1.restrictScalars Complex
  let N := isotypicLiftedMultiplicity.{0} nB
  let NC := isotypicLiftedMultiplicity.{0} nC
  let D := M.fourFactorD region
  let K : (Semantics.CompositeSystem N (Semantics.CompositeSystem HC D)) →ₗ[Complex]
      (Semantics.CompositeSystem N
        (Semantics.CompositeSystem (M.fourFactorC region) D)) :=
    TensorProduct.map (1 : Semantics.Operator N)
      (TensorProduct.map HC.subtype (1 : Semantics.Operator D))
  let V := composeUnitaryTransport (unitaryRTensor UC D)
    (tensorAssociatorUnitary (WC.restrictScalars Complex) NC D)
  (unitaryLTensor N V).conjOperator ((LinearMap.adjoint K).comp (Qright.comp K))

end BPTCommutingProjectorModel

end Bounds
end QEC
