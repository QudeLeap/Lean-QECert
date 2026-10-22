import QEC.Bounds.BPTDisentangling.ScalarCompression.LeftRankOneWitness

/-!
# BPT second-cut left rank-one block

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
/-- The three physical second-cut equations consumed by the rank-one block theorem. -/
def SecondCutActiveBlockConditions
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    {n : Nat} [NeZero n]
    (W : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (U : Semantics.UnitaryTransport (component.1.restrictScalars Complex)
      (Semantics.CompositeSystem (W.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} n)))
    (Pleft : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorA region) (W.restrictScalars Complex)))
    (Qright : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} n)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)))) : Prop :=
  M.secondCutCodeLift region * M.secondCutSectorLift region component =
      M.secondCutCodeLift region ∧
    (unitaryLTensor (M.fourFactorA region) U).conjOperator
        (overlapProjectorOnIsotypicComponent
          (M.fourFactorProjectorABLocal region) component) =
      rightTensorExtensionAfterLeft (M.fourFactorA region)
        (W.restrictScalars Complex) (isotypicLiftedMultiplicity.{0} n) Pleft ∧
    (unitaryRTensor U
      (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))).conjOperator
        (overlapRightProjectorOnIsotypicComponent
          (M.fourFactorProjectorABLocal region) (M.secondCutProjectorBbarM region)
          component) =
      leftTensorExtensionBeforeRight (W.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} n)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) Qright

set_option maxHeartbeats 800000 in
/-- The normalized rank-one product obtained after compressing the active B sector. -/
def SecondCutRankOneBlockProduct
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    {n : Nat} [NeZero n]
    (W : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (U : Semantics.UnitaryTransport (component.1.restrictScalars Complex)
      (Semantics.CompositeSystem (W.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} n)))
    (Qright : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} n)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)))) : Prop :=
  let A := M.fourFactorA region
  let H := component.1.restrictScalars Complex
  let W0 := W.restrictScalars Complex
  let N := isotypicLiftedMultiplicity.{0} n
  let CD := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)
  let J := tensorTripleSubtypeEmbedding (A := A) (C := CD) H
  let Rcompressed : Semantics.Operator (Semantics.CompositeSystem
      (Semantics.CompositeSystem A H) CD) :=
    (LinearMap.adjoint J).comp ((M.secondCutCodeLift region).comp J)
  let T := isotypicSectorBlockTransportLeft A H W0 N CD U
  ∃ phi : Semantics.CompositeSystem A W0,
    ‖phi‖ = 1 ∧
    T.conjOperator Rcompressed =
      TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap Qright

set_option maxHeartbeats 800000 in
theorem secondCut_compressed_overlap_rankOne_block_product_of_region_recoverable
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (hM : M.RegionErasureRecoverable region)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    {n : Nat} [NeZero n]
    (W : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (U : Semantics.UnitaryTransport (component.1.restrictScalars Complex)
      (Semantics.CompositeSystem (W.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} n)))
    (Pleft : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorA region) (W.restrictScalars Complex)))
    (Qright : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} n)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))
    (hsource : SecondCutActiveBlockConditions M region component W U Pleft Qright) :
    SecondCutRankOneBlockProduct M region component W U Qright := by
  unfold SecondCutActiveBlockConditions at hsource
  rcases hsource with ⟨hactive, hleft, hright⟩
  unfold SecondCutRankOneBlockProduct
  rcases M.secondCut_Pleft_eq_rankOne_of_region_recoverable
    region hcode hM component W U Pleft Qright hactive hleft hright with
    ⟨phi, hphi, hPleft⟩
  refine ⟨phi, hphi, ?_⟩
  calc
    _ = TensorProduct.map Pleft Qright :=
      M.secondCut_compressed_overlap_block_product
        region component W U Pleft Qright hleft hright
    _ = TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap Qright :=
      congrArg (fun left => TensorProduct.map left Qright) hPleft

end BPTCommutingProjectorModel

end Bounds
end QEC
