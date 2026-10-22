import QEC.Bounds.BPTDisentangling.Assembly.SelectedEmbeddingCore
import QEC.Bounds.BPTDisentangling.Assembly.ComplementEmbeddingCore

/-!
# BPT final physical embeddings

Cacheable concrete selected/complement embeddings and their exact relation to
the four-factor active-sector coordinates.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

private theorem linearMap_ext_sixTensorFactors
    {A W N X N2 D Y : Type u}
    [AddCommMonoid A] [Module Complex A]
    [AddCommMonoid W] [Module Complex W]
    [AddCommMonoid N] [Module Complex N]
    [AddCommMonoid X] [Module Complex X]
    [AddCommMonoid N2] [Module Complex N2]
    [AddCommMonoid D] [Module Complex D]
    [AddCommMonoid Y] [Module Complex Y]
    {f g : (((A ⊗[Complex] W) ⊗[Complex] N) ⊗[Complex]
      (X ⊗[Complex] (N2 ⊗[Complex] D))) →ₗ[Complex] Y}
    (h : ∀ a w n x n2 d,
      f (((a ⊗ₜ[Complex] w) ⊗ₜ[Complex] n) ⊗ₜ[Complex]
        (x ⊗ₜ[Complex] (n2 ⊗ₜ[Complex] d))) =
      g (((a ⊗ₜ[Complex] w) ⊗ₜ[Complex] n) ⊗ₜ[Complex]
        (x ⊗ₜ[Complex] (n2 ⊗ₜ[Complex] d)))) :
    f = g := by
  ext a w n x n2 d
  exact h a w n x n2 d

set_option maxHeartbeats 1600000 in
private theorem fourFactorTransportFromRegion_apply_activePreimages
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (a : M.fourFactorA region) (b : M.fourFactorB region)
    (c : M.fourFactorC region) (d : M.fourFactorD region) :
    M.fourFactorTransportFromRegion region
        ((M.regionSubsystem region).registerFactorization.symm
          (((M.regionSubsystem (M.interior region)).selectedFactorization
            (M.regionSubsystem region)
            (by
              intro site hsite
              exact (Finset.mem_sdiff.mp hsite).1)).symm
            (a ⊗ₜ[Complex] b) ⊗ₜ[Complex]
          ((M.regionSubsystem region).complementFactorization
            (M.regionSubsystem (region ∪ M.externalBoundary region))
            (by
              intro site hsite
              exact Finset.mem_union_left _ hsite)).symm
            (c ⊗ₜ[Complex] d))) =
      a ⊗ₜ[Complex] (b ⊗ₜ[Complex] (c ⊗ₜ[Complex] d)) := by
  simp [fourFactorTransportFromRegion, composeUnitaryTransport,
    unitaryRTensor, unitaryLTensor, tensorAssociatorUnitary]

set_option maxHeartbeats 1600000 in
private theorem jointActiveCoordinates_apply_productBlock
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
        (isotypicLiftedMultiplicity.{0} nC)))
    (a : M.fourFactorA region) (w : WB.restrictScalars Complex)
    (nB' : isotypicLiftedMultiplicity.{0} nB) (x : WC.restrictScalars Complex)
    (nC' : isotypicLiftedMultiplicity.{0} nC) (d : M.fourFactorD region) :
    (fourFactorJointBCSectorEmbedding (A := M.fourFactorA region)
      (D := M.fourFactorD region) (bcomponent.1.restrictScalars Complex)
      (ccomponent.1.restrictScalars Complex))
        ((M.secondCutJointActiveBlockTransport
          region bcomponent ccomponent WB WC UB UC).symm
          ((tensorAssociatorUnitary
            (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
            (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
              (WC.restrictScalars Complex))
            (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
              (M.fourFactorD region)))
            ((productBlockRegrouping (A := M.fourFactorA region)
              (W := WB.restrictScalars Complex) (N := isotypicLiftedMultiplicity.{0} nB)
              (X := WC.restrictScalars Complex)
              (D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
                (M.fourFactorD region))).symm
              (((a ⊗ₜ[Complex] w) ⊗ₜ[Complex] nB') ⊗ₜ[Complex]
                (x ⊗ₜ[Complex] (nC' ⊗ₜ[Complex] d)))))) =
      a ⊗ₜ[Complex]
        ((bcomponent.1.restrictScalars Complex).subtype
          (UB.symm (w ⊗ₜ[Complex] nB')) ⊗ₜ[Complex]
        ((ccomponent.1.restrictScalars Complex).subtype
          (UC.symm (x ⊗ₜ[Complex] nC')) ⊗ₜ[Complex] d)) := by
  simp [secondCutJointActiveBlockTransport, productBlockRegrouping,
    fourFactorJointBCSectorEmbedding, jointBCSectorEmbeddingRight,
    isotypicSectorBlockTransportLeft, composeUnitaryTransport,
    unitaryRTensor, unitaryLTensor, tensorAssociatorUnitary]

set_option maxHeartbeats 1600000 in
private theorem physicalActiveCoordinates_apply_productBlock
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
        (isotypicLiftedMultiplicity.{0} nC)))
    (a : M.fourFactorA region) (w : WB.restrictScalars Complex)
    (nB' : isotypicLiftedMultiplicity.{0} nB) (x : WC.restrictScalars Complex)
    (nC' : isotypicLiftedMultiplicity.{0} nC) (d : M.fourFactorD region) :
    ((M.fourFactorTransportFromRegion region).toLinearEquiv.toLinearMap.comp
      ((M.regionSubsystem region).registerFactorization.symm.toLinearEquiv.toLinearMap.comp
        (TensorProduct.map
          (M.activeSelectedEmbeddingCore region bcomponent WB UB).toLinearMap
          (M.activeComplementEmbeddingCore region ccomponent WC UC).toLinearMap)))
        (((a ⊗ₜ[Complex] w) ⊗ₜ[Complex] nB') ⊗ₜ[Complex]
          (x ⊗ₜ[Complex] (nC' ⊗ₜ[Complex] d))) =
      a ⊗ₜ[Complex]
        ((bcomponent.1.restrictScalars Complex).subtype
          (UB.symm (w ⊗ₜ[Complex] nB')) ⊗ₜ[Complex]
        ((ccomponent.1.restrictScalars Complex).subtype
          (UC.symm (x ⊗ₜ[Complex] nC')) ⊗ₜ[Complex] d)) := by
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul]
  have hSelected := M.activeSelectedEmbeddingCore_apply_tmul
    region bcomponent WB UB a w nB'
  have hComplement := M.activeComplementEmbeddingCore_apply_tmul
    region ccomponent WC UC x nC' d
  have hPair := congrArg₂ (fun selected complement => selected ⊗ₜ[Complex] complement)
    hSelected hComplement
  exact (congrArg
    (fun pair => M.fourFactorTransportFromRegion region
      ((M.regionSubsystem region).registerFactorization.symm pair))
    hPair).trans
      (M.fourFactorTransportFromRegion_apply_activePreimages region _ _ _ _)

-- Internal cache boundary; do not index its large dependent type as an automated premise.
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.modifyEnv fun env =>
    let env := Lean.LibrarySuggestions.nameDenyListExt.addEntry env
      "fourFactorTransportFromRegion_comp_activeRegionEmbeddingsCore"
    Lean.LibrarySuggestions.nameDenyListExt.addEntry env
      "fourFactorTransport_comp_activeRegionEmbeddingsCore"

set_option maxHeartbeats 4000000 in
/-- Exact coordinate identity in the cumulative `AB`-first transport presentation. -/
theorem fourFactorTransportFromRegion_comp_activeRegionEmbeddingsCore
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
    (M.fourFactorTransportFromRegion region).toLinearEquiv.toLinearMap.comp
        ((M.regionSubsystem region).registerFactorization.symm.toLinearEquiv.toLinearMap.comp
          (TensorProduct.map
            (M.activeSelectedEmbeddingCore region bcomponent WB UB).toLinearMap
            (M.activeComplementEmbeddingCore region ccomponent WC UC).toLinearMap)) =
      (fourFactorJointBCSectorEmbedding (A := M.fourFactorA region)
        (D := M.fourFactorD region) (bcomponent.1.restrictScalars Complex)
        (ccomponent.1.restrictScalars Complex)).comp
        ((M.secondCutJointActiveBlockTransport
          region bcomponent ccomponent WB WC UB UC).symm.toLinearEquiv.toLinearMap.comp
          ((tensorAssociatorUnitary
            (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
            (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
              (WC.restrictScalars Complex))
            (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
              (M.fourFactorD region))).toLinearEquiv.toLinearMap.comp
            (productBlockRegrouping (A := M.fourFactorA region)
              (W := WB.restrictScalars Complex) (N := isotypicLiftedMultiplicity.{0} nB)
              (X := WC.restrictScalars Complex)
              (D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
                (M.fourFactorD region))).symm.toLinearEquiv.toLinearMap)) := by
  refine linearMap_ext_sixTensorFactors
    (A := M.fourFactorA region) (W := WB.restrictScalars Complex)
    (N := isotypicLiftedMultiplicity.{0} nB) (X := WC.restrictScalars Complex)
    (N2 := isotypicLiftedMultiplicity.{0} nC) (D := M.fourFactorD region) ?_
  intro a w nBVector x nCVector d
  exact (physicalActiveCoordinates_apply_productBlock
    M region bcomponent ccomponent WB WC UB UC a w nBVector x nCVector d).trans
      (jointActiveCoordinates_apply_productBlock
        M region bcomponent ccomponent WB WC UB UC a w nBVector x nCVector d).symm

set_option maxHeartbeats 1600000 in
/-- Exact coordinate identity for the concrete active selected/complement embeddings. -/
theorem fourFactorTransport_comp_activeRegionEmbeddingsCore
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
    (M.fourFactorTransport region).toLinearEquiv.toLinearMap.comp
        ((M.regionSubsystem region).registerFactorization.symm.toLinearEquiv.toLinearMap.comp
          (TensorProduct.map
            (M.activeSelectedEmbeddingCore region bcomponent WB UB).toLinearMap
            (M.activeComplementEmbeddingCore region ccomponent WC UC).toLinearMap)) =
      (fourFactorJointBCSectorEmbedding (A := M.fourFactorA region)
        (D := M.fourFactorD region) (bcomponent.1.restrictScalars Complex)
        (ccomponent.1.restrictScalars Complex)).comp
        ((M.secondCutJointActiveBlockTransport
          region bcomponent ccomponent WB WC UB UC).symm.toLinearEquiv.toLinearMap.comp
          ((tensorAssociatorUnitary
            (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
            (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
              (WC.restrictScalars Complex))
            (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
              (M.fourFactorD region))).toLinearEquiv.toLinearMap.comp
            (productBlockRegrouping (A := M.fourFactorA region)
              (W := WB.restrictScalars Complex) (N := isotypicLiftedMultiplicity.{0} nB)
              (X := WC.restrictScalars Complex)
              (D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
                (M.fourFactorD region))).symm.toLinearEquiv.toLinearMap)) := by
  have htransport :
      (M.fourFactorTransport region).toLinearEquiv.toLinearMap =
        (M.fourFactorTransportFromRegion region).toLinearEquiv.toLinearMap :=
    congrArg (fun T : Semantics.UnitaryTransport L.Register _ =>
      T.toLinearEquiv.toLinearMap)
      (M.fourFactorTransport_eq_fourFactorTransportFromRegion region)
  exact (congrArg
    (fun F => F.comp
      ((M.regionSubsystem region).registerFactorization.symm.toLinearEquiv.toLinearMap.comp
        (TensorProduct.map
          (M.activeSelectedEmbeddingCore region bcomponent WB UB).toLinearMap
          (M.activeComplementEmbeddingCore region ccomponent WC UC).toLinearMap)))
    htransport).trans
      (M.fourFactorTransportFromRegion_comp_activeRegionEmbeddingsCore
        region bcomponent ccomponent WB WC UB UC)

end BPTCommutingProjectorModel

end Bounds
end QEC
