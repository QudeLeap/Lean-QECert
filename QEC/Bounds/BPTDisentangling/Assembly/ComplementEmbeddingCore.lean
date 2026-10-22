import QEC.Bounds.BPTDisentangling.Assembly.CoordinateTransport

/-!
# BPT active complement embedding core
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

set_option maxHeartbeats 450000 in
set_option synthInstance.maxHeartbeats 50000 in
/-- The concrete coordinate realization of the active complement embedding. -/
noncomputable def activeComplementCoordinateEmbedding
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nC : Nat} [NeZero nC]
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC))) :
    (Semantics.CompositeSystem (WC.restrictScalars Complex)
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
        (M.fourFactorD region))) →ₗᵢ[Complex]
      (M.regionSubsystem region).complementSystem := by
  let AB := M.regionSubsystem region
  let ABC := M.regionSubsystem (region ∪ M.externalBoundary region)
  have hABABC : AB.selected ⊆ ABC.selected := by
    intro site hsite
    exact Finset.mem_union_left _ hsite
  let eC : (Semantics.CompositeSystem (WC.restrictScalars Complex)
      (isotypicLiftedMultiplicity.{0} nC)) →ₗᵢ[Complex] M.fourFactorC region :=
    (ccomponent.1.restrictScalars Complex).subtypeₗᵢ.comp
      UC.symm.toLinearIsometryEquiv.toLinearIsometry
  exact
    (AB.complementFactorization ABC hABABC).symm.toLinearIsometryEquiv.toLinearIsometry.comp
      ((TensorProduct.mapIsometry eC (LinearIsometry.id)).comp
        (tensorAssociatorUnitary (WC.restrictScalars Complex)
          (isotypicLiftedMultiplicity.{0} nC)
          (M.fourFactorD region)).symm.toLinearIsometryEquiv.toLinearIsometry)

/-- Embed the active complement coordinates into the concrete complement subsystem. -/
noncomputable def activeComplementEmbeddingCore
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nC : Nat} [NeZero nC]
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC))) :=
  M.activeComplementCoordinateEmbedding region ccomponent WC UC

/-- The concrete active-complement embedding on a pure tensor. -/
theorem activeComplementEmbeddingCore_apply_tmul
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nC : Nat} [NeZero nC]
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC)))
    (x : WC.restrictScalars Complex) (n : isotypicLiftedMultiplicity.{0} nC)
    (d : M.fourFactorD region) :
    M.activeComplementEmbeddingCore region ccomponent WC UC
        (x ⊗ₜ[Complex] (n ⊗ₜ[Complex] d)) =
      ((M.regionSubsystem region).complementFactorization
        (M.regionSubsystem (region ∪ M.externalBoundary region))
        (by
          intro site hsite
          exact Finset.mem_union_left _ hsite)).symm
        ((ccomponent.1.restrictScalars Complex).subtype
          (UC.symm (x ⊗ₜ[Complex] n)) ⊗ₜ[Complex] d) := by
  rfl

end BPTCommutingProjectorModel

end Bounds
end QEC
