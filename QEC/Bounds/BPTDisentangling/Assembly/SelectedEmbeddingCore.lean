import QEC.Bounds.BPTDisentangling.Assembly.CoordinateTransport

/-!
# BPT active selected embedding core
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

/-- Embed the active selected coordinates into the concrete selected subsystem. -/
noncomputable def activeSelectedEmbeddingCore
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    {nB : Nat} [NeZero nB]
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (UB : Semantics.UnitaryTransport (bcomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WB.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nB))) :
    (Semantics.CompositeSystem
      (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
      (isotypicLiftedMultiplicity.{0} nB)) →ₗᵢ[Complex]
      (M.regionSubsystem region).selectedSystem := by
  let A := M.regionSubsystem (M.interior region)
  let AB := M.regionSubsystem region
  have hAAB : A.selected ⊆ AB.selected := by
    intro site hsite
    exact (Finset.mem_sdiff.mp hsite).1
  let eB : (Semantics.CompositeSystem (WB.restrictScalars Complex)
      (isotypicLiftedMultiplicity.{0} nB)) →ₗᵢ[Complex] M.fourFactorB region :=
    (bcomponent.1.restrictScalars Complex).subtypeₗᵢ.comp
      UB.symm.toLinearIsometryEquiv.toLinearIsometry
  exact
    (A.selectedFactorization AB hAAB).symm.toLinearIsometryEquiv.toLinearIsometry.comp
      ((TensorProduct.mapIsometry (LinearIsometry.id) eB).comp
        (tensorAssociatorUnitary (M.fourFactorA region) (WB.restrictScalars Complex)
          (isotypicLiftedMultiplicity.{0} nB)).toLinearIsometryEquiv.toLinearIsometry)

/-- The selected embedding on a pure active-sector tensor. -/
theorem activeSelectedEmbeddingCore_apply_tmul
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
    (a : M.fourFactorA region) (w : WB.restrictScalars Complex)
    (n : isotypicLiftedMultiplicity.{0} nB) :
    M.activeSelectedEmbeddingCore region bcomponent WB UB
        ((a ⊗ₜ[Complex] w) ⊗ₜ[Complex] n) =
      ((M.regionSubsystem (M.interior region)).selectedFactorization
        (M.regionSubsystem region)
        (by
          intro site hsite
          exact (Finset.mem_sdiff.mp hsite).1)).symm
        (a ⊗ₜ[Complex]
          (bcomponent.1.restrictScalars Complex).subtype
            (UB.symm (w ⊗ₜ[Complex] n))) := by
  rfl

end BPTCommutingProjectorModel

end Bounds
end QEC
