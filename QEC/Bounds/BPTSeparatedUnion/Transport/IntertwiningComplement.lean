import QEC.Bounds.BPTSeparatedUnion.Transport.IntertwiningStatement
import QEC.Bounds.BPTSeparatedUnion.Transport.ComplementIntertwiningCore

/-!
# Exterior action on the active complement embedding

The canonical exterior witness acts only on the final complement factor.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.modifyEnv fun env =>
    Lean.LibrarySuggestions.nameDenyListExt.addEntry env
      "activeComplementEmbeddingCore_intertwines_exteriorCompression"

set_option maxHeartbeats 3000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem activeComplementEmbeddingCore_intertwines_exteriorCompression
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
    (P : Semantics.Operator (M.regionSubsystem (M.exterior region)).selectedSystem) :
    let eComp := M.activeComplementEmbeddingCore region ccomponent WC UC
    let Dcomp : Semantics.Operator (ActiveComplementDomain M region nC WC) :=
      TensorProduct.map (1 : Semantics.Operator (WC.restrictScalars Complex))
        (TensorProduct.map
          (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} nC))
          (M.exteriorCompressionWitness region P))
    (M.exteriorCompressionComplementAction region P).comp eComp.toLinearMap =
      eComp.toLinearMap.comp Dcomp := by
  dsimp only
  let S := M.regionSubsystem region
  let T := M.regionSubsystem (region ∪ M.externalBoundary region)
  let splitCD := S.complementFactorization T (by
    intro site hsite
    exact Finset.mem_union_left _ hsite)
  let Q := M.exteriorCompressionComplementAction region P
  let eComp := M.activeComplementEmbeddingCore region ccomponent WC UC
  let Dcomp : Semantics.Operator (ActiveComplementDomain M region nC WC) :=
    TensorProduct.map (1 : Semantics.Operator (WC.restrictScalars Complex))
      (TensorProduct.map
        (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} nC))
        (M.exteriorCompressionWitness region P))
  let eC : Semantics.CompositeSystem (WC.restrictScalars Complex)
      (isotypicLiftedMultiplicity.{0} nC) →ₗᵢ[Complex] M.fourFactorC region :=
    (ccomponent.1.restrictScalars Complex).subtypeₗᵢ.comp
      UC.symm.toLinearIsometryEquiv.toLinearIsometry
  let reassociate := tensorAssociatorUnitary (WC.restrictScalars Complex)
    (isotypicLiftedMultiplicity.{0} nC) (M.fourFactorD region)
  let Jcomp := TensorProduct.map eC.toLinearMap
    (1 : Semantics.Operator (M.fourFactorD region))
  let Ecd := Jcomp.comp reassociate.symm.toLinearEquiv.toLinearMap
  have heComp : eComp.toLinearMap =
      splitCD.symm.toLinearEquiv.toLinearMap.comp Ecd := by
    rfl
  have hCoordinates := complementEmbedding_intertwines_coordinates
    splitCD eC.toLinearMap (M.exteriorCompressionWitness region P)
  dsimp only at hCoordinates
  change Q.comp eComp.toLinearMap = eComp.toLinearMap.comp Dcomp
  rw [heComp]
  change
    (splitCD.symm.conjOperator
      (TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region))
        (M.exteriorCompressionWitness region P))).comp
        (splitCD.symm.toLinearEquiv.toLinearMap.comp Ecd) =
      (splitCD.symm.toLinearEquiv.toLinearMap.comp Ecd).comp Dcomp
  exact hCoordinates

end BPTCommutingProjectorModel
end Bounds
end QEC
