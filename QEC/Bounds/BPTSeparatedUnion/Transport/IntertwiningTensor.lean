import QEC.Bounds.BPTSeparatedUnion.Transport.IntertwiningComplement
import QEC.Bounds.BPTSeparatedUnion.Transport.CompressionExteriorActiveStatement

/-!
# Exterior action on the active final-assembly tensor embedding

The complement intertwining equation is lifted through the selected tensor
factor without changing the selected coordinates.
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
      "finalAssemblyCompressionActiveEmbedding_intertwines_exteriorCompression"

set_option maxHeartbeats 1800000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option maxRecDepth 2000 in
theorem finalAssemblyCompressionActiveEmbedding_intertwines_exteriorCompression
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
    (P : Semantics.Operator (M.regionSubsystem (M.exterior region)).selectedSystem) :
    let S := M.regionSubsystem region
    let J := M.finalAssemblyCompressionActiveEmbedding
      region bcomponent ccomponent WB WC UB UC
    (TensorProduct.map (1 : Semantics.Operator S.selectedSystem)
        (M.exteriorCompressionComplementAction region P)).comp J =
      J.comp (M.finalAssemblyCompressionActiveResult region nB nC WB WC
        (M.exteriorCompressionWitness region P)) := by
  dsimp only [finalAssemblyCompressionActiveEmbedding]
  let S := M.regionSubsystem region
  let eSel := M.activeSelectedEmbeddingCore region bcomponent WB UB
  let eComp := M.activeComplementEmbeddingCore region ccomponent WC UC
  let Q := M.exteriorCompressionComplementAction region P
  let Dcomp : Semantics.Operator (ActiveComplementDomain M region nC WC) :=
    TensorProduct.map (1 : Semantics.Operator (WC.restrictScalars Complex))
      (TensorProduct.map
        (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} nC))
        (M.exteriorCompressionWitness region P))
  have hComp : Q.comp eComp.toLinearMap = eComp.toLinearMap.comp Dcomp := by
    simpa only [Q, eComp, Dcomp] using
      M.activeComplementEmbeddingCore_intertwines_exteriorCompression
        region ccomponent WC UC P
  apply TensorProduct.ext'
  intro x y
  simp only [TensorProduct.map_tmul, LinearMap.comp_apply, Module.End.one_apply,
    finalAssemblyCompressionActiveResult]
  have hComp_y := LinearMap.congr_fun hComp y
  exact congrArg (fun z => eSel.toLinearMap x ⊗ₜ[Complex] z) hComp_y

end BPTCommutingProjectorModel
end Bounds
end QEC
