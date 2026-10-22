import QEC.Bounds.BPTSeparatedUnion.Transport.ExteriorAction

/-!
# Exterior-compression witness

The source-derived exterior factor is chosen once so downstream active
compression does not repeatedly elaborate the large existential eliminator.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

/-- The concrete exterior factor supplied by region factorization. -/
noncomputable def exteriorCompressionWitness
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (M.regionSubsystem (M.exterior region)).selectedSystem) :
    Semantics.Operator (M.fourFactorD region) :=
  Classical.choose (M.regionFactorization_conj_exteriorLocal region P)

/-- The complement-coordinate action determined by the canonical exterior witness. -/
noncomputable def exteriorCompressionComplementAction
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (M.regionSubsystem (M.exterior region)).selectedSystem) :
    Semantics.Operator (M.regionSubsystem region).complementSystem :=
  let S := M.regionSubsystem region
  let T := M.regionSubsystem (region ∪ M.externalBoundary region)
  let splitCD := S.complementFactorization T (by
    intro site hsite
    exact Finset.mem_union_left _ hsite)
  splitCD.symm.conjOperator
    (TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region))
      (M.exteriorCompressionWitness region P))

-- The dependent witness specification is too large to be an automated premise.
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.modifyEnv fun env =>
    Lean.LibrarySuggestions.nameDenyListExt.addEntry env
      "exteriorCompressionWitness_spec"

set_option maxHeartbeats 500000 in
theorem exteriorCompressionWitness_spec
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (M.regionSubsystem (M.exterior region)).selectedSystem) :
    let S := M.regionSubsystem region
    S.registerFactorization.conjOperator
        ((M.regionSubsystem (M.exterior region)).extendLocalToRegister P) =
      TensorProduct.map (1 : Semantics.Operator S.selectedSystem)
        (M.exteriorCompressionComplementAction region P) := by
  exact Classical.choose_spec (M.regionFactorization_conj_exteriorLocal region P)

end BPTCommutingProjectorModel
end Bounds
end QEC
