import QEC.Bounds.BPTSeparatedUnion.Factorizations.ActualDataFactorization
import QEC.Bounds.BPTSeparatedUnion.Separation

/-! # Actual-separation factorization for the terminal BPT union lemma -/

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
      "sourceFactorization_of_actualProjectorSeparated"

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 2000 in
theorem sourceFactorization_of_actualProjectorSeparated
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hseparated : M.ActualProjectorSeparated left right)
    (hdisjoint : Disjoint left right)
    (hleft : M.RegionErasureRecoverable left)
    (hexternal : M.RegionErasureRecoverable (M.externalBoundary left))
    (hcode : M.codeSpace.carrier ≠ ⊥) :
    ∀ (A : Semantics.Operator (M.regionSubsystem left).selectedSystem)
      (B : Semantics.Operator (M.regionSubsystem right).selectedSystem),
      ∃ coefficient : Complex,
        M.fullCodeProjector * (M.regionSubsystem left).extendLocalToRegister A *
            (M.regionSubsystem right).extendLocalToRegister B * M.fullCodeProjector =
          coefficient •
            (M.fullCodeProjector * (M.regionSubsystem right).extendLocalToRegister B *
              M.fullCodeProjector) := by
  have hactual := M.exists_actual_fixed_active_data_productRankOneTensor_for_D5_of_nonzero_code
    left hcode hleft hexternal
  exact M.sourceFactorization_of_actualFixedActiveData_on_actualSeparatedRight
    left right hseparated hdisjoint hactual

end BPTCommutingProjectorModel
end Bounds
end QEC
