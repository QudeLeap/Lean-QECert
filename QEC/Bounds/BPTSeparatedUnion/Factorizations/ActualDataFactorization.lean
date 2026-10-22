import QEC.Bounds.BPTSeparatedUnion.Factorizations.FixedDataFactorization
import QEC.Bounds.BPTSeparatedUnion.Separation

/-! # Consume actual active data into separated factorization -/

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
      "sourceFactorization_of_actualFixedActiveData_on_actualSeparatedRight"

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 2000 in
theorem sourceFactorization_of_actualFixedActiveData_on_actualSeparatedRight
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hseparated : M.ActualProjectorSeparated left right)
    (hdisjoint : Disjoint left right)
    (hactual : M.ActualFixedActiveDataProductRankOneTensor left) :
    ∀ (A : Semantics.Operator (M.regionSubsystem left).selectedSystem)
      (B : Semantics.Operator (M.regionSubsystem right).selectedSystem),
      ∃ coefficient : Complex,
        M.fullCodeProjector * (M.regionSubsystem left).extendLocalToRegister A *
            (M.regionSubsystem right).extendLocalToRegister B * M.fullCodeProjector =
          coefficient •
            (M.fullCodeProjector * (M.regionSubsystem right).extendLocalToRegister B *
              M.fullCodeProjector) := by
  cases hactual with
  | intro ccomponent bcomponent nC WC UC P_D nB WB UB Qsecond hfixed =>
      exact M.sourceFactorization_of_fixedActiveData_on_actualSeparatedRight
        left right hseparated hdisjoint bcomponent ccomponent WB WC UB UC P_D Qsecond hfixed

end BPTCommutingProjectorModel
end Bounds
end QEC
