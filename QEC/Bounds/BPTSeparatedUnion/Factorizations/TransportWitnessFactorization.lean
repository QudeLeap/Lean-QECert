import QEC.Bounds.BPTSeparatedUnion.Factorizations.ExteriorFactorization
import QEC.Bounds.BPTDisentangling.Assembly.AssemblyTransportCore
import QEC.Bounds.BPTSeparatedUnion.Separation

/-! # Consume a final transport witness into separated factorization -/

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
      "sourceFactorization_of_finalAssemblyTransportWitness_on_actualSeparatedRight"

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 2000 in
theorem sourceFactorization_of_finalAssemblyTransportWitness_on_actualSeparatedRight
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hseparated : M.ActualProjectorSeparated left right)
    (hdisjoint : Disjoint left right)
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal left))
      (M.fourFactorB left))
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC left))
      (M.fourFactorC left))
    {nB nC : Nat} [NeZero nB] [NeZero nC]
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal left))
      (M.fourFactorB left))
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC left))
      (M.fourFactorC left))
    (UB : Semantics.UnitaryTransport (bcomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WB.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nB)))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC)))
    (P_D : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
        (M.fourFactorD left)))
    (hwitness : FinalAssemblyTransportWitness
      M left bcomponent ccomponent WB WC UB UC P_D) :
    ∀ (A : Semantics.Operator (M.regionSubsystem left).selectedSystem)
      (B : Semantics.Operator (M.regionSubsystem right).selectedSystem),
      ∃ coefficient : Complex,
        M.fullCodeProjector * (M.regionSubsystem left).extendLocalToRegister A *
            (M.regionSubsystem right).extendLocalToRegister B * M.fullCodeProjector =
          coefficient •
            (M.fullCodeProjector * (M.regionSubsystem right).extendLocalToRegister B *
              M.fullCodeProjector) := by
  cases hwitness with
  | intro phi n0 c0 U hphi hn0 hc0 _hP_D htransport =>
      apply M.sourceFactorization_of_finalAssemblyWitness_on_actualSeparatedRight
        left right hseparated hdisjoint bcomponent ccomponent WB WC UB UC P_D phi n0 c0 U
        hphi hn0 hc0
      exact htransport

end BPTCommutingProjectorModel
end Bounds
end QEC
