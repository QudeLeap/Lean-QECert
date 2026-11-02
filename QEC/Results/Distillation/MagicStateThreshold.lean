import Batteries.Tactic.OpenPrivate
import QEC.Distillation.MagicStateThreshold.Universality

/-!
# Magic-state fidelity thresholds and universality

Final theorem assembly over the reusable Distillation methods.
-/

noncomputable section

namespace QEC
namespace Distillation

open Semantics Semantics.Qubit

-- The complete compiler remains the owner of both physical route proofs.
open private tRoute_operationalApproximation hRoute_operationalApproximation
  from QEC.Distillation.MagicStateThreshold.Universality

/-- **BK05, Theorems 1–2.**  A one-qubit state above either the BK05 T-type
square-root fidelity threshold or the BK15 H-type square-root fidelity
threshold supplies universal adaptive ideal-Clifford computation.  The proof
uses the actual finite purification outputs and a complete, unconditioned
finite-register compiler; no success branch is postselected. -/
theorem bk05_magicState_fidelity_thresholds_imply_universality
    (rho : DensityOperator QubitSpace)
    (hthreshold :
      BK05T.bk05TFidelityThreshold < OneQubitMagic.tFidelity rho ∨
      BK15.Threshold.FStar < OneQubitMagic.hFidelity rho) :
    BK05AdaptiveUniversal rho := by
  intro Wire _ _ _ circuit precision hprecision
  rcases hthreshold with ht | hh
  · exact tRoute_operationalApproximation rho ht circuit precision hprecision
  · exact hRoute_operationalApproximation rho hh circuit precision hprecision

end Distillation
end QEC
