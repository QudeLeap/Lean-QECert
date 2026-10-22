import QEC.Bounds.BPTDisentangling.NoCloning.Fixed.Product
import QEC.Bounds.BPTDisentangling.NoCloning.ActualProductData

/-!
# BPT nonzero-code rank-one product closure

Cacheable internal proof layer for the finite-dimensional BPT Disentangling Lemma.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

-- Internal cache boundary; do not index its large dependent type as an automated premise.
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.modifyEnv fun env =>
    Lean.LibrarySuggestions.nameDenyListExt.addEntry env
      "exists_actual_fixed_active_data_productRankOneTensor_for_D5_of_nonzero_code"

set_option maxHeartbeats 1800000 in
/--
Choose one actual common-factor witness package and retain it through the
fixed-witness D2 product block.  The final nested proposition is the stronger
fixed-data theorem above, so its `phi`, joint compression, reconstruction, and
D1 product equation all remain attached to these exact sector witnesses.
-/
theorem exists_actual_fixed_active_data_productRankOneTensor_for_D5_of_nonzero_code
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (hM : M.RegionErasureRecoverable region)
    (hC : M.RegionErasureRecoverable (M.externalBoundary region)) :
    M.ActualFixedActiveDataProductRankOneTensor region := by
  rcases M.exists_actual_commonFactorization_of_nonzero_code region hcode hM hC with
    ⟨ccomponent, bcomponent, hCactive, hBactive, nC, hnC, WC, UC, Pfirst, P_D,
      hCleft, hCright, nB, hnB, WB, UB, Pleft, Qsecond, phi, hBleft, hBright, hphi,
      hcommon⟩
  letI : NeZero nC := hnC
  letI : NeZero nB := hnB
  have hproduct := M.exists_productRankOneTensor_of_fixed_active_data_for_D5
    region hcode hM hC bcomponent ccomponent WB WC UB UC Pfirst P_D Pleft Qsecond
      hCactive hBactive hCleft hCright hBleft hBright
  exact ⟨ccomponent, bcomponent, nC, WC, UC, P_D, nB, WB, UB, Qsecond, hproduct⟩

end BPTCommutingProjectorModel

end Bounds
end QEC
