import QEC.Bounds.BPTDisentangling.Assembly.AssemblyTransport
import QEC.Bounds.BPTDisentangling.Assembly.AssemblyDisentangling
import QEC.Bounds.BPTDisentangling.SeparatedUnionBridge

/-!
# BPT commuting-projector disentangling

Internal proof layer for the finite-dimensional BPT Disentangling Lemma.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 800000 in
private theorem disentangled_of_finalAssemblyTransportWitness
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
    (P_D : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
        (M.fourFactorD region)))
    (hfinal : FinalAssemblyTransportWitness M
      region bcomponent ccomponent WB WC UB UC P_D) :
    M.Disentangled region := by
  cases hfinal with
  | intro phi n0 c0 U hphi hn0 hc0 hP_D htransport =>
    exact M.disentangled_of_finalAssemblyFactorization
      region bcomponent ccomponent WB WC UB UC P_D phi n0 c0 U
      hphi hn0 hc0 hP_D htransport

/--
If `region` and its external boundary are erasure recoverable, the physical
boundary unitary disentangles the full code projector into a pure region factor
and an arbitrary orthogonal projection on the complement.
-/
theorem disentangled_of_region_and_externalBoundary_recoverable
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hM : M.RegionErasureRecoverable region)
    (hC : M.RegionErasureRecoverable (M.externalBoundary region)) :
    M.Disentangled region := by
  by_cases hzero : M.codeSpace.carrier = ⊥
  · exact M.disentangled_of_codeSpace_carrier_eq_bot region hzero
  have hactual :=
    M.exists_actual_fixed_active_data_productRankOneTensor_for_D5_of_nonzero_code
      region hzero hM hC
  cases hactual with
  | intro ccomponent bcomponent nC WC UC P_D nB WB UB Qsecond hfixed =>
    exact disentangled_of_finalAssemblyTransportWitness
      M region bcomponent ccomponent WB WC UB UC P_D
      (finalAssemblyTransportWitness_of_fixedActiveData
        M region bcomponent ccomponent WB WC UB UC P_D Qsecond hfixed)


end BPTCommutingProjectorModel

end Bounds
end QEC
