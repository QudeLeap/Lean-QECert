import QEC.Bounds.BPTDisentangling.FourFactor
noncomputable section

namespace QEC
namespace Bounds
open Classical

open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem regionErasureRecoverable_of_codeSpace_carrier_eq_bot
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier = ⊥) :
    M.RegionErasureRecoverable region := by
  apply ((M.regionSubsystem region).noInformationOn_iff_exists_erasureRecovery
    M.codeSpace L.localDimension_positive).mp
  exact Semantics.QuditSubsystem.noInformationOn_of_carrier_eq_bot
    M.codeSpace (M.regionSubsystem region) hcode

/--
Concrete local extensions on disjoint site regions commute.  The proof uses
the selected/complement tensor factorization of `left`: `right` is lifted to
the literal complement and the two maps become `A tensor 1` and `1 tensor B`.
-/
theorem commute_of_disjoint_region_support
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hdisjoint : Disjoint left right)
    {A B : Semantics.Operator L.Register}
    (hA : (M.regionSubsystem left).OperatorSupportedOnRegister A)
    (hB : (M.regionSubsystem right).OperatorSupportedOnRegister B) :
    Commute A B := by
  rcases hA with ⟨localA, hlocalA⟩
  have hrightComplement : right ⊆ leftᶜ := by
    intro site hright
    exact Finset.mem_compl.mpr (fun hleft =>
      (Finset.disjoint_left.mp hdisjoint) hleft hright)
  have hBComplement :
      (M.regionSubsystem leftᶜ).OperatorSupportedOnRegister B := by
    apply operatorSupportedOnRegister_of_subset (M.regionSubsystem right)
      (M.regionSubsystem leftᶜ)
    · simpa [BPTCommutingProjectorModel.regionSubsystem] using hrightComplement
    · exact hB
  rcases hBComplement with ⟨localB, hlocalB⟩
  let S := M.regionSubsystem left
  let relabel := M.regionComplementCoordinateRelabel left
  have hcomplement :
      B = extendComplementToRegister S (relabel.conjOperator localB) := by
    calc
      B = (M.regionSubsystem leftᶜ).extendLocalToRegister localB := hlocalB.symm
      _ = extendComplementToRegister S (relabel.conjOperator localB) := by
        simpa [S, relabel] using
          (M.extendLocalToRegister_complement_eq_extendComplementToRegister left localB)
  rw [← hlocalA, hcomplement]
  change
    S.registerFactorization.symm.conjOperator
        (TensorProduct.map localA (1 : Semantics.Operator S.complementSystem)) *
      S.registerFactorization.symm.conjOperator
        (TensorProduct.map (1 : Semantics.Operator S.selectedSystem)
          (relabel.conjOperator localB)) =
    S.registerFactorization.symm.conjOperator
        (TensorProduct.map (1 : Semantics.Operator S.selectedSystem)
          (relabel.conjOperator localB)) *
      S.registerFactorization.symm.conjOperator
        (TensorProduct.map localA (1 : Semantics.Operator S.complementSystem))
  rw [← Semantics.UnitaryTransport.conjOperator_mul,
    ← Semantics.UnitaryTransport.conjOperator_mul]
  congr 1
  rw [← TensorProduct.map_mul, ← TensorProduct.map_mul]
  simp

/-- A unitary supported away from a local operator fixes that operator by conjugation. -/
theorem unitary_conjOperator_eq_of_disjoint_region_support
    (M : BPTCommutingProjectorModel L kappa) (unitaryRegion operatorRegion : Finset L.Site)
    (hdisjoint : Disjoint unitaryRegion operatorRegion)
    (U : Semantics.UnitaryTransport L.Register L.Register)
    (hU : M.UnitarySupportedOn unitaryRegion U)
    {B : Semantics.Operator L.Register}
    (hB : (M.regionSubsystem operatorRegion).OperatorSupportedOnRegister B) :
    U.conjOperator B = B := by
  apply unitaryTransport_conjOperator_eq_of_intertwines U B B
  exact (M.commute_of_disjoint_region_support unitaryRegion operatorRegion hdisjoint hU hB).eq

/--
Scalar compression of a local operator is preserved when the code projector is
conjugated by a unitary supported on a disjoint region.
-/
theorem scalar_compression_conj_of_disjoint_region_support
    (M : BPTCommutingProjectorModel L kappa) (unitaryRegion operatorRegion : Finset L.Site)
    (hdisjoint : Disjoint unitaryRegion operatorRegion)
    (U : Semantics.UnitaryTransport L.Register L.Register)
    (hU : M.UnitarySupportedOn unitaryRegion U)
    {B : Semantics.Operator L.Register}
    (hB : (M.regionSubsystem operatorRegion).OperatorSupportedOnRegister B)
    {scalar : Complex}
    (hscalar : M.fullCodeProjector * B * M.fullCodeProjector =
      scalar • M.fullCodeProjector) :
    U.conjOperator M.fullCodeProjector * B * U.conjOperator M.fullCodeProjector =
      scalar • U.conjOperator M.fullCodeProjector := by
  have hfixed : U.conjOperator B = B :=
    M.unitary_conjOperator_eq_of_disjoint_region_support
      unitaryRegion operatorRegion hdisjoint U hU hB
  calc
    U.conjOperator M.fullCodeProjector * B * U.conjOperator M.fullCodeProjector =
        U.conjOperator M.fullCodeProjector * U.conjOperator B *
          U.conjOperator M.fullCodeProjector := by rw [hfixed]
    _ = U.conjOperator (M.fullCodeProjector * B * M.fullCodeProjector) := by
      rw [Semantics.UnitaryTransport.conjOperator_mul,
        Semantics.UnitaryTransport.conjOperator_mul]
    _ = U.conjOperator (scalar • M.fullCodeProjector) :=
      congrArg U.conjOperator hscalar
    _ = scalar • U.conjOperator M.fullCodeProjector := by
      exact U.conjOperatorLinearMap.map_smul scalar M.fullCodeProjector

end BPTCommutingProjectorModel
end Bounds
end QEC
