import QEC.Bounds.BPTDisentangling.FourFactor
noncomputable section

namespace QEC
namespace Bounds
open Classical

open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

set_option maxHeartbeats 1000000 in
theorem fourFactorTransport_conj_expandedExteriorLift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (Z : Semantics.Operator (M.fourFactorD region)) :
    (M.fourFactorTransport region).conjOperator
      (extendComplementToRegister
        (M.regionSubsystem (region ∪ M.externalBoundary region)) Z) =
      TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
        (TensorProduct.map (1 : Semantics.Operator (M.fourFactorB region))
          (TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region)) Z)) := by
  let A := M.regionSubsystem (M.interior region)
  let AB := M.regionSubsystem region
  let ABC := M.regionSubsystem (region ∪ M.externalBoundary region)
  have hAAB : A.selected ⊆ AB.selected := by
    intro site hsite
    exact (Finset.mem_sdiff.mp hsite).1
  have hABABC : AB.selected ⊆ ABC.selected := by
    intro site hsite
    exact Finset.mem_union_left _ hsite
  let splitAB : Semantics.UnitaryTransport AB.selectedSystem
      (Semantics.CompositeSystem A.selectedSystem (A.additionalRetainedSystem AB)) := by
    let e := A.selectedFactorization AB hAAB
    exact { toLinearEquiv := e.toLinearEquiv, map_inner := e.map_inner }
  let nested := nestedFactorizationRight AB ABC hABABC
  have hnested : nested =
      composeUnitaryTransport
        (composeUnitaryTransport ABC.registerFactorization
          (unitaryRTensor (AB.selectedFactorization ABC hABABC) ABC.complementSystem))
        (tensorAssociatorUnitary AB.selectedSystem
          (AB.additionalRetainedSystem ABC) ABC.complementSystem) := by
    apply unitaryTransport_ext
    rfl
  have hfirst : nested.conjOperator
      (extendComplementToRegister ABC Z) =
      TensorProduct.map (1 : Semantics.Operator AB.selectedSystem)
        (TensorProduct.map
          (1 : Semantics.Operator (AB.additionalRetainedSystem ABC)) Z) := by
    rw [hnested, composeUnitaryTransport_conjOperator,
      composeUnitaryTransport_conjOperator]
    unfold extendComplementToRegister
    rw [ABC.registerFactorization.conjOperator_symm_conjOperator]
    rw [unitaryRTensor_conj_tensorMap_right]
    rw [show (1 : Semantics.Operator
      (Semantics.CompositeSystem AB.selectedSystem
        (AB.additionalRetainedSystem ABC))) =
        TensorProduct.map (1 : Semantics.Operator AB.selectedSystem)
          (1 : Semantics.Operator (AB.additionalRetainedSystem ABC)) by
      symm
      exact TensorProduct.map_one]
    exact tensorAssociatorUnitary_conj_tensorMap
      (1 : Semantics.Operator AB.selectedSystem)
      (1 : Semantics.Operator (AB.additionalRetainedSystem ABC)) Z
  calc
    (M.fourFactorTransport region).conjOperator
        (extendComplementToRegister ABC Z) =
      (M.fourFactorTransportFromNestedRegion region).conjOperator
        (extendComplementToRegister ABC Z) := by
          exact congrArg (fun transport => transport.conjOperator
            (extendComplementToRegister ABC Z))
            (M.fourFactorTransport_eq_fourFactorTransportFromNestedRegion region)
    _ = (tensorAssociatorUnitary A.selectedSystem
        (A.additionalRetainedSystem AB)
        (Semantics.CompositeSystem (AB.additionalRetainedSystem ABC)
          ABC.complementSystem)).conjOperator
        ((unitaryRTensor splitAB
          (Semantics.CompositeSystem (AB.additionalRetainedSystem ABC)
            ABC.complementSystem)).conjOperator
          (nested.conjOperator (extendComplementToRegister ABC Z))) := by
          dsimp [fourFactorTransportFromNestedRegion]
          rw [composeUnitaryTransport_conjOperator,
            composeUnitaryTransport_conjOperator]
    _ = (tensorAssociatorUnitary A.selectedSystem
        (A.additionalRetainedSystem AB)
        (Semantics.CompositeSystem (AB.additionalRetainedSystem ABC)
          ABC.complementSystem)).conjOperator
        ((unitaryRTensor splitAB
          (Semantics.CompositeSystem (AB.additionalRetainedSystem ABC)
            ABC.complementSystem)).conjOperator
          (TensorProduct.map (1 : Semantics.Operator AB.selectedSystem)
            (TensorProduct.map
              (1 : Semantics.Operator (AB.additionalRetainedSystem ABC)) Z))) := by
          rw [hfirst]
    _ = TensorProduct.map (1 : Semantics.Operator A.selectedSystem)
          (TensorProduct.map (1 : Semantics.Operator (A.additionalRetainedSystem AB))
          (TensorProduct.map (1 : Semantics.Operator (AB.additionalRetainedSystem ABC)) Z)) := by
          rw [unitaryRTensor_conj_tensorMap_right]
          rw [show (1 : Semantics.Operator
            (Semantics.CompositeSystem A.selectedSystem
              (A.additionalRetainedSystem AB))) =
              TensorProduct.map (1 : Semantics.Operator A.selectedSystem)
                (1 : Semantics.Operator (A.additionalRetainedSystem AB)) by
              symm
              exact TensorProduct.map_one]
          exact tensorAssociatorUnitary_conj_tensorMap
            (1 : Semantics.Operator A.selectedSystem)
            (1 : Semantics.Operator (A.additionalRetainedSystem AB))
            (TensorProduct.map (1 : Semantics.Operator
              (AB.additionalRetainedSystem ABC)) Z)

set_option maxHeartbeats 1000000 in
/--
Every operator supported in the actual source exterior has a concrete `D`
representative after the four-factor transport.  The representative is
obtained by explicit coordinate lift and relabeling, rather than by an
abstract support or factorization premise.
-/
theorem fourFactorTransport_conj_exteriorLocal_exists
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (M.regionSubsystem (M.exterior region)).selectedSystem) :
    ∃ Z : Semantics.Operator (M.fourFactorD region),
      (M.fourFactorTransport region).conjOperator
        ((M.regionSubsystem (M.exterior region)).extendLocalToRegister P) =
        TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
          (TensorProduct.map (1 : Semantics.Operator (M.fourFactorB region))
            (TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region)) Z)) := by
  let exterior := M.regionSubsystem (M.exterior region)
  let expanded := M.regionSubsystem (region ∪ M.externalBoundary region)ᶜ
  have hexterior : exterior.selected ⊆ expanded.selected := by
    intro site hsite
    apply Finset.mem_compl.mpr
    intro hmember
    rcases Finset.mem_union.mp hmember with hregion | hboundary
    · exact (Finset.mem_compl.mp (Finset.mem_sdiff.mp hsite).1) hregion
    · exact (Finset.mem_sdiff.mp hsite).2 hboundary
  let Pexpanded := liftLocalToLarger exterior expanded hexterior P
  let Z := (M.regionComplementCoordinateRelabel
    (region ∪ M.externalBoundary region)).conjOperator Pexpanded
  refine ⟨Z, ?_⟩
  have hlift : expanded.extendLocalToRegister Pexpanded =
      exterior.extendLocalToRegister P :=
    extendLocalToRegister_liftLocalToLarger exterior expanded hexterior P
  have hcomplement : expanded.extendLocalToRegister Pexpanded =
      extendComplementToRegister
        (M.regionSubsystem (region ∪ M.externalBoundary region)) Z := by
    simpa [expanded, Z] using
      (M.extendLocalToRegister_complement_eq_extendComplementToRegister
        (region ∪ M.externalBoundary region) Pexpanded)
  calc
    (M.fourFactorTransport region).conjOperator
        (exterior.extendLocalToRegister P) =
      (M.fourFactorTransport region).conjOperator
        (expanded.extendLocalToRegister Pexpanded) := by rw [hlift]
    _ = (M.fourFactorTransport region).conjOperator
        (extendComplementToRegister
          (M.regionSubsystem (region ∪ M.externalBoundary region)) Z) := by
            rw [hcomplement]
    _ = TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
        (TensorProduct.map (1 : Semantics.Operator (M.fourFactorB region))
          (TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region)) Z)) :=
      M.fourFactorTransport_conj_expandedExteriorLift region Z

/--
An actual exterior-local global operator is also a literal complement lift of
`M1`, with a `C tensor D` representative whose `C` factor is the identity.
-/
theorem exteriorLocal_eq_regionComplementLift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (M.regionSubsystem (M.exterior region)).selectedSystem) :
    ∃ Z : Semantics.Operator (M.fourFactorD region),
      (M.regionSubsystem (M.exterior region)).extendLocalToRegister P =
        extendComplementToRegister (M.regionSubsystem region)
          (((M.regionSubsystem region).complementFactorization
            (M.regionSubsystem (region ∪ M.externalBoundary region)) (by
              intro site hsite
              exact Finset.mem_union_left _ hsite)).symm.conjOperator
            (TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region)) Z)) := by
  rcases M.fourFactorTransport_conj_exteriorLocal_exists region P with ⟨Z, hExterior⟩
  let S := M.regionSubsystem region
  let T := M.regionSubsystem (region ∪ M.externalBoundary region)
  let splitCD := S.complementFactorization T (by
    intro site hsite
    exact Finset.mem_union_left _ hsite)
  let Q := splitCD.symm.conjOperator
    (TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region)) Z)
  have hComplement : (M.fourFactorTransport region).conjOperator
      (extendComplementToRegister S Q) =
      TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
        (TensorProduct.map (1 : Semantics.Operator (M.fourFactorB region))
          (TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region)) Z)) := by
    rw [M.fourFactorTransport_eq_fourFactorTransportFromRegion]
    rw [M.fourFactorTransportFromRegion_conj_extendComplementToRegister]
    rw [show splitCD.conjOperator Q =
        TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region)) Z by
      dsimp [Q]
      rw [splitCD.conjOperator_symm_conjOperator]]
    rfl
  refine ⟨Z, ?_⟩
  calc
    (M.regionSubsystem (M.exterior region)).extendLocalToRegister P =
        (M.fourFactorTransport region).symm.conjOperator
          ((M.fourFactorTransport region).conjOperator
            ((M.regionSubsystem (M.exterior region)).extendLocalToRegister P)) := by
              symm
              exact (M.fourFactorTransport region).symm_conjOperator_conjOperator _
    _ = (M.fourFactorTransport region).symm.conjOperator
        ((M.fourFactorTransport region).conjOperator (extendComplementToRegister S Q)) := by
          rw [hExterior, hComplement]
    _ = extendComplementToRegister S Q :=
      (M.fourFactorTransport region).symm_conjOperator_conjOperator _
end BPTCommutingProjectorModel
end Bounds
end QEC
