import QEC.Bounds.BPTDisentangling.SecondCut.RankOne

/-!
# BPT second-cut physical locality transport

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

/--
An arbitrary operator supported on the physical region `M` becomes the
literal left `AB` lift in the four-factor coordinates.  This is the
locality transport used immediately below to carry hM no-information into
the second BV03 block, rather than only for the distinguished source
projector `Pi_AB`.
-/
theorem fourFactorTransport_conj_regionLift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (M.regionSubsystem region).selectedSystem) :
    (M.fourFactorTransport region).conjOperator
      ((M.regionSubsystem region).extendLocalToRegister P) =
      M.fourFactorExtendAB region
        (((M.regionSubsystem (M.interior region)).selectedFactorization
          (M.regionSubsystem region) (by
            intro site hsite
            exact (Finset.mem_sdiff.mp hsite).1)).conjOperator P) := by
  let A := M.regionSubsystem (M.interior region)
  let AB := M.regionSubsystem region
  let ABC := M.regionSubsystem (region ∪ M.externalBoundary region)
  have hAAB : A.selected ⊆ AB.selected := by
    intro site hsite
    exact (Finset.mem_sdiff.mp hsite).1
  have hABABC : AB.selected ⊆ ABC.selected := by
    intro site hsite
    exact Finset.mem_union_left _ hsite
  dsimp [fourFactorTransport]
  rw [composeUnitaryTransport_conjOperator,
    composeUnitaryTransport_conjOperator]
  rw [nestedFactorizationLeft_conj_extendLocalToRegister AB ABC hABABC]
  rw [unitaryRTensor_conj_tensorMap_left]
  rfl

/--
The preceding physical-region locality equation in the literal second-cut
coordinates.  It is the exact route by which a probe of the eventual
`Pleft` factor is supplied to `RegionErasureRecoverable region`.
-/
theorem secondCutGlobalCoordinateTransport_conj_regionLift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (M.regionSubsystem region).selectedSystem) :
    (M.secondCutGlobalCoordinateTransport region).conjOperator
      ((M.regionSubsystem region).extendLocalToRegister P) =
      overlapLiftLeft
        (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
        (((M.regionSubsystem (M.interior region)).selectedFactorization
          (M.regionSubsystem region) (by
            intro site hsite
            exact (Finset.mem_sdiff.mp hsite).1)).conjOperator P) := by
  let A := M.regionSubsystem (M.interior region)
  let AB := M.regionSubsystem region
  let E := (A.selectedFactorization AB (by
    intro site hsite
    exact (Finset.mem_sdiff.mp hsite).1)).conjOperator P
  let U := M.secondCutCoordinateTransport region
  have hfour : (M.fourFactorTransport region).conjOperator
      (AB.extendLocalToRegister P) = M.fourFactorExtendAB region E := by
    simpa [A, AB, E] using M.fourFactorTransport_conj_regionLift region P
  have hsecond : U.conjOperator
      (overlapLiftLeft
        (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) E) =
      M.fourFactorExtendAB region E := by
    simpa [U] using M.secondCutCoordinateTransport_conj_overlapLiftLeft_AB region E
  change (composeUnitaryTransport (M.fourFactorTransport region) U.symm).conjOperator
      (AB.extendLocalToRegister P) =
    overlapLiftLeft
      (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) E
  rw [composeUnitaryTransport_conjOperator]
  calc
    U.symm.conjOperator
        ((M.fourFactorTransport region).conjOperator (AB.extendLocalToRegister P)) =
        U.symm.conjOperator (M.fourFactorExtendAB region E) :=
      congrArg U.symm.conjOperator hfour
    _ = U.symm.conjOperator
        (U.conjOperator
          (overlapLiftLeft
            (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) E)) :=
      congrArg U.symm.conjOperator hsecond.symm
    _ = overlapLiftLeft
        (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) E :=
      U.symm_conjOperator_conjOperator _

end BPTCommutingProjectorModel

end Bounds
end QEC
