import QEC.Bounds.BPTDisentangling.SecondCut.LeftProjection

/-!
# BPT second-cut physical left-factor chain

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

set_option maxHeartbeats 800000 in
/--
For the hM-active second-cut sector, a nonempty physical code gives a nonzero
`Pleft` factor in the actual compressed `Pleft tensor Qright` equation.
-/
theorem secondCut_Pleft_ne_zero_of_nonzero_code
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    {n : Nat} [NeZero n]
    (W : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)) :
    let A := M.fourFactorA region
    let H := component.1.restrictScalars Complex
    let W0 := W.restrictScalars Complex
    let N := isotypicLiftedMultiplicity.{0} n
    let CD := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)
    ∀ (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W0 N))
      (Pleft : Semantics.Operator (Semantics.CompositeSystem A W0))
      (Qright : Semantics.Operator (Semantics.CompositeSystem N CD)),
      M.secondCutCodeLift region * M.secondCutSectorLift region component =
          M.secondCutCodeLift region →
      (unitaryLTensor A U).conjOperator
          (overlapProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) component) =
          rightTensorExtensionAfterLeft A W0 N Pleft →
      (unitaryRTensor U CD).conjOperator
          (overlapRightProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) (M.secondCutProjectorBbarM region) component) =
          leftTensorExtensionBeforeRight W0 N CD Qright →
      Pleft ≠ 0 := by
  dsimp only
  intro U Pleft Qright hactive hleft hright
  have hRcompressed := M.secondCutCodeLift_active_compression_ne_zero_of_nonzero_code
    region hcode component hactive
  have hblock := M.secondCut_compressed_overlap_block_product
    region component W U Pleft Qright hleft hright
  exact left_factor_ne_zero_of_nonzero_unitary_tensor_block
    (isotypicSectorBlockTransportLeft (M.fourFactorA region)
      (component.1.restrictScalars Complex) (W.restrictScalars Complex)
      (isotypicLiftedMultiplicity.{0} n)
      (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) U)
    ((LinearMap.adjoint
      (tensorTripleSubtypeEmbedding (A := M.fourFactorA region)
        (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
        (component.1.restrictScalars Complex))).comp
      ((M.secondCutCodeLift region).comp
        (tensorTripleSubtypeEmbedding (A := M.fourFactorA region)
        (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
        (component.1.restrictScalars Complex))))
    Pleft Qright
    hRcompressed hblock

/--
Region correctability makes every literal `A tensor B` probe scalar on the
actual second-cut code lift.  The equality is transported from the physical
region-local extension, so this is the hM input for the source `Pi_AB'`
rank-one argument rather than an abstract code assumption.
-/
theorem secondCut_all_leftLocal_scalar_compression_of_region_recoverable
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hM : M.RegionErasureRecoverable region)
    (E : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))) :
    ∃ scalar : Complex,
      M.secondCutCodeLift region *
          overlapLiftLeft
            (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) E *
          M.secondCutCodeLift region = scalar • M.secondCutCodeLift region := by
  let A := M.regionSubsystem (M.interior region)
  let AB := M.regionSubsystem region
  let CD := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)
  have hAAB : A.selected ⊆ AB.selected := by
    intro site hsite
    exact (Finset.mem_sdiff.mp hsite).1
  let split := A.selectedFactorization AB hAAB
  let Elocal : Semantics.Operator AB.selectedSystem := split.symm.conjOperator E
  let Ephysical : Semantics.Operator L.Register := AB.extendLocalToRegister Elocal
  let G := M.secondCutGlobalCoordinateTransport region
  let R := M.secondCutCodeLift region
  have hInformation := M.regionErasureRecoverable_implies_noInformationOn region hM
  have hAll := (AB.noInformationOn_iff_allLocalScalarCompression M.codeSpace).mp hInformation
  rcases hAll Elocal with ⟨scalar, hscalar⟩
  have hscalar' : M.fullCodeProjector * Ephysical * M.fullCodeProjector =
      scalar • M.fullCodeProjector := by
    change (M.fullCodeProjector.comp Ephysical).comp M.fullCodeProjector = _
    rw [LinearMap.comp_assoc]
    exact hscalar
  have hGcode : G.conjOperator M.fullCodeProjector = R := by
    simpa [G, R] using M.secondCutGlobalCoordinateTransport_conj_fullCodeProjector region
  have hGlocal : G.conjOperator Ephysical = overlapLiftLeft (C := CD) E := by
    calc
      G.conjOperator Ephysical = overlapLiftLeft (C := CD) (split.conjOperator Elocal) := by
        simpa [G, Ephysical] using
          M.secondCutGlobalCoordinateTransport_conj_regionLift region Elocal
      _ = overlapLiftLeft (C := CD) E := by
        rw [show split.conjOperator Elocal = E by
          simpa [Elocal] using split.conjOperator_symm_conjOperator E]
  refine ⟨scalar, ?_⟩
  calc
    R * overlapLiftLeft (C := CD) E * R =
        G.conjOperator M.fullCodeProjector * G.conjOperator Ephysical *
          G.conjOperator M.fullCodeProjector := by
      simpa only [hGcode, hGlocal]
    _ = G.conjOperator (M.fullCodeProjector * Ephysical * M.fullCodeProjector) := by
      calc
        G.conjOperator M.fullCodeProjector * G.conjOperator Ephysical *
            G.conjOperator M.fullCodeProjector =
            G.conjOperator (M.fullCodeProjector * Ephysical) *
              G.conjOperator M.fullCodeProjector :=
          congrArg (fun operator => operator * G.conjOperator M.fullCodeProjector)
            (Semantics.UnitaryTransport.conjOperator_mul G M.fullCodeProjector Ephysical).symm
        _ = G.conjOperator ((M.fullCodeProjector * Ephysical) * M.fullCodeProjector) :=
          (Semantics.UnitaryTransport.conjOperator_mul G
            (M.fullCodeProjector * Ephysical) M.fullCodeProjector).symm
        _ = G.conjOperator (M.fullCodeProjector * Ephysical * M.fullCodeProjector) := rfl
    _ = G.conjOperator (scalar • M.fullCodeProjector) :=
      congrArg G.conjOperator hscalar'
    _ = scalar • G.conjOperator M.fullCodeProjector := by
      exact G.conjOperatorLinearMap.map_smul scalar M.fullCodeProjector
    _ = scalar • R := by simpa only [hGcode]

end BPTCommutingProjectorModel

end Bounds
end QEC
