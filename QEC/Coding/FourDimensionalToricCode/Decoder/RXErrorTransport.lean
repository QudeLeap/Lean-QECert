import QEC.Coding.FourDimensionalToricCode.Decoder.RXCoarseGraining

/-!
# The RX q-sector algebraic error-difference transport

This module exposes the source-derived algebraic core of the RX transport
argument.  The input is only an upper
cochain supported on the Q correction sector together with the local Q
cocycle equations.  A lower correction and the degree-zero stabilizer are
chosen from the registered cohomology representative; neither is accepted
as a contract field or as caller-supplied conclusion data.

The input is sector-wide data, not an actual decoder leaf or assembly
projection.  Concrete owner/parent coherence and parent-local support remain
theorem-owned by the separate concrete-coherence bridge.
-/

namespace QEC
namespace Coding
namespace MultiscaleDecoder
namespace RXCoarseGraining

open scoped BigOperators

universe u v

variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]
variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {i : StepIndex depth}

variable {X Q Z : Type v} [Fintype X] [DecidableEq X]
  [Fintype Q] [DecidableEq Q] [Fintype Z] [DecidableEq Z]
variable {X0 : X → Type u} {Q0 : Q → Type u}
variable {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
variable [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
variable [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
variable {Lx : LocalComplexData X (C2 i.succ) (C1 i.succ)}
variable {Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ)}
variable {Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)}

namespace RXErrorTransport

private theorem qSector_error_decomposition
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (error : D.family.Cochain1 i.succ)
    (hSupported : SupportedOn A.qCorrectionSector error) :
    error = ∑ q : Q, extendWordLinear (Lq.correctionRegion q)
      (restrictWordLinear (Lq.correctionRegion q) error) := by
  rw [extend_restrict_sum_eq_mask
    (fun q => Lq.correctionRegion q)
    A.cq_correction_regions_pairwise_disjoint error]
  funext p
  by_cases hp : p ∈ correctionRegionUnion Lq
  · change error p = if p ∈ correctionRegionUnion Lq then error p else 0
    rw [if_pos hp]
  · change error p = if p ∈ correctionRegionUnion Lq then error p else 0
    rw [if_neg hp]
    exact hSupported p (by
      intro hpq
      apply hp
      simpa [A.qCorrectionSector_eq_regions] using hpq)

private theorem qSector_boundary_eq_flow
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (error : D.family.Cochain1 i.succ)
    (hSupported : SupportedOn A.qCorrectionSector error)
    (hCocycle : ∀ q,
      A.contract.rx_local_complexes.cqDelta1 q
        (restrictWordLinear (Lq.correctionRegion q) error) = 0) :
    D.family.coboundary1 i.succ error =
      ∑ q : Q, A.contract.support_decomposition.cqFlow q
        (restrictWordLinear (Lq.correctionRegion q) error) := by
  have hdecomp := qSector_error_decomposition A error hSupported
  calc
    D.family.coboundary1 i.succ error =
        D.family.coboundary1 i.succ
          (∑ q : Q, extendWordLinear (Lq.correctionRegion q)
            (restrictWordLinear (Lq.correctionRegion q) error)) :=
      congrArg (D.family.coboundary1 i.succ) hdecomp
    _ = ∑ q : Q, D.family.coboundary1 i.succ
        (extendWordLinear (Lq.correctionRegion q)
          (restrictWordLinear (Lq.correctionRegion q) error)) := by
      rw [map_sum]
    _ = ∑ q : Q, A.contract.support_decomposition.cqFlow q
        (restrictWordLinear (Lq.correctionRegion q) error) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [A.contract.support_decomposition.cqDelta1_decomposition]
      rw [hCocycle q]
      simp

private theorem qSector_boundary_zero_on_x
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (error : D.family.Cochain1 i.succ)
    (hSupported : SupportedOn A.qCorrectionSector error)
    (hCocycle : ∀ q,
      A.contract.rx_local_complexes.cqDelta1 q
        (restrictWordLinear (Lq.correctionRegion q) error) = 0) :
    ∀ p ∈ A.xSector, (D.family.coboundary1 i.succ error) p = 0 := by
  intro p hp
  rw [qSector_boundary_eq_flow A error hSupported hCocycle]
  simp only [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro q hq
  exact A.cqFlow_outside_xSector q
    (restrictWordLinear (Lq.correctionRegion q) error) p hp

private theorem qSector_boundary_zero_on_q
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (error : D.family.Cochain1 i.succ)
    (hSupported : SupportedOn A.qCorrectionSector error)
    (hCocycle : ∀ q,
      A.contract.rx_local_complexes.cqDelta1 q
        (restrictWordLinear (Lq.correctionRegion q) error) = 0) :
    ∀ p ∈ A.qSector, (D.family.coboundary1 i.succ error) p = 0 := by
  intro p hp
  rw [qSector_boundary_eq_flow A error hSupported hCocycle]
  simp only [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro q hq
  exact A.contract.support_decomposition.cqFlow_outside_q_sector q
    (restrictWordLinear (Lq.correctionRegion q) error) p (by
      simpa [A.qSector_eq_regions] using hp)

/-!
The Q-sector transport theorem is the RX half of the one-step API.  It is
deliberately stated as an existential theorem: the lower correction and the
degree-zero stabilizer are produced by the selected representative and the
local first-coboundary equations.  In particular no section, inverse, or
transport conclusion is stored in `RXCoarseGrainingData`.
-/
theorem q_sector_transport
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (hOdd : i.succ.val % 2 = 1)
    (error : D.family.Cochain1 i.succ)
    (hSupported : SupportedOn A.qCorrectionSector error)
    (hCocycle : ∀ q,
      A.contract.rx_local_complexes.cqDelta1 q
        (restrictWordLinear (Lq.correctionRegion q) error) = 0) :
    ∃ lowerCorrection : D.family.Cochain1 i.castSucc,
      ∃ lowerSyndrome : D.family.Syndrome i.castSucc,
        ∃ stabilizer : D.family.Cochain0 i.succ,
          (D.rxMap i).map1 lowerCorrection =
              error + D.family.coboundary0 i.succ stabilizer ∧
          D.family.coboundary1 i.succ
              (D.family.coboundary0 i.succ stabilizer) = 0 ∧
          (lowerSyndrome : D.family.Cochain2 i.castSucc) =
              D.family.coboundary1 i.castSucc lowerCorrection ∧
          (D.selectedMap i).map2 lowerSyndrome =
              D.family.coboundary1 i.succ error ∧
          SupportedOn A.zSector ((D.selectedMap i).map2 lowerSyndrome) := by
  classical
  let qClasses := RXCoarseGrainingData.qCohomologyClass A error hCocycle
  have hRepresentativeDifference : ∀ q, ∃ s : Word Field (Q0 q),
      A.contract.rx_local_complexes.cqDelta0 q s =
        (A.cqRepresentative q (qClasses q)).1 -
          restrictWordLinear (Lq.correctionRegion q) error := by
    intro q
    exact RXCoarseGrainingData.cqRepresentative_difference_exists A error hCocycle q
  let qStabilizers : ∀ q, Word Field (Q0 q) :=
    fun q => Classical.choose (hRepresentativeDifference q)
  have hqStabilizers : ∀ q,
      A.contract.rx_local_complexes.cqDelta0 q (qStabilizers q) =
        (A.cqRepresentative q (qClasses q)).1 -
          restrictWordLinear (Lq.correctionRegion q) error := by
    intro q
    exact Classical.choose_spec (hRepresentativeDifference q)
  let lowerCorrection := A.qCohomologyEquiv qClasses
  let stabilizer : D.family.Cochain0 i.succ :=
    ∑ q : Q, A.contract.support_decomposition.cqLift0 q
      (qStabilizers q)
  have hStabilizerZero : D.family.coboundary1 i.succ
      (D.family.coboundary0 i.succ stabilizer) = 0 := by
    have hcomp := BDL26CochainFamily.coboundary1_comp_coboundary0
      D.family i.succ
    have hcomp' := LinearMap.congr_fun hcomp stabilizer
    simpa [LinearMap.comp_apply] using hcomp'
  have hErrorDecomposition := qSector_error_decomposition A error hSupported
  have hRepresentativeSum :
      (∑ q : Q, extendWordLinear (Lq.correctionRegion q)
        ((A.cqRepresentative q (qClasses q)).1)) =
      error + D.family.coboundary0 i.succ stabilizer := by
    calc
      (∑ q : Q, extendWordLinear (Lq.correctionRegion q)
          ((A.cqRepresentative q (qClasses q)).1)) =
        ∑ q : Q, (extendWordLinear (Lq.correctionRegion q)
          (restrictWordLinear (Lq.correctionRegion q) error) +
          extendWordLinear (Lq.correctionRegion q)
            (A.contract.rx_local_complexes.cqDelta0 q
              (qStabilizers q))) := by
            apply Finset.sum_congr rfl
            intro q hq
            have hqdiff := hqStabilizers q
            have hqrep :
                (A.cqRepresentative q (qClasses q)).1 =
                  restrictWordLinear (Lq.correctionRegion q) error +
                    A.contract.rx_local_complexes.cqDelta0 q
                      (qStabilizers q) := by
              have hrr :
                  restrictWordLinear (Lq.correctionRegion q) error +
                      restrictWordLinear (Lq.correctionRegion q) error =
                    (0 : Word Field
                      (LocalRegionIndex (Lq.correctionRegion q))) := by
                ext p
                exact ZModModule.add_self _
              calc
                (A.cqRepresentative q (qClasses q)).1 =
                    ((A.cqRepresentative q (qClasses q)).1 +
                      restrictWordLinear (Lq.correctionRegion q) error) +
                      restrictWordLinear (Lq.correctionRegion q) error := by
                        symm
                        rw [add_assoc, hrr, add_zero]
                _ = A.contract.rx_local_complexes.cqDelta0 q
                      (qStabilizers q) +
                      restrictWordLinear (Lq.correctionRegion q) error := by
                        rw [hqdiff, ZModModule.sub_eq_add,
                          add_assoc, hrr, add_zero]
                _ = restrictWordLinear (Lq.correctionRegion q) error +
                      A.contract.rx_local_complexes.cqDelta0 q
                        (qStabilizers q) := by abel
            rw [hqrep, map_add]
      _ = (∑ q : Q, extendWordLinear (Lq.correctionRegion q)
            (restrictWordLinear (Lq.correctionRegion q) error)) +
          (∑ q : Q, extendWordLinear (Lq.correctionRegion q)
            (A.contract.rx_local_complexes.cqDelta0 q
              (qStabilizers q))) := by
            rw [Finset.sum_add_distrib]
      _ = error + D.family.coboundary0 i.succ stabilizer := by
            rw [← hErrorDecomposition]
            rw [← A.cqDelta0_sum_decomposition]
  have hMap1 : (D.rxMap i).map1 lowerCorrection =
      error + D.family.coboundary0 i.succ stabilizer := by
    rw [A.rxMap1_eq_cqRepresentative lowerCorrection]
    simpa [lowerCorrection] using hRepresentativeSum
  let lowerSyndrome : D.family.Syndrome i.castSucc :=
    ⟨D.family.coboundary1 i.castSucc lowerCorrection, by
      exact ⟨lowerCorrection, rfl⟩⟩
  have hSelected : D.selectedMap i = D.rxMap i :=
    RXCoarseGrainingData.selectedMap_eq_rx_of_odd_input D i hOdd
  have hMap2 : (D.selectedMap i).map2 lowerSyndrome =
      D.family.coboundary1 i.succ error := by
    have hcomm := LinearMap.congr_fun (D.rxMap i).commutes_coboundary1
      lowerCorrection
    simp only [LinearMap.comp_apply] at hcomm
    rw [hMap1, map_add, hStabilizerZero, add_zero] at hcomm
    simpa [hSelected] using hcomm.symm
  have hSupport : SupportedOn A.zSector
      (D.family.coboundary1 i.succ error) :=
    RXCoarseGrainingData.zero_outside_sector_of_zero_x_zero_q A
      (qSector_boundary_zero_on_x A error hSupported hCocycle)
      (qSector_boundary_zero_on_q A error hSupported hCocycle)
  refine ⟨lowerCorrection, lowerSyndrome, stabilizer, hMap1,
    hStabilizerZero, rfl, hMap2, ?_⟩
  simpa [hMap2] using hSupport

/-!
A q-sector run retains only its upper error and the syndrome equation used to
audit that sector-wide input.  It carries no decoder-leaf, assembly-owner, or
parent-locality claim.  The lower correction, its syndrome, and the
degree-zero witness remain theorem outputs rather than fields of the run.
-/
structure RXQSectorRun
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz) where
  upperCorrection : D.family.Cochain1 i.succ
  upperSyndrome : D.family.Syndrome i.succ
  upperSyndrome_eq :
    D.family.coboundary1 i.succ upperCorrection = upperSyndrome

/-!
The two-run theorem constructs the lower difference from the two independent
RX representative choices.  `eDelta` is an audited upper difference
premise; the lower difference and degree-zero stabilizer are existential
outputs, and all selected-map/support equations are derived below.
-/
theorem q_sector_error_difference_transport
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (hOdd : i.succ.val % 2 = 1)
    (left right : RXQSectorRun A)
    (hLeftSupported : SupportedOn A.qCorrectionSector left.upperCorrection)
    (hRightSupported : SupportedOn A.qCorrectionSector right.upperCorrection)
    (hLeftCocycle : ∀ q,
      A.contract.rx_local_complexes.cqDelta1 q
        (restrictWordLinear (Lq.correctionRegion q) left.upperCorrection) = 0)
    (hRightCocycle : ∀ q,
      A.contract.rx_local_complexes.cqDelta1 q
        (restrictWordLinear (Lq.correctionRegion q) right.upperCorrection) = 0)
    (eDelta : D.family.Cochain1 i.succ)
    (hDifference : eDelta = left.upperCorrection + right.upperCorrection) :
    ∃ eDeltaLower : D.family.Cochain1 i.castSucc,
      ∃ eDeltaSyndrome : D.family.Syndrome i.castSucc,
        ∃ eDeltaStabilizer : D.family.Cochain0 i.succ,
          (D.rxMap i).map1 eDeltaLower =
              eDelta + D.family.coboundary0 i.succ eDeltaStabilizer ∧
          D.family.coboundary1 i.succ
              (D.family.coboundary0 i.succ eDeltaStabilizer) = 0 ∧
          (eDeltaSyndrome : D.family.Cochain2 i.castSucc) =
              D.family.coboundary1 i.castSucc eDeltaLower ∧
          D.family.coboundary1 i.succ eDelta =
              (left.upperSyndrome : D.family.Cochain2 i.succ) +
                (right.upperSyndrome : D.family.Cochain2 i.succ) ∧
          (D.selectedMap i).map2 eDeltaSyndrome =
              D.family.coboundary1 i.succ eDelta ∧
          SupportedOn A.zSector ((D.selectedMap i).map2 eDeltaSyndrome) := by
  classical
  obtain ⟨leftLower, leftSyndrome, leftStabilizer,
      hLeftMap1, hLeftStabilizerZero, hLeftLowerSyndrome,
      hLeftMap2, hLeftSupport⟩ :=
    q_sector_transport A hOdd left.upperCorrection
      hLeftSupported hLeftCocycle
  obtain ⟨rightLower, rightSyndrome, rightStabilizer,
      hRightMap1, hRightStabilizerZero, hRightLowerSyndrome,
      hRightMap2, hRightSupport⟩ :=
    q_sector_transport A hOdd right.upperCorrection
      hRightSupported hRightCocycle
  let eDeltaLower := leftLower + rightLower
  let eDeltaStabilizer := leftStabilizer + rightStabilizer
  let eDeltaSyndrome : D.family.Syndrome i.castSucc :=
    ⟨D.family.coboundary1 i.castSucc eDeltaLower, by
      exact ⟨eDeltaLower, rfl⟩⟩
  have hMap1 : (D.rxMap i).map1 eDeltaLower =
      eDelta + D.family.coboundary0 i.succ eDeltaStabilizer := by
    calc
      (D.rxMap i).map1 eDeltaLower =
          (D.rxMap i).map1 leftLower + (D.rxMap i).map1 rightLower := by
            simp [eDeltaLower]
      _ = (left.upperCorrection + D.family.coboundary0 i.succ leftStabilizer) +
          (right.upperCorrection + D.family.coboundary0 i.succ rightStabilizer) := by
            rw [hLeftMap1, hRightMap1]
      _ = (left.upperCorrection + right.upperCorrection) +
          (D.family.coboundary0 i.succ leftStabilizer +
            D.family.coboundary0 i.succ rightStabilizer) := by abel
      _ = eDelta + D.family.coboundary0 i.succ eDeltaStabilizer := by
            rw [hDifference, ← map_add]
  have hStabilizerZero : D.family.coboundary1 i.succ
      (D.family.coboundary0 i.succ eDeltaStabilizer) = 0 := by
    calc
      D.family.coboundary1 i.succ
          (D.family.coboundary0 i.succ eDeltaStabilizer) =
          D.family.coboundary1 i.succ
            (D.family.coboundary0 i.succ leftStabilizer) +
          D.family.coboundary1 i.succ
            (D.family.coboundary0 i.succ rightStabilizer) := by
              simp [eDeltaStabilizer, map_add]
      _ = 0 := by rw [hLeftStabilizerZero, hRightStabilizerZero, add_zero]
  have hUpperSyndromeDifference :
      D.family.coboundary1 i.succ eDelta =
        (left.upperSyndrome : D.family.Cochain2 i.succ) +
          (right.upperSyndrome : D.family.Cochain2 i.succ) := by
    rw [hDifference, map_add, left.upperSyndrome_eq,
      right.upperSyndrome_eq]
  have hSelected : D.selectedMap i = D.rxMap i :=
    RXCoarseGrainingData.selectedMap_eq_rx_of_odd_input D i hOdd
  have hMap2 : (D.selectedMap i).map2 eDeltaSyndrome =
      D.family.coboundary1 i.succ eDelta := by
    have hcomm := LinearMap.congr_fun (D.rxMap i).commutes_coboundary1
      eDeltaLower
    simp only [LinearMap.comp_apply] at hcomm
    rw [hMap1, map_add, hStabilizerZero, add_zero] at hcomm
    simpa [eDeltaSyndrome, hSelected] using hcomm.symm
  have hSupport : SupportedOn A.zSector
      (D.family.coboundary1 i.succ eDelta) := by
    intro p hp
    rw [hDifference, map_add]
    rw [hLeftMap2] at hLeftSupport
    rw [hRightMap2] at hRightSupport
    simp only [Pi.add_apply]
    rw [hLeftSupport p hp, hRightSupport p hp, add_zero]
  refine ⟨eDeltaLower, eDeltaSyndrome, eDeltaStabilizer, hMap1,
    hStabilizerZero, ?_, hUpperSyndromeDifference, hMap2, ?_⟩
  · rfl
  · simpa [hMap2] using hSupport

end RXErrorTransport

end RXCoarseGraining
end MultiscaleDecoder
end Coding
end QEC
