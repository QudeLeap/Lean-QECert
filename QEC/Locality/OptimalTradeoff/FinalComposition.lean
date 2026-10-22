import QEC.Locality.OptimalTradeoff.CountComposition
import QEC.Locality.OptimalTradeoff.DistancePartition
import QEC.Locality.OptimalTradeoff.LargeDistanceSeparator
/-!
# Dai--Li final interaction-count composition

This internal module assembles the three finite Dai--Li branches into the
single two-scale count/length implication used by the downstream public result.
It retains the actual `Finset (Sym2 iota)` interaction cardinality from the
fixed presentation; incidence counters remain internal proof machinery.
-/

noncomputable section

namespace QEC.Locality

open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

/-- The `d / sqrt n` length term in the selected Dai--Li conclusion. -/
def daiLiFirstLengthScale (d n : ℝ) : ℝ :=
  d / Real.sqrt n

/-- The exact `1 / 200` max-form threshold discharged by this internal node. -/
def daiLiInteractionCountThreshold (k d n : ℝ) : ℝ :=
  (1 / 200 : ℝ) * max (daiLiFirstLengthScale d n)
    (daiLiFourthRoot (k * d ^ 2 / n))

private theorem daiLiFirstLengthScale_pow_four (d n : ℝ) (hn : 0 < n) :
    daiLiFirstLengthScale d n ^ 4 = d ^ 4 / n ^ 2 := by
  unfold daiLiFirstLengthScale
  rw [div_pow]
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn.le
  calc
    d ^ 4 / Real.sqrt n ^ 4 = d ^ 4 / (Real.sqrt n ^ 2) ^ 2 := by ring
    _ = d ^ 4 / n ^ 2 := by rw [hsq]

/-- The `rpow` scale used by the `d >= k` package agrees with the principal
square-root presentation used by the `k >= d` count theorem. -/
theorem daiLiPrincipalFourthRootScale_eq_daiLiKGeDFourthRootThreshold
    (k d n : ℝ) (hk : 0 ≤ k) (hn : 0 < n) :
    daiLiPrincipalFourthRootScale k d n =
      daiLiKGeDFourthRootThreshold k d n := by
  unfold daiLiPrincipalFourthRootScale daiLiKGeDFourthRootThreshold
  have hRatio : 0 ≤ k * d ^ 2 / n :=
    div_nonneg (mul_nonneg hk (sq_nonneg d)) hn.le
  rw [daiLiFourthRoot, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hRatio]
  norm_num
  ring

private theorem daiLi_firstScale_le_fourthRoot_of_lowScale
    (k d n : ℝ) (hk : 0 ≤ k) (hd : 0 ≤ d) (hn : 0 < n)
    (hLowScale : d ≤ Real.sqrt (k * n)) :
    daiLiFirstLengthScale d n ≤ daiLiFourthRoot (k * d ^ 2 / n) := by
  have hKn : 0 ≤ k * n := mul_nonneg hk hn.le
  have hSquare : d ^ 2 ≤ k * n := (Real.le_sqrt hd hKn).mp hLowScale
  have hRatio : 0 ≤ k * d ^ 2 / n :=
    div_nonneg (mul_nonneg hk (sq_nonneg d)) hn.le
  unfold daiLiFirstLengthScale
  apply (pow_le_pow_iff_left₀ (by positivity) (daiLiFourthRoot_nonneg _)
    (by norm_num : 4 ≠ 0)).mp
  rw [daiLiFourthRoot_pow_four _ hRatio,
    show (d / Real.sqrt n) ^ 4 = d ^ 4 / n ^ 2 by
      exact daiLiFirstLengthScale_pow_four d n hn]
  apply (div_le_iff₀ (sq_pos_of_pos hn)).2
  calc
    d ^ 4 = d ^ 2 * d ^ 2 := by ring
    _ ≤ (k * n) * d ^ 2 := mul_le_mul_of_nonneg_right hSquare (sq_nonneg d)
    _ = (k * d ^ 2 / n) * n ^ 2 := by field_simp

private theorem daiLi_fourthRoot_le_firstScale_of_largeDistance
    (k d n : ℝ) (hk : 0 ≤ k) (hd : 0 ≤ d) (hn : 0 < n)
    (hLargeDistance : Real.sqrt (k * n) ≤ d) :
    daiLiFourthRoot (k * d ^ 2 / n) ≤ daiLiFirstLengthScale d n := by
  have hSquare : k * n ≤ d ^ 2 := (Real.sqrt_le_iff).mp hLargeDistance |>.2
  have hRatio : 0 ≤ k * d ^ 2 / n :=
    div_nonneg (mul_nonneg hk (sq_nonneg d)) hn.le
  unfold daiLiFirstLengthScale
  apply (pow_le_pow_iff_left₀ (daiLiFourthRoot_nonneg _) (by positivity)
    (by norm_num : 4 ≠ 0)).mp
  rw [daiLiFourthRoot_pow_four _ hRatio,
    show (d / Real.sqrt n) ^ 4 = d ^ 4 / n ^ 2 by
      exact daiLiFirstLengthScale_pow_four d n hn]
  apply (le_div_iff₀ (sq_pos_of_pos hn)).2
  calc
    (k * d ^ 2 / n) * n ^ 2 = (k * n) * d ^ 2 := by field_simp
    _ ≤ d ^ 2 * d ^ 2 := mul_le_mul_of_nonneg_right hSquare (sq_nonneg d)
    _ = d ^ 4 := by ring

private theorem daiLi_encodedQubits_le_blockLength
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    P.encodedQubits ≤ Fintype.card ι := by
  rw [P.encodedQubits_eq_blockLength_sub_generatorRank]
  exact Nat.sub_le _ _

/-!
## The `d >= k` count bridge

The preceding package produces one concrete translated B/B-prime/C partition.
This local bridge turns its contradiction into the actual unordered-count
bound; it neither receives nor stores a partition, recovery, or count result.
-/

private theorem daiLiDGeK_lowScale_fourthRoot_longInteractionCount
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (ell w : ℝ)
    (hScale : ell = daiLiPrincipalFourthRootScale
      (P.encodedQubits : ℝ) (d : ℝ) (Fintype.card ι : ℝ))
    (hWidth : w = daiLiDGeKGridWidth (d : ℝ) ell)
    (hD : 0 < d) (hEncodedPositive : 0 < P.encodedQubits)
    (hDGeK : P.encodedQubits ≤ d)
    (hLowScale : (d : ℝ) ≤ Real.sqrt ((P.encodedQubits : ℝ) * Fintype.card ι))
    (hWidthNat : 1 ≤ w) (hEllNat : 1 ≤ ell)
    (baseHorizontalRadius baseVerticalRadius : ℝ) (steps : ℕ)
    (hBaseHorizontal : baseHorizontalRadius ≤ w / 2)
    (hBaseVerticalGood : baseVerticalRadius ≤ w / 2)
    (hBaseVerticalBad : baseVerticalRadius ≤ 5 * ell / 2)
    (hBaseHorizontalDiameter : 1 ≤ 2 * baseHorizontalRadius)
    (hBaseVerticalDiameter : 1 ≤ 2 * baseVerticalRadius)
    (hReachHorizontal : w / 2 ≤ baseHorizontalRadius + steps * ell)
    (hReachVerticalGood : w / 2 ≤ baseVerticalRadius + steps * ell)
    (hReachVerticalBad : w / 2 ≤ baseVerticalRadius + steps * ell)
    (hGoodBaseCard : ∀ (t : GridTranslation w) cell,
      cell ∈ embedding.gridOccupiedCells w (gridOrigin w t) →
        (centeredRectangleQubits embedding (daiLiGridCellCenter w (gridOrigin w t) cell)
          baseHorizontalRadius baseVerticalRadius).card < d)
    (hBoundaryBudget :
      48 * (w / 2 + w / 2 + ell) * ell + (d : ℝ) / 10 < d)
    (hShortPackingScale : 60 * w * ell < d)
    (hGridWidth : 4 * ell ≤ w) (hGridLong : 1 ≤ w - 4 * ell)
    (hGridSideSmall : 12 * ell * (w - 4 * ell) < d) :
    (d : ℝ) / 100 < (P.longInteractionCount embedding ell : ℝ) := by
  have hKPositiveNat : 0 < P.encodedQubits := hEncodedPositive
  have hKPositive : 0 < (P.encodedQubits : ℝ) := by exact_mod_cast hKPositiveNat
  have hDReal : 0 < (d : ℝ) := by exact_mod_cast hD
  have hKLeN : P.encodedQubits ≤ Fintype.card ι := daiLi_encodedQubits_le_blockLength P
  have hNPositiveNat : 0 < Fintype.card ι := lt_of_lt_of_le hKPositiveNat hKLeN
  have hNPositive : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast hNPositiveNat
  by_contra hNotCount
  have hLongCount : (P.longInteractionCount embedding ell : ℝ) ≤ (d : ℝ) / 100 :=
    le_of_not_gt hNotCount
  obtain ⟨t, hResidualLt, _hResidualSubset, hAB, hAC, hBC, hCover,
      ⟨recoveryA, hRecoveryA⟩, ⟨recoveryB, hRecoveryB⟩⟩ :=
    exists_daiLiDGeK_two_correctable_partition P embedding d hDistance ell w ell
      (P.encodedQubits : ℝ) hKPositive hDReal (by exact_mod_cast hDGeK) hNPositive
      hLowScale hScale hWidth hLongCount hGridWidth hEllNat hWidthNat hEllNat le_rfl
      (by nlinarith) hGridLong hGridSideSmall baseHorizontalRadius baseVerticalRadius steps
      hBaseHorizontal hBaseVerticalGood hBaseVerticalBad hBaseHorizontalDiameter
      hBaseVerticalDiameter hReachHorizontal hReachVerticalGood hReachVerticalBad hGoodBaseCard
      hBoundaryBudget hShortPackingScale
  have hDimension := two_correctable_regions_encodedQubits_le_separator_card P
    (daiLiDGeKASubsystem P embedding d ell w ell t)
    (daiLiDGeKTrimmedBSubsystem P embedding d ell w ell t)
    (daiLiDGeKResidualSubsystem P embedding d ell w ell t)
    hAB hAC hBC hCover recoveryA hRecoveryA recoveryB hRecoveryB
  have hDimensionReal : (P.encodedQubits : ℝ) ≤
      ((daiLiDGeKResidualSubsystem P embedding d ell w ell t).selected.card : ℝ) := by
    exact_mod_cast hDimension
  exact (not_lt_of_ge hDimensionReal) hResidualLt

/-- Lean-QEC's explicit finite-size witness for the terminal Dai--Li handoff.
It is deliberately stronger than the source's displayed `100^4` threshold so
that the source geometry is constructed here rather than supplied by a caller. -/
def daiLiFinalAboveBPTConstant : ℝ := (1000 : ℝ) ^ 4

private theorem daiLiFinal_branch_aboveBPT
    {k d n : ℝ} (hn : 0 < n)
    (hAboveBPT : daiLiFinalAboveBPTConstant * n ≤ k * d ^ 2) :
    (100 : ℝ) ^ 4 * n ≤ k * d ^ 2 := by
  rw [daiLiFinalAboveBPTConstant] at hAboveBPT
  nlinarith

private theorem daiLiFinal_distance_ge_seven
    {k d n : ℝ} (hd : 0 < d) (hn : 0 < n) (hKLeN : k ≤ n)
    (hAboveBPT : daiLiFinalAboveBPTConstant * n ≤ k * d ^ 2) :
    (7 : ℝ) ≤ d := by
  have hKDSqLeNDSq : k * d ^ 2 ≤ n * d ^ 2 :=
    mul_le_mul_of_nonneg_right hKLeN (sq_nonneg d)
  have hConstantLeDSq : daiLiFinalAboveBPTConstant ≤ d ^ 2 := by
    by_contra h
    have hSquareSmall : d ^ 2 < daiLiFinalAboveBPTConstant := lt_of_not_ge h
    have hMultSmall : n * d ^ 2 < n * daiLiFinalAboveBPTConstant :=
      mul_lt_mul_of_pos_left hSquareSmall hn
    have hMultLarge : n * daiLiFinalAboveBPTConstant ≤ n * d ^ 2 := by
      calc
        n * daiLiFinalAboveBPTConstant = daiLiFinalAboveBPTConstant * n := by ring
        _ ≤ k * d ^ 2 := hAboveBPT
        _ ≤ n * d ^ 2 := hKDSqLeNDSq
    exact (not_lt_of_ge hMultLarge) hMultSmall
  rw [daiLiFinalAboveBPTConstant] at hConstantLeDSq
  norm_num at hConstantLeDSq
  nlinarith [sq_nonneg (d - 7)]

private theorem daiLiFinal_unit_base_card_lt_distance
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ) (d : ℕ)
    (hDistanceLarge : 7 ≤ d) :
    (centeredRectangleQubits embedding center (1 / 2 : ℝ) (1 / 2 : ℝ)).card < d := by
  have hWidth : (1 : ℝ) ≤ (center.1 + 1 / 2) - (center.1 - 1 / 2) := by norm_num
  have hHeight : (1 : ℝ) ≤ (center.2 + 1 / 2) - (center.2 - 1 / 2) := by norm_num
  have hPacking := embedding.card_qubitsInRectangle_le_six_mul_area
    (center.1 - 1 / 2, center.2 - 1 / 2)
    (center.1 + 1 / 2, center.2 + 1 / 2) hWidth hHeight
  change (embedding.qubitsInRectangle
    (center.1 - 1 / 2, center.2 - 1 / 2)
    (center.1 + 1 / 2, center.2 + 1 / 2)).card < d
  have hCardReal :
      ((embedding.qubitsInRectangle
        (center.1 - 1 / 2, center.2 - 1 / 2)
        (center.1 + 1 / 2, center.2 + 1 / 2)).card : ℝ) ≤ 6 := by
    convert hPacking using 1
    all_goals ring_nf
  have hCard : (embedding.qubitsInRectangle
      (center.1 - 1 / 2, center.2 - 1 / 2)
      (center.1 + 1 / 2, center.2 + 1 / 2)).card ≤ 6 := by
    exact_mod_cast hCardReal
  omega

private theorem daiLiFinal_square_scale_le
    {k d n ell : ℝ} (hk : 0 ≤ k) (hd : 0 < d) (hn : 0 < n) (hKLeN : k ≤ n)
    (hScale : ell = daiLiKGeDFourthRootThreshold k d n) :
    ell ^ 2 ≤ d / 10000 := by
  have hFourth : ell ^ 4 = k * d ^ 2 / (100 ^ 4 * n) := by
    rw [hScale]
    exact daiLiKGeDFourthRootThreshold_pow_four hk hn
  have hFourthBound : ell ^ 4 ≤ d ^ 2 / 100 ^ 4 := by
    rw [hFourth]
    apply (div_le_iff₀ (mul_pos (by positivity : (0 : ℝ) < 100 ^ 4) hn)).2
    have hScaleNonneg : 0 ≤ (n - k) * d ^ 2 :=
      mul_nonneg (sub_nonneg.mpr hKLeN) (sq_nonneg d)
    nlinarith
  by_contra h
  have hSquareLarge : d / 10000 < ell ^ 2 := lt_of_not_ge h
  have hEllSqNonneg : 0 ≤ ell ^ 2 := sq_nonneg ell
  nlinarith [sq_nonneg (ell ^ 2 - d / 10000)]

/-- Conditional Dai--Li branch-composition intermediate.  Its explicit finite
recovery-side premises are discharged by the source-assumption bridge below;
callers of the final #387 handoff do not receive this interface.  The
actual distinct unordered interaction set has at least `max(k,d) / 200`
members whose Euclidean length is at least the selected max-form threshold.
No partition, recovery, branch result, or interaction count is supplied by
the caller. -/
theorem daiLi_final_interaction_count_max_length_of_geometry
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (ell w : ℝ)
    (hScale : ell = daiLiKGeDFourthRootThreshold
      (P.encodedQubits : ℝ) (d : ℝ) (Fintype.card ι : ℝ))
    (hWidth : w = daiLiKGeDGridWidth (d : ℝ) ell)
    (hD : 0 < d) (hEncodedPositive : 0 < P.encodedQubits)
    (hAboveBPT : (100 : ℝ) ^ 4 * Fintype.card ι ≤
      (P.encodedQubits : ℝ) * (d : ℝ) ^ 2)
    (hWidthNat : 1 ≤ w)
    (baseHorizontalRadius baseVerticalRadius : ℝ) (steps : ℕ)
    (hBaseHorizontal : baseHorizontalRadius ≤ w / 2)
    (hBaseVerticalGood : baseVerticalRadius ≤ w / 2)
    (hBaseVerticalBad : baseVerticalRadius ≤ 5 * ell / 2)
    (hBaseHorizontalDiameter : 1 ≤ 2 * baseHorizontalRadius)
    (hBaseVerticalDiameter : 1 ≤ 2 * baseVerticalRadius)
    (hReachHorizontal : w / 2 ≤ baseHorizontalRadius + steps * ell)
    (hReachVerticalGood : w / 2 ≤ baseVerticalRadius + steps * ell)
    (hReachVerticalBad : w / 2 ≤ baseVerticalRadius + steps * ell)
    (hKGeDGoodBaseCard : ∀ (t : GridTranslation w)
      (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
      (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))),
      (∀ cell ∈ daiLiBadGridCells P embedding ell d w (gridOrigin w t),
        DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
          ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
          ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell)) →
      (∀ cell ∈ daiLiBadGridCells P embedding ell d w (gridOrigin w t),
        rectangles cell = daiLiPhysicalGreedyRectangles P embedding ell
          ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
          ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell)) →
      ∀ cell,
        Sum.inl cell ∈ daiLiKGeDRegionCandidates P embedding ell d w
          (gridOrigin w t) rectangles →
        (centeredRectangleQubits embedding
          (daiLiGridCellCenter w (gridOrigin w t) cell)
          baseHorizontalRadius baseVerticalRadius).card < d)
    (hKGeDBadBaseCard : ∀ (t : GridTranslation w)
      (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
      (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))),
      (∀ cell ∈ daiLiBadGridCells P embedding ell d w (gridOrigin w t),
        DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
          ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
          ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell)) →
      (∀ cell ∈ daiLiBadGridCells P embedding ell d w (gridOrigin w t),
        rectangles cell = daiLiPhysicalGreedyRectangles P embedding ell
          ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
          ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell)) →
      ∀ cell slot,
        Sum.inr (cell, slot) ∈ daiLiKGeDRegionCandidates P embedding ell d w
          (gridOrigin w t) rectangles →
        (centeredRectangleQubits embedding
          (daiLiRectangleCenter
            (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles
              (Sum.inr (cell, slot))).1
            (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles
              (Sum.inr (cell, slot))).2)
          baseHorizontalRadius baseVerticalRadius).card < d)
    (hDGeKGoodBaseCard : ∀ (t : GridTranslation w) cell,
      cell ∈ embedding.gridOccupiedCells w (gridOrigin w t) →
        (centeredRectangleQubits embedding (daiLiGridCellCenter w (gridOrigin w t) cell)
          baseHorizontalRadius baseVerticalRadius).card < d)
    (hBoundaryBudget :
      48 * (w / 2 + w / 2 + ell) * ell + (d : ℝ) / 10 < d)
    (hShortPackingScale : 60 * w * ell < d)
    (hCellWidth : 5 * ell ≤ w) (hInternalSideScale : 12 * ell * w < d)
    (hGridWidth : 4 * ell ≤ w) (hGridLong : 1 ≤ w - 4 * ell)
    (hGridSideSmall : 12 * ell * (w - 4 * ell) < d) :
    max (P.encodedQubits : ℝ) (d : ℝ) / 200 ≤
      (P.longInteractionCount embedding
        (daiLiInteractionCountThreshold (P.encodedQubits : ℝ) d (Fintype.card ι) : ℝ) : ℝ) := by
  have hKLeN : P.encodedQubits ≤ Fintype.card ι := daiLi_encodedQubits_le_blockLength P
  have hNPositiveNat : 0 < Fintype.card ι := lt_of_lt_of_le hEncodedPositive hKLeN
  have hK : 0 ≤ (P.encodedQubits : ℝ) := Nat.cast_nonneg _
  have hDReal : 0 < (d : ℝ) := by exact_mod_cast hD
  have hN : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast hNPositiveNat
  have hKLeNReal : (P.encodedQubits : ℝ) ≤ Fintype.card ι := by exact_mod_cast hKLeN
  have hEllNat : 1 ≤ ell := by
    rw [hScale]
    exact one_le_daiLiKGeDFourthRootThreshold hK hN hAboveBPT
  have hPrincipalScale : ell = daiLiPrincipalFourthRootScale
      (P.encodedQubits : ℝ) (d : ℝ) (Fintype.card ι : ℝ) := by
    rw [hScale, daiLiPrincipalFourthRootScale_eq_daiLiKGeDFourthRootThreshold]
    exact hK
    exact hN
  have hDGeKWidth : w = daiLiDGeKGridWidth (d : ℝ) ell := by
    simpa [daiLiKGeDGridWidth, daiLiDGeKGridWidth] using hWidth
  by_cases hLargeDistance :
      Real.sqrt ((P.encodedQubits : ℝ) * Fintype.card ι) ≤ d
  · have hFourthLeFirst := daiLi_fourthRoot_le_firstScale_of_largeDistance
      (P.encodedQubits : ℝ) d (Fintype.card ι) hK hDReal.le hN hLargeDistance
    have hMaxLength : max (daiLiFirstLengthScale (d : ℝ) (Fintype.card ι))
        (daiLiFourthRoot ((P.encodedQubits : ℝ) * (d : ℝ) ^ 2 /
          Fintype.card ι)) = daiLiFirstLengthScale (d : ℝ) (Fintype.card ι) :=
      max_eq_left hFourthLeFirst
    have hKnLeDSq : (P.encodedQubits : ℝ) * Fintype.card ι ≤ (d : ℝ) ^ 2 :=
      (Real.sqrt_le_iff.mp hLargeDistance).2
    have hKSqLeKN : (P.encodedQubits : ℝ) ^ 2 ≤
        (P.encodedQubits : ℝ) * Fintype.card ι := by
      calc
        (P.encodedQubits : ℝ) ^ 2 = (P.encodedQubits : ℝ) * (P.encodedQubits : ℝ) := by ring
        _ ≤ (P.encodedQubits : ℝ) * Fintype.card ι :=
          mul_le_mul_of_nonneg_left hKLeNReal hK
    have hKLeD : (P.encodedQubits : ℝ) ≤ d := by
      apply (pow_le_pow_iff_left₀ hK hDReal.le (by norm_num : 2 ≠ 0)).mp
      exact hKSqLeKN.trans hKnLeDSq
    have hMaxCount : max (P.encodedQubits : ℝ) (d : ℝ) = d := max_eq_right hKLeD
    have hThreshold : daiLiInteractionCountThreshold (P.encodedQubits : ℝ) d
        (Fintype.card ι) = daiLiLargeDistanceThreshold d (Fintype.card ι) := by
      rw [daiLiInteractionCountThreshold, hMaxLength, daiLiFirstLengthScale,
        daiLiLargeDistanceThreshold]
      field_simp [ne_of_gt (Real.sqrt_pos.2 hN)]
    have hAboveBPTLargeReal : (100 : ℝ) * Fintype.card ι ≤
        (P.encodedQubits : ℝ) * (d : ℝ) ^ 2 := by
      nlinarith [hAboveBPT]
    have hAboveBPTLarge : 100 * Fintype.card ι ≤ P.encodedQubits * d ^ 2 := by
      exact_mod_cast hAboveBPTLargeReal
    have hCount := daiLiLargeDistance_interaction_count_lower_bound P embedding d hDistance
      hAboveBPTLarge hLargeDistance hEncodedPositive
    have hCountReal : (d : ℝ) ≤ 200 *
        (P.longInteractionCount embedding (daiLiLargeDistanceThreshold d (Fintype.card ι)) : ℝ) := by
      exact_mod_cast hCount
    rw [hMaxCount, hThreshold]
    nlinarith
  · have hLowScale : (d : ℝ) ≤
      Real.sqrt ((P.encodedQubits : ℝ) * Fintype.card ι) :=
      le_of_lt (lt_of_not_ge hLargeDistance)
    have hFirstLeFourth := daiLi_firstScale_le_fourthRoot_of_lowScale
      (P.encodedQubits : ℝ) d (Fintype.card ι) hK hDReal.le hN hLowScale
    have hMaxLength : max (daiLiFirstLengthScale (d : ℝ) (Fintype.card ι))
        (daiLiFourthRoot ((P.encodedQubits : ℝ) * (d : ℝ) ^ 2 /
          Fintype.card ι)) = daiLiFourthRoot ((P.encodedQubits : ℝ) * (d : ℝ) ^ 2 /
          Fintype.card ι) := max_eq_right hFirstLeFourth
    have hThresholdLeEll : daiLiInteractionCountThreshold (P.encodedQubits : ℝ) d
        (Fintype.card ι) ≤ ell := by
      rw [daiLiInteractionCountThreshold, hMaxLength, hScale,
        daiLiKGeDFourthRootThreshold]
      have hFourthNonneg := daiLiFourthRoot_nonneg
        ((P.encodedQubits : ℝ) * (d : ℝ) ^ 2 / Fintype.card ι)
      nlinarith
    have hMonoNat := P.longInteractionCount_anti_mono embedding hThresholdLeEll
    have hMono : (P.longInteractionCount embedding ell : ℝ) ≤
        (P.longInteractionCount embedding
          (daiLiInteractionCountThreshold (P.encodedQubits : ℝ) d (Fintype.card ι)) : ℝ) := by
      exact_mod_cast hMonoNat
    by_cases hKGeD : d ≤ P.encodedQubits
    · have hCount := daiLiKGeD_lowScale_fourthRoot_longInteractionCount P embedding d
        hDistance ell w hScale hWidth hD hKGeD hLowScale hAboveBPT hWidthNat
        baseHorizontalRadius baseVerticalRadius steps hBaseHorizontal hBaseVerticalGood
        hBaseVerticalBad hBaseHorizontalDiameter hBaseVerticalDiameter hReachHorizontal
        hReachVerticalGood hReachVerticalBad hKGeDGoodBaseCard hKGeDBadBaseCard
        hBoundaryBudget hShortPackingScale hCellWidth hInternalSideScale hGridWidth hGridLong
        hGridSideSmall
      have hMaxCount : max (P.encodedQubits : ℝ) (d : ℝ) = P.encodedQubits :=
        max_eq_left (by exact_mod_cast hKGeD)
      rw [hMaxCount]
      nlinarith
    · have hDGeK : P.encodedQubits ≤ d := by omega
      have hCount := daiLiDGeK_lowScale_fourthRoot_longInteractionCount P embedding d
        hDistance ell w hPrincipalScale hDGeKWidth hD hEncodedPositive hDGeK hLowScale
        hWidthNat hEllNat
        baseHorizontalRadius baseVerticalRadius steps hBaseHorizontal hBaseVerticalGood
        hBaseVerticalBad hBaseHorizontalDiameter hBaseVerticalDiameter hReachHorizontal
        hReachVerticalGood hReachVerticalBad hDGeKGoodBaseCard hBoundaryBudget hShortPackingScale
        hGridWidth hGridLong hGridSideSmall
      have hMaxCount : max (P.encodedQubits : ℝ) (d : ℝ) = d :=
        max_eq_right (by exact_mod_cast hDGeK)
      rw [hMaxCount]
      nlinarith

/-- Final internal Dai--Li handoff.  The source assumptions choose the unit
base rectangles and finite growth steps, and the project-owned above-BPT
witness discharges all low-scale packing and grid inequalities internally.
The conclusion counts the actual distinct unordered interactions. -/
theorem daiLi_final_interaction_count_max_length
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (hD : 0 < d) (hEncodedPositive : 0 < P.encodedQubits)
    (hAboveBPT : daiLiFinalAboveBPTConstant * Fintype.card ι ≤
      (P.encodedQubits : ℝ) * (d : ℝ) ^ 2) :
    max (P.encodedQubits : ℝ) (d : ℝ) / 200 ≤
      (P.longInteractionCount embedding
        (daiLiInteractionCountThreshold (P.encodedQubits : ℝ) d (Fintype.card ι) : ℝ) : ℝ) := by
  have hKLeN : P.encodedQubits ≤ Fintype.card ι := daiLi_encodedQubits_le_blockLength P
  have hNPositiveNat : 0 < Fintype.card ι := lt_of_lt_of_le hEncodedPositive hKLeN
  have hK : 0 ≤ (P.encodedQubits : ℝ) := Nat.cast_nonneg _
  have hDReal : 0 < (d : ℝ) := by exact_mod_cast hD
  have hN : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast hNPositiveNat
  have hKLeNReal : (P.encodedQubits : ℝ) ≤ Fintype.card ι := by exact_mod_cast hKLeN
  have hAboveBPTBranch : (100 : ℝ) ^ 4 * Fintype.card ι ≤
      (P.encodedQubits : ℝ) * (d : ℝ) ^ 2 :=
    daiLiFinal_branch_aboveBPT hN hAboveBPT
  let ell := daiLiKGeDFourthRootThreshold
    (P.encodedQubits : ℝ) (d : ℝ) (Fintype.card ι : ℝ)
  let w := daiLiKGeDGridWidth (d : ℝ) ell
  have hScale : ell = daiLiKGeDFourthRootThreshold
      (P.encodedQubits : ℝ) (d : ℝ) (Fintype.card ι : ℝ) := rfl
  have hWidth : w = daiLiKGeDGridWidth (d : ℝ) ell := rfl
  have hEllNat : 1 ≤ ell :=
    one_le_daiLiKGeDFourthRootThreshold hK hN hAboveBPTBranch
  have hEll : 0 < ell := lt_of_lt_of_le (by norm_num) hEllNat
  have hSquareBound : ell ^ 2 ≤ (d : ℝ) / 10000 :=
    daiLiFinal_square_scale_le hK hDReal hN hKLeNReal hScale
  have hWidthProduct : w * ell = (d : ℝ) / 100 := by
    rw [hWidth, daiLiKGeDGridWidth]
    field_simp [hEll.ne']
  have hHundredEllLeWidth : 100 * ell ≤ w := by
    rw [hWidth, daiLiKGeDGridWidth]
    apply (le_div_iff₀ (by nlinarith [hEll])).2
    nlinarith [hSquareBound]
  have hWidthNat : 1 ≤ w := by
    nlinarith [hHundredEllLeWidth, hEllNat]
  have hDistanceLargeReal : (7 : ℝ) ≤ d :=
    daiLiFinal_distance_ge_seven hDReal hN hKLeNReal hAboveBPT
  have hDistanceLarge : 7 ≤ d := by exact_mod_cast hDistanceLargeReal
  let steps : ℕ := Nat.ceil w
  have hStepsBound : w ≤ (steps : ℝ) := by
    dsimp [steps]
    exact_mod_cast (Nat.le_ceil w)
  have hStepsTimesEll : w ≤ (steps : ℝ) * ell := by
    have hProductNonneg : 0 ≤ (steps : ℝ) * (ell - 1) :=
      mul_nonneg (Nat.cast_nonneg _) (by linarith)
    nlinarith
  have hBaseHorizontal : (1 / 2 : ℝ) ≤ w / 2 := by
    nlinarith [hWidthNat]
  have hBaseVerticalGood : (1 / 2 : ℝ) ≤ w / 2 := hBaseHorizontal
  have hBaseVerticalBad : (1 / 2 : ℝ) ≤ 5 * ell / 2 := by
    nlinarith [hEllNat]
  have hBaseDiameter : (1 : ℝ) ≤ 2 * (1 / 2 : ℝ) := by norm_num
  have hReach : w / 2 ≤ (1 / 2 : ℝ) + (steps : ℝ) * ell := by
    nlinarith [hStepsTimesEll]
  have hBoundaryBudget :
      48 * (w / 2 + w / 2 + ell) * ell + (d : ℝ) / 10 < d := by
    nlinarith [hWidthProduct, hSquareBound]
  have hShortPackingScale : 60 * w * ell < d := by
    nlinarith [hWidthProduct]
  have hCellWidth : 5 * ell ≤ w := by
    nlinarith [hHundredEllLeWidth]
  have hInternalSideScale : 12 * ell * w < d := by
    nlinarith [hWidthProduct]
  have hGridWidth : 4 * ell ≤ w := by
    nlinarith [hHundredEllLeWidth]
  have hGridLong : 1 ≤ w - 4 * ell := by
    nlinarith [hHundredEllLeWidth, hEllNat]
  have hGridSideSmall : 12 * ell * (w - 4 * ell) < d := by
    nlinarith [hWidthProduct, sq_nonneg ell]
  have hUnitBaseCard (center : ℝ × ℝ) :
      (centeredRectangleQubits embedding center (1 / 2 : ℝ) (1 / 2 : ℝ)).card < d :=
    daiLiFinal_unit_base_card_lt_distance embedding center d hDistanceLarge
  refine daiLi_final_interaction_count_max_length_of_geometry
    P embedding d hDistance ell w hScale hWidth hD hEncodedPositive hAboveBPTBranch hWidthNat
    (1 / 2 : ℝ) (1 / 2 : ℝ) steps hBaseHorizontal hBaseVerticalGood hBaseVerticalBad
    hBaseDiameter hBaseDiameter hReach hReach hReach ?_ ?_ ?_ hBoundaryBudget
    hShortPackingScale hCellWidth hInternalSideScale hGridWidth hGridLong hGridSideSmall
  · intro t atoms rectangles hAtoms hRectangles cell hCandidate
    exact hUnitBaseCard _
  · intro t atoms rectangles hAtoms hRectangles cell slot hCandidate
    exact hUnitBaseCard _
  · intro t cell hOccupied
    exact hUnitBaseCard _

end QEC.Locality
