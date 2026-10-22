import QEC.Locality.OptimalTradeoff.CorrectablePartition
/-!
# Dai--Li long-interaction count composition

This internal module closes the quantitative handoff from the finite
correctable-region construction to a lower bound on the cardinality of the
actual unordered long-interaction set.  It is deliberately not imported by
`QEC.lean`: public source/TeX realization remains outside this internal module.

The project-owned factor-30 subdivision repair is consumed through
`card_daiLiKGeDSeparator_le_conservative`; it is not attributed to DL24.
-/

noncomputable section

namespace QEC.Locality

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

/-- The principal nonnegative fourth root used in the finite Dai--Li branch. -/
def daiLiFourthRoot (x : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt x)

theorem daiLiFourthRoot_nonneg (x : ℝ) :
    0 ≤ daiLiFourthRoot x :=
  Real.sqrt_nonneg _

theorem daiLiFourthRoot_sq (x : ℝ) :
    daiLiFourthRoot x ^ 2 = Real.sqrt x := by
  unfold daiLiFourthRoot
  exact Real.sq_sqrt (Real.sqrt_nonneg x)

theorem daiLiFourthRoot_pow_four (x : ℝ) (hx : 0 ≤ x) :
    daiLiFourthRoot x ^ 4 = x := by
  calc
    daiLiFourthRoot x ^ 4 = (daiLiFourthRoot x ^ 2) ^ 2 := by ring
    _ = (Real.sqrt x) ^ 2 := by rw [daiLiFourthRoot_sq x]
    _ = x := Real.sq_sqrt hx

/-- The project-owned low-scale Dai--Li threshold.  The source uses the
`1 / 100` witness; the fourth root is the principal nonnegative root. -/
def daiLiKGeDFourthRootThreshold (k d n : ℝ) : ℝ :=
  daiLiFourthRoot (k * d ^ 2 / n) / 100

/-- The source grid width paired with the low-scale fourth-root threshold. -/
def daiLiKGeDGridWidth (d ell : ℝ) : ℝ :=
  d / (100 * ell)

theorem daiLiKGeDFourthRootThreshold_nonneg (k d n : ℝ) :
    0 ≤ daiLiKGeDFourthRootThreshold k d n := by
  unfold daiLiKGeDFourthRootThreshold
  exact div_nonneg (daiLiFourthRoot_nonneg _) (by norm_num)

theorem daiLiKGeDFourthRootThreshold_pow_four
    {k d n : ℝ} (hk : 0 ≤ k) (hn : 0 < n) :
    daiLiKGeDFourthRootThreshold k d n ^ 4 =
      k * d ^ 2 / (100 ^ 4 * n) := by
  have hRatio : 0 ≤ k * d ^ 2 / n :=
    div_nonneg (mul_nonneg hk (sq_nonneg d)) hn.le
  rw [daiLiKGeDFourthRootThreshold]
  rw [div_pow, daiLiFourthRoot_pow_four _ hRatio]
  field_simp

/-- The explicit above-BPT threshold makes the source fourth-root scale at
least one.  This is a finite real-arithmetic fact, not a count hypothesis. -/
theorem one_le_daiLiKGeDFourthRootThreshold
    {k d n : ℝ} (hk : 0 ≤ k) (hn : 0 < n)
    (habove : (100 : ℝ) ^ 4 * n ≤ k * d ^ 2) :
    1 ≤ daiLiKGeDFourthRootThreshold k d n := by
  have hRatio : 0 ≤ k * d ^ 2 / n :=
    div_nonneg (mul_nonneg hk (sq_nonneg d)) hn.le
  have hRatioLarge : (100 : ℝ) ^ 4 ≤ k * d ^ 2 / n := by
    apply (le_div_iff₀ hn).2
    nlinarith
  have hRootNonneg : 0 ≤ daiLiFourthRoot (k * d ^ 2 / n) :=
    daiLiFourthRoot_nonneg _
  have hRootPow : daiLiFourthRoot (k * d ^ 2 / n) ^ 4 = k * d ^ 2 / n :=
    daiLiFourthRoot_pow_four _ hRatio
  have hRootLarge : (100 : ℝ) ≤ daiLiFourthRoot (k * d ^ 2 / n) := by
    by_contra h
    have hRootSmall : daiLiFourthRoot (k * d ^ 2 / n) < 100 := lt_of_not_ge h
    have hSquareSmall : daiLiFourthRoot (k * d ^ 2 / n) ^ 2 < 100 ^ 2 := by
      nlinarith [sq_nonneg (daiLiFourthRoot (k * d ^ 2 / n) - 100)]
    have hFourthSmall : daiLiFourthRoot (k * d ^ 2 / n) ^ 4 < 100 ^ 4 := by
      nlinarith [sq_nonneg (daiLiFourthRoot (k * d ^ 2 / n) ^ 2 - 100 ^ 2)]
    nlinarith
  unfold daiLiKGeDFourthRootThreshold
  linarith

/-- Algebraic inversion of the concrete #386 separator estimate.  This is
private because the public handoff below obtains both displayed inequalities
from the actual finite partition and its selected grid translation. -/
private theorem daiLiKGeD_lowScale_count_of_concrete_separator
    {k d n ell w vertex longCount : ℝ}
    (hk : 0 ≤ k) (hd : 0 < d) (hn : 0 < n)
    (hkn : k ≤ n) (hLowScale : d ^ 2 ≤ k * n) (hell : 0 < ell)
    (hFourth : ell ^ 4 = k * d ^ 2 / (100 ^ 4 * n))
    (hWidth : w = d / (100 * ell))
    (hVertex : vertex ≤ (32 * ell ^ 2 / w ^ 2) * n)
    (hSeparator : k ≤ vertex + 2 * longCount + 960 * ell ^ 2 * k / d) :
    k / 100 ≤ longCount := by
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hell0 : ell ≠ 0 := ne_of_gt hell
  have hFourthDenom : 0 < (100 : ℝ) ^ 4 * n := by positivity
  have hFourthCleared : ell ^ 4 * (100 ^ 4 * n) = k * d ^ 2 :=
    (eq_div_iff hFourthDenom.ne').mp hFourth
  have hVertexExact : (32 * ell ^ 2 / w ^ 2) * n = (8 / 2500 : ℝ) * k := by
    rw [hWidth]
    field_simp [hd0, hell0]
    nlinarith [hFourthCleared]
  have hVertexSmall : vertex ≤ k / 100 := by
    rw [hVertexExact] at hVertex
    nlinarith
  have hFourthBound : ell ^ 4 ≤ d ^ 2 / 100 ^ 4 := by
    rw [hFourth]
    apply (div_le_iff₀ (mul_pos (by positivity : (0 : ℝ) < 100 ^ 4) hn)).2
    have hScale : 0 ≤ (n - k) * d ^ 2 :=
      mul_nonneg (sub_nonneg.mpr hkn) (sq_nonneg d)
    have hSourceDomain : 0 ≤ k * n - d ^ 2 := sub_nonneg.mpr hLowScale
    nlinarith [hSourceDomain]
  have hSquareBound : ell ^ 2 ≤ d / 10000 := by
    by_contra h
    have hSquareLarge : d / 10000 < ell ^ 2 := lt_of_not_ge h
    have hdNonneg : 0 ≤ d := hd.le
    have hEllSqNonneg : 0 ≤ ell ^ 2 := sq_nonneg ell
    nlinarith [sq_nonneg (ell ^ 2 - d / 10000)]
  have hRectangleSmall : 960 * ell ^ 2 * k / d ≤ k / 10 := by
    apply (div_le_iff₀ hd).2
    have hScale : 0 ≤ (d / 10000 - ell ^ 2) * k :=
      mul_nonneg (sub_nonneg.mpr hSquareBound) hk
    nlinarith
  nlinarith

private theorem daiLi_encodedQubits_le_blockLength
    (P : Coding.StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    P.encodedQubits ≤ Fintype.card ι := by
  rw [P.encodedQubits_eq_blockLength_sub_generatorRank]
  exact Nat.sub_le _ _

/-- The actual low-scale `k >= d` fourth-root count branch.  The theorem
chooses the finite averaged grid translation, constructs the #496 rectangles,
then invokes #386's CPTP partition theorem and its concrete separator bound.
It counts the selected presentation's distinct unordered interactions exactly
once through `longInteractionCount`; the doubled incidence total appears only
as a derived internal bridge.  The hypotheses following the source scale are
the explicit finite recovery-side inequalities still required by #386, not a
supplied partition, separator, recovery, or interaction-count conclusion. -/
theorem daiLiKGeD_lowScale_fourthRoot_longInteractionCount
    (P : Coding.StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : Coding.StabilizerCode.SemanticStabilizerDistance P.code d)
    (ell w : ℝ)
    (hScale : ell = daiLiKGeDFourthRootThreshold
      (P.encodedQubits : ℝ) (d : ℝ) (Fintype.card ι : ℝ))
    (hWidth : w = daiLiKGeDGridWidth (d : ℝ) ell)
    (hD : 0 < d) (hKGeD : d ≤ P.encodedQubits)
    (hLowScale : (d : ℝ) ≤ Real.sqrt ((P.encodedQubits : ℝ) * Fintype.card ι))
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
    (hGoodBaseCard : ∀ (t : GridTranslation w)
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
    (hBadBaseCard : ∀ (t : GridTranslation w)
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
    (hBoundaryBudget :
      48 * (w / 2 + w / 2 + ell) * ell + (d : ℝ) / 10 < d)
    (hShortPackingScale : 60 * w * ell < d)
    (hCellWidth : 5 * ell ≤ w) (hInternalSideScale : 12 * ell * w < d)
    (hGridWidth : 4 * ell ≤ w) (hGridLong : 1 ≤ w - 4 * ell)
    (hGridSideSmall : 12 * ell * (w - 4 * ell) < d) :
    (P.encodedQubits : ℝ) / 100 ≤ (P.longInteractionCount embedding ell : ℝ) := by
  have hKPositiveNat : 0 < P.encodedQubits := lt_of_lt_of_le hD hKGeD
  have hKLeNNat : P.encodedQubits ≤ Fintype.card ι :=
    daiLi_encodedQubits_le_blockLength P
  have hNPositiveNat : 0 < Fintype.card ι :=
    lt_of_lt_of_le hKPositiveNat hKLeNNat
  have hk : 0 ≤ (P.encodedQubits : ℝ) := Nat.cast_nonneg _
  have hd : 0 < (d : ℝ) := by exact_mod_cast hD
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast hNPositiveNat
  have hkn : (P.encodedQubits : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast hKLeNNat
  have hProductNonneg : 0 ≤ (P.encodedQubits : ℝ) * Fintype.card ι :=
    mul_nonneg hk hn.le
  have hLowScaleSquare : (d : ℝ) ^ 2 ≤ (P.encodedQubits : ℝ) * Fintype.card ι := by
    have hRootSquare : Real.sqrt ((P.encodedQubits : ℝ) * Fintype.card ι) ^ 2 =
        (P.encodedQubits : ℝ) * Fintype.card ι :=
      Real.sq_sqrt hProductNonneg
    nlinarith [sq_nonneg ((d : ℝ) -
      Real.sqrt ((P.encodedQubits : ℝ) * Fintype.card ι))]
  have hEllNat : 1 ≤ ell := by
    rw [hScale]
    exact one_le_daiLiKGeDFourthRootThreshold hk hn hAboveBPT
  have hEll : 0 < ell := by linarith
  have hWidthPos : 0 < w := lt_of_lt_of_le (by norm_num) hWidthNat
  have hEdge : 1 ≤ 2 * ell := by nlinarith
  have hFourth : ell ^ 4 =
      (P.encodedQubits : ℝ) * (d : ℝ) ^ 2 /
        (100 ^ 4 * Fintype.card ι) := by
    rw [hScale]
    exact daiLiKGeDFourthRootThreshold_pow_four hk hn
  by_contra hLower
  have hLongSmall : (P.longInteractionCount embedding ell : ℝ) <
      (P.encodedQubits : ℝ) / 100 := lt_of_not_ge hLower
  have hLongSmallNat : 100 * P.longInteractionCount embedding ell < P.encodedQubits := by
    have hLongSmallReal : (100 : ℝ) * P.longInteractionCount embedding ell <
        P.encodedQubits := by
      nlinarith
    exact_mod_cast hLongSmallReal
  have hGlobal : 50 * (∑ q : ι, P.daiLiInteractionCounter embedding ell q) ≤
      P.encodedQubits := by
    rw [P.sum_daiLiInteractionCounter_eq_two_mul_longInteractionCount embedding ell]
    omega
  obtain ⟨t, hVertex⟩ := exists_good_vertex_translation w ell hEll hGridWidth embedding.point
  obtain ⟨atoms, rectangles, hAtoms, hRectangles, _hOrdered, _hPairwise, _hCover,
      _hPieces, hRectangleCount⟩ :=
    exists_daiLiBadGridCellSubdivision P embedding ell ell d w (gridOrigin w t) hEll hCellWidth
  have hOverlap := daiLiBadGridTotalF_le_four_mul_globalCounter P embedding ell d hWidthPos
    (gridOrigin w t)
  have hDimensionNat := daiLiKGeD_encodedQubits_le_separator_card P embedding d hDistance
    ell w ell t atoms rectangles hAtoms hRectangles hEllNat hWidthNat hEllNat hWidthPos hEll
    le_rfl baseHorizontalRadius baseVerticalRadius steps hBaseHorizontal hBaseVerticalGood
    hBaseVerticalBad hBaseHorizontalDiameter hBaseVerticalDiameter hReachHorizontal
    hReachVerticalGood hReachVerticalBad
    (hGoodBaseCard t atoms rectangles hAtoms hRectangles)
    (hBadBaseCard t atoms rectangles hAtoms hRectangles)
    hBoundaryBudget hShortPackingScale hCellWidth hInternalSideScale hGridWidth hEdge hGridLong
    hGridSideSmall
  have hDimension : (P.encodedQubits : ℝ) ≤
      ((daiLiKGeDSeparator P embedding ell w ell t
        (daiLiBadGridCells P embedding ell d w (gridOrigin w t)) rectangles).card : ℝ) := by
    exact_mod_cast hDimensionNat
  have hSeparator := card_daiLiKGeDSeparator_le_conservative P embedding ell w ell t
    (daiLiBadGridCells P embedding ell d w (gridOrigin w t)) rectangles d P.encodedQubits
    hEllNat hD hRectangleCount hOverlap hGlobal
  have hCombined : (P.encodedQubits : ℝ) ≤
      (vertexBadCount w (2 * ell) embedding.point t : ℝ) +
        2 * (P.longInteractionCount embedding ell : ℝ) +
          960 * ell ^ 2 * (P.encodedQubits : ℝ) / d := by
    rw [P.sum_daiLiInteractionCounter_eq_two_mul_longInteractionCount embedding ell] at hSeparator
    norm_num at hSeparator
    exact hDimension.trans hSeparator
  have hConclusion := daiLiKGeD_lowScale_count_of_concrete_separator hk hd hn hkn
    hLowScaleSquare hEll hFourth hWidth hVertex hCombined
  exact (not_lt_of_ge hConclusion hLongSmall)

end QEC.Locality
