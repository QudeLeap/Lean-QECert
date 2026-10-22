import QEC.Coding.ExpanderCodes.LocalParameterSelection

/-!
# Concrete local pairs at compatible prime degrees

This module closes the finite local-code selection step.  For every finite
field and every target rate below one, it chooses one coefficient block, one
source-compatible prime degree, and an actual simultaneous pair of local
matrices at exactly that degree.  The result also records the rate inequality
and the arithmetic comparison between the LPS Ramanujan scale `2 √p` and
the deterministic spectral scale used by the Tanner distance theorem.
-/

namespace QEC.Coding.TannerLiftedProduct

variable {F : Type}

noncomputable local instance pk22LocalPairDecidableEq : DecidableEq F :=
  Classical.decEq F

/-- Direction coordinates at one compatible PK22 prime degree. -/
abbrev PK22Direction (q t : Nat)
    (a : CompatibleDegreePrime (pk22LocalWidth q t)) :=
  Fin (a.p + 1)

/-- Local check coordinates replicated to the same compatible degree. -/
abbrev PK22Check (q t : Nat)
    (a : CompatibleDegreePrime (pk22LocalWidth q t)) :=
  Fin (pk22RowCoefficient q t * a.blocks)

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 5000 in
/-- Concrete simultaneous local-code selection at a source-compatible prime
degree.  No matrix property is supplied as an assumption: both matrices and
all their distance/product-expansion properties are obtained from the finite
six-event union bound. -/
theorem exists_pk22CompatibleLocalPair
    (F : Type) [Field F] [Fintype F]
    (rate : ℝ) (hRate : rate < 1) :
    ∃ (t : Nat)
      (a : CompatibleDegreePrime (pk22LocalWidth (Nat.card F) t))
      (h h' : Matrix (PK22Check (Nat.card F) t a)
        (PK22Direction (Nat.card F) t a) F),
      pk22ScaleThreshold (Nat.card F) t ≤ Nat.nthRoot 6 a.blocks ∧
      pk22DistanceCoefficient (Nat.card F) t * a.blocks ≤
        Fintype.card (PK22Direction (Nat.card F) t a) ∧
      h.rank = Fintype.card (PK22Check (Nat.card F) t a) ∧
      h'.rank = Fintype.card (PK22Check (Nat.card F) t a) ∧
      (∀ c : Word F (PK22Direction (Nat.card F) t a),
        c ∈ (ProductExpansion.parityCheckCode h).carrier → c ≠ 0 →
        pk22DistanceCoefficient (Nat.card F) t * a.blocks ≤
          HammingWeight c) ∧
      (∀ c : Word F (PK22Direction (Nat.card F) t a),
        c ∈ (ProductExpansion.parityCheckCode h').carrier → c ≠ 0 →
        pk22DistanceCoefficient (Nat.card F) t * a.blocks ≤
          HammingWeight c) ∧
      ProductExpansion.ProductExpanding h
        (ProductExpansion.generatorImageParityCheck h')
        (pk22FaceCoefficient (Nat.card F) t *
          (Nat.nthRoot 6 a.blocks) ^ 7)
        (2 * (Nat.nthRoot 6 a.blocks) ^ 4)
        (((pk22DistanceCoefficient (Nat.card F) t * a.blocks : Nat) : ℝ) /
          (3 * (Fintype.card (PK22Direction (Nat.card F) t a) : ℝ))) ∧
      ProductExpansion.ProductExpanding h'
        (ProductExpansion.generatorImageParityCheck h)
        (pk22FaceCoefficient (Nat.card F) t *
          (Nat.nthRoot 6 a.blocks) ^ 7)
        (2 * (Nat.nthRoot 6 a.blocks) ^ 4)
        (((pk22DistanceCoefficient (Nat.card F) t * a.blocks : Nat) : ℝ) /
          (3 * (Fintype.card (PK22Direction (Nat.card F) t a) : ℝ))) ∧
      2 * ((Fintype.card (PK22Check (Nat.card F) t a) : ℝ) +
          Fintype.card (PK22Check (Nat.card F) t a)) *
          Fintype.card (PK22Direction (Nat.card F) t a) ≤
        (1 - rate) *
          ((Fintype.card (PK22Direction (Nat.card F) t a) : ℝ) ^ 2 +
            4 * Fintype.card (PK22Check (Nat.card F) t a) *
              Fintype.card (PK22Check (Nat.card F) t a)) ∧
      2 * Real.sqrt (a.p : ℝ) ≤
        ((pk22SpectralCoefficient (Nat.card F) t *
          (Nat.nthRoot 6 a.blocks) ^ 3 : Nat) : ℝ) := by
  let q := Nat.card F
  have hq : 2 ≤ q := by
    dsimp [q]
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  obtain ⟨t, hRowsLarge, hDistanceLarge, hRateLarge⟩ :=
    exists_pk22ParameterIndex q hq rate hRate
  let A := pk22LocalWidth q t
  let D := pk22DistanceCoefficient q t
  let B := pk22RowCoefficient q t
  let C := pk22SpectralCoefficient q t
  let S := pk22FaceCoefficient q t
  have hAPositive : 0 < A := by
    dsimp [A, pk22LocalWidth]
    exact Nat.pow_pos (pk22ParameterBase_pos q t)
  have hAOdd : Odd A := by
    simpa [A] using pk22LocalWidth_odd q t
  obtain ⟨a, hScale⟩ :=
    exists_compatibleDegreePrime_nthRoot_ge
      A (pk22ScaleThreshold q t) hAPositive hAOdd
  let N := a.blocks
  let x := Nat.nthRoot 6 N
  have hNPositive : 0 < N := by
    exact a.blocks_pos hAPositive
  have hxLower : x ^ 6 ≤ N := by
    exact Nat.pow_nthRoot_le (by norm_num)
  have hxUpper : N ≤ 64 * x ^ 6 :=
    le_sixtyFour_mul_nthRoot_six_pow N hNPositive
  have hScale' : pk22ScaleThreshold q t ≤ x := by
    simpa [A, N, x] using hScale
  obtain ⟨hxPositive, hSmall, hBudgetCoefficient, hRectangleScale,
      hVertical, hEdge, hFace, hRectangleThreshold⟩ :=
    pk22_scale_bounds q t x hScale'
  obtain ⟨hDLe, hBLe, hLPositive, hFirstKernel, hFirstImage,
      hSecondKernel, hSecondImage⟩ :=
    pk22_blockWitnesses q t hq hRowsLarge hDistanceLarge
  have hRankCoefficient : 36 * 1 * S ≤ 5 * D ^ 2 := by
    simpa [S, D] using pk22_rankCoefficient_bound q t
  have hWCard : Fintype.card (PK22Direction q t a) = A * N := by
    simpa [PK22Direction, A, N] using a.degree_eq_block_mul
  have hRCard : Fintype.card (PK22Check q t a) = B * N := by
    simp [PK22Check, B, N]
  have hRectangleThreshold' :
      2 * (64 * A) + 2 * (64 * A) * S + 4 * 1 * (64 * A) +
          16 * S + 11 < 1 * B * x := by
    simpa [pk22RectangleConstant, A, B, S] using hRectangleThreshold
  obtain ⟨h, h', hRank, h'Rank, hDistance, _hImageDistance,
      hDistanceReverse, _hImageDistanceReverse,
      hProductExpand, hProductExpandReverse⟩ :=
    exists_rootScheduled_localPair
      (F := F) (W := PK22Direction q t a)
      (R := PK22Check q t a) (R' := PK22Check q t a)
      A D 1 S 1 B B (quadraticWeightBase q A) N x
      hWCard hRCard hRCard
      (by simpa [D, A] using hDLe)
      (by simpa [B, A] using hBLe)
      (by simpa [B, A] using hBLe)
      hAPositive (by simpa [D] using pk22DistanceCoefficient_pos q t)
      (by simpa [A] using hLPositive) hxPositive hxLower hxUpper
      (by simpa [D] using hSmall) hRankCoefficient
      (by simpa only [A, D, B] using hFirstKernel)
      (by simpa only [A, D, B] using hFirstImage)
      (by simpa only [A, D, B] using hSecondKernel)
      (by simpa only [A, D, B] using hSecondImage)
      hRectangleThreshold' hRectangleThreshold'
  have hRateCoefficient :=
    pk22_rateCoefficient_bound q t hq rate hRate hRateLarge
  have hRateRatio :=
    replicatedSchedule_rateRatio A B B N rate (by
      simpa [A, B] using hRateCoefficient)
  have hSpectralScale :=
    two_mul_sqrt_compatibleDegreePrime_le_pk22SpectralScale q t x a hxUpper
  have hLength : D * N ≤ Fintype.card (PK22Direction q t a) := by
    rw [hWCard]
    exact Nat.mul_le_mul_right N hDLe
  refine ⟨t, a, h, h', ?_, ?_, hRank, h'Rank, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [q, N, x] using hScale'
  · simpa [q, D, N] using hLength
  · simpa [q, D, N] using hDistance
  · simpa [q, D, N] using hDistanceReverse
  · simpa [q, D, S, N, x] using hProductExpand
  · simpa [q, D, S, N, x] using hProductExpandReverse
  · simpa [q, A, B, N, hWCard, hRCard] using hRateRatio
  · simpa [q, N, x] using hSpectralScale

end QEC.Coding.TannerLiftedProduct
