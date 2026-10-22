import QEC.Coding.ExpanderCodes.CompatiblePrimeDegree
import QEC.Coding.ExpanderCodes.TannerScheduledLocalPair

/-!
# Concrete local parameter selection for good lifted-product codes

This module chooses the fixed local coefficients used by the PK22 family.
The width is a fourth power of an odd number, while the distance and spectral
coefficients grow only quadratically.  The logarithmic row selector then has
vanishing relative size, so every requested rate below one is attainable.
-/

namespace QEC.Coding.TannerLiftedProduct

/-- Odd base used by the concrete local parameter family. -/
def pk22ParameterBase (q t : Nat) : Nat := 2 * q ^ t + 1

/-- Fixed local direction count. -/
def pk22LocalWidth (q t : Nat) : Nat := (pk22ParameterBase q t) ^ 4

/-- Coefficient absorbing the Ramanujan square-root scale. -/
def pk22SpectralCoefficient (q t : Nat) : Nat :=
  16 * (pk22ParameterBase q t) ^ 2

/-- Sparse-rectangle size coefficient. -/
def pk22FaceCoefficient (q t : Nat) : Nat :=
  112 * (pk22SpectralCoefficient q t) ^ 2

/-- Relative local-distance coefficient. -/
def pk22DistanceCoefficient (q t : Nat) : Nat :=
  32 * pk22SpectralCoefficient q t

/-- Number of local parity-check rows in either orientation. -/
def pk22RowCoefficient (q t : Nat) : Nat :=
  logarithmicLocalRows q (pk22LocalWidth q t) (pk22DistanceCoefficient q t)

theorem pk22ParameterBase_pos (q t : Nat) :
    0 < pk22ParameterBase q t := by
  simp [pk22ParameterBase]

theorem pk22ParameterBase_odd (q t : Nat) :
    Odd (pk22ParameterBase q t) := by
  exact ⟨q ^ t, by simp [pk22ParameterBase, two_mul]⟩

theorem pk22LocalWidth_odd (q t : Nat) :
    Odd (pk22LocalWidth q t) := by
  exact (pk22ParameterBase_odd q t).pow

theorem pow_le_pk22ParameterBase (q t : Nat) :
    q ^ t ≤ pk22ParameterBase q t := by
  simp [pk22ParameterBase]
  omega

theorem pk22ParameterBase_le_three_mul_pow
    (q t : Nat) (hq : 0 < q) :
    pk22ParameterBase q t ≤ 3 * q ^ t := by
  have hPow : 0 < q ^ t := Nat.pow_pos hq
  simp only [pk22ParameterBase]
  omega

theorem pk22ParameterBase_le_pow_add_two
    (q t : Nat) (hq : 2 ≤ q) :
    pk22ParameterBase q t ≤ q ^ (t + 2) := by
  have hqPositive : 0 < q := by omega
  calc
    pk22ParameterBase q t ≤ 3 * q ^ t :=
      pk22ParameterBase_le_three_mul_pow q t hqPositive
    _ ≤ q ^ 2 * q ^ t := by
      gcongr
      nlinarith
    _ = q ^ (t + 2) := by rw [pow_add]; ring

theorem pk22LocalWidth_log_le
    (q t : Nat) (hq : 2 ≤ q) :
    Nat.log q (pk22LocalWidth q t) ≤ 4 * t + 8 := by
  apply log_le_exponent_of_le_pow q _ _ (by omega)
  calc
    pk22LocalWidth q t ≤ (q ^ (t + 2)) ^ 4 := by
      exact Nat.pow_le_pow_left (pk22ParameterBase_le_pow_add_two q t hq) 4
    _ = q ^ (4 * t + 8) := by
      rw [← pow_mul]
      congr 1
      omega

theorem pk22DistanceCoefficient_le
    (q t : Nat) (hq : 2 ≤ q) :
    pk22DistanceCoefficient q t ≤ 4608 * q ^ (2 * t) := by
  have hBase := pk22ParameterBase_le_three_mul_pow q t (by omega)
  unfold pk22DistanceCoefficient pk22SpectralCoefficient
  calc
    32 * (16 * pk22ParameterBase q t ^ 2) =
        512 * pk22ParameterBase q t ^ 2 := by ring
    _ ≤ 512 * (3 * q ^ t) ^ 2 := by gcongr
    _ = 4608 * q ^ (2 * t) := by rw [mul_pow, ← pow_mul]; ring

/-- The concrete row count is bounded by a cubic field-size power.  This
explicit bound is the quantitative reason its ratio to the fourth-power
local width tends to zero. -/
theorem pk22RowCoefficient_le
    (q t : Nat) (hq : 2 ≤ q) :
    pk22RowCoefficient q t ≤ 124421 * q ^ (3 * t) := by
  let Q := q ^ t
  have hQPositive : 0 < Q := Nat.pow_pos (by omega)
  have htQ : t ≤ Q := by
    simpa [Q] using self_le_base_pow q t hq
  have hLog := pk22LocalWidth_log_le q t hq
  have hDistance := pk22DistanceCoefficient_le q t hq
  have hLinear : 8 * t + 19 ≤ 27 * Q := by omega
  have hQOne : 1 ≤ Q ^ 3 := Nat.one_le_pow 3 Q hQPositive
  unfold pk22RowCoefficient logarithmicLocalRows
  calc
    pk22DistanceCoefficient q t +
          2 * pk22DistanceCoefficient q t *
            (Nat.log q (pk22LocalWidth q t) + 1) + 5 ≤
        pk22DistanceCoefficient q t * (8 * t + 19) + 5 := by
      nlinarith
    _ ≤ (4608 * q ^ (2 * t)) * (27 * Q) + 5 := by gcongr
    _ = 124416 * Q ^ 3 + 5 := by
      dsimp [Q]
      rw [show 2 * t = t * 2 by omega, pow_mul]
      ring
    _ ≤ 124421 * Q ^ 3 := by nlinarith
    _ = 124421 * q ^ (3 * t) := by
      dsimp [Q]
      rw [show 3 * t = t * 3 by omega, pow_mul]

theorem pk22DistanceCoefficient_le_localWidth
    (q t : Nat) (_hq : 2 ≤ q) (hLarge : 23 ≤ q ^ t) :
    pk22DistanceCoefficient q t ≤ pk22LocalWidth q t := by
  have hBaseLarge : 23 ≤ pk22ParameterBase q t :=
    hLarge.trans (pow_le_pk22ParameterBase q t)
  unfold pk22DistanceCoefficient pk22SpectralCoefficient pk22LocalWidth
  have hSquare : 512 ≤ pk22ParameterBase q t ^ 2 := by nlinarith
  calc
    32 * (16 * pk22ParameterBase q t ^ 2) =
        512 * pk22ParameterBase q t ^ 2 := by ring
    _ ≤ pk22ParameterBase q t ^ 2 * pk22ParameterBase q t ^ 2 :=
      Nat.mul_le_mul_right _ hSquare
    _ = pk22ParameterBase q t ^ 4 := by ring

theorem pk22RowCoefficient_twice_le_localWidth
    (q t : Nat) (hq : 2 ≤ q)
    (hLarge : 2 * 124421 ≤ q ^ t) :
    2 * pk22RowCoefficient q t ≤ pk22LocalWidth q t := by
  have hRows := pk22RowCoefficient_le q t hq
  have hPowPositive : 0 < q ^ (3 * t) := Nat.pow_pos (by omega)
  have hWidthLower : q ^ (4 * t) ≤ pk22LocalWidth q t := by
    unfold pk22LocalWidth
    calc
      q ^ (4 * t) = (q ^ t) ^ 4 := by
        rw [show 4 * t = t * 4 by omega, pow_mul]
      _ ≤ pk22ParameterBase q t ^ 4 :=
        Nat.pow_le_pow_left (pow_le_pk22ParameterBase q t) 4
  calc
    2 * pk22RowCoefficient q t ≤
        2 * (124421 * q ^ (3 * t)) := Nat.mul_le_mul_left 2 hRows
    _ = (2 * 124421) * q ^ (3 * t) := by ring
    _ ≤ q ^ t * q ^ (3 * t) := Nat.mul_le_mul_right _ hLarge
    _ = q ^ (4 * t) := by rw [← pow_add]; congr 1; omega
    _ ≤ pk22LocalWidth q t := hWidthLower

/-- The concrete local dimensions meet any requested rate below one once
the exponential index is large enough. -/
theorem pk22_rateCoefficient_bound
    (q t : Nat) (hq : 2 ≤ q) (rate : ℝ) (hRate : rate < 1)
    (hLarge : (4 * 124421 : ℝ) <
      (1 - rate) * ((q ^ t : Nat) : ℝ)) :
    2 * ((pk22RowCoefficient q t : ℝ) + pk22RowCoefficient q t) *
        pk22LocalWidth q t ≤
      (1 - rate) *
        ((pk22LocalWidth q t : ℝ) ^ 2 +
          4 * (pk22RowCoefficient q t : ℝ) * pk22RowCoefficient q t) := by
  have hRows := pk22RowCoefficient_le q t hq
  have hWidthLower : q ^ (4 * t) ≤ pk22LocalWidth q t := by
    unfold pk22LocalWidth
    calc
      q ^ (4 * t) = (q ^ t) ^ 4 := by
        rw [show 4 * t = t * 4 by omega, pow_mul]
      _ ≤ pk22ParameterBase q t ^ 4 :=
        Nat.pow_le_pow_left (pow_le_pk22ParameterBase q t) 4
  have hPowPositiveReal : (0 : ℝ) < ((q ^ (3 * t) : Nat) : ℝ) := by
    positivity
  have hRowsRate :
      4 * (pk22RowCoefficient q t : ℝ) <
        (1 - rate) * (pk22LocalWidth q t : ℝ) := by
    calc
      4 * (pk22RowCoefficient q t : ℝ) ≤
          ((4 * (124421 * q ^ (3 * t)) : Nat) : ℝ) := by
        exact_mod_cast Nat.mul_le_mul_left 4 hRows
      _ = (4 * 124421 : ℝ) * ((q ^ (3 * t) : Nat) : ℝ) := by
        push_cast
        ring
      _ < ((1 - rate) * ((q ^ t : Nat) : ℝ)) *
          ((q ^ (3 * t) : Nat) : ℝ) :=
        mul_lt_mul_of_pos_right hLarge hPowPositiveReal
      _ = (1 - rate) * ((q ^ (4 * t) : Nat) : ℝ) := by
        push_cast
        rw [show 4 * t = t + 3 * t by omega, pow_add]
        ring
      _ ≤ (1 - rate) * (pk22LocalWidth q t : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hRate.le)
        exact_mod_cast hWidthLower
  have hWidthNonnegative : (0 : ℝ) ≤ pk22LocalWidth q t := by positivity
  have hRowsNonnegative : (0 : ℝ) ≤ pk22RowCoefficient q t := by positivity
  nlinarith [sq_nonneg (pk22LocalWidth q t : ℝ),
    sq_nonneg (pk22RowCoefficient q t : ℝ)]

/-- There is an exponential index simultaneously large enough for row fit,
positive distance, and an arbitrary target rate below one. -/
theorem exists_pk22ParameterIndex
    (q : Nat) (hq : 2 ≤ q) (rate : ℝ) (hRate : rate < 1) :
    ∃ t : Nat,
      2 * 124421 ≤ q ^ t ∧
      23 ≤ q ^ t ∧
      (4 * 124421 : ℝ) < (1 - rate) * ((q ^ t : Nat) : ℝ) := by
  have hGap : 0 < 1 - rate := sub_pos.mpr hRate
  have hqReal : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  let target : ℝ := max (2 * 124421) (max 23 ((4 * 124421) / (1 - rate)))
  obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt target hqReal
  have hRowsReal : (2 * 124421 : ℝ) < (q : ℝ) ^ t :=
    (le_max_left _ _).trans_lt ht
  have hDistanceReal : (23 : ℝ) < (q : ℝ) ^ t :=
    (le_max_of_le_right (le_max_left _ _)).trans_lt ht
  have hRateDiv : (4 * 124421 : ℝ) / (1 - rate) < (q : ℝ) ^ t :=
    (le_max_of_le_right (le_max_right _ _)).trans_lt ht
  refine ⟨t, ?_, ?_, ?_⟩
  · exact_mod_cast hRowsReal.le
  · exact_mod_cast hDistanceReal.le
  · rw [div_lt_iff₀ hGap] at hRateDiv
    simpa [Nat.cast_pow, mul_comm] using hRateDiv

theorem pk22_blockWitnesses
    (q t : Nat) (hq : 2 ≤ q)
    (hRows : 2 * 124421 ≤ q ^ t)
    (hDistance : 23 ≤ q ^ t) :
    let A := pk22LocalWidth q t
    let D := pk22DistanceCoefficient q t
    let B := pk22RowCoefficient q t
    let L := quadraticWeightBase q A
    D ≤ A ∧ B ≤ A ∧ 0 < L ∧
    (6 * (q + L) ^ A < q ^ B * L ^ (A - D)) ∧
    (6 * (q + L) ^ A < q ^ (A - B) * L ^ (A - D)) ∧
    (6 * (q + L) ^ A < q ^ B * L ^ (A - D)) ∧
    (6 * (q + L) ^ A < q ^ (A - B) * L ^ (A - D)) := by
  dsimp only
  have hA : 0 < pk22LocalWidth q t := by
    unfold pk22LocalWidth
    exact Nat.pow_pos (pk22ParameterBase_pos q t)
  have hD := pk22DistanceCoefficient_le_localWidth q t hq hDistance
  have hRowsFit := pk22RowCoefficient_twice_le_localWidth q t hq hRows
  have hB : pk22RowCoefficient q t ≤ pk22LocalWidth q t := by omega
  have hL : 0 < quadraticWeightBase q (pk22LocalWidth q t) := by
    unfold quadraticWeightBase
    exact Nat.mul_pos (by omega) (Nat.pow_pos hA)
  have hWitnesses := logarithmicRows_blockWitnesses
    q (pk22LocalWidth q t) (pk22DistanceCoefficient q t)
    hq hA hD hRowsFit
  exact ⟨hD, hB, hL, hWitnesses⟩

/-- Constant part of the two sparse-rectangle exponent thresholds. -/
def pk22RectangleConstant (q t : Nat) : Nat :=
  let A := pk22LocalWidth q t
  let S := pk22FaceCoefficient q t
  2 * (64 * A) + 2 * (64 * A) * S + 4 * 1 * (64 * A) +
    16 * S + 11

/-- One scale threshold simultaneously discharges every deterministic local
and graph inequality used by the sixth-root schedule. -/
def pk22ScaleThreshold (q t : Nat) : Nat :=
  let A := pk22LocalWidth q t
  let C := pk22SpectralCoefficient q t
  let S := pk22FaceCoefficient q t
  18 + 4 * S + (C + 2) + 4 * C + (128 * A + 1) +
    (pk22RectangleConstant q t + 1)

theorem pk22DistanceCoefficient_pos (q t : Nat) :
    0 < pk22DistanceCoefficient q t := by
  unfold pk22DistanceCoefficient pk22SpectralCoefficient
  exact Nat.mul_pos (by norm_num)
    (Nat.mul_pos (by norm_num) (Nat.pow_pos (pk22ParameterBase_pos q t)))

theorem pk22SpectralCoefficient_pos (q t : Nat) :
    0 < pk22SpectralCoefficient q t := by
  unfold pk22SpectralCoefficient
  exact Nat.mul_pos (by norm_num) (Nat.pow_pos (pk22ParameterBase_pos q t))

theorem pk22_scale_bounds
    (q t x : Nat) (hx : pk22ScaleThreshold q t ≤ x) :
    0 < x ∧
    12 * 1 ≤ pk22DistanceCoefficient q t * x ^ 2 ∧
    12 * 1 + 6 ≤ pk22DistanceCoefficient q t * x ^ 2 ∧
    4 * pk22FaceCoefficient q t ≤
      1 * pk22DistanceCoefficient q t * x ^ 3 ∧
    2 * 1 + pk22SpectralCoefficient q t ≤
      pk22DistanceCoefficient q t * x ^ 2 ∧
    4 * pk22SpectralCoefficient q t ≤ 1 * x ∧
    16 * (128 * pk22LocalWidth q t + 6 * x + 1) *
        (pk22SpectralCoefficient q t) ^ 2 ≤
      pk22FaceCoefficient q t * x ∧
    pk22RectangleConstant q t <
      1 * pk22RowCoefficient q t * x := by
  have hEighteen : 18 ≤ x := by
    apply le_trans _ hx
    simp only [pk22ScaleThreshold]
    omega
  have hFaceScale : 4 * pk22FaceCoefficient q t ≤ x := by
    apply le_trans _ hx
    simp only [pk22ScaleThreshold]
    omega
  have hVerticalScale : pk22SpectralCoefficient q t + 2 ≤ x := by
    apply le_trans _ hx
    simp only [pk22ScaleThreshold]
    omega
  have hEdgeScale : 4 * pk22SpectralCoefficient q t ≤ x := by
    apply le_trans _ hx
    simp only [pk22ScaleThreshold]
    omega
  have hFaceConstant : 128 * pk22LocalWidth q t + 1 ≤ x := by
    apply le_trans _ hx
    simp only [pk22ScaleThreshold]
    omega
  have hRectangle : pk22RectangleConstant q t + 1 ≤ x := by
    apply le_trans _ hx
    simp only [pk22ScaleThreshold]
    omega
  have hxPositive : 0 < x := by omega
  have hDPositive := pk22DistanceCoefficient_pos q t
  have hCPositive := pk22SpectralCoefficient_pos q t
  have hSquare : x ≤ x ^ 2 := by
    simpa using Nat.pow_le_pow_right hxPositive (by norm_num : 1 ≤ 2)
  have hCube : x ≤ x ^ 3 := by
    simpa using Nat.pow_le_pow_right hxPositive (by norm_num : 1 ≤ 3)
  have hSmall : 12 * 1 ≤ pk22DistanceCoefficient q t * x ^ 2 := by
    calc
      12 * 1 ≤ x := by omega
      _ ≤ x ^ 2 := hSquare
      _ ≤ pk22DistanceCoefficient q t * x ^ 2 :=
        Nat.le_mul_of_pos_left _ hDPositive
  have hBudget : 12 * 1 + 6 ≤ pk22DistanceCoefficient q t * x ^ 2 := by
    calc
      12 * 1 + 6 ≤ x := hEighteen
      _ ≤ x ^ 2 := hSquare
      _ ≤ pk22DistanceCoefficient q t * x ^ 2 :=
        Nat.le_mul_of_pos_left _ hDPositive
  have hRectangleScale :
      4 * pk22FaceCoefficient q t ≤
        1 * pk22DistanceCoefficient q t * x ^ 3 := by
    calc
      4 * pk22FaceCoefficient q t ≤ x := hFaceScale
      _ ≤ x ^ 3 := hCube
      _ ≤ 1 * pk22DistanceCoefficient q t * x ^ 3 := by
        simp only [one_mul]
        exact Nat.le_mul_of_pos_left _ hDPositive
  have hVertical :
      2 * 1 + pk22SpectralCoefficient q t ≤
        pk22DistanceCoefficient q t * x ^ 2 := by
    calc
      2 * 1 + pk22SpectralCoefficient q t ≤ x := by
        simpa [Nat.add_comm] using hVerticalScale
      _ ≤ x ^ 2 := hSquare
      _ ≤ pk22DistanceCoefficient q t * x ^ 2 :=
        Nat.le_mul_of_pos_left _ hDPositive
  have hFace :
      16 * (128 * pk22LocalWidth q t + 6 * x + 1) *
          (pk22SpectralCoefficient q t) ^ 2 ≤
        pk22FaceCoefficient q t * x := by
    have hCore :
        2048 * pk22LocalWidth q t + 96 * x + 16 ≤ 112 * x := by
      omega
    unfold pk22FaceCoefficient
    calc
      16 * (128 * pk22LocalWidth q t + 6 * x + 1) *
          pk22SpectralCoefficient q t ^ 2 =
          (2048 * pk22LocalWidth q t + 96 * x + 16) *
            pk22SpectralCoefficient q t ^ 2 := by ring
      _ ≤ (112 * x) * pk22SpectralCoefficient q t ^ 2 :=
        Nat.mul_le_mul_right _ hCore
      _ = 112 * pk22SpectralCoefficient q t ^ 2 * x := by ring
  have hRowsPositive : 0 < pk22RowCoefficient q t := by
    unfold pk22RowCoefficient logarithmicLocalRows
    omega
  have hRectangleStrict : pk22RectangleConstant q t <
      1 * pk22RowCoefficient q t * x := by
    calc
      pk22RectangleConstant q t < x := by omega
      _ ≤ 1 * pk22RowCoefficient q t * x := by
        simp only [one_mul]
        exact Nat.le_mul_of_pos_left _ hRowsPositive
  exact ⟨hxPositive, hSmall, hBudget, hRectangleScale, hVertical,
    by simpa using hEdgeScale, hFace, hRectangleStrict⟩

theorem pk22_rankCoefficient_bound (q t : Nat) :
    36 * 1 * pk22FaceCoefficient q t ≤
      5 * (pk22DistanceCoefficient q t) ^ 2 := by
  unfold pk22FaceCoefficient pk22DistanceCoefficient
  calc
    36 * 1 * (112 * pk22SpectralCoefficient q t ^ 2) =
        4032 * pk22SpectralCoefficient q t ^ 2 := by ring
    _ ≤ 5120 * pk22SpectralCoefficient q t ^ 2 :=
      Nat.mul_le_mul_right _ (by norm_num)
    _ = 5 * (32 * pk22SpectralCoefficient q t) ^ 2 := by ring

/-- The Ramanujan scale `2 √p` of any compatible prime degree is bounded
by the concrete spectral schedule whenever its replication count lies below
`64 x⁶`.  This is the arithmetic bridge from the LPS eigenvalue theorem to
the deterministic PK22 local-code thresholds. -/
theorem two_mul_sqrt_compatibleDegreePrime_le_pk22SpectralScale
    (q t x : Nat)
    (a : CompatibleDegreePrime (pk22LocalWidth q t))
    (hUpper : a.blocks ≤ 64 * x ^ 6) :
    2 * Real.sqrt (a.p : ℝ) ≤
      ((pk22SpectralCoefficient q t * x ^ 3 : Nat) : ℝ) := by
  let U := pk22ParameterBase q t
  have hpDegree : a.p ≤ pk22LocalWidth q t * a.blocks := by
    rw [← a.degree_eq_block_mul]
    omega
  have hpBound : a.p ≤ (8 * U ^ 2 * x ^ 3) ^ 2 := by
    calc
      a.p ≤ pk22LocalWidth q t * a.blocks := hpDegree
      _ ≤ pk22LocalWidth q t * (64 * x ^ 6) := by gcongr
      _ = (8 * U ^ 2 * x ^ 3) ^ 2 := by
        unfold pk22LocalWidth
        dsimp [U]
        ring
  have hRoot : Real.sqrt (a.p : ℝ) ≤
      ((8 * U ^ 2 * x ^ 3 : Nat) : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · exact_mod_cast hpBound
  calc
    2 * Real.sqrt (a.p : ℝ) ≤
        2 * ((8 * U ^ 2 * x ^ 3 : Nat) : ℝ) :=
      mul_le_mul_of_nonneg_left hRoot (by norm_num)
    _ = ((pk22SpectralCoefficient q t * x ^ 3 : Nat) : ℝ) := by
      unfold pk22SpectralCoefficient
      dsimp [U]
      push_cast
      ring

end QEC.Coding.TannerLiftedProduct
