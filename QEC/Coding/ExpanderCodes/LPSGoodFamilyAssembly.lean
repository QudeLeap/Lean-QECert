import QEC.Coding.ExpanderCodes.CompatibleLocalPair
import QEC.Coding.ExpanderCodes.LPSCodeFamily
import QEC.Coding.ExpanderCodes.SmallSetExpansionSpectrum
import QEC.Coding.ExpanderCodes.LPSRamanujanTraceBridge

/-!
# Assembly of the PK22 family from the LPS spectral theorem

This module discharges the finite parameter arithmetic between the selected
local matrix pair and the semantic family theorem.  The concrete schedule
only needs a `4 √p` LPS spectral estimate, although the established
Ramanujan route supplies the stronger `2 √p` bound.  Both are conditional
inputs here; no unconditional LPS spectral estimate is asserted.
-/

namespace QEC.Coding.TannerLiftedProduct

noncomputable local instance pk22LPSFamilyQubitDecidableEq
    {p : ℕ} {R R' : Type} (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    DecidableEq
      (FamilyQubitIndex (W := Fin (p + 1)) (R := R) (R' := R')
        (G := LPSVertexGroup hp hp4) n) :=
  Classical.decEq _

private theorem log_two_mul_block_bound
    (A N x : ℕ) (hA : 0 < A) (hNPositive : 0 < N) (hx : 0 < x)
    (hN : N ≤ 64 * x ^ 6) :
    Nat.log 2 (2 * (A * N)) + 1 ≤ 128 * A + 6 * x + 1 := by
  have hAexp : A < 2 ^ A := A.lt_two_pow_self
  have hxexp : x < 2 ^ x := x.lt_two_pow_self
  have hxpow : x ^ 6 ≤ (2 ^ x) ^ 6 :=
    Nat.pow_le_pow_left hxexp.le 6
  have harg : 2 * (A * N) < 2 ^ (128 * A + 6 * x + 1) := by
    calc
      2 * (A * N) ≤ 2 * (A * (64 * x ^ 6)) := by gcongr
      _ = 128 * A * x ^ 6 := by ring
      _ < 128 * 2 ^ A * x ^ 6 := by gcongr
      _ ≤ 128 * 2 ^ A * (2 ^ x) ^ 6 := by gcongr
      _ = 2 ^ 7 * 2 ^ A * 2 ^ (6 * x) := by
        simp [pow_mul, Nat.mul_comm]
      _ = 2 ^ (7 + A + 6 * x) := by rw [← pow_add, ← pow_add]
      _ ≤ 2 ^ (128 * A + 6 * x + 1) := by
        apply Nat.pow_le_pow_right (by norm_num)
        omega
  have hlog : Nat.log 2 (2 * (A * N)) < 128 * A + 6 * x + 1 :=
    Nat.log_lt_of_lt_pow (by positivity) harg
  omega

private theorem le_twelve_mul_nthRoot_six_pow
    (N x : ℕ) (hx : x = Nat.nthRoot 6 N)
    (hxTwo : 2 ≤ x) :
    N ≤ 12 * x ^ 6 := by
  have hUpper : N < (x + 1) ^ 6 := by
    subst x
    exact Nat.lt_pow_nthRoot_add_one (by norm_num) N
  have hLinear : 2 * (x + 1) ≤ 3 * x := by omega
  have hPow := Nat.pow_le_pow_left hLinear 6
  have hScaled : 64 * (x + 1) ^ 6 ≤ 729 * x ^ 6 := by
    convert hPow using 1 <;> ring
  have hCrude : 64 * N < 768 * x ^ 6 := by
    calc
      64 * N < 64 * (x + 1) ^ 6 :=
        (Nat.mul_lt_mul_left (by norm_num : 0 < 64)).2 hUpper
      _ ≤ 729 * x ^ 6 := hScaled
      _ ≤ 768 * x ^ 6 := by
        apply Nat.mul_le_mul_right
        norm_num
  omega

/-- The same local-code schedule permits the weaker spectral input
`4 √p`, using the sharper sixth-root estimate `N ≤ 12 x⁶`. -/
private theorem four_sqrt_scale_add_one_le_schedule
    (q t x : ℕ)
    (a : CompatibleDegreePrime (pk22LocalWidth q t))
    (hx : 0 < x) (hUpper : a.blocks ≤ 12 * x ^ 6) :
    4 * Real.sqrt (a.p : ℝ) + 1 ≤
      ((pk22SpectralCoefficient q t * x ^ 3 : Nat) : ℝ) := by
  let U := pk22ParameterBase q t
  let X : ℕ := U ^ 2 * x ^ 3
  have hU : 0 < U := by simpa [U] using pk22ParameterBase_pos q t
  have hX : (1 : ℝ) ≤ X := by
    exact_mod_cast (show 1 ≤ X by
      dsimp [X]
      exact Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (Nat.mul_pos (Nat.pow_pos hU) (Nat.pow_pos hx))))
  have hpDegree : a.p ≤ pk22LocalWidth q t * a.blocks := by
    rw [← a.degree_eq_block_mul]
    omega
  have hpBound : a.p ≤ 12 * X ^ 2 := by
    calc
      a.p ≤ pk22LocalWidth q t * a.blocks := hpDegree
      _ ≤ pk22LocalWidth q t * (12 * x ^ 6) := by gcongr
      _ = 12 * X ^ 2 := by
        unfold pk22LocalWidth
        dsimp [U, X]
        ring
  have hpReal : (a.p : ℝ) ≤ 12 * (X : ℝ) ^ 2 := by
    exact_mod_cast hpBound
  have hRoot : Real.sqrt (a.p : ℝ) ≤ (7 / 2 : ℝ) * X := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have hCompare : 12 * (X : ℝ) ^ 2 ≤ ((7 / 2 : ℝ) * X) ^ 2 := by
        nlinarith [sq_nonneg (X : ℝ)]
      exact hpReal.trans hCompare
  calc
    4 * Real.sqrt (a.p : ℝ) + 1 ≤
        4 * ((7 / 2 : ℝ) * X) + 1 := by gcongr
    _ ≤ 16 * (X : ℝ) := by nlinarith
    _ = ((pk22SpectralCoefficient q t * x ^ 3 : Nat) : ℝ) := by
      unfold pk22SpectralCoefficient
      dsimp [U, X]
      push_cast
      ring

set_option maxHeartbeats 1200000 in
/-- All coding-theoretic and finite-parameter obligations of the PK22
construction, conditional on a `4 √p` LPS spectral estimate.  This is
strictly weaker than the optimal Ramanujan bound. -/
theorem exists_pk22LPSFamily_of_fourSqrtBound
    (F : Type) [Field F] [Fintype F]
    (targetRate : ℝ) (hRatePositive : 0 < targetRate)
    (hRate : targetRate < 1)
    (hSpectral : ∀ (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ),
      SmallSetExpansion.HasMeanZeroBilinearBound
        (rightCayleyGraph (lpsQuaternionFamilyLabel hp hp4 n))
        (4 * Real.sqrt (p : ℝ))) :
    ∃ (t : ℕ)
      (a : CompatibleDegreePrime (pk22LocalWidth (Nat.card F) t))
      (h h' : Matrix (PK22Check (Nat.card F) t a)
        (PK22Direction (Nat.card F) t a) F),
      let hCount := card_lpsQuaternionShell_eq_prime_add_one
        a.prime a.oneModFour
      QEC.QLDPC.IsAsymptoticallyGoodQLDPCFamily
          (lpsSemanticFamily a.prime a.oneModFour hCount h h') ∧
        QEC.QLDPC.HasEventualRateAtLeast
          (lpsSemanticFamily a.prime a.oneModFour hCount h h') targetRate := by
  let _ : DecidableEq F := Classical.decEq F
  obtain ⟨t, a, h, h', hScale, hLength, hRank, h'Rank,
      hDistance, hDistanceReverse, hProductExpand,
      hProductExpandReverse, hRatio, _hSpectralScale⟩ :=
    exists_pk22CompatibleLocalPair F targetRate hRate
  let q := Nat.card F
  let N := a.blocks
  let x := Nat.nthRoot 6 N
  let D := pk22DistanceCoefficient q t
  let C := pk22SpectralCoefficient q t
  let S := pk22FaceCoefficient q t
  let w := a.p + 1
  let d := D * N
  let m := x ^ 4
  let s := S * x ^ 7
  let spectral : ℝ := 4 * Real.sqrt (a.p : ℝ)
  have hAPositive : 0 < pk22LocalWidth q t := by
    unfold pk22LocalWidth
    exact Nat.pow_pos (pk22ParameterBase_pos q t)
  have hNPositive : 0 < N := by
    exact a.blocks_pos hAPositive
  have hScale' : pk22ScaleThreshold q t ≤ x := by
    simpa [q, N, x] using hScale
  obtain ⟨hxPositive, hSmall, hBudgetCoefficient, hRectangleCoefficient,
      hVerticalCoefficient, hEdgeCoefficient, hFaceCoefficient,
      _hRectangleThreshold⟩ := pk22_scale_bounds q t x hScale'
  have hxLower : x ^ 6 ≤ N := by
    dsimp [x]
    exact Nat.pow_nthRoot_le (by norm_num)
  have hxEighteen : 18 ≤ x := by
    apply le_trans _ hScale'
    simp only [pk22ScaleThreshold]
    omega
  have hxUpper : N ≤ 12 * x ^ 6 :=
    le_twelve_mul_nthRoot_six_pow N x rfl (by omega)
  have hLog : Nat.log 2 (2 * w) + 1 ≤
      128 * pk22LocalWidth q t + 6 * x + 1 := by
    rw [show w = pk22LocalWidth q t * N by
      simpa [q, w, N] using a.degree_eq_block_mul]
    exact log_two_mul_block_bound _ _ _ hAPositive hNPositive
      hxPositive (hxUpper.trans (by gcongr; norm_num))
  have hLambdaSchedule : spectral + 1 ≤ ((C * x ^ 3 : Nat) : ℝ) := by
    simpa [spectral, C] using
      four_sqrt_scale_add_one_le_schedule q t x a hxPositive hxUpper
  have hFour : 4 ≤ d := by
    have hxTwoSix : x ^ 2 ≤ x ^ 6 :=
      Nat.pow_le_pow_right hxPositive (by norm_num)
    calc
      4 ≤ 12 := by omega
      _ ≤ D * x ^ 2 := by simpa [D] using hSmall
      _ ≤ D * x ^ 6 := Nat.mul_le_mul_left D hxTwoSix
      _ ≤ D * N := Nat.mul_le_mul_left D hxLower
  have hDistanceScale : 4 * m ≤ d := by
    calc
      4 * x ^ 4 ≤ 12 * x ^ 4 :=
        Nat.mul_le_mul_right (x ^ 4) (by norm_num)
      _ ≤ (D * x ^ 2) * x ^ 4 := by
        exact Nat.mul_le_mul_right (x ^ 4) (by simpa [D] using hSmall)
      _ = D * x ^ 6 := by ring
      _ ≤ D * N := Nat.mul_le_mul_left D hxLower
  have hRectangleScale : 4 * s ≤ m * d := by
    calc
      4 * (S * x ^ 7) = (4 * S) * x ^ 7 := by ring
      _ ≤ (D * x ^ 3) * x ^ 7 := by
        exact Nat.mul_le_mul_right (x ^ 7)
          (by simpa [D, S] using hRectangleCoefficient)
      _ = x ^ 4 * (D * x ^ 6) := by ring
      _ ≤ x ^ 4 * (D * N) := by gcongr
  have hBudgetNat : 12 * m + 6 ≤ d := by
    have hxFourPositive : 0 < x ^ 4 := Nat.pow_pos hxPositive
    calc
      12 * x ^ 4 + 6 ≤ 18 * x ^ 4 := by omega
      _ ≤ (D * x ^ 2) * x ^ 4 := by
        exact Nat.mul_le_mul_right (x ^ 4)
          (by simpa [D] using hBudgetCoefficient)
      _ = D * x ^ 6 := by ring
      _ ≤ D * N := Nat.mul_le_mul_left D hxLower
  have hwPositive : (0 : ℝ) < w := by
    exact_mod_cast (show 0 < w by dsimp [w]; omega)
  have hBudget : 4 * (m : ℝ) + 2 ≤
      ((d : ℝ) / (3 * (w : ℝ))) * w := by
    have hBudgetReal : 12 * (m : ℝ) + 6 ≤ (d : ℝ) := by
      exact_mod_cast hBudgetNat
    have hCancel : ((d : ℝ) / (3 * (w : ℝ))) * w = (d : ℝ) / 3 := by
      field_simp
    rw [hCancel]
    linarith
  have hVerticalSchedule : 2 * m + C * x ^ 3 ≤ d := by
    have hxThreeFour : x ^ 3 ≤ x ^ 4 :=
      Nat.pow_le_pow_right hxPositive (by norm_num)
    calc
      2 * x ^ 4 + C * x ^ 3 ≤ 2 * x ^ 4 + C * x ^ 4 := by gcongr
      _ = (2 + C) * x ^ 4 := by ring
      _ ≤ (D * x ^ 2) * x ^ 4 := by
        exact Nat.mul_le_mul_right (x ^ 4)
          (by simpa [D, C] using hVerticalCoefficient)
      _ = D * x ^ 6 := by ring
      _ ≤ D * N := Nat.mul_le_mul_left D hxLower
  have hVertical : (2 * m : ℝ) + (spectral + 1) ≤ d := by
    have hScheduleReal : ((2 * m + C * x ^ 3 : Nat) : ℝ) ≤ d := by
      exact_mod_cast hVerticalSchedule
    push_cast at hScheduleReal
    push_cast at hLambdaSchedule
    nlinarith
  have hEdgeSchedule : 4 * (C * x ^ 3) ≤ m := by
    calc
      4 * (C * x ^ 3) = (4 * C) * x ^ 3 := by ring
      _ ≤ x * x ^ 3 := by
        exact Nat.mul_le_mul_right (x ^ 3)
          (by simpa [C] using hEdgeCoefficient)
      _ = x ^ 4 := by ring
  have hEdge : 2 * (2 * (spectral + 1)) ≤ (m : ℝ) := by
    have hScheduleReal : (4 * ((C * x ^ 3 : Nat) : ℝ)) ≤ (m : ℝ) := by
      exact_mod_cast hEdgeSchedule
    nlinarith
  have hFaceSchedule :
      16 * (Nat.log 2 (2 * w) + 1) * (C * x ^ 3) ^ 2 ≤ s := by
    calc
      16 * (Nat.log 2 (2 * w) + 1) * (C * x ^ 3) ^ 2 =
          (16 * (Nat.log 2 (2 * w) + 1) * C ^ 2) * x ^ 6 := by ring
      _ ≤ (16 * (128 * pk22LocalWidth q t + 6 * x + 1) * C ^ 2) *
          x ^ 6 := by gcongr
      _ ≤ (S * x) * x ^ 6 := by
        exact Nat.mul_le_mul_right (x ^ 6)
          (by simpa [C, S] using hFaceCoefficient)
      _ = S * x ^ 7 := by ring
  have hFace :
      2 * (((Nat.log 2 (2 * w) + 1 : Nat) : ℝ) *
        (8 * (spectral + 1) ^ 2)) ≤ (s : ℝ) := by
    have hScheduleReal :
        (16 * (Nat.log 2 (2 * w) + 1) * (C * x ^ 3) ^ 2 : ℕ) ≤ s :=
      hFaceSchedule
    have hScheduleReal' :
        (16 : ℝ) * (Nat.log 2 (2 * w) + 1) *
          (((C * x ^ 3 : Nat) : ℝ) ^ 2) ≤ (s : ℝ) := by
      exact_mod_cast hScheduleReal
    push_cast at hScheduleReal'
    have hLambdaNonnegative : 0 ≤ spectral + 1 := by
      dsimp [spectral]
      positivity
    have hSquare : (spectral + 1) ^ 2 ≤
        (((C * x ^ 3 : Nat) : ℝ) ^ 2) := by
      nlinarith [sq_nonneg
        (((C * x ^ 3 : Nat) : ℝ) - (spectral + 1))]
    push_cast at hSquare
    have hScaledSquare := mul_le_mul_of_nonneg_left hSquare
      (show (0 : ℝ) ≤ 16 * (Nat.log 2 (2 * w) + 1) by positivity)
    calc
      2 * (((Nat.log 2 (2 * w) + 1 : Nat) : ℝ) *
          (8 * (spectral + 1) ^ 2)) =
          16 * ((Nat.log 2 (2 * w) : ℝ) + 1) *
            (spectral + 1) ^ 2 := by
        norm_num only [Nat.cast_add, Nat.cast_one]
        ring
      _ ≤ 16 * ((Nat.log 2 (2 * w) : ℝ) + 1) *
          ((C : ℝ) * x ^ 3) ^ 2 := hScaledSquare
      _ ≤ (s : ℝ) := hScheduleReal'
  let hCount := card_lpsQuaternionShell_eq_prime_add_one
    a.prime a.oneModFour
  let label := lpsFinQuaternionFamilyLabel
    a.prime a.oneModFour hCount
  have hMixing : ∀ n,
      HasPartiteExpanderMixingBound
        (rightDoubleCoverGraph (label n)) (Fintype.card (Fin w)) spectral := by
    intro n
    have hBase : SmallSetExpansion.HasMeanZeroBilinearBound
        (rightCayleyGraph (label n)) spectral := by
      rw [rightCayleyGraph_lpsFinQuaternionFamilyLabel]
      exact hSpectral a.p a.prime a.oneModFour n
    simpa [label, spectral, w] using
      lpsFinRightDoubleCoverGraph_hasPartiteExpanderMixingBound_of_bilinearBound
        a.prime a.oneModFour hCount n spectral (by positivity) hBase
  have hGood : QEC.QLDPC.IsAsymptoticallyGoodQLDPCFamily
      (lpsSemanticFamily a.prime a.oneModFour hCount h h') := by
    have hProductExpand' : ProductExpansion.ProductExpanding h
        (ProductExpansion.generatorImageParityCheck h') s (2 * m)
        ((d : ℝ) / (3 * (w : ℝ))) := by
      simpa [q, N, x, D, S, d, m, s, w] using hProductExpand
    have hProductExpandReverse' : ProductExpansion.ProductExpanding h'
        (ProductExpansion.generatorImageParityCheck h) s (2 * m)
        ((d : ℝ) / (3 * (w : ℝ))) := by
      simpa [q, N, x, D, S, d, m, s, w] using hProductExpandReverse
    have hDistance' : ∀ c : Word F (Fin w),
        c ∈ (ProductExpansion.parityCheckCode h).carrier → c ≠ 0 →
        d ≤ HammingWeight c := by
      simpa [q, N, D, d, w] using hDistance
    have hDistanceReverse' : ∀ c : Word F (Fin w),
        c ∈ (ProductExpansion.parityCheckCode h').carrier → c ≠ 0 →
        d ≤ HammingWeight c := by
      simpa [q, N, D, d, w] using hDistanceReverse
    apply semanticFamily_isAsymptoticallyGood_of_partiteMixingBound
      label h h' (by simp) (lpsVertexGroup_card_cofinal a.prime a.oneModFour)
      hRank h'Rank
      d m s ((d : ℝ) / (3 * (w : ℝ)))
      hProductExpand' hProductExpandReverse' hDistance' hDistanceReverse'
      (by simpa [q, D, N, d] using hLength)
      (by
        have hpTwo := a.prime.two_le
        simp only [Fintype.card_fin]
        omega)
      hFour hDistanceScale hRectangleScale
      (by simpa [w] using hBudget)
      spectral (by dsimp [spectral]; positivity) hMixing hVertical hEdge
      (by simpa [w] using hFace)
      targetRate hRatePositive
    simpa [q, w] using hRatio
  have hRequestedRate : QEC.QLDPC.HasEventualRateAtLeast
      (lpsSemanticFamily a.prime a.oneModFour hCount h h') targetRate := by
    apply lpsSemanticFamily_hasEventualRateAtLeast_of_local_ratio
    simpa [q, w] using hRatio
  exact ⟨t, a, h, h', hGood, hRequestedRate⟩

/-- The original Ramanujan interface remains available: its optimal
`2 √p` estimate implies the weaker `4 √p` estimate used by the concrete
PK22 parameter schedule. -/
theorem exists_pk22LPSFamily_of_ramanujan
    (F : Type) [Field F] [Fintype F]
    (targetRate : ℝ) (hRatePositive : 0 < targetRate)
    (hRate : targetRate < 1)
    (hRamanujan : ∀ (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ),
      SmallSetExpansion.HasMeanZeroBilinearBound
        (rightCayleyGraph (lpsQuaternionFamilyLabel hp hp4 n))
        (2 * Real.sqrt (p : ℝ))) :
    ∃ (t : ℕ)
      (a : CompatibleDegreePrime (pk22LocalWidth (Nat.card F) t))
      (h h' : Matrix (PK22Check (Nat.card F) t a)
        (PK22Direction (Nat.card F) t a) F),
      let hCount := card_lpsQuaternionShell_eq_prime_add_one
        a.prime a.oneModFour
      QEC.QLDPC.IsAsymptoticallyGoodQLDPCFamily
          (lpsSemanticFamily a.prime a.oneModFour hCount h h') ∧
        QEC.QLDPC.HasEventualRateAtLeast
          (lpsSemanticFamily a.prime a.oneModFour hCount h h') targetRate := by
  apply exists_pk22LPSFamily_of_fourSqrtBound F targetRate hRatePositive hRate
  intro p hp hp4 n f g hf hg
  have hBound := hRamanujan p hp hp4 n f g hf hg
  have hFactor : 0 ≤ Real.sqrt
      ((∑ v, (f v) ^ 2) * ∑ v, (g v) ^ 2) := Real.sqrt_nonneg _
  have hScale : 2 * Real.sqrt (p : ℝ) ≤
      4 * Real.sqrt (p : ℝ) := by
    nlinarith [Real.sqrt_nonneg (p : ℝ)]
  exact hBound.trans (mul_le_mul_of_nonneg_right hScale hFactor)

/-- Operator-norm form of the terminal LPS assembly.  This is the interface
produced directly by a representation-theoretic proof of the LPS theorem;
the finite self-adjoint spectral bridge above converts it to the bilinear
estimate used by graph mixing. -/
theorem exists_pk22LPSFamily_of_ramanujanOperatorBound
    (F : Type) [Field F] [Fintype F]
    (targetRate : ℝ) (hRatePositive : 0 < targetRate)
    (hRate : targetRate < 1)
    (hRamanujan : ∀ (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ),
      SmallSetExpansion.HasMeanZeroOperatorBound
        (rightCayleyGraph (lpsQuaternionFamilyLabel hp hp4 n))
        (2 * Real.sqrt (p : ℝ))) :
    ∃ (t : ℕ)
      (a : CompatibleDegreePrime (pk22LocalWidth (Nat.card F) t))
      (h h' : Matrix (PK22Check (Nat.card F) t a)
        (PK22Direction (Nat.card F) t a) F),
      let hCount := card_lpsQuaternionShell_eq_prime_add_one
        a.prime a.oneModFour
      QEC.QLDPC.IsAsymptoticallyGoodQLDPCFamily
          (lpsSemanticFamily a.prime a.oneModFour hCount h h') ∧
        QEC.QLDPC.HasEventualRateAtLeast
          (lpsSemanticFamily a.prime a.oneModFour hCount h h') targetRate := by
  apply exists_pk22LPSFamily_of_ramanujan F targetRate hRatePositive hRate
  intro p hp hp4 n
  exact
    (SmallSetExpansion.hasMeanZeroBilinearBound_iff_operatorBound
      (lpsRightCayleyGraph_isSymmetric hp hp4 n)
      (lpsRightCayleyGraph_isRegular hp hp4 n)
      (by positivity)).2
        (hRamanujan p hp hp4 n)

/-- Complex operator-norm form of the terminal LPS assembly.  This removes
the final real/complex mismatch between the unitary regular representation
and the graph-expansion API. -/
theorem exists_pk22LPSFamily_of_ramanujanComplexOperatorBound
    (F : Type) [Field F] [Fintype F]
    (targetRate : ℝ) (hRatePositive : 0 < targetRate)
    (hRate : targetRate < 1)
    (hRamanujan : ∀ (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ),
      SmallSetExpansion.HasMeanZeroComplexOperatorBound
        (rightCayleyGraph (lpsQuaternionFamilyLabel hp hp4 n))
        (2 * Real.sqrt (p : ℝ))) :
    ∃ (t : ℕ)
      (a : CompatibleDegreePrime (pk22LocalWidth (Nat.card F) t))
      (h h' : Matrix (PK22Check (Nat.card F) t a)
        (PK22Direction (Nat.card F) t a) F),
      let hCount := card_lpsQuaternionShell_eq_prime_add_one
        a.prime a.oneModFour
      QEC.QLDPC.IsAsymptoticallyGoodQLDPCFamily
          (lpsSemanticFamily a.prime a.oneModFour hCount h h') ∧
        QEC.QLDPC.HasEventualRateAtLeast
          (lpsSemanticFamily a.prime a.oneModFour hCount h h') targetRate := by
  apply exists_pk22LPSFamily_of_ramanujanOperatorBound
    F targetRate hRatePositive hRate
  intro p hp hp4 n
  exact (hRamanujan p hp hp4 n).toReal

/-- Eigenvalue form of the terminal LPS assembly.  The constant mode is
removed explicitly, so the only remaining external input is the usual
Ramanujan bound on the centered LPS adjacency spectrum. -/
theorem exists_pk22LPSFamily_of_ramanujanCenteredEigenvalueBound
    (F : Type) [Field F] [Fintype F]
    (targetRate : ℝ) (hRatePositive : 0 < targetRate)
    (hRate : targetRate < 1)
    (hRamanujan : ∀ (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ)
      (i : Fin (Module.finrank ℂ
        (EuclideanSpace ℂ (LPSVertexGroup hp hp4 n)))),
      |(SmallSetExpansion.centeredAdjacencyEuclidean_isSymmetric
          (rightCayleyGraph (lpsQuaternionFamilyLabel hp hp4 n)) (p + 1)
          (lpsRightCayleyGraph_isSymmetric hp hp4 n)).eigenvalues rfl i| ≤
        2 * Real.sqrt (p : ℝ)) :
    ∃ (t : ℕ)
      (a : CompatibleDegreePrime (pk22LocalWidth (Nat.card F) t))
      (h h' : Matrix (PK22Check (Nat.card F) t a)
        (PK22Direction (Nat.card F) t a) F),
      let hCount := card_lpsQuaternionShell_eq_prime_add_one
        a.prime a.oneModFour
      QEC.QLDPC.IsAsymptoticallyGoodQLDPCFamily
          (lpsSemanticFamily a.prime a.oneModFour hCount h h') ∧
        QEC.QLDPC.HasEventualRateAtLeast
          (lpsSemanticFamily a.prime a.oneModFour hCount h h') targetRate := by
  apply exists_pk22LPSFamily_of_ramanujanComplexOperatorBound
    F targetRate hRatePositive hRate
  intro p hp hp4 n
  apply SmallSetExpansion.hasMeanZeroComplexOperatorBound_of_abs_meanZeroEigenvalues_le
      (rightCayleyGraph (lpsQuaternionFamilyLabel hp hp4 n)) (p + 1)
      (lpsRightCayleyGraph_isSymmetric hp hp4 n) (by positivity)
  exact hRamanujan p hp hp4 n

/-- Hecke-growth form of the terminal LPS assembly.  The finite-dimensional
trace endgame is fully discharged: it is enough to bound every even Hecke
evaluation at every exponential rate strictly above `√p`; the sharp
Ramanujan interval and hence the PK22 qLDPC family follow. -/
theorem exists_pk22LPSFamily_of_evenHeckeGrowth
    (F : Type) [Field F] [Fintype F]
    (targetRate : ℝ) (hRatePositive : 0 < targetRate)
    (hRate : targetRate < 1)
    (hHeckeGrowth : ∀ (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1)
      (n : ℕ)
      (i : Fin (Module.finrank ℂ
        (EuclideanSpace ℂ (LPSVertexGroup hp hp4 n))))
      (t : ℝ), Real.sqrt (p : ℝ) < t →
      (fun m : ℕ =>
        (lpsHeckePolynomial ℝ (p : ℝ) (2 * m)).eval
          ((SmallSetExpansion.centeredAdjacencyEuclidean_isSymmetric
            (rightCayleyGraph (lpsQuaternionFamilyLabel hp hp4 n)) (p + 1)
            (lpsRightCayleyGraph_isSymmetric hp hp4 n)).eigenvalues rfl i))
        =O[Filter.atTop] fun m : ℕ => t ^ (2 * m)) :
    ∃ (t : ℕ)
      (a : CompatibleDegreePrime (pk22LocalWidth (Nat.card F) t))
      (h h' : Matrix (PK22Check (Nat.card F) t a)
        (PK22Direction (Nat.card F) t a) F),
      let hCount := card_lpsQuaternionShell_eq_prime_add_one
        a.prime a.oneModFour
      QEC.QLDPC.IsAsymptoticallyGoodQLDPCFamily
          (lpsSemanticFamily a.prime a.oneModFour hCount h h') ∧
        QEC.QLDPC.HasEventualRateAtLeast
          (lpsSemanticFamily a.prime a.oneModFour hCount h h') targetRate := by
  apply exists_pk22LPSFamily_of_ramanujanCenteredEigenvalueBound
    F targetRate hRatePositive hRate
  intro p hp hp4 n i
  exact abs_le_two_mul_sqrt_of_lpsHeckePolynomial_even_isBigO
    (Nat.cast_pos.mpr hp.pos) _ (hHeckeGrowth p hp hp4 n i)

/-- Arithmetic form of the terminal LPS assembly.  All finite graph,
spectral, cancellation, and asymptotic steps are discharged; the sole
remaining source theorem is the optimal centered theta coefficient bound
for each residue-prime member of the explicit LPS family. -/
theorem exists_pk22LPSFamily_of_optimalCenteredThetaCoefficientBound
    (F : Type) [Field F] [Fintype F]
    (targetRate : ℝ) (hRatePositive : 0 < targetRate)
    (hRate : targetRate < 1)
    (hTheta : ∀ (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ),
      HasOptimalCenteredThetaCoefficientBound
        (lpsResiduePrimeSequence hp hp4 n)) :
    ∃ (t : ℕ)
      (a : CompatibleDegreePrime (pk22LocalWidth (Nat.card F) t))
      (h h' : Matrix (PK22Check (Nat.card F) t a)
        (PK22Direction (Nat.card F) t a) F),
      let hCount := card_lpsQuaternionShell_eq_prime_add_one
        a.prime a.oneModFour
      QEC.QLDPC.IsAsymptoticallyGoodQLDPCFamily
          (lpsSemanticFamily a.prime a.oneModFour hCount h h') ∧
        QEC.QLDPC.HasEventualRateAtLeast
          (lpsSemanticFamily a.prime a.oneModFour hCount h h') targetRate := by
  apply exists_pk22LPSFamily_of_evenHeckeGrowth
    F targetRate hRatePositive hRate
  intro p hp hp4 n i t ht
  obtain ⟨C, hC, hResidual⟩ := hTheta p hp hp4 n
  simpa [lpsQuaternionFamilyLabel, card_lpsGeneratorIndex,
    card_lpsQuaternionShell_eq_prime_add_one hp hp4] using
    (lpsHeckePolynomial_eigenvalue_isBigO_of_residual_bound
      (lpsResiduePrimeSequence hp hp4 n) C hC hResidual i t ht)

/-- Arithmetic `4√p` route to the terminal PK22 family.  The only
remaining input is the explicitly stated, relaxed centered theta
coefficient estimate; its proof is not supplied by the finite graph and
coding-theoretic lemmas. -/
theorem exists_pk22LPSFamily_of_fourSqrtCenteredThetaCoefficientBound
    (F : Type) [Field F] [Fintype F]
    (targetRate : ℝ) (hRatePositive : 0 < targetRate)
    (hRate : targetRate < 1)
    (hTheta : ∀ (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ),
      HasFourSqrtCenteredThetaCoefficientBound
        (lpsResiduePrimeSequence hp hp4 n)) :
    ∃ (t : ℕ)
      (a : CompatibleDegreePrime (pk22LocalWidth (Nat.card F) t))
      (h h' : Matrix (PK22Check (Nat.card F) t a)
        (PK22Direction (Nat.card F) t a) F),
      let hCount := card_lpsQuaternionShell_eq_prime_add_one
        a.prime a.oneModFour
      QEC.QLDPC.IsAsymptoticallyGoodQLDPCFamily
          (lpsSemanticFamily a.prime a.oneModFour hCount h h') ∧
        QEC.QLDPC.HasEventualRateAtLeast
          (lpsSemanticFamily a.prime a.oneModFour hCount h h') targetRate := by
  apply exists_pk22LPSFamily_of_fourSqrtBound
    F targetRate hRatePositive hRate
  intro p hp hp4 n
  apply (SmallSetExpansion.hasMeanZeroBilinearBound_iff_operatorBound
    (lpsRightCayleyGraph_isSymmetric hp hp4 n)
    (lpsRightCayleyGraph_isRegular hp hp4 n)
    (by positivity)).2
  apply SmallSetExpansion.HasMeanZeroComplexOperatorBound.toReal
  apply SmallSetExpansion.hasMeanZeroComplexOperatorBound_of_abs_meanZeroEigenvalues_le
    (rightCayleyGraph (lpsQuaternionFamilyLabel hp hp4 n)) (p + 1)
    (lpsRightCayleyGraph_isSymmetric hp hp4 n) (by positivity)
  intro i
  simpa [lpsQuaternionFamilyLabel, card_lpsGeneratorIndex,
    card_lpsQuaternionShell_eq_prime_add_one hp hp4] using
    (abs_lpsCenteredEigenvalue_le_four_mul_sqrt_of_theta_bound
      (lpsResiduePrimeSequence hp hp4 n) (hTheta p hp hp4 n) i)

end QEC.Coding.TannerLiftedProduct
