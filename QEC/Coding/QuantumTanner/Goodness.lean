import QEC.Coding.QuantumTanner.Core
import QEC.Coding.QuantumTanner.CayleyLink
import QEC.Coding.QLDPC.AsymptoticallyGoodFamily
import QEC.Coding.ChainComplex.Duality
import QEC.Coding.CSS.Distance
import QEC.Locality.CorrectableRegions.TwoCorrectableRegionsDimension
import QEC.Semantics.ErrorCorrection.FiniteMeasurementDistance
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.Projective
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The LZ22 Quantum Tanner goodness theorem

This module develops the proof closure for the positive-probability Quantum
Tanner construction of Leverrier--Zemor, *Quantum Tanner codes*
(arXiv:2202.13641v3).  The first results record the construction-owned
locality estimates: a local tensor check is extended only across one vertex
link, so its weight is at most the link size `|A| |B|`.
-/

noncomputable section

namespace QEC.Coding.QuantumTanner

open Classical
open scoped TensorProduct

universe u v

/-! ## Source parameters -/

/-- Binary entropy in the normalization used by LZ22's Gilbert--Varshamov
hypothesis. -/
def binaryEntropy (delta : ℝ) : ℝ :=
  -delta * Real.logb 2 delta - (1 - delta) * Real.logb 2 (1 - delta)

/-- The source's base-two entropy is Mathlib's binary entropy in nats divided
by `log 2`.  This lets the later Hamming-ball estimate use Mathlib's analytic
properties without changing the normalization in the public statement. -/
theorem binaryEntropy_eq_binEntropy_div_log_two (delta : ℝ) :
    binaryEntropy delta = Real.binEntropy delta / Real.log 2 := by
  simp only [binaryEntropy, Real.logb, Real.binEntropy, Real.log_inv]
  ring

theorem binaryEntropy_lt_iff_binEntropy_lt (delta rho : ℝ) :
    binaryEntropy delta < rho ↔
      Real.binEntropy delta < rho * Real.log 2 := by
  rw [binaryEntropy_eq_binEntropy_div_log_two]
  exact div_lt_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))

/-- The number of rows in each random local matrix is
`floor (rho * Delta)`. -/
def randomRowCount (rho : ℝ) (Delta : Nat) : Nat :=
  Nat.floor (rho * Delta)

/-- The integer number of random rows never exceeds the real row budget from
which it is obtained by flooring. -/
theorem randomRowCount_cast_le
    {rho : ℝ} {Delta : Nat} (hRhoNonnegative : 0 ≤ rho) :
    (randomRowCount rho Delta : ℝ) ≤ rho * Delta := by
  exact Nat.floor_le (mul_nonneg hRhoNonnegative (Nat.cast_nonneg Delta))

/-- Flooring loses strictly less than one row. -/
theorem randomRowCount_lt_add_one (rho : ℝ) (Delta : Nat) :
    rho * Delta < (randomRowCount rho Delta : ℝ) + 1 := by
  exact Nat.lt_floor_add_one (rho * Delta)

/-- At a nonempty degree and a source rate strictly below one, the random
matrix has fewer rows than columns.  In particular this supplies the
`r ≤ Delta` side condition used by the exact `Delta²` locality estimate. -/
theorem randomRowCount_lt_degree
    {rho : ℝ} {Delta : Nat} (hRhoNonnegative : 0 ≤ rho)
    (hRhoOne : rho < 1) (hDelta : 0 < Delta) :
    randomRowCount rho Delta < Delta := by
  have hDeltaReal : 0 < (Delta : ℝ) := by
    exact_mod_cast hDelta
  have hRowsReal : (randomRowCount rho Delta : ℝ) ≤ rho * Delta :=
    randomRowCount_cast_le hRhoNonnegative
  have hProduct : rho * (Delta : ℝ) < Delta := by
    nlinarith
  exact_mod_cast hRowsReal.trans_lt hProduct

/-- Degrees selected in LZ22 are `q + 1` for an odd prime power `q`.
The degree is fixed before the infinite square-complex family grows. -/
def IsLZ22AdmissibleDegree (Delta : Nat) : Prop :=
  ∃ q : Nat, IsPrimePow q ∧ Odd q ∧ Delta = q + 1

theorem lz22AdmissibleDegree_two_le
    {Delta : Nat} (hDelta : IsLZ22AdmissibleDegree Delta) : 2 ≤ Delta := by
  obtain ⟨q, hq, _hqOdd, rfl⟩ := hDelta
  have hqTwo : 2 ≤ q := hq.two_le
  omega

/-- Every exponent `epsilon` in the range used by LZ22 admits the auxiliary
robustness exponent `gamma` required in Theorem `thm:P-robust`.  The explicit
midpoint choice keeps the strict source inequalities visible for the later
probabilistic robustness argument. -/
theorem exists_robustnessExponent
    {epsilon : ℝ} (_hEpsilonPositive : 0 < epsilon)
    (hEpsilonHalf : epsilon < 1 / 2) :
    ∃ gamma : ℝ, 1 / 2 + epsilon < gamma ∧ gamma < 1 := by
  refine ⟨3 / 4 + epsilon / 2, ?_, ?_⟩
  · linarith
  · linarith

section RobustnessAsymptotics

open Filter

/-- The positive epsilon margin dominates the source's logarithmic loss,
using the actual little-o limit for log / rpow, not a numerical hypothesis. -/
private theorem exists_eventual_robustness_weight_log_margin
    (epsilon delta : ℝ) (hEpsilon : 0 < epsilon) (hDelta : 0 < delta) :
    ∃ threshold : Nat, ∀ degree : Nat, threshold ≤ degree →
      2 ≤ degree ∧
        (degree : ℝ) ^ ((3 : ℝ) / 2 - epsilon) * Real.logb 2 degree <
          delta / 2 * (degree : ℝ) ^ ((3 : ℝ) / 2) := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hSmall := (isLittleO_log_rpow_atTop hEpsilon).bound
    (show 0 < delta * Real.log 2 / 4 by positivity)
  have hNat := (tendsto_natCast_atTop_atTop :
    Tendsto (fun n : Nat => (n : ℝ)) atTop atTop).eventually hSmall
  obtain ⟨threshold, hThreshold⟩ := eventually_atTop.mp hNat
  refine ⟨max threshold 2, ?_⟩
  intro degree hDegree
  have hTwo : 2 ≤ degree := (Nat.le_max_right _ _).trans hDegree
  have hPos : 0 < (degree : ℝ) := by exact_mod_cast (by omega : 0 < degree)
  have hOne : (1 : ℝ) ≤ degree := by exact_mod_cast (by omega : 1 ≤ degree)
  have hBound : Real.log (degree : ℝ) ≤
      (delta * Real.log 2 / 4) * (degree : ℝ) ^ epsilon := by
    simpa only [Real.norm_of_nonneg (Real.log_nonneg hOne),
      Real.norm_of_nonneg (Real.rpow_nonneg hPos.le epsilon)] using
      hThreshold degree ((Nat.le_max_left _ _).trans hDegree)
  have hBase : Real.logb 2 (degree : ℝ) ≤
      (delta / 4) * (degree : ℝ) ^ epsilon := by
    rw [Real.logb, div_le_iff₀ hlog]
    nlinarith [hBound]
  have hPower : (degree : ℝ) ^ ((3 : ℝ) / 2 - epsilon) *
      (degree : ℝ) ^ epsilon = (degree : ℝ) ^ ((3 : ℝ) / 2) := by
    rw [← Real.rpow_add hPos]
    congr 1
    ring
  refine ⟨hTwo, ?_⟩
  calc
    (degree : ℝ) ^ ((3 : ℝ) / 2 - epsilon) * Real.logb 2 degree ≤
        (degree : ℝ) ^ ((3 : ℝ) / 2 - epsilon) *
          ((delta / 4) * (degree : ℝ) ^ epsilon) :=
      mul_le_mul_of_nonneg_left hBase (Real.rpow_nonneg hPos.le _)
    _ = delta / 4 * (degree : ℝ) ^ ((3 : ℝ) / 2) := by
      rw [mul_left_comm, hPower]
    _ < delta / 2 * (degree : ℝ) ^ ((3 : ℝ) / 2) :=
      mul_lt_mul_of_pos_right (by linarith) (Real.rpow_pos_of_pos hPos _)

/-- The eventual weight comparison used in the proof of LZ22's
`thm:P-robust` (distance-arxiv-v3.tex). The logarithm is positive at the
chosen degrees, so this is the source's actual divided weight bound. -/
private theorem exists_eventual_robustness_weight_source_bound
    (epsilon delta : ℝ) (hEpsilon : 0 < epsilon) (hDelta : 0 < delta) :
    ∃ threshold : Nat, ∀ degree : Nat, threshold ≤ degree →
      2 ≤ degree ∧
        (degree : ℝ) ^ ((3 : ℝ) / 2 - epsilon) <
          (delta / 2 * (degree : ℝ) ^ ((3 : ℝ) / 2)) /
            Real.logb 2 degree := by
  obtain ⟨threshold, hThreshold⟩ :=
    exists_eventual_robustness_weight_log_margin epsilon delta hEpsilon hDelta
  refine ⟨threshold, ?_⟩
  intro degree hDegree
  obtain ⟨hTwo, hMargin⟩ := hThreshold degree hDegree
  have hOne : (1 : ℝ) < degree := by exact_mod_cast (by omega : 1 < degree)
  have hLog : 0 < Real.logb 2 (degree : ℝ) := by
    rw [Real.logb]
    exact div_pos (Real.log_pos hOne) (Real.log_pos (by norm_num))
  exact ⟨hTwo, (lt_div_iff₀ hLog).mpr hMargin⟩

/-- The source's sublinear puncture count has an eventual linear distance
margin. This controls the actual integer floor, not only a real proxy. -/
private theorem exists_eventual_puncture_floor_linear_margin
    (gamma delta : ℝ) (hGamma : gamma < 1) (hDelta : 0 < delta) :
    ∃ threshold : Nat, ∀ degree : Nat, threshold ≤ degree →
      2 ≤ degree ∧
        (Nat.floor ((degree : ℝ) ^ gamma) : ℝ) < delta / 4 * degree := by
  have hSmall := (tendsto_rpow_neg_atTop (sub_pos.mpr hGamma)).eventually
    (gt_mem_nhds (show (0 : ℝ) < delta / 4 by positivity))
  have hNat := (tendsto_natCast_atTop_atTop :
    Tendsto (fun n : Nat => (n : ℝ)) atTop atTop).eventually hSmall
  obtain ⟨threshold, hThreshold⟩ := eventually_atTop.mp hNat
  refine ⟨max threshold 2, ?_⟩
  intro degree hDegree
  have hTwo : 2 ≤ degree := (Nat.le_max_right _ _).trans hDegree
  have hPos : 0 < (degree : ℝ) := by exact_mod_cast (by omega : 0 < degree)
  have hPower : (degree : ℝ) ^ gamma =
      (degree : ℝ) ^ (-(1 - gamma)) * degree := by
    calc
      (degree : ℝ) ^ gamma = (degree : ℝ) ^ (-(1 - gamma) + 1) := by
        congr 1
        ring
      _ = (degree : ℝ) ^ (-(1 - gamma)) * (degree : ℝ) ^ (1 : ℝ) :=
        Real.rpow_add hPos _ _
      _ = (degree : ℝ) ^ (-(1 - gamma)) * degree := by rw [Real.rpow_one]
  refine ⟨hTwo, ?_⟩
  calc
    (Nat.floor ((degree : ℝ) ^ gamma) : ℝ) ≤ (degree : ℝ) ^ gamma :=
      Nat.floor_le (Real.rpow_nonneg hPos.le _)
    _ = (degree : ℝ) ^ (-(1 - gamma)) * degree := hPower
    _ < delta / 4 * degree :=
      mul_lt_mul_of_pos_right
        (hThreshold degree ((Nat.le_max_left _ _).trans hDegree)) hPos

end RobustnessAsymptotics

section RobustnessIndexBounds

/-- A low-radius binomial sum has a polynomial bound even at degree zero. -/
private theorem partialChooseSum_le (n k : Nat) :
    (∑ i ∈ Finset.range (k + 1), Nat.choose n i) ≤ (k + 1) * (n + 1) ^ k := by
  calc
    _ ≤ ∑ i ∈ Finset.range (k + 1), (n + 1) ^ k := by
      apply Finset.sum_le_sum
      intro i hi
      have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact (Nat.choose_le_pow n i).trans
        ((pow_le_pow_left' (Nat.le_succ n) i).trans
          (pow_le_pow_right' (by omega : 1 ≤ n + 1) hik))
    _ = _ := by simp

/-- Count the source's matching puncture pairs by their common size. -/
private theorem matchingChooseSum_le (n q : Nat) :
    (∑ i ∈ Finset.range (q + 1), Nat.choose n i * Nat.choose n i) ≤
      (q + 1) * (n + 1) ^ (2 * q) := by
  calc
    _ ≤ ∑ i ∈ Finset.range (q + 1), (n + 1) ^ (2 * q) := by
      apply Finset.sum_le_sum
      intro i hi
      have hiq : i ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hc : Nat.choose n i ≤ (n + 1) ^ q :=
        (Nat.choose_le_pow n i).trans
          ((pow_le_pow_left' (Nat.le_succ n) i).trans
            (pow_le_pow_right' (by omega : 1 ≤ n + 1) hiq))
      simpa only [← pow_add, two_mul] using Nat.mul_le_mul hc hc
    _ = _ := by simp

/-- Bound the actual two-sided failure-index numerator without enumerating full words. -/
private theorem robustIndexNumerator_le (n q cutoff : Nat)
    (hq : q ≤ n) (hc : cutoff ≤ n) :
    2 * ((∑ i ∈ Finset.range (q + 1), Nat.choose n i * Nat.choose n i) *
      (2 ^ n * (∑ i ∈ Finset.range (cutoff + 1), Nat.choose n i) ^ n)) ≤
        2 ^ (n + 1) * (n + 1) ^ (2 * q + 1 + (cutoff + 1) * n) := by
  have hMatch : (∑ i ∈ Finset.range (q + 1), Nat.choose n i * Nat.choose n i) ≤
      (n + 1) ^ (2 * q + 1) := by
    calc
      _ ≤ (q + 1) * (n + 1) ^ (2 * q) := matchingChooseSum_le n q
      _ ≤ (n + 1) * (n + 1) ^ (2 * q) := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by rw [pow_succ]; ring
  have hBall : (∑ i ∈ Finset.range (cutoff + 1), Nat.choose n i) ≤
      (n + 1) ^ (cutoff + 1) := by
    calc
      _ ≤ (cutoff + 1) * (n + 1) ^ cutoff := partialChooseSum_le n cutoff
      _ ≤ (n + 1) * (n + 1) ^ cutoff := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by rw [pow_succ]; ring
  calc
    _ ≤ 2 * ((n + 1) ^ (2 * q + 1) *
        (2 ^ n * ((n + 1) ^ (cutoff + 1)) ^ n)) := by
      gcongr
    _ = _ := by simp only [pow_mul, pow_add, pow_succ]; ring

/-- Convert the polynomial index bound using a binary bit-length budget. -/
private theorem robustIndexNumerator_le_pow (n q cutoff t : Nat)
    (hq : q ≤ n) (hc : cutoff ≤ n) (ht : n + 1 ≤ 2 ^ t) :
    2 * ((∑ i ∈ Finset.range (q + 1), Nat.choose n i * Nat.choose n i) *
      (2 ^ n * (∑ i ∈ Finset.range (cutoff + 1), Nat.choose n i) ^ n)) ≤
      2 ^ (n + 1 + t * (2 * q + 1 + (cutoff + 1) * n)) := by
  calc
    _ ≤ 2 ^ (n + 1) * (n + 1) ^ (2 * q + 1 + (cutoff + 1) * n) :=
      robustIndexNumerator_le n q cutoff hq hc
    _ ≤ 2 ^ (n + 1) * (2 ^ t) ^ (2 * q + 1 + (cutoff + 1) * n) :=
      Nat.mul_le_mul_left _ (pow_le_pow_left' ht _)
    _ = _ := by rw [← pow_mul, ← pow_add]

/-- The canonical integer ceiling logarithm supplies that budget without a hypothesis. -/
private theorem robustIndexNumerator_le_pow_clog (n q cutoff : Nat)
    (hq : q ≤ n) (hc : cutoff ≤ n) :
    2 * ((∑ i ∈ Finset.range (q + 1), Nat.choose n i * Nat.choose n i) *
      (2 ^ n * (∑ i ∈ Finset.range (cutoff + 1), Nat.choose n i) ^ n)) ≤
      2 ^ (n + 1 + Nat.clog 2 (n + 1) * (2 * q + 1 + (cutoff + 1) * n)) := by
  exact robustIndexNumerator_le_pow n q cutoff (Nat.clog 2 (n + 1)) hq hc
    (Nat.le_pow_clog (by decide) (n + 1))

/-- Relate the actual integer bit-length budget to the source's real logarithm. -/
private theorem binaryCeilLog_lt_logb_add_two {n : Nat} (hn : 1 ≤ n) :
    (Nat.clog 2 (n + 1) : ℝ) < Real.logb 2 (n : ℝ) + 2 := by
  have hb : (1 : ℝ) < 2 := by norm_num
  have hnReal : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hCeil : (Nat.clog 2 (n + 1) : ℝ) < Real.logb 2 (n + 1 : Nat) + 1 := by
    rw [← Real.natCeil_logb_natCast]
    exact Nat.ceil_lt_add_one (Real.logb_nonneg hb (by exact_mod_cast (by omega : 1 ≤ n + 1)))
  have hLog : Real.logb 2 (n + 1 : Nat) ≤ Real.logb 2 (2 * (n : ℝ)) := by
    apply Real.logb_le_logb_of_le hb
    · positivity
    · push_cast
      have h : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
  have hProduct : Real.logb 2 (2 * (n : ℝ)) = 1 + Real.logb 2 (n : ℝ) := by
    rw [Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hnReal)]
    norm_num [Real.logb]
  linarith


open Filter

/-- A strict exponent gap absorbs the source logarithmic factor. -/
private theorem exists_eventual_rpow_logb_margin
    (a s c : ℝ) (hGap : a < s) (hc : 0 < c) :
    ∃ threshold : Nat, ∀ n : Nat, threshold ≤ n →
      2 ≤ n ∧ (n : ℝ) ^ a * Real.logb 2 n < c * (n : ℝ) ^ s := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hSmall := (isLittleO_log_rpow_atTop (sub_pos.mpr hGap)).bound
    (show 0 < c * Real.log 2 / 2 by positivity)
  have hNat := (tendsto_natCast_atTop_atTop :
    Tendsto (fun n : Nat => (n : ℝ)) atTop atTop).eventually hSmall
  obtain ⟨threshold, hThreshold⟩ := eventually_atTop.mp hNat
  refine ⟨max threshold 2, ?_⟩
  intro n hn
  have hTwo : 2 ≤ n := (Nat.le_max_right _ _).trans hn
  have hPos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hOne : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hBound : Real.log (n : ℝ) ≤
      (c * Real.log 2 / 2) * (n : ℝ) ^ (s - a) := by
    simpa only [Real.norm_of_nonneg (Real.log_nonneg hOne),
      Real.norm_of_nonneg (Real.rpow_nonneg hPos.le _)] using
      hThreshold n ((Nat.le_max_left _ _).trans hn)
  have hBase : Real.logb 2 (n : ℝ) ≤ (c / 2) * (n : ℝ) ^ (s - a) := by
    rw [Real.logb, div_le_iff₀ hlog]
    nlinarith [hBound]
  have hPower : (n : ℝ) ^ a * (n : ℝ) ^ (s - a) = (n : ℝ) ^ s := by
    rw [← Real.rpow_add hPos]
    congr 1
    ring
  refine ⟨hTwo, ?_⟩
  calc
    _ ≤ (n : ℝ) ^ a * ((c / 2) * (n : ℝ) ^ (s - a)) :=
      mul_le_mul_of_nonneg_left hBase (Real.rpow_nonneg hPos.le _)
    _ = c / 2 * (n : ℝ) ^ s := by rw [mul_left_comm, hPower]
    _ < c * (n : ℝ) ^ s :=
      mul_lt_mul_of_pos_right (by linarith) (Real.rpow_pos_of_pos hPos _)

/-- The actual integer matching/light-column index exponent is negligible
relative to degree^(3/2), with the source's floored puncture count and a
strictly sub-square-root light cutoff. No eventual numerical bound is assumed. -/
private theorem exists_eventual_robustIndexExponent_margin
    (alpha gamma c : ℝ) (hAlpha : alpha < 1 / 2) (hGamma : gamma < 1)
    (hc : 0 < c) :
    ∃ threshold : Nat, ∀ n : Nat, threshold ≤ n →
      2 ≤ n ∧
        ((n + 1 + Nat.clog 2 (n + 1) *
          (2 * Nat.floor ((n : ℝ) ^ gamma) + 1 +
            (Nat.floor ((n : ℝ) ^ alpha) + 1) * n) : Nat) : ℝ) <
          c * (n : ℝ) ^ ((3 : ℝ) / 2) := by
  obtain ⟨tOne, htOne⟩ := exists_eventual_rpow_logb_margin
    1 ((3 : ℝ) / 2) (c / 32) (by norm_num) (by positivity)
  obtain ⟨tAlpha, htAlpha⟩ := exists_eventual_rpow_logb_margin
    (alpha + 1) ((3 : ℝ) / 2) (c / 12) (by linarith) (by positivity)
  obtain ⟨tGamma, htGamma⟩ := exists_eventual_puncture_floor_linear_margin
    gamma 4 hGamma (by norm_num)
  refine ⟨max tOne (max tAlpha tGamma), ?_⟩
  intro n hn
  have hnOne := (Nat.le_max_left _ _).trans hn
  have hnAlpha := (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hn)
  have hnGamma := (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hn)
  obtain ⟨hTwo, hOneMargin⟩ := htOne n hnOne
  obtain ⟨_, hAlphaMargin⟩ := htAlpha n hnAlpha
  obtain ⟨_, hGammaMargin⟩ := htGamma n hnGamma
  have hPos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hOne : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hLog : 1 ≤ Real.logb 2 (n : ℝ) := by
    calc
      1 = Real.logb 2 (2 : ℝ) := (Real.logb_self_eq_one (by norm_num)).symm
      _ ≤ _ := Real.logb_le_logb_of_le (by norm_num) (by norm_num)
        (by exact_mod_cast hTwo)
  have hClog : (Nat.clog 2 (n + 1) : ℝ) ≤ 3 * Real.logb 2 (n : ℝ) := by
    have h := binaryCeilLog_lt_logb_add_two (by omega : 1 ≤ n)
    linarith
  have hFloor : (Nat.floor ((n : ℝ) ^ alpha) : ℝ) ≤ (n : ℝ) ^ alpha :=
    Nat.floor_le (Real.rpow_nonneg hPos.le _)
  have hQ : (Nat.floor ((n : ℝ) ^ gamma) : ℝ) ≤ n := by
    have h : (Nat.floor ((n : ℝ) ^ gamma) : ℝ) < n := by
      simpa only [show (4 : ℝ) / 4 = 1 by norm_num, one_mul] using hGammaMargin
    exact h.le
  have hPow : (n : ℝ) ^ alpha * n = (n : ℝ) ^ (alpha + 1) := by
    rw [Real.rpow_add hPos, Real.rpow_one]
  have hIndex :
      ((n + 1 + Nat.clog 2 (n + 1) *
        (2 * Nat.floor ((n : ℝ) ^ gamma) + 1 +
          (Nat.floor ((n : ℝ) ^ alpha) + 1) * n) : Nat) : ℝ) ≤
        2 * n + 12 * (n : ℝ) * Real.logb 2 n +
          3 * (n : ℝ) ^ (alpha + 1) * Real.logb 2 n := by
    push_cast
    calc
      _ ≤ 2 * (n : ℝ) + (3 * Real.logb 2 n) *
          (4 * n + (n : ℝ) ^ alpha * n) := by
        have hInner : 2 * (Nat.floor ((n : ℝ) ^ gamma) : ℝ) + 1 +
            ((Nat.floor ((n : ℝ) ^ alpha) : ℝ) + 1) * n ≤
              4 * n + (n : ℝ) ^ alpha * n := by nlinarith
        exact add_le_add (by linarith) (mul_le_mul hClog hInner
          (by positivity) (by positivity))
      _ = _ := by rw [hPow]; ring
  rw [Real.rpow_one] at hOneMargin
  have hNLog : (n : ℝ) ≤ n * Real.logb 2 n := by
    nlinarith
  have hPowerPos : 0 < (n : ℝ) ^ ((3 : ℝ) / 2) :=
    Real.rpow_pos_of_pos hPos _
  refine ⟨hTwo, ?_⟩
  nlinarith [hIndex, hOneMargin, hAlphaMargin]


/-- A fixed positive linear floor eventually retains three quarters of its
real budget. The threshold is chosen explicitly, without a limit hypothesis. -/
private theorem exists_eventual_floor_linear_lower
    (a : ℝ) (ha : 0 < a) :
    ∃ threshold : Nat, ∀ n : Nat, threshold ≤ n →
      2 ≤ n ∧ (3 * a / 4) * n ≤ (Nat.floor (a * n) : ℝ) := by
  refine ⟨max (Nat.ceil (4 / a)) 2, ?_⟩
  intro n hn
  have hTwo : 2 ≤ n := (Nat.le_max_right _ _).trans hn
  have hLarge : (4 : ℝ) / a ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_max_left _ _).trans hn)
  have hScale : (4 : ℝ) ≤ a * n := by
    have h := (div_le_iff₀ ha).mp hLarge
    nlinarith
  have hFloor := Nat.lt_floor_add_one (a * (n : ℝ))
  exact ⟨hTwo, by nlinarith⟩

/-- The actual integer division syndrome exponent has a square-root lower
bound once its independently stated row and deletion budgets are supplied. -/
private theorem syndromeExponent_lower_of_budgets
    (n p cutoff r q : Nat) (beta rho : ℝ) (hn : 0 < n)
    (hCutoff : 0 < cutoff) (hBeta : 0 < beta) (hRho : 0 < rho)
    (hP : beta / 2 * n ≤ (p : ℝ))
    (hK : (cutoff : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2))
    (hBudget : rho / 4 * n ≤ ((r - (q + p) : Nat) : ℝ)) :
    beta * rho / 8 * (n : ℝ) ^ ((3 : ℝ) / 2) ≤
      (((p / cutoff + 1) * (r - (q + p)) : Nat) : ℝ) := by
  have hPos : (0 : ℝ) < n := by exact_mod_cast hn
  have hSqrtPos : 0 < (n : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_pos_of_pos hPos _
  have hSquare : (n : ℝ) ^ ((1 : ℝ) / 2) *
      (n : ℝ) ^ ((1 : ℝ) / 2) = n := by
    rw [← Real.rpow_add hPos]
    norm_num
  have hDiv : p < (p / cutoff + 1) * cutoff := by
    calc
      p = p % cutoff + cutoff * (p / cutoff) := (Nat.mod_add_div _ _).symm
      _ < cutoff + cutoff * (p / cutoff) :=
        Nat.add_lt_add_right (Nat.mod_lt _ hCutoff) _
      _ = _ := by ring
  have hRank : beta / 2 * (n : ℝ) ^ ((1 : ℝ) / 2) ≤
      (p / cutoff + 1 : Nat) := by
    apply (mul_le_mul_iff_right₀ hSqrtPos).mp
    calc
      (n : ℝ) ^ ((1 : ℝ) / 2) *
          (beta / 2 * (n : ℝ) ^ ((1 : ℝ) / 2)) = beta / 2 * n := by
        rw [mul_left_comm, hSquare]
      _ ≤ (p : ℝ) := hP
      _ ≤ (p / cutoff + 1 : Nat) * (cutoff : ℝ) := by
        exact_mod_cast hDiv.le
      _ ≤ (n : ℝ) ^ ((1 : ℝ) / 2) * (p / cutoff + 1 : Nat) := by
        nlinarith [mul_le_mul_of_nonneg_left hK
          (Nat.cast_nonneg (p / cutoff + 1) : (0 : ℝ) ≤ (p / cutoff + 1 : Nat))]
  have hPower : (n : ℝ) ^ ((1 : ℝ) / 2) * n =
      (n : ℝ) ^ ((3 : ℝ) / 2) := by
    calc
      _ = (n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = (n : ℝ) ^ (((1 : ℝ) / 2) + 1) := (Real.rpow_add hPos _ _).symm
      _ = _ := by congr 1; norm_num
  calc
    beta * rho / 8 * (n : ℝ) ^ ((3 : ℝ) / 2) =
        (beta / 2 * (n : ℝ) ^ ((1 : ℝ) / 2)) * (rho / 4 * n) := by
      rw [← hPower]
      ring
    _ ≤ (p / cutoff + 1 : Nat) * ((r - (q + p) : Nat) : ℝ) :=
      mul_le_mul hRank hBudget (by positivity) (by positivity)
    _ = _ := by push_cast; rfl

/-- Genuine floored source-style choices give a syndrome exponent at least a
positive constant times degree^(3/2). This is not a joint goodness estimate. -/
private theorem exists_eventual_floored_syndromeExponent_lower
    (alpha gamma beta rho : ℝ) (hAlphaNonneg : 0 ≤ alpha)
    (hAlpha : alpha ≤ 1 / 2) (hGamma : gamma < 1)
    (hBeta : 0 < beta) (hRho : 0 < rho) (hBetaRho : beta ≤ rho / 4) :
    ∃ threshold : Nat, ∀ n : Nat, threshold ≤ n →
      2 ≤ n ∧ 0 < Nat.floor ((n : ℝ) ^ alpha) ∧
        Nat.floor ((n : ℝ) ^ gamma) + Nat.floor (beta * n) ≤ Nat.floor (rho * n) ∧
        beta * rho / 8 * (n : ℝ) ^ ((3 : ℝ) / 2) ≤
          (((Nat.floor (beta * n) / Nat.floor ((n : ℝ) ^ alpha) + 1) *
            (Nat.floor (rho * n) -
              (Nat.floor ((n : ℝ) ^ gamma) + Nat.floor (beta * n))) : Nat) : ℝ) := by
  obtain ⟨tP, htP⟩ := exists_eventual_floor_linear_lower beta hBeta
  obtain ⟨tR, htR⟩ := exists_eventual_floor_linear_lower rho hRho
  obtain ⟨tQ, htQ⟩ := exists_eventual_puncture_floor_linear_margin gamma rho hGamma hRho
  refine ⟨max tP (max tR tQ), ?_⟩
  intro n hn
  obtain ⟨hTwo, hPLower⟩ := htP n ((Nat.le_max_left _ _).trans hn)
  obtain ⟨_, hRLower⟩ := htR n
    ((Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hn))
  obtain ⟨_, hQUpper⟩ := htQ n
    ((Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hn))
  have hPos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hOne : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hPUpper : (Nat.floor (beta * n) : ℝ) ≤ rho / 4 * n := by
    have hFloor := Nat.floor_le (show 0 ≤ beta * (n : ℝ) by positivity)
    nlinarith
  have hQPReal : (Nat.floor ((n : ℝ) ^ gamma) : ℝ) +
      (Nat.floor (beta * n) : ℝ) ≤ (Nat.floor (rho * n) : ℝ) := by
    nlinarith
  have hQP : Nat.floor ((n : ℝ) ^ gamma) + Nat.floor (beta * n) ≤
      Nat.floor (rho * n) := by exact_mod_cast hQPReal
  have hBudget : rho / 4 * n ≤
      ((Nat.floor (rho * n) -
        (Nat.floor ((n : ℝ) ^ gamma) + Nat.floor (beta * n)) : Nat) : ℝ) := by
    rw [Nat.cast_sub hQP, Nat.cast_add]
    nlinarith
  have hKPos : 0 < Nat.floor ((n : ℝ) ^ alpha) := by
    have h := Nat.floor_mono (Real.one_le_rpow hOne hAlphaNonneg)
    have hOneFloor : 1 ≤ Nat.floor ((n : ℝ) ^ alpha) := by
      simpa only [Nat.floor_one] using h
    omega
  have hK : (Nat.floor ((n : ℝ) ^ alpha) : ℝ) ≤
      (n : ℝ) ^ ((1 : ℝ) / 2) :=
    (Nat.floor_le (Real.rpow_nonneg hPos.le _)).trans
      (Real.rpow_le_rpow_of_exponent_le hOne hAlpha)
  refine ⟨hTwo, hKPos, hQP, ?_⟩
  exact syndromeExponent_lower_of_budgets n _ _ _ _ beta rho
    (by omega) hKPos hBeta hRho (by nlinarith) hK hBudget

/-- Actual floored parameter choices leave two full binary exponent bits
between the matching/light-column numerator and the syndrome denominator.
This is still separate from the five-family rank/distance union estimate. -/
private theorem exists_eventual_robustIndexExponent_add_two_le_syndrome
    (alpha gamma beta rho : ℝ) (hAlphaNonneg : 0 ≤ alpha)
    (hAlpha : alpha < 1 / 2) (hGamma : gamma < 1)
    (hBeta : 0 < beta) (hRho : 0 < rho) (hBetaRho : beta ≤ rho / 4) :
    ∃ threshold : Nat, ∀ n : Nat, threshold ≤ n →
      n + 1 + Nat.clog 2 (n + 1) *
          (2 * Nat.floor ((n : ℝ) ^ gamma) + 1 +
            (Nat.floor ((n : ℝ) ^ alpha) + 1) * n) + 2 ≤
        (Nat.floor (beta * n) / Nat.floor ((n : ℝ) ^ alpha) + 1) *
          (Nat.floor (rho * n) -
            (Nat.floor ((n : ℝ) ^ gamma) + Nat.floor (beta * n))) := by
  obtain ⟨tI, htI⟩ := exists_eventual_robustIndexExponent_margin
    alpha gamma (beta * rho / 16) hAlpha hGamma (by positivity)
  obtain ⟨tD, htD⟩ := exists_eventual_floored_syndromeExponent_lower
    alpha gamma beta rho hAlphaNonneg hAlpha.le hGamma hBeta hRho hBetaRho
  refine ⟨max tI (max tD (Nat.ceil (32 / (beta * rho)))), ?_⟩
  intro n hn
  obtain ⟨hTwo, hIndex⟩ := htI n ((Nat.le_max_left _ _).trans hn)
  obtain ⟨_, _, _, hDen⟩ := htD n
    ((Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hn))
  have hLarge : (32 : ℝ) / (beta * rho) ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast
      (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hn))
  have hOne : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hPowN : (n : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) / 2) := by
    calc
      (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hOne (by norm_num)
  have hMarginTwo : (2 : ℝ) ≤ beta * rho / 16 * (n : ℝ) ^ ((3 : ℝ) / 2) := by
    have hScale := (div_le_iff₀ (show 0 < beta * rho by positivity)).mp hLarge
    have hMul := mul_le_mul_of_nonneg_left hPowN
      (show 0 ≤ beta * rho / 16 by positivity)
    nlinarith
  have hReal :
      ((n + 1 + Nat.clog 2 (n + 1) *
        (2 * Nat.floor ((n : ℝ) ^ gamma) + 1 +
          (Nat.floor ((n : ℝ) ^ alpha) + 1) * n) : Nat) : ℝ) + 2 ≤
        (((Nat.floor (beta * n) / Nat.floor ((n : ℝ) ^ alpha) + 1) *
          (Nat.floor (rho * n) -
            (Nat.floor ((n : ℝ) ^ gamma) + Nat.floor (beta * n))) : Nat) : ℝ) := by
    nlinarith [hIndex, hDen, hMarginTwo]
  exact_mod_cast hReal


/-- A strictly smaller real power eventually fits any positive multiple of
a larger power; the threshold comes from the negative-rpow limit. -/
private theorem exists_eventual_rpow_margin
    (a b c : ℝ) (hab : a < b) (hc : 0 < c) :
    ∃ threshold : Nat, ∀ n : Nat, threshold ≤ n →
      2 ≤ n ∧ (n : ℝ) ^ a < c * (n : ℝ) ^ b := by
  have hSmall := (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).eventually
    (gt_mem_nhds hc)
  have hNat := (tendsto_natCast_atTop_atTop :
    Tendsto (fun n : Nat => (n : ℝ)) atTop atTop).eventually hSmall
  obtain ⟨t, ht⟩ := eventually_atTop.mp hNat
  refine ⟨max t 2, ?_⟩
  intro n hn
  have hTwo : 2 ≤ n := (Nat.le_max_right _ _).trans hn
  have hPos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  refine ⟨hTwo, ?_⟩
  calc
    (n : ℝ) ^ a = (n : ℝ) ^ (-(b - a)) * (n : ℝ) ^ b := by
      rw [← Real.rpow_add hPos]
      congr 1
      ring
    _ < c * (n : ℝ) ^ b := mul_lt_mul_of_pos_right
      (ht n ((Nat.le_max_left _ _).trans hn)) (Real.rpow_pos_of_pos hPos _)

/-- For the source weight exponent and a cutoff exponent halfway through its
epsilon margin, the actual floored heavy-column budget eventually holds. -/
private theorem exists_eventual_floored_robustness_weight_budget
    (epsilon beta : ℝ) (hEpsilon : 0 < epsilon) (hBeta : 0 < beta) :
    ∃ threshold : Nat, ∀ n : Nat, threshold ≤ n →
      Nat.floor ((n : ℝ) ^ ((3 : ℝ) / 2 - epsilon)) <
        (Nat.floor (beta * n) + 1) *
          (Nat.floor ((n : ℝ) ^ ((1 : ℝ) / 2 - epsilon / 2)) + 1) := by
  obtain ⟨t, ht⟩ := exists_eventual_rpow_margin
    ((3 : ℝ) / 2 - epsilon) (1 + ((1 : ℝ) / 2 - epsilon / 2))
    beta (by linarith) hBeta
  refine ⟨t, ?_⟩
  intro n hn
  obtain ⟨hTwo, hSmall⟩ := ht n hn
  have hPos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hP : beta * n < (Nat.floor (beta * n) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hK : (n : ℝ) ^ ((1 : ℝ) / 2 - epsilon / 2) <
      (Nat.floor ((n : ℝ) ^ ((1 : ℝ) / 2 - epsilon / 2)) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hPower : (n : ℝ) ^ (1 + ((1 : ℝ) / 2 - epsilon / 2)) =
      (n : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 2 - epsilon / 2) := by
    rw [Real.rpow_add hPos, Real.rpow_one]
  have hProduct : beta * (n : ℝ) ^ (1 + ((1 : ℝ) / 2 - epsilon / 2)) <
      ((Nat.floor (beta * n) : ℝ) + 1) *
        ((Nat.floor ((n : ℝ) ^ ((1 : ℝ) / 2 - epsilon / 2)) : ℝ) + 1) := by
    rw [hPower, ← mul_assoc]
    exact mul_lt_mul hP hK.le (by positivity) (by positivity)
  have hFloor := Nat.floor_le
    (Real.rpow_nonneg hPos.le ((3 : ℝ) / 2 - epsilon))
  have hResult : (Nat.floor ((n : ℝ) ^ ((3 : ℝ) / 2 - epsilon)) : ℝ) <
      ((Nat.floor (beta * n) : ℝ) + 1) *
        ((Nat.floor ((n : ℝ) ^ ((1 : ℝ) / 2 - epsilon / 2)) : ℝ) + 1) :=
    hFloor.trans_lt (hSmall.trans hProduct)
  exact_mod_cast hResult

/-- Actual linear distance and sublinear puncture/cutoff floors supply both
normalized distance budgets and the ambient index bounds. These are genuine
eventual parameter inequalities, not assumptions of the final count bound. -/
private theorem exists_eventual_floored_robustness_distance_budgets
    (alpha gamma beta delta : ℝ) (hAlphaNonneg : 0 ≤ alpha)
    (hAlpha : alpha < 1) (hGamma : gamma < 1)
    (hBeta : 0 < beta) (hDelta : 0 < delta) (hBetaDelta : beta ≤ delta / 8) :
    ∃ threshold : Nat, ∀ n : Nat, threshold ≤ n →
      let p := Nat.floor (beta * n)
      let cutoff := Nat.floor ((n : ℝ) ^ alpha)
      let q := Nat.floor ((n : ℝ) ^ gamma)
      let distance := Nat.floor (delta * n)
      0 < cutoff ∧ q ≤ n ∧ cutoff ≤ n ∧
        (p / cutoff + 1) * cutoff < distance - q ∧
        2 * p ≤ distance - q := by
  obtain ⟨tD, htD⟩ := exists_eventual_floor_linear_lower delta hDelta
  obtain ⟨tK, htK⟩ := exists_eventual_puncture_floor_linear_margin
    alpha (min delta 4) hAlpha (lt_min hDelta (by norm_num))
  obtain ⟨tQ, htQ⟩ := exists_eventual_puncture_floor_linear_margin
    gamma (min delta 4) hGamma (lt_min hDelta (by norm_num))
  refine ⟨max tD (max tK tQ), ?_⟩
  intro n hn
  dsimp only
  obtain ⟨hTwo, hD⟩ := htD n ((Nat.le_max_left _ _).trans hn)
  obtain ⟨_, hK⟩ := htK n
    ((Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hn))
  obtain ⟨_, hQ⟩ := htQ n
    ((Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hn))
  have hPos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hOne : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hKPos : 0 < Nat.floor ((n : ℝ) ^ alpha) := by
    have h := Nat.floor_mono (Real.one_le_rpow hOne hAlphaNonneg)
    have hOneFloor : 1 ≤ Nat.floor ((n : ℝ) ^ alpha) := by
      simpa only [Nat.floor_one] using h
    omega
  have hP := Nat.floor_le (show 0 ≤ beta * (n : ℝ) by positivity)
  have hMinD := min_le_left delta (4 : ℝ)
  have hMinFour := min_le_right delta (4 : ℝ)
  have hKDistance : (Nat.floor ((n : ℝ) ^ alpha) : ℝ) < delta / 4 * n := by
    nlinarith
  have hQDistance : (Nat.floor ((n : ℝ) ^ gamma) : ℝ) < delta / 4 * n := by
    nlinarith
  have hKN : Nat.floor ((n : ℝ) ^ alpha) ≤ n := by
    have h : (Nat.floor ((n : ℝ) ^ alpha) : ℝ) ≤ n := by nlinarith
    exact_mod_cast h
  have hQN : Nat.floor ((n : ℝ) ^ gamma) ≤ n := by
    have h : (Nat.floor ((n : ℝ) ^ gamma) : ℝ) ≤ n := by nlinarith
    exact_mod_cast h
  have hQD : Nat.floor ((n : ℝ) ^ gamma) ≤ Nat.floor (delta * n) := by
    have h : (Nat.floor ((n : ℝ) ^ gamma) : ℝ) ≤
        (Nat.floor (delta * n) : ℝ) := by nlinarith
    exact_mod_cast h
  have hRankLe : (Nat.floor (beta * n) / Nat.floor ((n : ℝ) ^ alpha) + 1) *
      Nat.floor ((n : ℝ) ^ alpha) ≤
        Nat.floor (beta * n) + Nat.floor ((n : ℝ) ^ alpha) := by
    have h := Nat.div_mul_le_self (Nat.floor (beta * n))
      (Nat.floor ((n : ℝ) ^ alpha))
    nlinarith
  have hRankReal :
      (((Nat.floor (beta * n) / Nat.floor ((n : ℝ) ^ alpha) + 1) *
        Nat.floor ((n : ℝ) ^ alpha) : Nat) : ℝ) <
      ((Nat.floor (delta * n) - Nat.floor ((n : ℝ) ^ gamma) : Nat) : ℝ) := by
    rw [Nat.cast_sub hQD]
    have hRankCast : (((Nat.floor (beta * n) / Nat.floor ((n : ℝ) ^ alpha) + 1) *
        Nat.floor ((n : ℝ) ^ alpha) : Nat) : ℝ) ≤
        (Nat.floor (beta * n) : ℝ) + (Nat.floor ((n : ℝ) ^ alpha) : ℝ) := by
      exact_mod_cast hRankLe
    nlinarith
  have hCoverReal : (2 : ℝ) * (Nat.floor (beta * n) : ℝ) ≤
      ((Nat.floor (delta * n) - Nat.floor ((n : ℝ) ^ gamma) : Nat) : ℝ) := by
    rw [Nat.cast_sub hQD]
    nlinarith
  exact ⟨hKPos, hQN, hKN, by exact_mod_cast hRankReal,
    by exact_mod_cast hCoverReal⟩

/-- A concrete positive deletion budget, chosen from distance and rate,
makes the source epsilon cutoff satisfy all finite robustness prerequisites.
The syndrome/index estimate and the joint union margin remain separate. -/
private theorem exists_eventual_source_robustness_floor_budgets
    (epsilon gamma delta rho : ℝ) (hEpsilon : 0 < epsilon)
    (hEpsilonUpper : epsilon < 1 / 2) (hGamma : gamma < 1)
    (hDelta : 0 < delta) (hRho : 0 < rho) :
    ∃ threshold : Nat, ∀ n : Nat, threshold ≤ n →
      let beta := min delta rho / 8
      let p := Nat.floor (beta * n)
      let cutoff := Nat.floor ((n : ℝ) ^ ((1 : ℝ) / 2 - epsilon / 2))
      let q := Nat.floor ((n : ℝ) ^ gamma)
      let distance := Nat.floor (delta * n)
      let w := Nat.floor ((n : ℝ) ^ ((3 : ℝ) / 2 - epsilon))
      0 < cutoff ∧ q ≤ n ∧ cutoff ≤ n ∧
        w < (p + 1) * (cutoff + 1) ∧
        (p / cutoff + 1) * cutoff < distance - q ∧
        2 * p ≤ distance - q := by
  have hBeta : 0 < min delta rho / 8 := by
    exact div_pos (lt_min hDelta hRho) (by norm_num)
  have hBetaDelta : min delta rho / 8 ≤ delta / 8 :=
    div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  obtain ⟨tW, htW⟩ := exists_eventual_floored_robustness_weight_budget
    epsilon (min delta rho / 8) hEpsilon hBeta
  obtain ⟨tD, htD⟩ := exists_eventual_floored_robustness_distance_budgets
    ((1 : ℝ) / 2 - epsilon / 2) gamma (min delta rho / 8) delta
    (by linarith) (by linarith) hGamma hBeta hDelta hBetaDelta
  refine ⟨max tW tD, ?_⟩
  intro n hn
  obtain ⟨hK, hQ, hKN, hRank, hCover⟩ :=
    htD n ((Nat.le_max_right _ _).trans hn)
  exact ⟨hK, hQ, hKN, htW n ((Nat.le_max_left _ _).trans hn), hRank, hCover⟩

end RobustnessIndexBounds


/-! ## Positive probability and the exact successful local-code event -/

/-- For a finite uniform experiment, positive probability is exactly positive
cardinality of the event.  This keeps the source's probability quantifier
visible instead of replacing it by a deterministic local-code choice. -/
def HasPositiveUniformProbability {Ω : Type u} [Fintype Ω]
    (event : Ω → Prop) [DecidablePred event] : Prop :=
  0 < (eventFinset event).card

theorem hasPositiveUniformProbability_iff_exists
    {Ω : Type u} [Fintype Ω] (event : Ω → Prop) [DecidablePred event] :
    HasPositiveUniformProbability event ↔ ∃ sample, event sample := by
  unfold HasPositiveUniformProbability
  constructor
  · intro hpositive
    obtain ⟨sample, hsample⟩ := Finset.card_pos.mp hpositive
    exact ⟨sample, (Finset.mem_filter.mp hsample).2⟩
  · rintro ⟨sample, hsample⟩
    apply Finset.card_pos.mpr
    exact ⟨sample, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsample⟩⟩

/-- Finite union bound in the form needed by the LZ22 random local-code
argument.  If every failed sample lies in one of a finite family of bad events
and the sum of their cardinalities is smaller than the sample space, then the
simultaneous good event has positive uniform probability. -/
theorem hasPositiveUniformProbability_of_union_bound
    {Ω : Type u} {J : Type v} [Fintype Ω] [Fintype J]
    (good : Ω → Prop) [DecidablePred good]
    (bad : J → Ω → Prop) [∀ j, DecidablePred (bad j)]
    (hcover : ∀ sample, ¬ good sample → ∃ j, bad j sample)
    (hcount : ∑ j, (eventFinset (bad j)).card < Fintype.card Ω) :
    HasPositiveUniformProbability good := by
  rw [hasPositiveUniformProbability_iff_exists]
  by_contra hnoGood
  push_neg at hnoGood
  let badUnion : Finset Ω :=
    Finset.univ.biUnion fun j => eventFinset (bad j)
  have hsubset : (Finset.univ : Finset Ω) ⊆ badUnion := by
    intro sample _hsample
    obtain ⟨j, hj⟩ := hcover sample (hnoGood sample)
    exact Finset.mem_biUnion.mpr
      ⟨j, Finset.mem_univ j, (mem_eventFinset (bad j) sample).mpr hj⟩
  have hspaceLeUnion : Fintype.card Ω ≤ badUnion.card := by
    simpa only [Finset.card_univ] using Finset.card_le_card hsubset
  have hUnionLeSum : badUnion.card ≤
      ∑ j, (eventFinset (bad j)).card := by
    exact Finset.card_biUnion_le
  exact (not_lt_of_ge (hspaceLeUnion.trans hUnionLeSum)) hcount

/-! ## Tensor-code realization -/

/-- The canonical coordinate equivalence from a tensor product of two word
spaces to the word space on their Cartesian product. -/
private noncomputable def tensorWordEquiv
    (F : Type u) (A B : Type v) [Field F] [Fintype B] :
    (Word F A ⊗[F] Word F B) ≃ₗ[F] Word F (A × B) := by
  letI := Classical.decEq B
  exact (TensorProduct.piScalarRight F F (Word F A) B).trans
    ((LinearEquiv.curry F F B A).symm.trans
      (LinearEquiv.funCongrLeft F F (Equiv.prodComm A B)))

@[simp]
private theorem tensorWordEquiv_tmul_apply
    {F : Type u} {A B : Type v} [Field F] [Fintype B]
    (x : Word F A) (y : Word F B) (a : A) (b : B) :
    tensorWordEquiv F A B (x ⊗ₜ[F] y) (a, b) = x a * y b := by
  letI := Classical.decEq B
  simp [tensorWordEquiv, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul, mul_comm]

/-- Pure tensors of local-code words satisfy both the column and row
constraints, hence give a canonical map into the product code. -/
private noncomputable def tensorCodeTensorMap
    {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]
    (CA : LinearCode F A) (CB : LinearCode F B) :
    CA.carrier ⊗[F] CB.carrier →ₗ[F] (tensorCode CA CB).carrier :=
  LinearMap.codRestrict (tensorCode CA CB).carrier
    ((tensorWordEquiv F A B).toLinearMap.comp
      (TensorProduct.mapIncl CA.carrier CB.carrier)) fun z => by
        induction z with
        | zero => simpa only [map_zero] using (tensorCode CA CB).carrier.zero_mem
        | add x y hx hy =>
            simpa only [map_add] using (tensorCode CA CB).carrier.add_mem hx hy
        | tmul x y =>
            simp only [LinearMap.comp_apply, TensorProduct.map_tmul,
              Submodule.coe_subtype]
            rw [mem_tensorCode]
            constructor
            · intro b
              change (fun a => tensorWordEquiv F A B
                ((x : Word F A) ⊗ₜ[F] (y : Word F B)) (a, b)) ∈ CA.carrier
              simp only [tensorWordEquiv_tmul_apply]
              rw [show (fun a => (x : Word F A) a * (y : Word F B) b) =
                  (y.1 b) • (x : Word F A) by
                funext a
                simp only [Pi.smul_apply, smul_eq_mul, mul_comm]]
              exact CA.carrier.smul_mem (y.1 b) x.2
            · intro a
              change (fun b => tensorWordEquiv F A B
                ((x : Word F A) ⊗ₜ[F] (y : Word F B)) (a, b)) ∈ CB.carrier
              simp only [tensorWordEquiv_tmul_apply]
              rw [show (fun b => (x : Word F A) a * (y : Word F B) b) =
                  (x.1 a) • (y : Word F B) by
                funext b
                simp only [Pi.smul_apply, smul_eq_mul]]
              exact CB.carrier.smul_mem (x.1 a) y.2

/-- The canonical tensor-to-product-code map is injective. -/
private theorem tensorCodeTensorMap_injective
    {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]
    (CA : LinearCode F A) (CB : LinearCode F B) :
    Function.Injective (tensorCodeTensorMap CA CB) := by
  intro x y hxy
  have hxy' := congrArg Subtype.val hxy
  change tensorWordEquiv F A B
      (TensorProduct.mapIncl CA.carrier CB.carrier x) =
    tensorWordEquiv F A B
      (TensorProduct.mapIncl CA.carrier CB.carrier y) at hxy'
  apply TensorProduct.map_injective_of_flat_flat
      CA.carrier.subtype CB.carrier.subtype
      CA.carrier.injective_subtype CB.carrier.injective_subtype
  exact (tensorWordEquiv F A B).injective hxy'

/-- Under the coordinate equivalence, tensoring a subspace inclusion on the
right records the included word in each column. -/
private theorem tensorWordEquiv_rTensor_apply
    {F : Type u} {A B : Type v} [Field F] [Fintype A] [Fintype B]
    (C : Submodule F (Word F A)) (z : C ⊗[F] Word F B) (a : A) (b : B) :
    tensorWordEquiv F A B (C.subtype.rTensor (Word F B) z) (a, b) =
      ((TensorProduct.piScalarRight F F C B z b : C) : Word F A) a := by
  induction z with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul x y =>
      simp [LinearMap.rTensor_tmul, tensorWordEquiv_tmul_apply,
        TensorProduct.piScalarRight_apply,
        TensorProduct.piScalarRightHom_tmul, Pi.smul_apply,
        smul_eq_mul, mul_comm]

/-- Under the coordinate equivalence, tensoring a subspace inclusion on the
left records the included word in each row. -/
private theorem tensorWordEquiv_lTensor_apply
    {F : Type u} {A B : Type v} [Field F] [Fintype A] [Fintype B]
    (C : Submodule F (Word F B)) (z : Word F A ⊗[F] C) (a : A) (b : B) :
    tensorWordEquiv F A B (C.subtype.lTensor (Word F A) z) (a, b) =
      ((TensorProduct.piScalarRight F F C A
          (TensorProduct.comm F (Word F A) C z) a : C) : Word F B) b := by
  induction z with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul x y =>
      simp [LinearMap.lTensor_tmul, tensorWordEquiv_tmul_apply,
        TensorProduct.piScalarRight_apply,
        TensorProduct.piScalarRightHom_tmul, Pi.smul_apply,
        smul_eq_mul]

/-- Column constraints are exactly membership in the range obtained by
tensoring the column-code inclusion with the full row word space. -/
private theorem mem_range_rTensor_of_columns
    {F : Type u} {A B : Type v} [Field F] [Fintype A] [Fintype B]
    (C : Submodule F (Word F A)) (x : Word F (A × B))
    (hx : ∀ b, columnRestriction b x ∈ C) :
    (tensorWordEquiv F A B).symm x ∈
      LinearMap.range (C.subtype.rTensor (Word F B)) := by
  let columns : B → C := fun b ↦ ⟨columnRestriction b x, hx b⟩
  let z := (TensorProduct.piScalarRight F F C B).symm columns
  refine ⟨z, ?_⟩
  apply (tensorWordEquiv F A B).injective
  ext ab
  rcases ab with ⟨a, b⟩
  rw [tensorWordEquiv_rTensor_apply]
  simp only [z, LinearEquiv.apply_symm_apply]
  rfl

/-- Row constraints are exactly membership in the range obtained by
tensoring the row-code inclusion with the full column word space. -/
private theorem mem_range_lTensor_of_rows
    {F : Type u} {A B : Type v} [Field F] [Fintype A] [Fintype B]
    (C : Submodule F (Word F B)) (x : Word F (A × B))
    (hx : ∀ a, rowRestriction a x ∈ C) :
    (tensorWordEquiv F A B).symm x ∈
      LinearMap.range (C.subtype.lTensor (Word F A)) := by
  let rows : A → C := fun a ↦ ⟨rowRestriction a x, hx a⟩
  let z₀ := (TensorProduct.piScalarRight F F C A).symm rows
  let z := TensorProduct.comm F C (Word F A) z₀
  refine ⟨z, ?_⟩
  apply (tensorWordEquiv F A B).injective
  ext ab
  rcases ab with ⟨a, b⟩
  rw [tensorWordEquiv_lTensor_apply]
  simp only [z, z₀, TensorProduct.comm_comm,
    LinearEquiv.apply_symm_apply]
  rfl

/-- Every word satisfying both product-code constraints comes from a tensor
of local-code words.  Right exactness is used only after the two coordinate
range descriptions above have converted the constraints into tensor ranges. -/
private theorem tensorCodeTensorMap_surjective
    {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]
    (CA : LinearCode F A) (CB : LinearCode F B) :
    Function.Surjective (tensorCodeTensorMap CA CB) := by
  intro x
  have hx := (mem_tensorCode CA CB x.1).mp x.2
  let xt := (tensorWordEquiv F A B).symm x.1
  have hColumn : xt ∈ LinearMap.range
      (CA.carrier.subtype.rTensor (Word F B)) :=
    mem_range_rTensor_of_columns CA.carrier x.1 hx.1
  have hRow : xt ∈ LinearMap.range
      (CB.carrier.subtype.lTensor (Word F A)) :=
    mem_range_lTensor_of_rows CB.carrier x.1 hx.2
  obtain ⟨y, hy⟩ := hColumn
  have hRowZero : CB.carrier.mkQ.lTensor (Word F A) xt = 0 := by
    rw [← LinearMap.mem_ker, lTensor_mkQ]
    exact hRow
  have hMapZero : TensorProduct.map CA.carrier.subtype CB.carrier.mkQ y = 0 := by
    rw [← LinearMap.lTensor_comp_rTensor]
    simp only [LinearMap.comp_apply, hy, hRowZero]
  have hQuotientZero : CB.carrier.mkQ.lTensor CA.carrier y = 0 := by
    apply Module.Flat.rTensor_preserves_injective_linearMap
        CA.carrier.subtype CA.carrier.injective_subtype
    simp only [map_zero]
    rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor]
    exact hMapZero
  have hyRange : y ∈ LinearMap.range
      (CB.carrier.subtype.lTensor CA.carrier) := by
    rw [← lTensor_mkQ]
    exact LinearMap.mem_ker.mpr hQuotientZero
  obtain ⟨z, hz⟩ := hyRange
  refine ⟨z, Subtype.ext ?_⟩
  change tensorWordEquiv F A B
      (TensorProduct.mapIncl CA.carrier CB.carrier z) = x.1
  have hambient : TensorProduct.mapIncl CA.carrier CB.carrier z = xt := by
    change TensorProduct.map CA.carrier.subtype CB.carrier.subtype z = xt
    rw [← LinearMap.rTensor_comp_lTensor]
    simp only [LinearMap.comp_apply, hz, hy]
  rw [hambient]
  exact (tensorWordEquiv F A B).apply_symm_apply x.1

/-- Induction on actual tensor-code words through pure local-code products.
This bridges the row-and-column definition to its tensor-product realization. -/
theorem tensorCode_induction
    {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]
    (CA : LinearCode F A) (CB : LinearCode F B)
    {P : Word F (A × B) → Prop}
    (hZero : P 0)
    (hAdd : ∀ x y, P x → P y → P (x + y))
    (hPure : ∀ a, a ∈ CA.carrier → ∀ b, b ∈ CB.carrier →
      P (fun ab => a ab.1 * b ab.2))
    (x : Word F (A × B)) (hx : x ∈ (tensorCode CA CB).carrier) : P x := by
  obtain ⟨t, ht⟩ := tensorCodeTensorMap_surjective CA CB ⟨x, hx⟩
  have h (z : CA.carrier ⊗[F] CB.carrier) : P ((tensorCodeTensorMap CA CB z).val) := by
    induction z with
    | zero => simpa using hZero
    | add a b ha hb =>
        simpa only [map_add, Submodule.coe_add] using hAdd _ _ ha hb
    | tmul a b =>
        simp only [tensorCodeTensorMap, LinearMap.codRestrict_apply,
          LinearMap.comp_apply, TensorProduct.map_tmul, Submodule.coe_subtype,
          LinearMap.toFun_eq_coe]
        have hWord : tensorWordEquiv F A B
            ((a : Word F A) ⊗ₜ[F] (b : Word F B)) =
            (fun ab => a.1 ab.1 * b.1 ab.2) := by
          ext ab
          exact tensorWordEquiv_tmul_apply a.1 b.1 ab.1 ab.2
        change P ((tensorWordEquiv F A B) ((a : Word F A) ⊗ₜ[F] (b : Word F B)))
        rw [hWord]
        exact hPure a.1 a.2 b.1 b.2
  simpa only [ht] using h t

/-- The row-and-column presentation of the product code is canonically
linearly equivalent to the tensor product of the two local codes. -/
private noncomputable def tensorCodeTensorEquiv
    {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]
    (CA : LinearCode F A) (CB : LinearCode F B) :
    CA.carrier ⊗[F] CB.carrier ≃ₗ[F] (tensorCode CA CB).carrier :=
  LinearEquiv.ofBijective (tensorCodeTensorMap CA CB)
    ⟨tensorCodeTensorMap_injective CA CB,
      tensorCodeTensorMap_surjective CA CB⟩

/-- The concrete row-and-column tensor code has the expected product
dimension. -/
theorem Dimension_tensorCode
    {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]
    (CA : LinearCode F A) (CB : LinearCode F B) :
    Dimension (tensorCode CA CB) = Dimension CA * Dimension CB := by
  rw [Dimension_eq_finrank_carrier,
    ← (tensorCodeTensorEquiv CA CB).finrank_eq,
    Module.finrank_tensorProduct,
    ← Dimension_eq_finrank_carrier,
    ← Dimension_eq_finrank_carrier]

/-- A lower bound on every nonzero word of a concrete linear code. -/
def HasMinimumDistanceAtLeast
    {F : Type u} {ι : Type v} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] (code : LinearCode F ι) (distance : Nat) : Prop :=
  ∀ word, word ∈ code.carrier → word ≠ 0 → distance ≤ HammingWeight word

/-! ### Exact binary Hamming-ball counts -/

/-- The unique nonzero element of the binary field is one. -/
private theorem binary_eq_one_of_ne_zero
    (x : ZMod 2) (hx : x ≠ 0) : x = 1 := by
  apply ZMod.val_injective 2
  rw [ZMod.val_one]
  have hxval : x.val ≠ 0 := (ZMod.val_eq_zero x).not.mpr hx
  have hxlt : x.val < 2 := x.val_lt
  omega

/-- The binary indicator word of a finite coordinate set. -/
private def binarySupportWord
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (support : Finset ι) : Word (ZMod 2) ι :=
  fun i => if i ∈ support then 1 else 0

@[simp]
private theorem hammingSupport_binarySupportWord
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (support : Finset ι) :
    hammingSupport (binarySupportWord support) = support := by
  ext i
  simp [hammingSupport, binarySupportWord]

@[simp]
private theorem binarySupportWord_hammingSupport
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (word : Word (ZMod 2) ι) :
    binarySupportWord (hammingSupport word) = word := by
  funext i
  by_cases hi : word i = 0
  · simp [binarySupportWord, hammingSupport, hi]
  · rw [binary_eq_one_of_ne_zero (word i) hi]
    simp only [binarySupportWord, hammingSupport, Finset.mem_filter,
      Finset.mem_univ, true_and, if_pos hi]

/-- Binary words whose Hamming weight is strictly below `distance`. -/
abbrev BinaryLowWeightWords
    (ι : Type v) [Fintype ι] (distance : Nat) :=
  {word : Word (ZMod 2) ι // HammingWeight word < distance}

/-- A low binary word is uniquely represented by its support and its support
cardinality. -/
private def binaryLowWeightWordsEquivSupports
    (ι : Type v) [Fintype ι] [DecidableEq ι] (distance : Nat) :
    BinaryLowWeightWords ι distance ≃
      Σ weight : Fin distance, Set.powersetCard ι weight.1 where
  toFun word :=
    ⟨⟨HammingWeight word.1, word.2⟩,
      ⟨hammingSupport word.1,
        HammingWeight_eq_card_hammingSupport word.1⟩⟩
  invFun support :=
    ⟨binarySupportWord support.2.1, by
      simp [HammingWeight_eq_card_hammingSupport, support.1.2]⟩
  left_inv word := by
    apply Subtype.ext
    exact binarySupportWord_hammingSupport word.1
  right_inv support := by
    apply Sigma.subtype_ext
    · simp [HammingWeight_eq_card_hammingSupport]
    · exact hammingSupport_binarySupportWord support.2.1

/-- The exact cardinality of a binary Hamming ball of strict radius
`distance` on an arbitrary finite coordinate type. -/
theorem card_binaryLowWeightWords
    (ι : Type v) [Fintype ι] [DecidableEq ι] (distance : Nat) :
    Fintype.card (BinaryLowWeightWords ι distance) =
      ∑ weight ∈ Finset.range distance,
        Nat.choose (Fintype.card ι) weight := by
  rw [Fintype.card_congr
      (binaryLowWeightWordsEquivSupports ι distance),
    Fintype.card_sigma, Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro weight hweight
  rw [dif_pos (Finset.mem_range.mp hweight)]
  rw [Fintype.card_eq_nat_card, Set.powersetCard.card,
    Nat.card_eq_fintype_card]

/-- A binomial term below the midpoint has at least the weight of the
midpoint-truncated term when evaluated in the binomial expansion at
`m + (n - m)`.  This is the finite counting step behind the entropy bound;
it uses no asymptotic approximation. -/
private theorem lowWeight_binomialWeight_ge
    {n m k : Nat} (hk : k ≤ m) (hhalf : 2 * m ≤ n) :
    m ^ m * (n - m) ^ (n - m) ≤
      m ^ k * (n - m) ^ (n - k) := by
  have hm : m = k + (m - k) := by omega
  have hnk : n - k = (n - m) + (m - k) := by omega
  have hpow : m ^ (m - k) ≤ (n - m) ^ (m - k) :=
    pow_le_pow_left₀ (Nat.zero_le _) (by omega) _
  have hsplitM : m ^ m = m ^ k * m ^ (m - k) := by
    calc
      m ^ m = m ^ (k + (m - k)) := congrArg (m ^ ·) hm
      _ = m ^ k * m ^ (m - k) := pow_add _ _ _
  have hsplitN :
      (n - m) ^ (n - k) =
        (n - m) ^ (n - m) * (n - m) ^ (m - k) := by
    calc
      (n - m) ^ (n - k) =
          (n - m) ^ ((n - m) + (m - k)) :=
            congrArg ((n - m) ^ ·) hnk
      _ = (n - m) ^ (n - m) * (n - m) ^ (m - k) := pow_add _ _ _
  calc
    m ^ m * (n - m) ^ (n - m) =
        (m ^ k * m ^ (m - k)) * (n - m) ^ (n - m) := by
          rw [hsplitM]
    _ ≤ (m ^ k * (n - m) ^ (m - k)) * (n - m) ^ (n - m) :=
      Nat.mul_le_mul_right _
        (Nat.mul_le_mul_left _ hpow)
    _ = m ^ k * (n - m) ^ (n - k) := by
          rw [hsplitN]
          ring

/-- The binary Hamming-ball volume times its entropy denominator is at most
the full binomial expansion.  In particular this reduces the analytic GV
estimate to a comparison of the explicit powers
`n ^ n` and `m ^ m * (n-m) ^ (n-m)`. -/
private theorem binaryHammingBall_mul_entropyDenominator_le
    (n m : Nat) (hhalf : 2 * m ≤ n) :
    (∑ k ∈ Finset.range (m + 1), Nat.choose n k) *
        (m ^ m * (n - m) ^ (n - m)) ≤ n ^ n := by
  have hmle : m ≤ n := by omega
  have hrange : Finset.range (m + 1) ⊆ Finset.range (n + 1) := by
    exact Finset.range_mono (by omega)
  calc
    (∑ k ∈ Finset.range (m + 1), Nat.choose n k) *
        (m ^ m * (n - m) ^ (n - m)) =
        ∑ k ∈ Finset.range (m + 1),
          Nat.choose n k * (m ^ m * (n - m) ^ (n - m)) := by
          rw [Finset.sum_mul]
    _ ≤ ∑ k ∈ Finset.range (m + 1),
          Nat.choose n k * (m ^ k * (n - m) ^ (n - k)) := by
          apply Finset.sum_le_sum
          intro k hk
          exact Nat.mul_le_mul_left _
            (lowWeight_binomialWeight_ge
              (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hhalf)
    _ ≤ ∑ k ∈ Finset.range (n + 1),
          Nat.choose n k * (m ^ k * (n - m) ^ (n - k)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hrange
          intro k _ _
          exact Nat.zero_le _
    _ = (m + (n - m)) ^ n := by
          rw [add_pow]
          apply Finset.sum_congr rfl
          intro k _
          simp only [Nat.cast_id]
          ac_rfl
    _ = n ^ n := by
          congr 1
          omega

/-- The elementary logarithmic expression from the weighted binomial
expansion is exactly `n` times binary entropy at the relative radius
`m/n`. -/
private theorem natEntropyRay_eq_mul_binEntropy
    (n m : Nat) (hm : 0 < m) (hmn : m < n) :
    (n : ℝ) * Real.log n -
        (m : ℝ) * Real.log m -
        ((n - m : Nat) : ℝ) *
          Real.log ((n - m : Nat) : ℝ) =
      (n : ℝ) * Real.binEntropy ((m : ℝ) / n) := by
  have hn : 0 < n := lt_trans hm hmn
  have hsub : 0 < n - m := Nat.sub_pos_of_lt hmn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hsubR : ((n - m : Nat) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hsub
  have hcastSub : ((n - m : Nat) : ℝ) = (n : ℝ) - m := by
    rw [Nat.cast_sub hmn.le]
  have hone_sub : 1 - (m : ℝ) / n =
      ((n - m : Nat) : ℝ) / n := by
    rw [hcastSub]
    field_simp [hnR]
  have hinv_m : ((m : ℝ) / n)⁻¹ = (n : ℝ) / m := by
    field_simp [hnR, hmR]
  have hinv_sub : (((n - m : Nat) : ℝ) / n)⁻¹ =
      (n : ℝ) / (n - m) := by
    rw [hcastSub]
    field_simp [hnR, hsubR]
  have hlog_sub : Real.log ((n : ℝ) / ((n : ℝ) - m)) =
      Real.log (n : ℝ) - Real.log ((n - m : Nat) : ℝ) := by
    rw [← hcastSub]
    exact Real.log_div hnR hsubR
  unfold Real.binEntropy
  rw [hinv_m, hone_sub, hinv_sub,
    Real.log_div hnR hmR, hlog_sub]
  rw [hcastSub]
  field_simp [hnR]
  ring

/-- The strict-radius binary Hamming ball is at most the exponential of
binary entropy at its normalized integral radius.  The proof uses the exact
finite weighted-binomial inequality above, rather than an asymptotic
approximation or an assumed GV estimate. -/
private theorem binaryHammingBall_le_exp_binEntropy
    (n m : Nat) (hm : 0 < m) (hhalf : 2 * m ≤ n) :
    (((∑ k ∈ Finset.range (m + 1), Nat.choose n k) : Nat) : ℝ) ≤
      Real.exp ((n : ℝ) * Real.binEntropy ((m : ℝ) / n)) := by
  let volume := ∑ k ∈ Finset.range (m + 1), Nat.choose n k
  have hmn : m < n := by omega
  have hsub : 0 < n - m := Nat.sub_pos_of_lt hmn
  have hvolumeOne : 1 ≤ volume := by
    have h := Finset.single_le_sum
      (fun k _ => Nat.zero_le (Nat.choose n k))
      (show 0 ∈ Finset.range (m + 1) by simp)
    simpa [volume] using h
  have hvolumePos : (0 : ℝ) < volume := by
    exact_mod_cast (show 0 < volume by omega)
  have hmPos : (0 : ℝ) < m := by exact_mod_cast hm
  have hsubPos : (0 : ℝ) < (n - m : Nat) := by exact_mod_cast hsub
  have hdenPos :
      (0 : ℝ) < (m : ℝ) ^ m *
        (((n - m : Nat) : ℝ) ^ (n - m)) := by positivity
  have hfinite :
      (volume : ℝ) *
          ((m : ℝ) ^ m * (((n - m : Nat) : ℝ) ^ (n - m))) ≤
        (n : ℝ) ^ n := by
    dsimp [volume]
    exact_mod_cast binaryHammingBall_mul_entropyDenominator_le n m hhalf
  have hlog := Real.log_le_log
    (mul_pos hvolumePos hdenPos) hfinite
  rw [Real.log_mul (ne_of_gt hvolumePos) (ne_of_gt hdenPos),
    Real.log_mul (pow_ne_zero _ (ne_of_gt hmPos))
      (pow_ne_zero _ (ne_of_gt hsubPos)),
    Real.log_pow, Real.log_pow, Real.log_pow] at hlog
  have hlogVolume :
      Real.log (volume : ℝ) ≤
        (n : ℝ) * Real.binEntropy ((m : ℝ) / n) := by
    rw [← natEntropyRay_eq_mul_binEntropy n m hm hmn]
    linarith
  calc
    (volume : ℝ) = Real.exp (Real.log (volume : ℝ)) :=
      (Real.exp_log hvolumePos).symm
    _ ≤ Real.exp ((n : ℝ) * Real.binEntropy ((m : ℝ) / n)) :=
      Real.exp_le_exp.mpr hlogVolume

/-- Moving an integral radius to a larger real radius below one half only
increases the entropy upper bound on the binary Hamming-ball volume. -/
private theorem binaryHammingBall_le_exp_binEntropy_of_radius_le
    (n m : Nat) (delta : ℝ) (hm : 0 < m) (hhalf : 2 * m ≤ n)
    (hradius : (m : ℝ) / n ≤ delta) (hdeltaHalf : delta ≤ 1 / 2) :
    (((∑ k ∈ Finset.range (m + 1), Nat.choose n k) : Nat) : ℝ) ≤
      Real.exp ((n : ℝ) * Real.binEntropy delta) := by
  have hn : 0 < n := by omega
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hradiusNonnegative : (0 : ℝ) ≤ (m : ℝ) / n :=
    div_nonneg (Nat.cast_nonneg _) hnReal.le
  have hradiusHalf : (m : ℝ) / n ≤ (2 : ℝ)⁻¹ := by
    rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
    apply (div_le_iff₀ hnReal).2
    have hhalfReal : (2 : ℝ) * m ≤ n := by exact_mod_cast hhalf
    nlinarith
  have hdeltaNonnegative : 0 ≤ delta :=
    hradiusNonnegative.trans hradius
  have hentropy :
      Real.binEntropy ((m : ℝ) / n) ≤ Real.binEntropy delta :=
    Real.binEntropy_strictMonoOn.monotoneOn
      ⟨hradiusNonnegative, hradiusHalf⟩
      ⟨hdeltaNonnegative, by simpa only [inv_eq_one_div] using hdeltaHalf⟩
      hradius
  exact (binaryHammingBall_le_exp_binEntropy n m hm hhalf).trans
    (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hentropy hnReal.le))

/-- For the strict integer radius `ceil (delta * n)`, the Hamming-ball
entropy estimate can be evaluated directly at the prescribed real relative
distance `delta`.  The lower bound on the ceiling makes the intermediate
radius nonzero; the source proof uses sufficiently large degrees. -/
private theorem binaryHammingBall_le_exp_binEntropy_ceilRadius
    (n : Nat) (delta : ℝ) (hn : 0 < n)
    (hdeltaPositive : 0 < delta) (hdeltaHalf : delta < 1 / 2)
    (hceil : 2 ≤ Nat.ceil (delta * n)) :
    (((∑ k ∈ Finset.range (Nat.ceil (delta * n)),
        Nat.choose n k) : Nat) : ℝ) ≤
      Real.exp ((n : ℝ) * Real.binEntropy delta) := by
  let m := Nat.ceil (delta * n) - 1
  have hm : 0 < m := by dsimp [m]; omega
  have hceilPositive : 0 ≤ delta * (n : ℝ) :=
    mul_nonneg hdeltaPositive.le (Nat.cast_nonneg n)
  have hceilBound :
      (Nat.ceil (delta * n) : ℝ) < delta * n + 1 :=
    Nat.ceil_lt_add_one hceilPositive
  have hmCast : (m : ℝ) = (Nat.ceil (delta * n) : ℝ) - 1 := by
    dsimp [m]
    rw [Nat.cast_sub (by omega : 1 ≤ Nat.ceil (delta * n))]
    norm_num
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hmBelow : (m : ℝ) < delta * n := by linarith
  have hradius : (m : ℝ) / n ≤ delta := by
    apply (div_le_iff₀ hnReal).2
    exact hmBelow.le
  have hhalfReal : (2 : ℝ) * m < n := by
    have hdeltaBound : delta * (n : ℝ) < (1 / 2 : ℝ) * n :=
      mul_lt_mul_of_pos_right hdeltaHalf hnReal
    nlinarith
  have hhalf : 2 * m ≤ n := by
    exact_mod_cast hhalfReal.le
  have hbound := binaryHammingBall_le_exp_binEntropy_of_radius_le
    n m delta hm hhalf hradius hdeltaHalf.le
  simpa only [m, Nat.sub_add_cancel (by omega : 1 ≤ Nat.ceil (delta * n))]
    using hbound

/-- Flooring the random parity-check row count costs less than one binary
row.  An entropy gap larger than that single-row loss therefore makes the
real Hamming-ball bound strictly smaller than the number of parity-check
syndromes. -/
private theorem exp_binEntropy_lt_pow_two_randomRowCount
    (rho delta : ℝ) (Delta : Nat)
    (hmargin : Real.log 2 <
      (rho * Real.log 2 - Real.binEntropy delta) * (Delta : ℝ)) :
    Real.exp ((Delta : ℝ) * Real.binEntropy delta) <
      (2 : ℝ) ^ randomRowCount rho Delta := by
  have hlog : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hfloor := randomRowCount_lt_add_one rho Delta
  have hfloorLog := mul_lt_mul_of_pos_right hfloor hlog
  have hlt :
      (Delta : ℝ) * Real.binEntropy delta <
        (randomRowCount rho Delta : ℝ) * Real.log 2 := by
    nlinarith [hmargin, hfloorLog]
  calc
    Real.exp ((Delta : ℝ) * Real.binEntropy delta) <
        Real.exp ((randomRowCount rho Delta : ℝ) * Real.log 2) :=
          Real.exp_lt_exp.mpr hlt
    _ = (Real.exp (Real.log (2 : ℝ))) ^ randomRowCount rho Delta :=
      Real.exp_nat_mul (Real.log (2 : ℝ)) (randomRowCount rho Delta)
    _ = (2 : ℝ) ^ randomRowCount rho Delta := by
      rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]

/-- Failure of the generator-row code's distance bound is witnessed by a
nonzero row combination attaining a nonzero low-weight binary word. -/
theorem exists_rowCombination_lowWeight_of_not_codeA_distance
    {r distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (sample : RandomLocalCodeSample r A B)
    (hDistance :
      ¬HasMinimumDistanceAtLeast sample.codeA distance) :
    ∃ coefficients : ULift.{v} (Fin r) → ZMod 2,
      coefficients ≠ 0 ∧
      ∃ target : BinaryLowWeightWords A distance,
        target.1 ≠ 0 ∧
        Matrix.vecMul coefficients sample.1 = target.1 := by
  unfold HasMinimumDistanceAtLeast at hDistance
  push_neg at hDistance
  obtain ⟨target, htargetCode, htargetNonzero, htargetWeight⟩ := hDistance
  rw [RandomLocalCodeSample.codeA,
    mem_parityCheckRowCode] at htargetCode
  obtain ⟨coefficients, hcoefficientsTarget⟩ := htargetCode
  have hvecMul : Matrix.vecMul coefficients sample.1 = target := by
    funext coordinate
    rw [← hcoefficientsTarget,
      wordLinearMapTranspose_toLin'_apply]
    rfl
  have hcoefficientsNonzero : coefficients ≠ 0 := by
    intro hzero
    subst coefficients
    simp at hvecMul
    exact htargetNonzero hvecMul.symm
  exact ⟨coefficients, hcoefficientsNonzero,
    ⟨target, htargetWeight⟩, htargetNonzero, hvecMul⟩

/-- Both matrices in a random LZ22 local-code sample have full row rank.
This is the exact rank event used to turn the nominal matrix rates into the
dimensions recorded by `GoodLocalCodeEvent`. -/
def RandomLocalCodeSample.HasFullRowRank
    {r : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (sample : RandomLocalCodeSample r A B) : Prop :=
  Function.Surjective (Matrix.toLin' sample.1) ∧
    Function.Surjective (Matrix.toLin' sample.2)

/-- Injectivity of binary row combinations forces a matrix to have full row
rank.  This is the linear-algebra direction used to expose a concrete witness
whenever the rank event fails. -/
private theorem surjective_toLin'_of_vecMul_injective
    {row col : Type v} [Fintype row] [Fintype col]
    (M : Matrix row col (ZMod 2))
    (hinjective : Function.Injective fun coefficients : row → ZMod 2 =>
      Matrix.vecMul coefficients M) :
    Function.Surjective (Matrix.toLin' M) := by
  have hrows : LinearIndependent (ZMod 2) M.row := by
    rw [← Matrix.vecMul_injective_iff]
    exact hinjective
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  rw [Matrix.range_toLin', ← Matrix.rank_eq_finrank_span_cols,
    hrows.rank_matrix]
  simp

/-- Failure of full row rank yields a nonzero binary combination of rows whose
sum is zero.  The LZ22 probability estimate counts exactly these witnesses. -/
private theorem exists_nonzero_vecMul_eq_zero_of_not_surjective
    {row col : Type v} [Fintype row] [Fintype col]
    (M : Matrix row col (ZMod 2))
    (hM : ¬Function.Surjective (Matrix.toLin' M)) :
    ∃ coefficients : row → ZMod 2,
      coefficients ≠ 0 ∧ Matrix.vecMul coefficients M = 0 := by
  have hnotInjective :
      ¬Function.Injective (fun coefficients : row → ZMod 2 =>
        Matrix.vecMul coefficients M) := by
    intro hinjective
    exact hM (surjective_toLin'_of_vecMul_injective M hinjective)
  rw [Function.not_injective_iff] at hnotInjective
  obtain ⟨x, y, hxyImage, hxy⟩ := hnotInjective
  refine ⟨x - y, sub_ne_zero.mpr hxy, ?_⟩
  rw [Matrix.sub_vecMul, hxyImage, sub_self]

/-- For fixed row coefficients, take their linear combination in every matrix
column.  Its kernel is the fixed-witness rank-failure event counted in the
source union bound. -/
private def fixedRowCombinationMap
    {row col : Type v} [Fintype row]
    (coefficients : row → ZMod 2) :
    Matrix row col (ZMod 2) →ₗ[ZMod 2] Word (ZMod 2) col where
  toFun M := Matrix.vecMul coefficients M
  map_add' M N := Matrix.vecMul_add M N coefficients
  map_smul' scalar M := Matrix.vecMul_smul coefficients scalar M

/-- Every nonzero row-coefficient vector gives a surjective map from matrices
to their corresponding row combination.  Thus a fixed nonzero dependency
imposes exactly one independent binary equation per column. -/
private theorem fixedRowCombinationMap_surjective
    {row col : Type v} [Fintype row]
    {coefficients : row → ZMod 2} (hcoefficients : coefficients ≠ 0) :
    Function.Surjective (fixedRowCombinationMap (col := col) coefficients) := by
  have hexists : ∃ i, coefficients i ≠ 0 := by
    by_contra hzero
    push Not at hzero
    apply hcoefficients
    funext i
    exact hzero i
  obtain ⟨i, hi⟩ := hexists
  intro y
  let M : Matrix row col (ZMod 2) := fun r c =>
    if r = i then (coefficients i)⁻¹ * y c else 0
  refine ⟨M, ?_⟩
  funext c
  simp [fixedRowCombinationMap, M, Matrix.vecMul, dotProduct, hi]

/-- The matrices killed by one fixed nonzero row dependency have codimension
one binary equation in every column. -/
private theorem finrank_ker_fixedRowCombinationMap
    {row col : Type v} [Fintype row] [Fintype col]
    {coefficients : row → ZMod 2} (hcoefficients : coefficients ≠ 0) :
    Module.finrank (ZMod 2)
        (LinearMap.ker (fixedRowCombinationMap (col := col) coefficients)) =
      Fintype.card row * Fintype.card col - Fintype.card col := by
  let f := fixedRowCombinationMap (col := col) coefficients
  have hSurjective : Function.Surjective f :=
    fixedRowCombinationMap_surjective (col := col) hcoefficients
  have hRange : LinearMap.range f = ⊤ :=
    LinearMap.range_eq_top.mpr hSurjective
  have hRankNullity := f.finrank_range_add_finrank_ker
  rw [hRange, finrank_top, finrank_word_eq_length] at hRankNullity
  simp only [Length] at hRankNullity
  norm_num [f, fixedRowCombinationMap, Module.finrank_matrix] at hRankNullity
  have hKernel := Nat.eq_sub_of_add_eq (by
    simpa [Nat.add_comm] using hRankNullity)
  simpa [f, Nat.mul_comm] using hKernel

/-- Consequently a fixed nonzero dependency is satisfied by exactly
`2^(|row||col|-|col|)` binary matrices. -/
private theorem card_ker_fixedRowCombinationMap
    {row col : Type v} [Fintype row] [Fintype col]
    {coefficients : row → ZMod 2} (hcoefficients : coefficients ≠ 0) :
    Fintype.card
        (LinearMap.ker (fixedRowCombinationMap (col := col) coefficients)) =
      2 ^ (Fintype.card row * Fintype.card col - Fintype.card col) := by
  rw [@Module.card_eq_pow_finrank (ZMod 2)
    (LinearMap.ker (fixedRowCombinationMap (col := col) coefficients))
    _ _ _ _ _]
  have hbase : Fintype.card (ZMod 2) = 2 := ZMod.card 2
  rw [hbase, finrank_ker_fixedRowCombinationMap hcoefficients]

/-- Translation identifies any nonempty fiber of a linear map with its
kernel. -/
private def linearFiberEquivKer
    {F V W : Type*} [Field F] [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    (f : V →ₗ[F] W) (base : V) :
    {x : V // f x = f base} ≃ LinearMap.ker f where
  toFun x := ⟨x.1 - base, by simp [x.2]⟩
  invFun z := ⟨z.1 + base, by simp⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv z := by
    apply Subtype.ext
    simp

/-- A fixed nonzero row combination is uniformly distributed over binary
column words: every target fiber has the same exact cardinality. -/
private theorem card_fixedRowCombinationFiber
    {row col : Type v} [Fintype row] [Fintype col]
    {coefficients : row → ZMod 2} (hcoefficients : coefficients ≠ 0)
    (target : Word (ZMod 2) col) :
    Fintype.card
        {matrix : Matrix row col (ZMod 2) //
          Matrix.vecMul coefficients matrix = target} =
      2 ^ (Fintype.card row * Fintype.card col - Fintype.card col) := by
  obtain ⟨base, hbase⟩ :=
    fixedRowCombinationMap_surjective
      (col := col) hcoefficients target
  change Fintype.card
      {matrix : Matrix row col (ZMod 2) //
        fixedRowCombinationMap coefficients matrix = target} = _
  rw [← hbase,
    Fintype.card_congr
      (linearFiberEquivKer
        (fixedRowCombinationMap (col := col) coefficients) base),
    card_ker_fixedRowCombinationMap hcoefficients]

/-- The ambient space of binary `row × col` matrices has the expected power
of two cardinality. -/
private theorem card_binaryMatrix
    (row col : Type v) [Fintype row] [Fintype col] :
    Fintype.card (Matrix row col (ZMod 2)) =
      2 ^ (Fintype.card row * Fintype.card col) := by
  rw [@Module.card_eq_pow_finrank (ZMod 2) (Matrix row col (ZMod 2))
    _ _ _ _ _]
  have hbase : Fintype.card (ZMod 2) = 2 := ZMod.card 2
  rw [hbase]
  congr 1
  norm_num [Module.finrank_matrix]

/-- Fixing one row combination of the first matrix to a target word leaves
the second matrix completely free. -/
private def firstRowCombinationFiberEventEquiv
    {row A B : Type v} [Fintype row]
    (coefficients : row → ZMod 2) (target : Word (ZMod 2) A) :
    {sample : Matrix row A (ZMod 2) × Matrix row B (ZMod 2) //
        Matrix.vecMul coefficients sample.1 = target} ≃
      {matrix : Matrix row A (ZMod 2) //
        Matrix.vecMul coefficients matrix = target} ×
        Matrix row B (ZMod 2) where
  toFun sample := ⟨⟨sample.1.1, sample.2⟩, sample.1.2⟩
  invFun sample := ⟨⟨sample.1.1, sample.2⟩, sample.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Fixing one row combination of the second matrix to a target word leaves
the first matrix completely free. -/
private def secondRowCombinationFiberEventEquiv
    {row A B : Type v} [Fintype row]
    (coefficients : row → ZMod 2) (target : Word (ZMod 2) B) :
    {sample : Matrix row A (ZMod 2) × Matrix row B (ZMod 2) //
        Matrix.vecMul coefficients sample.2 = target} ≃
      Matrix row A (ZMod 2) ×
        {matrix : Matrix row B (ZMod 2) //
          Matrix.vecMul coefficients matrix = target} where
  toFun sample := ⟨sample.1.1, ⟨sample.1.2, sample.2⟩⟩
  invFun sample := ⟨⟨sample.1, sample.2.1⟩, sample.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact sample count for a fixed nonzero row combination of the first
matrix attaining a prescribed target word. -/
private theorem card_firstRowCombinationFiberEvent
    {row A B : Type v} [Fintype row] [Fintype A] [Fintype B]
    {coefficients : row → ZMod 2} (hcoefficients : coefficients ≠ 0)
    (target : Word (ZMod 2) A) :
    (eventFinset fun sample :
        Matrix row A (ZMod 2) × Matrix row B (ZMod 2) =>
      Matrix.vecMul coefficients sample.1 = target).card =
      2 ^ (Fintype.card row * Fintype.card A - Fintype.card A) *
        2 ^ (Fintype.card row * Fintype.card B) := by
  rw [eventFinset, ← Fintype.card_subtype,
    Fintype.card_congr
      (firstRowCombinationFiberEventEquiv coefficients target),
    Fintype.card_prod,
    card_fixedRowCombinationFiber hcoefficients target,
    card_binaryMatrix]

/-- Exact sample count for a fixed nonzero row combination of the second
matrix attaining a prescribed target word. -/
private theorem card_secondRowCombinationFiberEvent
    {row A B : Type v} [Fintype row] [Fintype A] [Fintype B]
    {coefficients : row → ZMod 2} (hcoefficients : coefficients ≠ 0)
    (target : Word (ZMod 2) B) :
    (eventFinset fun sample :
        Matrix row A (ZMod 2) × Matrix row B (ZMod 2) =>
      Matrix.vecMul coefficients sample.2 = target).card =
      2 ^ (Fintype.card row * Fintype.card A) *
        2 ^ (Fintype.card row * Fintype.card B - Fintype.card B) := by
  rw [eventFinset, ← Fintype.card_subtype,
    Fintype.card_congr
      (secondRowCombinationFiberEventEquiv coefficients target),
    Fintype.card_prod, card_binaryMatrix,
    card_fixedRowCombinationFiber hcoefficients target]

/-- A generator-code distance failure indexed by a nonzero row combination
and a nonzero target word below the requested distance. -/
private def firstDistanceBad
    {r distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (index :
      {coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0} ×
        {target : BinaryLowWeightWords A distance // target.1 ≠ 0})
    (sample : RandomLocalCodeSample r A B) : Prop :=
  Matrix.vecMul index.1.1 sample.1 = index.2.1.1

/-- Every failure of the generator-row code's distance is covered by one of
the explicit finite low-word events. -/
private theorem firstDistanceBad_covers_not_codeA_distance
    {r distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (sample : RandomLocalCodeSample r A B)
    (hDistance :
      ¬HasMinimumDistanceAtLeast sample.codeA distance) :
    ∃ index :
        {coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0} ×
          {target : BinaryLowWeightWords A distance // target.1 ≠ 0},
      firstDistanceBad index sample := by
  obtain ⟨coefficients, hcoefficients, target, htarget, hvecMul⟩ :=
    exists_rowCombination_lowWeight_of_not_codeA_distance
      sample hDistance
  exact ⟨⟨⟨coefficients, hcoefficients⟩, ⟨target, htarget⟩⟩,
    hvecMul⟩

/-- The subtype cut out by one explicit generator-distance witness is the
product of its constrained first-matrix fiber with the freely chosen second
matrix.  Stating this equivalence directly avoids dependence on the particular
decidability instance used to build the event finset. -/
private def firstDistanceBadEventEquiv
    {r distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (index :
      {coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0} ×
        {target : BinaryLowWeightWords A distance // target.1 ≠ 0}) :
    {sample : RandomLocalCodeSample r A B // firstDistanceBad index sample} ≃
      {matrix : Matrix (ULift.{v} (Fin r)) A (ZMod 2) //
        Matrix.vecMul index.1.1 matrix = index.2.1.1} ×
        Matrix (ULift.{v} (Fin r)) B (ZMod 2) where
  toFun sample := ⟨⟨sample.1.1, sample.2⟩, sample.1.2⟩
  invFun sample := ⟨⟨sample.1.1, sample.2⟩, sample.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Every fixed generator-distance witness has the exact uniform fiber count
computed above. -/
private theorem card_firstDistanceBad
    {r distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (index :
      {coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0} ×
        {target : BinaryLowWeightWords A distance // target.1 ≠ 0}) :
    (eventFinset (firstDistanceBad (B := B) index)).card =
      2 ^ (r * Fintype.card A - Fintype.card A) *
        2 ^ (r * Fintype.card B) := by
  obtain ⟨base, hbase⟩ :=
    fixedRowCombinationMap_surjective
      (col := A) index.1.2 index.2.1.1
  have hFiberEquiv :
      {matrix : Matrix (ULift.{v} (Fin r)) A (ZMod 2) //
        Matrix.vecMul index.1.1 matrix = index.2.1.1} ≃
        LinearMap.ker
          (fixedRowCombinationMap (col := A) index.1.1) := by
    change
      {matrix : Matrix (ULift.{v} (Fin r)) A (ZMod 2) //
        fixedRowCombinationMap index.1.1 matrix = index.2.1.1} ≃ _
    rw [← hbase]
    exact linearFiberEquivKer
      (fixedRowCombinationMap (col := A) index.1.1) base
  rw [eventFinset, ← Fintype.card_subtype,
    Fintype.card_congr (firstDistanceBadEventEquiv index),
    Fintype.card_prod, Fintype.card_congr hFiberEquiv]
  rw [@Module.card_eq_pow_finrank (ZMod 2)
    (LinearMap.ker
      (fixedRowCombinationMap (col := A) index.1.1)) _ _ _ _ _,
    @Module.card_eq_pow_finrank (ZMod 2)
      (Matrix (ULift.{v} (Fin r)) B (ZMod 2)) _ _ _ _ _]
  have hbaseCard : Fintype.card (ZMod 2) = 2 := ZMod.card 2
  rw [hbaseCard,
    finrank_ker_fixedRowCombinationMap index.1.2,
    Module.finrank_matrix]
  simp

/-- The explicit vanishing-row-combination predicate is equivalent to the
kernel subtype of its linear map. -/
private def fixedRowDependencyEventEquiv
    {row col : Type v} [Fintype row]
    (coefficients : row → ZMod 2) :
    {M : Matrix row col (ZMod 2) // Matrix.vecMul coefficients M = 0} ≃
      LinearMap.ker (fixedRowCombinationMap (col := col) coefficients) where
  toFun M := ⟨M.1, by
    change Matrix.vecMul coefficients M.1 = 0
    exact M.2⟩
  invFun M := ⟨M.1, by
    exact (show fixedRowCombinationMap coefficients M.1 = 0 from M.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The exact number of matrices satisfying one fixed nonzero row dependency
is the kernel cardinality computed above. -/
private theorem card_fixedRowDependencyEvent
    {row col : Type v} [Fintype row] [Fintype col]
    {coefficients : row → ZMod 2} (hcoefficients : coefficients ≠ 0) :
    (eventFinset fun M : Matrix row col (ZMod 2) =>
      Matrix.vecMul coefficients M = 0).card =
      2 ^ (Fintype.card row * Fintype.card col - Fintype.card col) := by
  rw [eventFinset, ← Fintype.card_subtype,
    Fintype.card_congr (fixedRowDependencyEventEquiv coefficients)]
  exact card_ker_fixedRowCombinationMap hcoefficients

/-- A fixed dependency in the first matrix leaves the second matrix free. -/
private def firstRankDependencyEventEquiv
    {row A B : Type v} [Fintype row]
    (coefficients : row → ZMod 2) :
    {sample : Matrix row A (ZMod 2) × Matrix row B (ZMod 2) //
        Matrix.vecMul coefficients sample.1 = 0} ≃
      LinearMap.ker (fixedRowCombinationMap (col := A) coefficients) ×
        Matrix row B (ZMod 2) where
  toFun sample := ⟨⟨sample.1.1, by
    change Matrix.vecMul coefficients sample.1.1 = 0
    exact sample.2⟩, sample.1.2⟩
  invFun sample := ⟨⟨sample.1.1, sample.2⟩, by
    change Matrix.vecMul coefficients sample.1.1 = 0
    exact (show fixedRowCombinationMap coefficients sample.1.1 = 0
      from sample.1.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A fixed dependency in the second matrix leaves the first matrix free. -/
private def secondRankDependencyEventEquiv
    {row A B : Type v} [Fintype row]
    (coefficients : row → ZMod 2) :
    {sample : Matrix row A (ZMod 2) × Matrix row B (ZMod 2) //
        Matrix.vecMul coefficients sample.2 = 0} ≃
      Matrix row A (ZMod 2) ×
        LinearMap.ker (fixedRowCombinationMap (col := B) coefficients) where
  toFun sample := ⟨sample.1.1, ⟨sample.1.2, by
    change Matrix.vecMul coefficients sample.1.2 = 0
    exact sample.2⟩⟩
  invFun sample := ⟨⟨sample.1, sample.2.1⟩, by
    change Matrix.vecMul coefficients sample.2.1 = 0
    exact (show fixedRowCombinationMap coefficients sample.2.1 = 0
      from sample.2.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact sample-space count for a fixed nonzero dependency in the first
matrix of the random pair. -/
private theorem card_firstRankDependencyEvent
    {row A B : Type v} [Fintype row] [Fintype A] [Fintype B]
    {coefficients : row → ZMod 2} (hcoefficients : coefficients ≠ 0) :
    (eventFinset fun sample :
        Matrix row A (ZMod 2) × Matrix row B (ZMod 2) =>
      Matrix.vecMul coefficients sample.1 = 0).card =
      2 ^ (Fintype.card row * Fintype.card A - Fintype.card A) *
        2 ^ (Fintype.card row * Fintype.card B) := by
  rw [eventFinset, ← Fintype.card_subtype,
    Fintype.card_congr (firstRankDependencyEventEquiv coefficients),
    Fintype.card_prod, card_ker_fixedRowCombinationMap hcoefficients,
    card_binaryMatrix]

/-- Exact sample-space count for a fixed nonzero dependency in the second
matrix of the random pair. -/
private theorem card_secondRankDependencyEvent
    {row A B : Type v} [Fintype row] [Fintype A] [Fintype B]
    {coefficients : row → ZMod 2} (hcoefficients : coefficients ≠ 0) :
    (eventFinset fun sample :
        Matrix row A (ZMod 2) × Matrix row B (ZMod 2) =>
      Matrix.vecMul coefficients sample.2 = 0).card =
      2 ^ (Fintype.card row * Fintype.card A) *
        2 ^ (Fintype.card row * Fintype.card B - Fintype.card B) := by
  rw [eventFinset, ← Fintype.card_subtype,
    Fintype.card_congr (secondRankDependencyEventEquiv coefficients),
    Fintype.card_prod, card_ker_fixedRowCombinationMap hcoefficients,
    card_binaryMatrix]

/-- There are exactly `2^|row| - 1` nonzero binary row-coefficient vectors. -/
private theorem card_nonzeroBinaryRowCombination
    (row : Type v) [Fintype row] :
    Fintype.card {coefficients : row → ZMod 2 // coefficients ≠ 0} =
      2 ^ Fintype.card row - 1 := by
  rw [Fintype.card_subtype_compl
      (fun coefficients : row → ZMod 2 => coefficients = 0),
    Fintype.card_subtype_eq, Fintype.card_fun]
  have hbase : Fintype.card (ZMod 2) = 2 := ZMod.card 2
  rw [hbase]

/-- Summing the exact first-matrix distance-witness fibers separates into the
number of nonzero row combinations, the number of nonzero low-weight target
words, and the common fiber cardinality. -/
private theorem sum_card_firstDistanceBad
    {r Delta distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta) :
    ∑ index :
        {coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0} ×
          {target : BinaryLowWeightWords A distance // target.1 ≠ 0},
      (eventFinset (firstDistanceBad (B := B) index)).card =
        ((2 ^ r - 1) *
          Fintype.card {target : BinaryLowWeightWords A distance // target.1 ≠ 0}) *
            (2 ^ (r * Delta - Delta) * 2 ^ (r * Delta)) := by
  have hEach : ∀ index :
      {coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0} ×
        {target : BinaryLowWeightWords A distance // target.1 ≠ 0},
      (eventFinset (firstDistanceBad (B := B) index)).card =
        2 ^ (r * Delta - Delta) * 2 ^ (r * Delta) := by
    intro index
    rw [card_firstDistanceBad]
    simp only [hA, hB]
  have hIndex :
      Fintype.card
        ({coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0} ×
          {target : BinaryLowWeightWords A distance // target.1 ≠ 0}) =
        (2 ^ r - 1) *
          Fintype.card
            {target : BinaryLowWeightWords A distance // target.1 ≠ 0} := by
    have hCoefficients :
        Fintype.card
          {coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0} =
          2 ^ r - 1 := by
      rw [Fintype.card_subtype_compl
          (fun coefficients : ULift.{v} (Fin r) → ZMod 2 =>
            coefficients = 0),
        Fintype.card_subtype_eq, Fintype.card_fun]
      have hbase : Fintype.card (ZMod 2) = 2 := ZMod.card 2
      rw [hbase, Fintype.card_ulift, Fintype.card_fin]
    rw [Fintype.card_prod, hCoefficients]
  simp_rw [hEach]
  rw [Finset.sum_const, Finset.card_univ, hIndex, nsmul_eq_mul]
  norm_num

/-- The total first-matrix generator-distance failure count is bounded by the
binary Hamming-ball volume times the exact nonzero-row-combination count and
the common matrix fiber size. -/
private theorem sum_card_firstDistanceBad_le
    {r Delta distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta) :
    ∑ index :
        {coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0} ×
          {target : BinaryLowWeightWords A distance // target.1 ≠ 0},
      (eventFinset (firstDistanceBad (B := B) index)).card ≤
        ((2 ^ r - 1) *
          (∑ weight ∈ Finset.range distance, Nat.choose Delta weight)) *
            (2 ^ (r * Delta - Delta) * 2 ^ (r * Delta)) := by
  rw [sum_card_firstDistanceBad hA hB]
  apply Nat.mul_le_mul_right
  apply Nat.mul_le_mul_left
  calc
    Fintype.card
        {target : BinaryLowWeightWords A distance // target.1 ≠ 0} ≤
        Fintype.card (BinaryLowWeightWords A distance) :=
      Fintype.card_subtype_le _
    _ = ∑ weight ∈ Finset.range distance,
        Nat.choose (Fintype.card A) weight :=
      card_binaryLowWeightWords A distance
    _ = ∑ weight ∈ Finset.range distance, Nat.choose Delta weight := by
      rw [hA]

/-- The rank-failure union has two sides and one index for every nonzero row
combination. -/
private theorem card_rankDependencyIndex
    (row : Type v) [Fintype row] :
    Fintype.card (Bool ×
      {coefficients : row → ZMod 2 // coefficients ≠ 0}) =
      2 * (2 ^ Fintype.card row - 1) := by
  rw [Fintype.card_prod, card_nonzeroBinaryRowCombination]
  norm_num

/-- The finite bad-event family used for the full-rank union bound.  `false`
selects a dependency in the generator matrix and `true` one in the check
matrix. -/
private def rankDependencyBad
    {row A B : Type v} [Fintype row]
    (index : Bool ×
      {coefficients : row → ZMod 2 // coefficients ≠ 0})
    (sample : Matrix row A (ZMod 2) × Matrix row B (ZMod 2)) : Prop :=
  if index.1 then Matrix.vecMul index.2.1 sample.2 = 0
  else Matrix.vecMul index.2.1 sample.1 = 0

/-- Each member of the rank-failure cover has the exact product count from
the corresponding free and constrained matrices. -/
private theorem card_rankDependencyBad
    {row A B : Type v} [Fintype row] [Fintype A] [Fintype B]
    (index : Bool ×
      {coefficients : row → ZMod 2 // coefficients ≠ 0}) :
    (eventFinset (rankDependencyBad (A := A) (B := B) index)).card =
      if index.1 then
        2 ^ (Fintype.card row * Fintype.card A) *
          2 ^ (Fintype.card row * Fintype.card B - Fintype.card B)
      else
        2 ^ (Fintype.card row * Fintype.card A - Fintype.card A) *
          2 ^ (Fintype.card row * Fintype.card B) := by
  rcases index with ⟨side, ⟨coefficients, hcoefficients⟩⟩
  cases side
  · rw [eventFinset, ← Fintype.card_subtype]
    simp only [rankDependencyBad, Bool.false_eq_true, if_false]
    rw [Fintype.card_congr (firstRankDependencyEventEquiv coefficients),
      Fintype.card_prod, card_ker_fixedRowCombinationMap hcoefficients,
      card_binaryMatrix]
  · rw [eventFinset, ← Fintype.card_subtype]
    simp only [rankDependencyBad, if_true]
    rw [Fintype.card_congr (secondRankDependencyEventEquiv coefficients),
      Fintype.card_prod, card_ker_fixedRowCombinationMap hcoefficients,
      card_binaryMatrix]

/-- If either matrix in a random local-code sample loses full row rank, the
failure is witnessed by a nonzero vanishing row combination in that matrix. -/
theorem exists_rankFailureWitness_of_not_fullRowRank
    {r : Nat} {A B : Type v} [Fintype A] [Fintype B]
    {sample : RandomLocalCodeSample r A B}
    (hFull : ¬sample.HasFullRowRank) :
    (∃ coefficients : ULift.{v} (Fin r) → ZMod 2,
      coefficients ≠ 0 ∧ Matrix.vecMul coefficients sample.1 = 0) ∨
    (∃ coefficients : ULift.{v} (Fin r) → ZMod 2,
      coefficients ≠ 0 ∧ Matrix.vecMul coefficients sample.2 = 0) := by
  rw [RandomLocalCodeSample.HasFullRowRank, not_and_or] at hFull
  exact hFull.imp
    (exists_nonzero_vecMul_eq_zero_of_not_surjective sample.1)
    (exists_nonzero_vecMul_eq_zero_of_not_surjective sample.2)

/-- Every failure of full row rank is covered by one of the explicit finite
dependency events. -/
private theorem rankDependencyBad_covers_not_fullRowRank
    {r : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (sample : RandomLocalCodeSample r A B)
    (hFull : ¬sample.HasFullRowRank) :
    ∃ index : Bool ×
        {coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0},
      rankDependencyBad index sample := by
  rcases exists_rankFailureWitness_of_not_fullRowRank hFull with
    ⟨coefficients, hcoefficients, hvanishes⟩ |
      ⟨coefficients, hcoefficients, hvanishes⟩
  · exact ⟨⟨false, ⟨coefficients, hcoefficients⟩⟩, hvanishes⟩
  · exact ⟨⟨true, ⟨coefficients, hcoefficients⟩⟩, hvanishes⟩

/-- Exact cardinality of the uniform experiment consisting of two independent
binary `r × Delta` matrices. -/
private theorem card_randomLocalCodeSample
    {r Delta : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta) :
    Fintype.card (RandomLocalCodeSample r A B) =
      2 ^ (r * Delta) * 2 ^ (r * Delta) := by
  change Fintype.card
      (Matrix (ULift.{v} (Fin r)) A (ZMod 2) ×
        Matrix (ULift.{v} (Fin r)) B (ZMod 2)) = _
  rw [@Module.card_eq_pow_finrank (ZMod 2)
    (Matrix (ULift.{v} (Fin r)) A (ZMod 2) ×
      Matrix (ULift.{v} (Fin r)) B (ZMod 2)) _ _ _ _ _]
  have hbase : Fintype.card (ZMod 2) = 2 := ZMod.card 2
  rw [hbase, Module.finrank_prod, Module.finrank_matrix,
    Module.finrank_matrix, pow_add]
  simp [hA, hB]

/-- The finite low-word cover proves positive probability for the generator
row code's target distance whenever its explicit Hamming-ball numerator is
smaller than the two-matrix sample space. -/
theorem hasPositiveUniformProbability_codeA_distance_of_count_bound
    {r Delta distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (hcount :
      ((2 ^ r - 1) *
        (∑ weight ∈ Finset.range distance, Nat.choose Delta weight)) *
          (2 ^ (r * Delta - Delta) * 2 ^ (r * Delta)) <
        2 ^ (r * Delta) * 2 ^ (r * Delta)) :
    HasPositiveUniformProbability
      (fun sample : RandomLocalCodeSample r A B =>
        HasMinimumDistanceAtLeast sample.codeA distance) := by
  apply hasPositiveUniformProbability_of_union_bound
    (J :=
      {coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0} ×
        {target : BinaryLowWeightWords A distance // target.1 ≠ 0})
    (bad := firstDistanceBad (B := B))
  · exact firstDistanceBad_covers_not_codeA_distance
  · rw [card_randomLocalCodeSample hA hB]
    exact (sum_card_firstDistanceBad_le hA hB).trans_lt hcount

/-- With a nonempty row set, the generator-code distance event's exact
matrix-fiber count reduces to its finite Hamming-ball numerator. -/
theorem hasPositiveUniformProbability_codeA_distance_of_ball_count
    {r Delta distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (hRows : 0 < r)
    (hball :
      (2 ^ r - 1) *
        (∑ weight ∈ Finset.range distance, Nat.choose Delta weight) <
          2 ^ Delta) :
    HasPositiveUniformProbability
      (fun sample : RandomLocalCodeSample r A B =>
        HasMinimumDistanceAtLeast sample.codeA distance) := by
  have hDeltaLe : Delta ≤ r * Delta := by
    have hOne : 1 ≤ r := hRows
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right Delta hOne
  have hpow :
      2 ^ (r * Delta - Delta) * 2 ^ Delta = 2 ^ (r * Delta) := by
    rw [← pow_add]
    congr 1
    omega
  have hcommon :
      0 < 2 ^ (r * Delta - Delta) * 2 ^ (r * Delta) := by
    positivity
  apply hasPositiveUniformProbability_codeA_distance_of_count_bound hA hB
  calc
    ((2 ^ r - 1) *
        (∑ weight ∈ Finset.range distance, Nat.choose Delta weight)) *
        (2 ^ (r * Delta - Delta) * 2 ^ (r * Delta)) <
        2 ^ Delta *
          (2 ^ (r * Delta - Delta) * 2 ^ (r * Delta)) :=
      Nat.mul_lt_mul_of_pos_right hball hcommon
    _ = 2 ^ (r * Delta) * 2 ^ (r * Delta) := by
      calc
        2 ^ Delta *
            (2 ^ (r * Delta - Delta) * 2 ^ (r * Delta)) =
            (2 ^ (r * Delta - Delta) * 2 ^ Delta) *
              2 ^ (r * Delta) := by ring
        _ = 2 ^ (r * Delta) * 2 ^ (r * Delta) := by rw [hpow]

/-- The entropy gap below the local generator rate, together with
`rho < 1/2`, bounds the generator-code Hamming-ball numerator strictly
below the number of binary words. -/
theorem hasPositiveUniformProbability_codeA_distance_of_entropy_gap
    {Delta : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (rho delta : ℝ) (hA : Fintype.card A = Delta)
    (hB : Fintype.card B = Delta)
    (hRhoNonnegative : 0 ≤ rho) (hRhoHalf : rho < 1 / 2)
    (hDelta : 0 < Delta) (hRows : 0 < randomRowCount rho Delta)
    (hdeltaPositive : 0 < delta) (hdeltaHalf : delta < 1 / 2)
    (hceil : 2 ≤ Nat.ceil (delta * Delta))
    (hentropy : Real.binEntropy delta < rho * Real.log 2) :
    HasPositiveUniformProbability
      (fun sample : RandomLocalCodeSample (randomRowCount rho Delta) A B =>
        HasMinimumDistanceAtLeast sample.codeA
          (Nat.ceil (delta * Delta))) := by
  let volume := ∑ weight ∈ Finset.range (Nat.ceil (delta * Delta)),
    Nat.choose Delta weight
  let r := randomRowCount rho Delta
  have hvolume : (volume : ℝ) ≤
      Real.exp ((Delta : ℝ) * Real.binEntropy delta) :=
    binaryHammingBall_le_exp_binEntropy_ceilRadius
      Delta delta hDelta hdeltaPositive hdeltaHalf hceil
  have hlog : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hRhoLog : rho * Real.log 2 < (1 / 2 : ℝ) * Real.log 2 :=
    mul_lt_mul_of_pos_right hRhoHalf hlog
  have hsum :
      Real.binEntropy delta + rho * Real.log 2 < Real.log 2 := by
    linarith
  have hDeltaReal : (0 : ℝ) < Delta := by exact_mod_cast hDelta
  have hRowsReal : (r : ℝ) ≤ rho * Delta :=
    randomRowCount_cast_le hRhoNonnegative
  have hRowsLog :
      (r : ℝ) * Real.log 2 ≤
        (rho * Delta) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hRowsReal hlog.le
  have hsumScaled :
      (Delta : ℝ) * (Real.binEntropy delta + rho * Real.log 2) <
        (Delta : ℝ) * Real.log 2 :=
    mul_lt_mul_of_pos_left hsum hDeltaReal
  have hExponent :
      (r : ℝ) * Real.log 2 +
          (Delta : ℝ) * Real.binEntropy delta <
        (Delta : ℝ) * Real.log 2 := by
    nlinarith [hRowsLog, hsumScaled]
  have hPow (k : Nat) :
      ((2 ^ k : Nat) : ℝ) =
        Real.exp ((k : ℝ) * Real.log 2) := by
    calc
      ((2 ^ k : Nat) : ℝ) = (2 : ℝ) ^ k := by norm_cast
      _ = (Real.exp (Real.log (2 : ℝ))) ^ k := by
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ = Real.exp ((k : ℝ) * Real.log 2) :=
        (Real.exp_nat_mul (Real.log (2 : ℝ)) k).symm
  have hNumerator : (2 ^ r - 1) * volume < 2 ^ Delta := by
    have hCountReal :
        (((2 ^ r - 1) * volume : Nat) : ℝ) <
          ((2 ^ Delta : Nat) : ℝ) := by
      calc
        (((2 ^ r - 1) * volume : Nat) : ℝ) =
            ((2 ^ r - 1 : Nat) : ℝ) * (volume : ℝ) := by norm_cast
        _ ≤ ((2 ^ r : Nat) : ℝ) * (volume : ℝ) :=
          mul_le_mul_of_nonneg_right
            (by exact_mod_cast Nat.sub_le (2 ^ r) 1)
            (Nat.cast_nonneg _)
        _ ≤ Real.exp ((r : ℝ) * Real.log 2) *
            Real.exp ((Delta : ℝ) * Real.binEntropy delta) := by
          rw [← hPow r]
          exact mul_le_mul_of_nonneg_left hvolume (Nat.cast_nonneg _)
        _ < ((2 ^ Delta : Nat) : ℝ) := by
          rw [← Real.exp_add, hPow Delta]
          exact Real.exp_lt_exp.mpr hExponent
    exact_mod_cast hCountReal
  exact hasPositiveUniformProbability_codeA_distance_of_ball_count
    hA hB hRows hNumerator

/-- Failure of the kernel code's distance bound is witnessed by a nonzero
low-weight input annihilated by the second random matrix. -/
theorem exists_lowWeight_kernel_of_not_codeB_distance
    {r distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (sample : RandomLocalCodeSample r A B)
    (hDistance :
      ¬HasMinimumDistanceAtLeast sample.codeB distance) :
    ∃ target : BinaryLowWeightWords B distance,
      target.1 ≠ 0 ∧ Matrix.mulVec sample.2 target.1 = 0 := by
  unfold HasMinimumDistanceAtLeast at hDistance
  push_neg at hDistance
  obtain ⟨target, htargetCode, htargetNonzero, htargetWeight⟩ := hDistance
  rw [RandomLocalCodeSample.codeB,
    mem_parityCheckKernelCode] at htargetCode
  refine ⟨⟨target, htargetWeight⟩, htargetNonzero, ?_⟩
  simpa only [Matrix.toLin'_apply] using htargetCode

/-- For a fixed input word, multiply every binary matrix by that word.  Its
kernel is the fixed-witness event used for the random kernel-code distance
bound. -/
private def fixedColumnCombinationMap
    {row col : Type v} [Fintype col]
    (target : col → ZMod 2) :
    Matrix row col (ZMod 2) →ₗ[ZMod 2] Word (ZMod 2) row where
  toFun M := Matrix.mulVec M target
  map_add' M N := Matrix.add_mulVec M N target
  map_smul' scalar M := Matrix.smul_mulVec scalar M target

/-- A nonzero fixed input makes matrix evaluation surjective: one nonzero
coordinate can realize each requested output coordinate independently. -/
private theorem fixedColumnCombinationMap_surjective
    {row col : Type v} [Fintype col]
    {target : col → ZMod 2} (htarget : target ≠ 0) :
    Function.Surjective (fixedColumnCombinationMap (row := row) target) := by
  have hexists : ∃ j, target j ≠ 0 := by
    by_contra hzero
    push Not at hzero
    apply htarget
    funext j
    exact hzero j
  obtain ⟨j, hj⟩ := hexists
  intro y
  let M : Matrix row col (ZMod 2) := fun i k =>
    if k = j then y i * (target j)⁻¹ else 0
  refine ⟨M, ?_⟩
  funext i
  simp [fixedColumnCombinationMap, M, Matrix.mulVec, dotProduct, hj]

/-- A fixed nonzero kernel word imposes one independent binary equation per
matrix row. -/
private theorem finrank_ker_fixedColumnCombinationMap
    {row col : Type v} [Fintype row] [Fintype col]
    {target : col → ZMod 2} (htarget : target ≠ 0) :
    Module.finrank (ZMod 2)
        (LinearMap.ker
          (fixedColumnCombinationMap (row := row) target)) =
      Fintype.card row * Fintype.card col - Fintype.card row := by
  let f := fixedColumnCombinationMap (row := row) target
  have hSurjective : Function.Surjective f :=
    fixedColumnCombinationMap_surjective (row := row) htarget
  have hRange : LinearMap.range f = ⊤ :=
    LinearMap.range_eq_top.mpr hSurjective
  have hRankNullity := f.finrank_range_add_finrank_ker
  rw [hRange, finrank_top, finrank_word_eq_length] at hRankNullity
  simp only [Length] at hRankNullity
  norm_num [f, fixedColumnCombinationMap,
    Module.finrank_matrix] at hRankNullity
  have hKernel := Nat.eq_sub_of_add_eq (by
    simpa [Nat.add_comm] using hRankNullity)
  simpa [f, Nat.mul_comm] using hKernel

/-- A kernel-code distance failure indexed by one nonzero low-weight input
word for the second random matrix. -/
private def secondDistanceBad
    {r distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (index : {target : BinaryLowWeightWords B distance // target.1 ≠ 0})
    (sample : RandomLocalCodeSample r A B) : Prop :=
  Matrix.mulVec sample.2 index.1.1 = 0

/-- Every kernel-code distance failure belongs to one explicit low-word
event. -/
private theorem secondDistanceBad_covers_not_codeB_distance
    {r distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (sample : RandomLocalCodeSample r A B)
    (hDistance :
      ¬HasMinimumDistanceAtLeast sample.codeB distance) :
    ∃ index : {target : BinaryLowWeightWords B distance // target.1 ≠ 0},
      secondDistanceBad (A := A) index sample := by
  obtain ⟨target, htarget, hkernel⟩ :=
    exists_lowWeight_kernel_of_not_codeB_distance sample hDistance
  exact ⟨⟨target, htarget⟩, hkernel⟩

/-- One fixed kernel witness leaves the first matrix free and restricts the
second matrix to the kernel of fixed-input evaluation. -/
private def secondDistanceBadEventEquiv
    {r distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (index : {target : BinaryLowWeightWords B distance // target.1 ≠ 0}) :
    {sample : RandomLocalCodeSample r A B //
      secondDistanceBad (A := A) index sample} ≃
      Matrix (ULift.{v} (Fin r)) A (ZMod 2) ×
        LinearMap.ker
          (fixedColumnCombinationMap
            (row := ULift.{v} (Fin r)) index.1.1) where
  toFun sample := ⟨sample.1.1, ⟨sample.1.2, sample.2⟩⟩
  invFun sample := ⟨⟨sample.1, sample.2.1⟩, sample.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact count for one fixed nonzero low-weight kernel witness. -/
private theorem card_secondDistanceBad
    {r distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (index : {target : BinaryLowWeightWords B distance // target.1 ≠ 0}) :
    (eventFinset (secondDistanceBad (r := r) (A := A) index)).card =
      2 ^ (r * Fintype.card A) *
        2 ^ (r * Fintype.card B - r) := by
  rw [eventFinset, ← Fintype.card_subtype,
    Fintype.card_congr (secondDistanceBadEventEquiv (r := r) index),
    Fintype.card_prod]
  rw [@Module.card_eq_pow_finrank (ZMod 2)
      (Matrix (ULift.{v} (Fin r)) A (ZMod 2)) _ _ _ _ _,
    @Module.card_eq_pow_finrank (ZMod 2)
      (LinearMap.ker
        (fixedColumnCombinationMap
          (row := ULift.{v} (Fin r)) index.1.1)) _ _ _ _ _]
  have hbaseCard : Fintype.card (ZMod 2) = 2 := ZMod.card 2
  rw [hbaseCard, Module.finrank_matrix,
    finrank_ker_fixedColumnCombinationMap index.2]
  simp

/-- The total fixed-input failure count is bounded by the binary Hamming-ball
volume times the common free-matrix/kernel cardinality. -/
private theorem sum_card_secondDistanceBad_le
    {r Delta distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta) :
    ∑ index : {target : BinaryLowWeightWords B distance // target.1 ≠ 0},
      (eventFinset
        (secondDistanceBad (r := r) (A := A) index)).card ≤
        (∑ weight ∈ Finset.range distance, Nat.choose Delta weight) *
          (2 ^ (r * Delta) * 2 ^ (r * Delta - r)) := by
  have hEach : ∀ index :
      {target : BinaryLowWeightWords B distance // target.1 ≠ 0},
      (eventFinset
        (secondDistanceBad (r := r) (A := A) index)).card =
        2 ^ (r * Delta) * 2 ^ (r * Delta - r) := by
    intro index
    rw [card_secondDistanceBad (r := r)]
    simp only [hA, hB]
  simp_rw [hEach]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  apply Nat.mul_le_mul_right
  calc
    Fintype.card
        {target : BinaryLowWeightWords B distance // target.1 ≠ 0} ≤
        Fintype.card (BinaryLowWeightWords B distance) :=
      Fintype.card_subtype_le _
    _ = ∑ weight ∈ Finset.range distance,
        Nat.choose (Fintype.card B) weight :=
      card_binaryLowWeightWords B distance
    _ = ∑ weight ∈ Finset.range distance,
        Nat.choose Delta weight := by
      rw [hB]

/-- Cancelling the common positive matrix count reduces the kernel-code
distance union bound to the finite Hamming-ball inequality `volume < 2^r`.
The positive degree ensures that the `r` constrained column equations fit
inside the `r * Delta` matrix coordinates. -/
private theorem secondDistanceBad_count_bound_of_ball_lt
    {r Delta distance : Nat} (hDelta : 0 < Delta)
    (hball :
      (∑ weight ∈ Finset.range distance, Nat.choose Delta weight) < 2 ^ r) :
    (∑ weight ∈ Finset.range distance, Nat.choose Delta weight) *
        (2 ^ (r * Delta) * 2 ^ (r * Delta - r)) <
      2 ^ (r * Delta) * 2 ^ (r * Delta) := by
  have hrle : r ≤ r * Delta := by
    simpa using Nat.mul_le_mul_left r hDelta
  have hscaled :
      (∑ weight ∈ Finset.range distance, Nat.choose Delta weight) *
          2 ^ (r * Delta - r) < 2 ^ (r * Delta) := by
    calc
      (∑ weight ∈ Finset.range distance, Nat.choose Delta weight) *
          2 ^ (r * Delta - r) <
          2 ^ r * 2 ^ (r * Delta - r) :=
        Nat.mul_lt_mul_of_pos_right hball (pow_pos (by omega) _)
      _ = 2 ^ (r * Delta) := by
        rw [← pow_add]
        congr 1
        omega
  calc
    (∑ weight ∈ Finset.range distance, Nat.choose Delta weight) *
        (2 ^ (r * Delta) * 2 ^ (r * Delta - r)) =
        2 ^ (r * Delta) *
          ((∑ weight ∈ Finset.range distance, Nat.choose Delta weight) *
            2 ^ (r * Delta - r)) := by ring
    _ < 2 ^ (r * Delta) * 2 ^ (r * Delta) :=
      Nat.mul_lt_mul_of_pos_left hscaled (pow_pos (by omega) _)

/-- The finite low-word cover proves positive probability for the kernel
code's target distance whenever its explicit numerator is smaller than the
two-matrix sample space. -/
theorem hasPositiveUniformProbability_codeB_distance_of_count_bound
    {r Delta distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (hcount :
      (∑ weight ∈ Finset.range distance, Nat.choose Delta weight) *
          (2 ^ (r * Delta) * 2 ^ (r * Delta - r)) <
        2 ^ (r * Delta) * 2 ^ (r * Delta)) :
    HasPositiveUniformProbability
      (fun sample : RandomLocalCodeSample r A B =>
        HasMinimumDistanceAtLeast sample.codeB distance) := by
  apply hasPositiveUniformProbability_of_union_bound
    (J := {target : BinaryLowWeightWords B distance // target.1 ≠ 0})
    (bad := secondDistanceBad (r := r) (A := A))
  · exact secondDistanceBad_covers_not_codeB_distance
  · rw [card_randomLocalCodeSample hA hB]
    exact (sum_card_secondDistanceBad_le hA hB).trans_lt hcount

/-- The exact Hamming-ball count, the entropy estimate, and the one-row
flooring margin together yield positive probability of the kernel local
code's prescribed relative distance. -/
theorem hasPositiveUniformProbability_codeB_distance_of_entropy_margin
    {Delta : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (rho delta : ℝ) (hA : Fintype.card A = Delta)
    (hB : Fintype.card B = Delta) (hDelta : 0 < Delta)
    (hdeltaPositive : 0 < delta) (hdeltaHalf : delta < 1 / 2)
    (hceil : 2 ≤ Nat.ceil (delta * Delta))
    (hmargin : Real.log 2 <
      (rho * Real.log 2 - Real.binEntropy delta) * (Delta : ℝ)) :
    HasPositiveUniformProbability
      (fun sample : RandomLocalCodeSample (randomRowCount rho Delta) A B =>
        HasMinimumDistanceAtLeast sample.codeB
          (Nat.ceil (delta * Delta))) := by
  have hballReal := binaryHammingBall_le_exp_binEntropy_ceilRadius
    Delta delta hDelta hdeltaPositive hdeltaHalf hceil
  have hpowReal := exp_binEntropy_lt_pow_two_randomRowCount
    rho delta Delta hmargin
  have hball :
      (∑ weight ∈ Finset.range (Nat.ceil (delta * Delta)),
        Nat.choose Delta weight) <
        2 ^ randomRowCount rho Delta := by
    exact_mod_cast hballReal.trans_lt hpowReal
  exact hasPositiveUniformProbability_codeB_distance_of_count_bound
    hA hB (secondDistanceBad_count_bound_of_ball_lt hDelta hball)

/-- Swapping the two matrices is a bijection between the corresponding
finite random experiments. -/
private def swapRandomLocalCodeSample
    (r : Nat) (A B : Type v) :
    RandomLocalCodeSample r A B ≃ RandomLocalCodeSample r B A :=
  Equiv.prodComm _ _

/-- Pulling an event back along an equivalence preserves its exact finite
cardinality. -/
private theorem card_eventFinset_comp_equiv
    {Omega : Type u} {Omega' : Type v} [Fintype Omega] [Fintype Omega']
    (equiv : Omega ≃ Omega') (event : Omega' → Prop)
    [DecidablePred event] [DecidablePred (fun sample => event (equiv sample))] :
    (eventFinset (fun sample => event (equiv sample))).card =
      (eventFinset event).card := by
  rw [eventFinset, ← Fintype.card_subtype,
    eventFinset, ← Fintype.card_subtype]
  apply Fintype.card_congr
  exact Equiv.subtypeEquiv equiv (by simp)

/-- Pointwise equivalent decidable predicates cut out event finsets with the
same cardinality, independently of which decidability instances were chosen. -/
private theorem card_eventFinset_congr
    {Omega : Type u} [Fintype Omega]
    (event event' : Omega → Prop)
    [DecidablePred event] [DecidablePred event']
    (hiff : ∀ sample, event sample ↔ event' sample) :
    (eventFinset event).card = (eventFinset event').card := by
  have heq : eventFinset event = eventFinset event' := by
    ext sample
    rw [mem_eventFinset, mem_eventFinset]
    exact hiff sample
  rw [heq]

/-- Exact cardinality transport for a first-matrix kernel-distance event after
swapping the two random matrices. -/
private theorem card_swapped_secondDistanceBad
    {r distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (index : {target : BinaryLowWeightWords A distance // target.1 ≠ 0}) :
    (eventFinset (fun sample : RandomLocalCodeSample r A B =>
      secondDistanceBad (r := r) (A := B) index
        (swapRandomLocalCodeSample r A B sample))).card =
      (eventFinset
        (secondDistanceBad (r := r) (A := B) index)).card := by
  exact card_eventFinset_comp_equiv
    (swapRandomLocalCodeSample r A B)
    (secondDistanceBad (r := r) (A := B) index)

/-- Exact cardinality transport for a second-matrix row-distance event after
swapping the two random matrices. -/
private theorem card_swapped_firstDistanceBad
    {r distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (index :
      {coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0} ×
        {target : BinaryLowWeightWords B distance // target.1 ≠ 0}) :
    (eventFinset (fun sample : RandomLocalCodeSample r A B =>
      firstDistanceBad (B := A) index
        (swapRandomLocalCodeSample r A B sample))).card =
      (eventFinset (firstDistanceBad (B := A) index)).card := by
  exact card_eventFinset_comp_equiv
    (swapRandomLocalCodeSample r A B)
    (firstDistanceBad (B := A) index)

/-- Positive uniform probability is preserved when an event is pulled back
along a finite equivalence. -/
private theorem hasPositiveUniformProbability_comp_equiv
    {Omega : Type u} {Omega' : Type v} [Fintype Omega] [Fintype Omega']
    (equiv : Omega ≃ Omega') (event : Omega' → Prop)
    [DecidablePred event] [DecidablePred (fun sample => event (equiv sample))]
    (hpositive : HasPositiveUniformProbability event) :
    HasPositiveUniformProbability (fun sample => event (equiv sample)) := by
  rw [hasPositiveUniformProbability_iff_exists] at hpositive ⊢
  obtain ⟨sample, hsample⟩ := hpositive
  exact ⟨equiv.symm sample, by simpa⟩

/-- Finite-coordinate duality is involutive at the carrier level for the
project's nondegenerate symmetric word pairing. -/
private theorem dual_dual_carrier_eq
    {F : Type u} {I : Type v} [Field F] [Fintype F] [Fintype I]
    (code : LinearCode F I) :
    code.dual.dual.carrier = code.carrier := by
  let pairing :=
    LinearMap.BilinForm.flipHom (wordPairing (F := F) (ι := I))
  have hNondegenerate : pairing.Nondegenerate :=
    (wordPairing_nondegenerate (F := F) (ι := I)).flip
  have hRefl : pairing.IsRefl := by
    intro x y hxy
    change wordPairing (F := F) (ι := I) y x = 0 at hxy
    change wordPairing (F := F) (ι := I) x y = 0
    rw [wordPairing_apply, dotProduct_comm]
    exact hxy
  change pairing.orthogonal (pairing.orthogonal code.carrier) = code.carrier
  exact pairing.orthogonal_orthogonal hNondegenerate hRefl code.carrier

/-- The first random row code's dual is the first-matrix kernel.  Swapping
the matrices therefore transfers the proved kernel-distance probability to
`codeA.dual`. -/
theorem hasPositiveUniformProbability_codeA_dual_distance_of_count_bound
    {r Delta distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (hcount :
      (∑ weight ∈ Finset.range distance, Nat.choose Delta weight) *
          (2 ^ (r * Delta) * 2 ^ (r * Delta - r)) <
        2 ^ (r * Delta) * 2 ^ (r * Delta)) :
    HasPositiveUniformProbability
      (fun sample : RandomLocalCodeSample r A B =>
        HasMinimumDistanceAtLeast sample.codeA.dual distance) := by
  have hSwapped :=
    hasPositiveUniformProbability_codeB_distance_of_count_bound
      (r := r) (A := B) (B := A) hB hA hcount
  have hTransport := hasPositiveUniformProbability_comp_equiv
    (swapRandomLocalCodeSample r A B)
    (fun sample : RandomLocalCodeSample r B A =>
      HasMinimumDistanceAtLeast sample.codeB distance)
    hSwapped
  rw [hasPositiveUniformProbability_iff_exists] at hTransport ⊢
  obtain ⟨sample, hDistance⟩ := hTransport
  refine ⟨sample, ?_⟩
  unfold HasMinimumDistanceAtLeast at hDistance ⊢
  intro word hword hwordNonzero
  apply hDistance word
  · simpa [swapRandomLocalCodeSample, RandomLocalCodeSample.codeA,
      RandomLocalCodeSample.codeB,
      parityCheckRowCode_dual_eq_kernelCode] using hword
  · exact hwordNonzero

/-- The second random kernel code's dual is the second-matrix row code.
Swapping the matrices transfers the proved row-code distance probability to
`codeB.dual`. -/
theorem hasPositiveUniformProbability_codeB_dual_distance_of_count_bound
    {r Delta distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (hcount :
      ((2 ^ r - 1) *
        (∑ weight ∈ Finset.range distance, Nat.choose Delta weight)) *
          (2 ^ (r * Delta - Delta) * 2 ^ (r * Delta)) <
        2 ^ (r * Delta) * 2 ^ (r * Delta)) :
    HasPositiveUniformProbability
      (fun sample : RandomLocalCodeSample r A B =>
        HasMinimumDistanceAtLeast sample.codeB.dual distance) := by
  have hSwapped :=
    hasPositiveUniformProbability_codeA_distance_of_count_bound
      (r := r) (A := B) (B := A) hB hA hcount
  have hTransport := hasPositiveUniformProbability_comp_equiv
    (swapRandomLocalCodeSample r A B)
    (fun sample : RandomLocalCodeSample r B A =>
      HasMinimumDistanceAtLeast sample.codeA distance)
    hSwapped
  rw [hasPositiveUniformProbability_iff_exists] at hTransport ⊢
  obtain ⟨sample, hDistance⟩ := hTransport
  refine ⟨sample, ?_⟩
  have hCarrier :
      sample.codeB.dual.carrier =
        ((swapRandomLocalCodeSample r A B sample).codeA).carrier := by
    change
      (parityCheckKernelCode (Matrix.toLin' sample.2)).dual.carrier =
        (parityCheckRowCode (Matrix.toLin' sample.2)).carrier
    rw [← parityCheckRowCode_dual_eq_kernelCode]
    exact dual_dual_carrier_eq _
  unfold HasMinimumDistanceAtLeast at hDistance ⊢
  intro word hword hwordNonzero
  apply hDistance word
  · rw [← hCarrier]
    exact hword
  · exact hwordNonzero

/-- The five bad-event families used to obtain full rank together with the
four primal/dual distance bounds on one and the same random sample. -/
private abbrev SimultaneousDistanceBadIndex
    (r distance : Nat) (A B : Type v) [Fintype A] [Fintype B] :=
  Sum
    (Bool ×
      {coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0})
    (Sum
      ({coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0} ×
        {target : BinaryLowWeightWords A distance // target.1 ≠ 0})
      (Sum
        {target : BinaryLowWeightWords B distance // target.1 ≠ 0}
        (Sum
          {target : BinaryLowWeightWords A distance // target.1 ≠ 0}
          ({coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0} ×
            {target : BinaryLowWeightWords B distance // target.1 ≠ 0}))))

/-- One tagged family contains every way that full rank or one of the four
distance clauses can fail.  The last two tags are the already-counted kernel
and row events after swapping the two random matrices. -/
private def simultaneousDistanceBad
    {r distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (index : SimultaneousDistanceBadIndex r distance A B)
    (sample : RandomLocalCodeSample r A B) : Prop :=
  match index with
  | Sum.inl rankIndex =>
      rankDependencyBad rankIndex sample
  | Sum.inr (Sum.inl firstIndex) =>
      firstDistanceBad (B := B) firstIndex sample
  | Sum.inr (Sum.inr (Sum.inl secondIndex)) =>
      secondDistanceBad (r := r) (A := A) secondIndex sample
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl firstDualIndex))) =>
      secondDistanceBad (r := r) (A := B) firstDualIndex
        (swapRandomLocalCodeSample r A B sample)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr secondDualIndex))) =>
      firstDistanceBad (B := A) secondDualIndex
        (swapRandomLocalCodeSample r A B sample)

private theorem card_simultaneousDistanceBad_rank
    {r distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (index : Bool ×
      {coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0}) :
    (eventFinset (simultaneousDistanceBad
      (distance := distance) (A := A) (B := B) (Sum.inl index))).card =
      (eventFinset (rankDependencyBad (A := A) (B := B) index)).card := by
  apply card_eventFinset_congr
  intro sample
  rfl

private theorem card_simultaneousDistanceBad_first
    {r distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (index :
      {coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0} ×
        {target : BinaryLowWeightWords A distance // target.1 ≠ 0}) :
    (eventFinset (simultaneousDistanceBad
      (B := B) (Sum.inr (Sum.inl index)))).card =
      (eventFinset (firstDistanceBad (B := B) index)).card := by
  apply card_eventFinset_congr
  intro sample
  rfl

private theorem card_simultaneousDistanceBad_second
    {r distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (index : {target : BinaryLowWeightWords B distance // target.1 ≠ 0}) :
    (eventFinset (simultaneousDistanceBad
      (r := r) (A := A) (Sum.inr (Sum.inr (Sum.inl index))))).card =
      (eventFinset (secondDistanceBad (r := r) (A := A) index)).card := by
  apply card_eventFinset_congr
  intro sample
  rfl

private theorem card_simultaneousDistanceBad_firstDual
    {r distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (index : {target : BinaryLowWeightWords A distance // target.1 ≠ 0}) :
    (eventFinset (simultaneousDistanceBad
      (r := r) (B := B)
      (Sum.inr (Sum.inr (Sum.inr (Sum.inl index)))))).card =
      (eventFinset
        (secondDistanceBad (r := r) (A := B) index)).card := by
  calc
    _ = (eventFinset (fun sample : RandomLocalCodeSample r A B =>
          secondDistanceBad (r := r) (A := B) index
            (swapRandomLocalCodeSample r A B sample))).card := by
      apply card_eventFinset_congr
      intro sample
      rfl
    _ = _ := card_swapped_secondDistanceBad index

private theorem card_simultaneousDistanceBad_secondDual
    {r distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (index :
      {coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0} ×
        {target : BinaryLowWeightWords B distance // target.1 ≠ 0}) :
    (eventFinset (simultaneousDistanceBad
      (A := A) (Sum.inr (Sum.inr (Sum.inr (Sum.inr index)))))).card =
      (eventFinset (firstDistanceBad (B := A) index)).card := by
  calc
    _ = (eventFinset (fun sample : RandomLocalCodeSample r A B =>
          firstDistanceBad (B := A) index
            (swapRandomLocalCodeSample r A B sample))).card := by
      apply card_eventFinset_congr
      intro sample
      rfl
    _ = _ := card_swapped_firstDistanceBad index

/-- Failure of any simultaneous rank/distance clause is covered by the
corresponding tagged finite bad event. -/
private theorem simultaneousDistanceBad_covers
    {r distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (sample : RandomLocalCodeSample r A B)
    (hgood : ¬(sample.HasFullRowRank ∧
      HasMinimumDistanceAtLeast sample.codeA distance ∧
      HasMinimumDistanceAtLeast sample.codeB distance ∧
      HasMinimumDistanceAtLeast sample.codeA.dual distance ∧
      HasMinimumDistanceAtLeast sample.codeB.dual distance)) :
    ∃ index : SimultaneousDistanceBadIndex r distance A B,
      simultaneousDistanceBad index sample := by
  by_cases hRank : sample.HasFullRowRank
  · by_cases hA : HasMinimumDistanceAtLeast sample.codeA distance
    · by_cases hB : HasMinimumDistanceAtLeast sample.codeB distance
      · by_cases hADual :
          HasMinimumDistanceAtLeast sample.codeA.dual distance
        · by_cases hBDual :
            HasMinimumDistanceAtLeast sample.codeB.dual distance
          · exact False.elim (hgood ⟨hRank, hA, hB, hADual, hBDual⟩)
          · have hSwapped :
                ¬HasMinimumDistanceAtLeast
                  (swapRandomLocalCodeSample r A B sample).codeA distance := by
              intro hDistance
              apply hBDual
              unfold HasMinimumDistanceAtLeast at hDistance ⊢
              intro word hword hwordNonzero
              apply hDistance word
              · have hCarrier :
                    sample.codeB.dual.carrier =
                      ((swapRandomLocalCodeSample r A B sample).codeA).carrier := by
                  change
                    (parityCheckKernelCode
                        (Matrix.toLin' sample.2)).dual.carrier =
                      (parityCheckRowCode
                        (Matrix.toLin' sample.2)).carrier
                  rw [← parityCheckRowCode_dual_eq_kernelCode]
                  exact dual_dual_carrier_eq _
                rw [← hCarrier]
                exact hword
              · exact hwordNonzero
            obtain ⟨index, hindex⟩ :=
              firstDistanceBad_covers_not_codeA_distance
                (swapRandomLocalCodeSample r A B sample) hSwapped
            exact ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inr index))), hindex⟩
        · have hSwapped :
              ¬HasMinimumDistanceAtLeast
                (swapRandomLocalCodeSample r A B sample).codeB distance := by
            intro hDistance
            apply hADual
            unfold HasMinimumDistanceAtLeast at hDistance ⊢
            intro word hword hwordNonzero
            apply hDistance word
            · simpa [swapRandomLocalCodeSample,
                RandomLocalCodeSample.codeA,
                RandomLocalCodeSample.codeB,
                parityCheckRowCode_dual_eq_kernelCode] using hword
            · exact hwordNonzero
          obtain ⟨index, hindex⟩ :=
            secondDistanceBad_covers_not_codeB_distance
              (swapRandomLocalCodeSample r A B sample) hSwapped
          exact ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inl index))), hindex⟩
      · obtain ⟨index, hindex⟩ :=
          secondDistanceBad_covers_not_codeB_distance sample hB
        exact ⟨Sum.inr (Sum.inr (Sum.inl index)), hindex⟩
    · obtain ⟨index, hindex⟩ :=
        firstDistanceBad_covers_not_codeA_distance sample hA
      exact ⟨Sum.inr (Sum.inl index), hindex⟩
  · obtain ⟨index, hindex⟩ :=
      rankDependencyBad_covers_not_fullRowRank sample hRank
    exact ⟨Sum.inl index, hindex⟩

/-- Summing the exact dependency-event counts over the two matrices and all
nonzero row combinations gives the numerator in the finite union bound. -/
private theorem sum_card_rankDependencyBad
    {r Delta : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta) :
    ∑ index : Bool ×
        {coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0},
      (eventFinset (rankDependencyBad (A := A) (B := B) index)).card =
        2 * (2 ^ r - 1) *
          (2 ^ (r * Delta - Delta) * 2 ^ (r * Delta)) := by
  have hEach : ∀ index : Bool ×
      {coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0},
      (eventFinset (rankDependencyBad (A := A) (B := B) index)).card =
        2 ^ (r * Delta - Delta) * 2 ^ (r * Delta) := by
    rintro ⟨side, ⟨coefficients, hcoefficients⟩⟩
    cases side
    · rw [eventFinset, ← Fintype.card_subtype]
      simp only [rankDependencyBad, Bool.false_eq_true, if_false]
      rw [Fintype.card_congr (firstRankDependencyEventEquiv coefficients)]
      rw [@Module.card_eq_pow_finrank (ZMod 2)
        (LinearMap.ker (fixedRowCombinationMap (col := A) coefficients) ×
          Matrix (ULift.{v} (Fin r)) B (ZMod 2)) _ _ _ _ _]
      have hbase : Fintype.card (ZMod 2) = 2 := ZMod.card 2
      rw [hbase, Module.finrank_prod,
        finrank_ker_fixedRowCombinationMap hcoefficients,
        Module.finrank_matrix, pow_add]
      simp [hA, hB]
    · rw [eventFinset, ← Fintype.card_subtype]
      simp only [rankDependencyBad, if_true]
      rw [Fintype.card_congr (secondRankDependencyEventEquiv coefficients)]
      rw [@Module.card_eq_pow_finrank (ZMod 2)
        (Matrix (ULift.{v} (Fin r)) A (ZMod 2) ×
          LinearMap.ker (fixedRowCombinationMap (col := B) coefficients))
        _ _ _ _ _]
      have hbase : Fintype.card (ZMod 2) = 2 := ZMod.card 2
      rw [hbase, Module.finrank_prod, Module.finrank_matrix,
        finrank_ker_fixedRowCombinationMap hcoefficients, pow_add]
      simp [hA, hB, Nat.mul_comm]
  simp_rw [hEach]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  simpa using card_rankDependencyIndex (ULift.{v} (Fin r))

/-- The total cardinality of the five tagged bad-event families is bounded by
one rank numerator, two generator-distance numerators, and two kernel-distance
numerators.  The duplicate terms are the two dual-distance failures transported
by the matrix-swap equivalence. -/
private theorem sum_card_simultaneousDistanceBad_le
    {r Delta distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta) :
    ∑ index : SimultaneousDistanceBadIndex r distance A B,
      (eventFinset (simultaneousDistanceBad index)).card ≤
        2 * (2 ^ r - 1) *
            (2 ^ (r * Delta - Delta) * 2 ^ (r * Delta)) +
          2 * (((2 ^ r - 1) *
              (∑ weight ∈ Finset.range distance,
                Nat.choose Delta weight)) *
            (2 ^ (r * Delta - Delta) * 2 ^ (r * Delta))) +
          2 * ((∑ weight ∈ Finset.range distance,
              Nat.choose Delta weight) *
            (2 ^ (r * Delta) * 2 ^ (r * Delta - r))) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type,
    Fintype.sum_sum_type, Fintype.sum_sum_type]
  have hRank := sum_card_rankDependencyBad (r := r) hA hB
  have hFirstA := sum_card_firstDistanceBad_le
    (r := r) (distance := distance) hA hB
  have hSecondB := sum_card_secondDistanceBad_le
    (r := r) (distance := distance) hA hB
  have hSecondA := sum_card_secondDistanceBad_le
    (r := r) (distance := distance) hB hA
  have hFirstB := sum_card_firstDistanceBad_le
    (r := r) (distance := distance) hB hA
  simp_rw [card_simultaneousDistanceBad_rank,
    card_simultaneousDistanceBad_first,
    card_simultaneousDistanceBad_second,
    card_simultaneousDistanceBad_firstDual,
    card_simultaneousDistanceBad_secondDual]
  omega

/-- Cancel the common power of two from the five-event union bound.  The
resulting inequality isolates the Hamming-ball volume, which is the quantity
controlled by the source's binary-entropy hypothesis. -/
theorem simultaneousDistance_count_bound_of_ball_bound
    {r Delta distance : Nat} (hr : 0 < r) (hrDelta : r ≤ Delta)
    (hball :
      2 * (2 ^ r - 1) +
          2 * ((2 ^ r - 1) *
            (∑ weight ∈ Finset.range distance,
              Nat.choose Delta weight)) +
          2 * ((∑ weight ∈ Finset.range distance,
              Nat.choose Delta weight) * 2 ^ (Delta - r)) <
        2 ^ Delta) :
    2 * (2 ^ r - 1) *
          (2 ^ (r * Delta - Delta) * 2 ^ (r * Delta)) +
        2 * (((2 ^ r - 1) *
            (∑ weight ∈ Finset.range distance,
              Nat.choose Delta weight)) *
          (2 ^ (r * Delta - Delta) * 2 ^ (r * Delta))) +
        2 * ((∑ weight ∈ Finset.range distance,
            Nat.choose Delta weight) *
          (2 ^ (r * Delta) * 2 ^ (r * Delta - r))) <
      2 ^ (r * Delta) * 2 ^ (r * Delta) := by
  have hDeltaLe : Delta ≤ r * Delta := by
    calc
      Delta = 1 * Delta := by omega
      _ ≤ r * Delta := Nat.mul_le_mul_right Delta hr
  have hrLe : r ≤ r * Delta := hrDelta.trans hDeltaLe
  have hSplitDelta :
      2 ^ (r * Delta) = 2 ^ (r * Delta - Delta) * 2 ^ Delta := by
    rw [← pow_add, Nat.sub_add_cancel hDeltaLe]
  have hSplitR :
      2 ^ (r * Delta - r) =
        2 ^ (r * Delta - Delta) * 2 ^ (Delta - r) := by
    rw [← pow_add]
    congr 1
    omega
  let volume := ∑ weight ∈ Finset.range distance,
    Nat.choose Delta weight
  let common := 2 ^ (r * Delta - Delta) * 2 ^ (r * Delta)
  have hcommon : 0 < common := by
    dsimp [common]
    positivity
  calc
    2 * (2 ^ r - 1) * common +
        2 * (((2 ^ r - 1) * volume) * common) +
        2 * (volume * (2 ^ (r * Delta) * 2 ^ (r * Delta - r))) =
      (2 * (2 ^ r - 1) +
          2 * ((2 ^ r - 1) * volume) +
          2 * (volume * 2 ^ (Delta - r))) * common := by
      rw [hSplitR]
      ring
    _ < 2 ^ Delta * common :=
      Nat.mul_lt_mul_of_pos_right hball hcommon
    _ = 2 ^ (r * Delta) * 2 ^ (r * Delta) := by
      dsimp [common]
      calc
        2 ^ Delta *
            (2 ^ (r * Delta - Delta) * 2 ^ (r * Delta)) =
          (2 ^ (r * Delta - Delta) * 2 ^ Delta) *
            2 ^ (r * Delta) := by ring
        _ = 2 ^ (r * Delta) * 2 ^ (r * Delta) := by
          rw [← hSplitDelta]

/-- A convenient finite form of the five-event union bound: each of its
three distinct numerators may spend less than one sixth of the ambient
binary-word count, accounting for the two symmetric occurrences of each
distance event. -/
private theorem simultaneousDistance_ball_bound_of_sixfold_components
    {r Delta distance : Nat}
    (hRank : 6 * (2 ^ r - 1) < 2 ^ Delta)
    (hGenerator :
      6 * ((2 ^ r - 1) *
        (∑ weight ∈ Finset.range distance,
          Nat.choose Delta weight)) < 2 ^ Delta)
    (hKernel :
      6 * ((∑ weight ∈ Finset.range distance,
        Nat.choose Delta weight) * 2 ^ (Delta - r)) < 2 ^ Delta) :
    2 * (2 ^ r - 1) +
        2 * ((2 ^ r - 1) *
          (∑ weight ∈ Finset.range distance,
            Nat.choose Delta weight)) +
        2 * ((∑ weight ∈ Finset.range distance,
          Nat.choose Delta weight) * 2 ^ (Delta - r)) <
      2 ^ Delta := by
  omega

/-- The analytic Hamming-ball estimate reduces the three finite sixfold
conditions to two strict exponential margins.  The generator margin also
controls the rank term because a nonempty Hamming ball contains the zero
word. -/
private theorem simultaneousDistance_sixfold_bounds_of_real_margins
    (Delta r distance : Nat) (delta : ℝ)
    (hDelta : 0 < Delta) (hrDelta : r ≤ Delta) (hDistance : 0 < distance)
    (hdeltaPositive : 0 < delta) (hdeltaHalf : delta < 1 / 2)
    (hDistanceCeil : distance = Nat.ceil (delta * Delta))
    (hceil : 2 ≤ distance)
    (hGeneratorMargin :
      6 * (((2 ^ r : Nat) : ℝ) *
        Real.exp ((Delta : ℝ) * Real.binEntropy delta)) <
        ((2 ^ Delta : Nat) : ℝ))
    (hKernelMargin :
      6 * Real.exp ((Delta : ℝ) * Real.binEntropy delta) <
        ((2 ^ r : Nat) : ℝ)) :
    6 * (2 ^ r - 1) < 2 ^ Delta ∧
      6 * ((2 ^ r - 1) *
        (∑ weight ∈ Finset.range distance, Nat.choose Delta weight)) <
        2 ^ Delta ∧
      6 * ((∑ weight ∈ Finset.range distance,
        Nat.choose Delta weight) * 2 ^ (Delta - r)) <
        2 ^ Delta := by
  let volume := ∑ weight ∈ Finset.range distance, Nat.choose Delta weight
  have hVolume : (volume : ℝ) ≤
      Real.exp ((Delta : ℝ) * Real.binEntropy delta) := by
    subst distance
    exact binaryHammingBall_le_exp_binEntropy_ceilRadius
      Delta delta hDelta hdeltaPositive hdeltaHalf hceil
  have hOne : 1 ≤ volume := by
    have hzero : 0 ∈ Finset.range distance := Finset.mem_range.mpr hDistance
    simpa [volume] using
      (Finset.single_le_sum
        (fun weight _ => Nat.zero_le (Nat.choose Delta weight)) hzero)
  have hGenerator : 6 * ((2 ^ r - 1) * volume) < 2 ^ Delta := by
    have hSub : (((2 ^ r - 1 : Nat) : ℝ)) ≤ ((2 ^ r : Nat) : ℝ) := by
      exact_mod_cast Nat.sub_le (2 ^ r) 1
    have hReal : (((6 * ((2 ^ r - 1) * volume) : Nat) : ℝ)) <
        ((2 ^ Delta : Nat) : ℝ) := by
      calc
        (((6 * ((2 ^ r - 1) * volume) : Nat) : ℝ)) =
            6 * ((2 ^ r - 1 : Nat) : ℝ) * (volume : ℝ) := by
              norm_cast
              ring
        _ ≤ 6 * ((2 ^ r : Nat) : ℝ) * (volume : ℝ) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hSub (by norm_num))
            (Nat.cast_nonneg _)
        _ ≤ 6 * ((2 ^ r : Nat) : ℝ) *
            Real.exp ((Delta : ℝ) * Real.binEntropy delta) := by
          exact mul_le_mul_of_nonneg_left hVolume (by positivity)
        _ < ((2 ^ Delta : Nat) : ℝ) := by
          simpa only [mul_assoc] using hGeneratorMargin
    exact_mod_cast hReal
  have hRank : 6 * (2 ^ r - 1) < 2 ^ Delta := by
    have hLe : (2 ^ r - 1) ≤ (2 ^ r - 1) * volume := by
      calc
        2 ^ r - 1 = (2 ^ r - 1) * 1 := by omega
        _ ≤ (2 ^ r - 1) * volume :=
          Nat.mul_le_mul_left _ hOne
    exact (Nat.mul_le_mul_left 6 hLe).trans_lt hGenerator
  have hKernelSmall : 6 * volume < 2 ^ r := by
    have hReal : (((6 * volume : Nat) : ℝ)) < ((2 ^ r : Nat) : ℝ) := by
      calc
        (((6 * volume : Nat) : ℝ)) = 6 * (volume : ℝ) := by norm_cast
        _ ≤ 6 * Real.exp ((Delta : ℝ) * Real.binEntropy delta) := by
          exact mul_le_mul_of_nonneg_left hVolume (by norm_num)
        _ < ((2 ^ r : Nat) : ℝ) := hKernelMargin
    exact_mod_cast hReal
  have hKernel : 6 * (volume * 2 ^ (Delta - r)) < 2 ^ Delta := by
    calc
      6 * (volume * 2 ^ (Delta - r)) =
          (6 * volume) * 2 ^ (Delta - r) := by ring
      _ < 2 ^ r * 2 ^ (Delta - r) :=
        Nat.mul_lt_mul_of_pos_right hKernelSmall (by positivity)
      _ = 2 ^ Delta := by
        rw [← pow_add]
        congr 1
        omega
  exact ⟨hRank, hGenerator, hKernel⟩

/-- The generator and kernel exponential margins follow from the two
entropy gaps after accounting for the single row lost when `rho * Delta` is
floored.  The kernel bound therefore reserves one extra `log 2` of margin. -/
private theorem simultaneousDistance_real_margins_of_entropy_gaps
    (rho delta : ℝ) (Delta : Nat) (hRhoNonnegative : 0 ≤ rho)
    (hGeneratorGap :
      Real.log 6 <
        ((1 - rho) * Real.log 2 - Real.binEntropy delta) * (Delta : ℝ))
    (hKernelGap :
      Real.log 6 + Real.log 2 <
        (rho * Real.log 2 - Real.binEntropy delta) * (Delta : ℝ)) :
    6 * (((2 ^ randomRowCount rho Delta : Nat) : ℝ) *
      Real.exp ((Delta : ℝ) * Real.binEntropy delta)) <
        ((2 ^ Delta : Nat) : ℝ) ∧
      6 * Real.exp ((Delta : ℝ) * Real.binEntropy delta) <
        ((2 ^ randomRowCount rho Delta : Nat) : ℝ) := by
  let r := randomRowCount rho Delta
  have hlog : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hRows : (r : ℝ) ≤ rho * Delta :=
    randomRowCount_cast_le hRhoNonnegative
  have hRowsLog := mul_le_mul_of_nonneg_right hRows hlog.le
  have hFloor : rho * Delta < (r : ℝ) + 1 :=
    randomRowCount_lt_add_one rho Delta
  have hFloorLog := mul_lt_mul_of_pos_right hFloor hlog
  have hGeneratorExponent :
      Real.log 6 +
          ((r : ℝ) * Real.log 2 +
            (Delta : ℝ) * Real.binEntropy delta) <
        (Delta : ℝ) * Real.log 2 := by
    nlinarith [hGeneratorGap, hRowsLog]
  have hKernelExponent :
      Real.log 6 + (Delta : ℝ) * Real.binEntropy delta <
        (r : ℝ) * Real.log 2 := by
    nlinarith [hKernelGap, hFloorLog]
  have hPow (k : Nat) :
      ((2 ^ k : Nat) : ℝ) =
        Real.exp ((k : ℝ) * Real.log 2) := by
    calc
      ((2 ^ k : Nat) : ℝ) = (2 : ℝ) ^ k := by norm_cast
      _ = (Real.exp (Real.log (2 : ℝ))) ^ k := by
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ = Real.exp ((k : ℝ) * Real.log 2) :=
        (Real.exp_nat_mul (Real.log (2 : ℝ)) k).symm
  constructor
  · change 6 * (((2 ^ r : Nat) : ℝ) *
        Real.exp ((Delta : ℝ) * Real.binEntropy delta)) <
      ((2 ^ Delta : Nat) : ℝ)
    calc
      6 * (((2 ^ r : Nat) : ℝ) *
          Real.exp ((Delta : ℝ) * Real.binEntropy delta)) =
          Real.exp (Real.log 6 +
            ((r : ℝ) * Real.log 2 +
              (Delta : ℝ) * Real.binEntropy delta)) := by
        rw [Real.exp_add, Real.exp_add,
          Real.exp_log (by norm_num : (0 : ℝ) < 6), ← hPow r]
      _ < Real.exp ((Delta : ℝ) * Real.log 2) :=
        Real.exp_lt_exp.mpr hGeneratorExponent
      _ = ((2 ^ Delta : Nat) : ℝ) := (hPow Delta).symm
  · change 6 * Real.exp ((Delta : ℝ) * Real.binEntropy delta) <
      ((2 ^ r : Nat) : ℝ)
    calc
      6 * Real.exp ((Delta : ℝ) * Real.binEntropy delta) =
          Real.exp (Real.log 6 +
            (Delta : ℝ) * Real.binEntropy delta) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 6)]
      _ < Real.exp ((r : ℝ) * Real.log 2) :=
        Real.exp_lt_exp.mpr hKernelExponent
      _ = ((2 ^ r : Nat) : ℝ) := (hPow r).symm

/-- Under the corrected source hypotheses `rho < 1/2` and
`h₂(delta) < rho`, both finite-degree margins needed for simultaneous
rank and distance hold once the fixed local degree is large enough. -/
private theorem exists_eventual_simultaneousDistance_entropy_margins
    (rho delta : ℝ) (hRhoHalf : rho < 1 / 2)
    (hEntropy : Real.binEntropy delta < rho * Real.log 2) :
    ∃ threshold : Nat, ∀ Delta : Nat, threshold ≤ Delta →
      Real.log 6 <
          ((1 - rho) * Real.log 2 - Real.binEntropy delta) *
            (Delta : ℝ) ∧
        Real.log 6 + Real.log 2 <
          (rho * Real.log 2 - Real.binEntropy delta) *
            (Delta : ℝ) := by
  have hlog : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hRhoLog : rho * Real.log 2 < (1 / 2 : ℝ) * Real.log 2 :=
    mul_lt_mul_of_pos_right hRhoHalf hlog
  have hGeneratorSlope :
      0 < (1 - rho) * Real.log 2 - Real.binEntropy delta := by
    nlinarith [hEntropy, hRhoLog]
  have hKernelSlope :
      0 < rho * Real.log 2 - Real.binEntropy delta := by
    linarith
  obtain ⟨generatorThreshold, hGeneratorThreshold⟩ :=
    exists_nat_gt
      (Real.log 6 /
        ((1 - rho) * Real.log 2 - Real.binEntropy delta))
  obtain ⟨kernelThreshold, hKernelThreshold⟩ :=
    exists_nat_gt
      ((Real.log 6 + Real.log 2) /
        (rho * Real.log 2 - Real.binEntropy delta))
  refine ⟨max generatorThreshold kernelThreshold, ?_⟩
  intro Delta hThreshold
  have hGeneratorLe : generatorThreshold ≤ Delta :=
    (Nat.le_max_left _ _).trans hThreshold
  have hKernelLe : kernelThreshold ≤ Delta :=
    (Nat.le_max_right _ _).trans hThreshold
  have hGeneratorCast :
      (generatorThreshold : ℝ) ≤ Delta := by
    exact_mod_cast hGeneratorLe
  have hKernelCast :
      (kernelThreshold : ℝ) ≤ Delta := by
    exact_mod_cast hKernelLe
  have hGeneratorAtThreshold :
      Real.log 6 <
        ((1 - rho) * Real.log 2 - Real.binEntropy delta) *
          (generatorThreshold : ℝ) := by
    have h := (div_lt_iff₀ hGeneratorSlope).mp hGeneratorThreshold
    nlinarith [h]
  have hKernelAtThreshold :
      Real.log 6 + Real.log 2 <
        (rho * Real.log 2 - Real.binEntropy delta) *
          (kernelThreshold : ℝ) := by
    have h := (div_lt_iff₀ hKernelSlope).mp hKernelThreshold
    nlinarith [h]
  constructor
  · have hScaled :=
      mul_le_mul_of_nonneg_left hGeneratorCast hGeneratorSlope.le
    nlinarith [hGeneratorAtThreshold, hScaled]
  · have hScaled :=
      mul_le_mul_of_nonneg_left hKernelCast hKernelSlope.le
    nlinarith [hKernelAtThreshold, hScaled]

/-- One threshold supplies every elementary finite-degree side condition
for the simultaneous local-code event: a nonzero row count, fewer rows than
columns, a nontrivial ceiling radius, and both strict entropy margins. -/
private theorem exists_eventual_simultaneousDistance_parameters
    (rho delta : ℝ) (hRhoPositive : 0 < rho)
    (hRhoHalf : rho < 1 / 2) (hdeltaPositive : 0 < delta)
    (hEntropy : Real.binEntropy delta < rho * Real.log 2) :
    ∃ threshold : Nat, ∀ Delta : Nat, threshold ≤ Delta →
      0 < Delta ∧
        0 < randomRowCount rho Delta ∧
        randomRowCount rho Delta < Delta ∧
        2 ≤ Nat.ceil (delta * Delta) ∧
        Real.log 6 <
          ((1 - rho) * Real.log 2 - Real.binEntropy delta) *
            (Delta : ℝ) ∧
        Real.log 6 + Real.log 2 <
          (rho * Real.log 2 - Real.binEntropy delta) *
            (Delta : ℝ) := by
  obtain ⟨entropyThreshold, hEntropyThreshold⟩ :=
    exists_eventual_simultaneousDistance_entropy_margins
      rho delta hRhoHalf hEntropy
  obtain ⟨rowThreshold, hRowThreshold⟩ :=
    exists_nat_gt ((1 : ℝ) / rho)
  obtain ⟨radiusThreshold, hRadiusThreshold⟩ :=
    exists_nat_gt ((1 : ℝ) / delta)
  refine ⟨max entropyThreshold (max rowThreshold radiusThreshold), ?_⟩
  intro Delta hThreshold
  have hEntropyLe : entropyThreshold ≤ Delta :=
    (Nat.le_max_left _ _).trans hThreshold
  have hRowLe : rowThreshold ≤ Delta :=
    (Nat.le_max_left _ _).trans
      ((Nat.le_max_right _ _).trans hThreshold)
  have hRadiusLe : radiusThreshold ≤ Delta :=
    (Nat.le_max_right _ _).trans
      ((Nat.le_max_right _ _).trans hThreshold)
  have hRowCast : (rowThreshold : ℝ) ≤ Delta := by
    exact_mod_cast hRowLe
  have hRadiusCast : (radiusThreshold : ℝ) ≤ Delta := by
    exact_mod_cast hRadiusLe
  have hRowAtThreshold : (1 : ℝ) < rho * rowThreshold := by
    have h := (div_lt_iff₀ hRhoPositive).mp hRowThreshold
    nlinarith [h]
  have hRadiusAtThreshold : (1 : ℝ) < delta * radiusThreshold := by
    have h := (div_lt_iff₀ hdeltaPositive).mp hRadiusThreshold
    nlinarith [h]
  have hRowLarge : (1 : ℝ) < rho * Delta := by
    have hScaled :=
      mul_le_mul_of_nonneg_left hRowCast hRhoPositive.le
    linarith
  have hRadiusLarge : (1 : ℝ) < delta * Delta := by
    have hScaled :=
      mul_le_mul_of_nonneg_left hRadiusCast hdeltaPositive.le
    linarith
  have hDeltaPositive : 0 < Delta := by
    by_contra h
    have hzero : Delta = 0 := by omega
    subst Delta
    norm_num at hRowLarge
  have hRowsPositive : 0 < randomRowCount rho Delta := by
    by_contra h
    have hzero : randomRowCount rho Delta = 0 := by omega
    have hfloor := randomRowCount_lt_add_one rho Delta
    rw [hzero] at hfloor
    norm_num at hfloor
    linarith
  have hRowsDegree : randomRowCount rho Delta < Delta :=
    randomRowCount_lt_degree hRhoPositive.le
      (by linarith : rho < 1) hDeltaPositive
  have hRadius : 2 ≤ Nat.ceil (delta * Delta) := by
    have hOne : 1 < Nat.ceil (delta * Delta) :=
      Nat.lt_ceil.mpr (by simpa only [Nat.cast_one] using hRadiusLarge)
    omega
  obtain ⟨hGeneratorGap, hKernelGap⟩ :=
    hEntropyThreshold Delta hEntropyLe
  exact ⟨hDeltaPositive, hRowsPositive, hRowsDegree, hRadius,
    hGeneratorGap, hKernelGap⟩

/-- A single finite union bound gives one random local-code sample on which
both matrices have full row rank and all four primal/dual distance bounds hold
simultaneously. -/
theorem hasPositiveUniformProbability_fullRowRank_and_distances_of_count_bound
    {r Delta distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (hcount :
      2 * (2 ^ r - 1) *
            (2 ^ (r * Delta - Delta) * 2 ^ (r * Delta)) +
          2 * (((2 ^ r - 1) *
              (∑ weight ∈ Finset.range distance,
                Nat.choose Delta weight)) *
            (2 ^ (r * Delta - Delta) * 2 ^ (r * Delta))) +
          2 * ((∑ weight ∈ Finset.range distance,
              Nat.choose Delta weight) *
            (2 ^ (r * Delta) * 2 ^ (r * Delta - r))) <
        2 ^ (r * Delta) * 2 ^ (r * Delta)) :
    HasPositiveUniformProbability
      (fun sample : RandomLocalCodeSample r A B =>
        sample.HasFullRowRank ∧
          HasMinimumDistanceAtLeast sample.codeA distance ∧
          HasMinimumDistanceAtLeast sample.codeB distance ∧
          HasMinimumDistanceAtLeast sample.codeA.dual distance ∧
          HasMinimumDistanceAtLeast sample.codeB.dual distance) := by
  rw [hasPositiveUniformProbability_iff_exists]
  by_contra hnoGood
  have hnoGood' : ∀ sample : RandomLocalCodeSample r A B,
      ¬(sample.HasFullRowRank ∧
        HasMinimumDistanceAtLeast sample.codeA distance ∧
        HasMinimumDistanceAtLeast sample.codeB distance ∧
        HasMinimumDistanceAtLeast sample.codeA.dual distance ∧
        HasMinimumDistanceAtLeast sample.codeB.dual distance) := by
    intro sample hsample
    exact hnoGood ⟨sample, hsample⟩
  let badUnion : Finset (RandomLocalCodeSample r A B) :=
    Finset.univ.biUnion fun index :
      SimultaneousDistanceBadIndex r distance A B =>
        eventFinset (simultaneousDistanceBad index)
  have hsubset :
      (Finset.univ : Finset (RandomLocalCodeSample r A B)) ⊆ badUnion := by
    intro sample _hsample
    obtain ⟨index, hindex⟩ :=
      simultaneousDistanceBad_covers sample (hnoGood' sample)
    exact Finset.mem_biUnion.mpr
      ⟨index, Finset.mem_univ index,
        (mem_eventFinset (simultaneousDistanceBad index) sample).mpr hindex⟩
  have hspaceLeUnion :
      Fintype.card (RandomLocalCodeSample r A B) ≤ badUnion.card := by
    simpa only [Finset.card_univ] using Finset.card_le_card hsubset
  have hUnionLeSum : badUnion.card ≤
      ∑ index : SimultaneousDistanceBadIndex r distance A B,
        (eventFinset (simultaneousDistanceBad index)).card := by
    exact Finset.card_biUnion_le
  have hsumLt :
      (∑ index : SimultaneousDistanceBadIndex r distance A B,
        (eventFinset (simultaneousDistanceBad index)).card) <
          Fintype.card (RandomLocalCodeSample r A B) := by
    rw [card_randomLocalCodeSample hA hB]
    exact (sum_card_simultaneousDistanceBad_le hA hB).trans_lt hcount
  exact (not_lt_of_ge (hspaceLeUnion.trans hUnionLeSum)) hsumLt

/-- Sixfold bounds on the rank, generator-distance, and kernel-distance
numerators give one positive-probability local-code draw satisfying all
five finite rank/distance requirements simultaneously. -/
theorem hasPositiveUniformProbability_fullRowRank_and_distances_of_sixfold_bounds
    {r Delta distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (hr : 0 < r) (hrDelta : r ≤ Delta)
    (hRank : 6 * (2 ^ r - 1) < 2 ^ Delta)
    (hGenerator :
      6 * ((2 ^ r - 1) *
        (∑ weight ∈ Finset.range distance,
          Nat.choose Delta weight)) < 2 ^ Delta)
    (hKernel :
      6 * ((∑ weight ∈ Finset.range distance,
        Nat.choose Delta weight) * 2 ^ (Delta - r)) < 2 ^ Delta) :
    HasPositiveUniformProbability
      (fun sample : RandomLocalCodeSample r A B =>
        sample.HasFullRowRank ∧
          HasMinimumDistanceAtLeast sample.codeA distance ∧
          HasMinimumDistanceAtLeast sample.codeB distance ∧
          HasMinimumDistanceAtLeast sample.codeA.dual distance ∧
          HasMinimumDistanceAtLeast sample.codeB.dual distance) := by
  apply hasPositiveUniformProbability_fullRowRank_and_distances_of_count_bound
    hA hB
  exact simultaneousDistance_count_bound_of_ball_bound hr hrDelta
    (simultaneousDistance_ball_bound_of_sixfold_components
      hRank hGenerator hKernel)

/-- Strict finite-degree entropy margins give one random local-code sample
with both full-rank matrices and all four primal/dual distance bounds.  In
contrast to separate positive-probability statements, this conclusion is
about a single simultaneous draw. -/
theorem hasPositiveUniformProbability_fullRowRank_and_distances_of_entropy_margins
    {Delta : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (rho delta : ℝ) (hA : Fintype.card A = Delta)
    (hB : Fintype.card B = Delta)
    (hRhoNonnegative : 0 ≤ rho) (hDelta : 0 < Delta)
    (hRows : 0 < randomRowCount rho Delta)
    (hRowsDelta : randomRowCount rho Delta ≤ Delta)
    (hdeltaPositive : 0 < delta) (hdeltaHalf : delta < 1 / 2)
    (hceil : 2 ≤ Nat.ceil (delta * Delta))
    (hGeneratorGap :
      Real.log 6 <
        ((1 - rho) * Real.log 2 - Real.binEntropy delta) * (Delta : ℝ))
    (hKernelGap :
      Real.log 6 + Real.log 2 <
        (rho * Real.log 2 - Real.binEntropy delta) * (Delta : ℝ)) :
    HasPositiveUniformProbability
      (fun sample :
          RandomLocalCodeSample (randomRowCount rho Delta) A B =>
        sample.HasFullRowRank ∧
          HasMinimumDistanceAtLeast sample.codeA
            (Nat.ceil (delta * Delta)) ∧
          HasMinimumDistanceAtLeast sample.codeB
            (Nat.ceil (delta * Delta)) ∧
          HasMinimumDistanceAtLeast sample.codeA.dual
            (Nat.ceil (delta * Delta)) ∧
          HasMinimumDistanceAtLeast sample.codeB.dual
            (Nat.ceil (delta * Delta))) := by
  obtain ⟨hGeneratorReal, hKernelReal⟩ :=
    simultaneousDistance_real_margins_of_entropy_gaps
      rho delta Delta hRhoNonnegative hGeneratorGap hKernelGap
  obtain ⟨hRank, hGenerator, hKernel⟩ :=
    simultaneousDistance_sixfold_bounds_of_real_margins
      Delta (randomRowCount rho Delta) (Nat.ceil (delta * Delta)) delta
      hDelta hRowsDelta (by omega) hdeltaPositive hdeltaHalf rfl hceil
      hGeneratorReal hKernelReal
  exact hasPositiveUniformProbability_fullRowRank_and_distances_of_sixfold_bounds
    hA hB hRows hRowsDelta hRank hGenerator hKernel

/-- At every sufficiently large fixed degree, the corrected local entropy
hypothesis yields one positive-probability draw satisfying the two full-rank
and four distance conditions simultaneously.  The degree remains a local
parameter here; selecting the source's square-complex family is separate. -/
theorem exists_eventual_hasPositiveUniformProbability_fullRowRank_and_distances
    (rho delta : ℝ) (hRhoPositive : 0 < rho)
    (hRhoHalf : rho < 1 / 2) (hdeltaPositive : 0 < delta)
    (hdeltaHalf : delta < 1 / 2)
    (hEntropy : Real.binEntropy delta < rho * Real.log 2) :
    ∃ threshold : Nat, ∀ (Delta : Nat), threshold ≤ Delta →
      ∀ (A B : Type v) [Fintype A] [Fintype B],
        Fintype.card A = Delta → Fintype.card B = Delta →
          HasPositiveUniformProbability
            (fun sample :
                RandomLocalCodeSample (randomRowCount rho Delta) A B =>
              sample.HasFullRowRank ∧
                HasMinimumDistanceAtLeast sample.codeA
                  (Nat.ceil (delta * Delta)) ∧
                HasMinimumDistanceAtLeast sample.codeB
                  (Nat.ceil (delta * Delta)) ∧
                HasMinimumDistanceAtLeast sample.codeA.dual
                  (Nat.ceil (delta * Delta)) ∧
                HasMinimumDistanceAtLeast sample.codeB.dual
                  (Nat.ceil (delta * Delta))) := by
  obtain ⟨threshold, hThreshold⟩ :=
    exists_eventual_simultaneousDistance_parameters
      rho delta hRhoPositive hRhoHalf hdeltaPositive hEntropy
  refine ⟨threshold, ?_⟩
  intro Delta hDegree A B _ _ hA hB
  obtain ⟨hDelta, hRows, hRowsDelta, hceil,
    hGeneratorGap, hKernelGap⟩ := hThreshold Delta hDegree
  exact hasPositiveUniformProbability_fullRowRank_and_distances_of_entropy_margins
    rho delta hA hB hRhoPositive.le hDelta hRows hRowsDelta.le
    hdeltaPositive hdeltaHalf hceil hGeneratorGap hKernelGap

/-- The exact dependency-event count closes the finite union bound whenever
its explicit numerator is smaller than the sample space.  This theorem keeps
the remaining arithmetic estimate separate from the finite-probability
argument. -/
theorem hasPositiveUniformProbability_fullRowRank_of_dependency_bound
    {r Delta : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (hcount :
      2 * (2 ^ r - 1) *
          (2 ^ (r * Delta - Delta) * 2 ^ (r * Delta)) <
        2 ^ (r * Delta) * 2 ^ (r * Delta)) :
    HasPositiveUniformProbability
      (fun sample : RandomLocalCodeSample r A B =>
        sample.HasFullRowRank) := by
  apply hasPositiveUniformProbability_of_union_bound
    (J := Bool ×
      {coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0})
    (bad := rankDependencyBad (A := A) (B := B))
  · exact rankDependencyBad_covers_not_fullRowRank
  · rw [sum_card_rankDependencyBad hA hB,
      card_randomLocalCodeSample hA hB]
    exact hcount

/-- If the number of random rows is strictly smaller than the common column
count, the exact dependency numerator is strictly smaller than the uniform
sample space. -/
private theorem rankDependency_count_lt_sampleSpace
    {r Delta : Nat} (hr : r < Delta) :
    2 * (2 ^ r - 1) *
          (2 ^ (r * Delta - Delta) * 2 ^ (r * Delta)) <
        2 ^ (r * Delta) * 2 ^ (r * Delta) := by
  by_cases hrZero : r = 0
  · subst r
    norm_num
  · have hrPositive : 0 < r := Nat.pos_of_ne_zero hrZero
    have hDeltaLe : Delta ≤ r * Delta := by
      have hOneLe : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hrZero
      simpa using Nat.mul_le_mul_right Delta hOneLe
    have hSplit :
        2 ^ (r * Delta) =
          2 ^ (r * Delta - Delta) * 2 ^ Delta := by
      rw [← pow_add, Nat.sub_add_cancel hDeltaLe]
    have hPred : 2 ^ r - 1 < 2 ^ r := by
      have hPowPositive : 0 < (2 : Nat) ^ r := pow_pos (by omega) r
      omega
    have hSmall : 2 * (2 ^ r - 1) < 2 ^ Delta := by
      calc
        2 * (2 ^ r - 1) < 2 * 2 ^ r :=
          Nat.mul_lt_mul_of_pos_left hPred (by omega)
        _ = 2 ^ (r + 1) := by simp [pow_succ, Nat.mul_comm]
        _ ≤ 2 ^ Delta :=
          pow_le_pow_right' (by omega : 1 ≤ (2 : Nat)) (by omega)
    have hReduced :
        2 * (2 ^ r - 1) * 2 ^ (r * Delta - Delta) <
          2 ^ (r * Delta) := by
      calc
        2 * (2 ^ r - 1) * 2 ^ (r * Delta - Delta) <
            2 ^ Delta * 2 ^ (r * Delta - Delta) :=
          Nat.mul_lt_mul_of_pos_right hSmall (pow_pos (by omega) _)
        _ = 2 ^ (r * Delta - Delta) * 2 ^ Delta := by
          rw [Nat.mul_comm]
        _ = 2 ^ (r * Delta) := hSplit.symm
    have hScaled := Nat.mul_lt_mul_of_pos_right hReduced
      (pow_pos (by omega : 0 < (2 : Nat)) (r * Delta))
    simpa only [mul_assoc] using hScaled

/-- Two independent random binary `r × Delta` matrices have full row rank
simultaneously with positive uniform probability whenever `r < Delta`. -/
theorem hasPositiveUniformProbability_fullRowRank
    {r Delta : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (hr : r < Delta) :
    HasPositiveUniformProbability
      (fun sample : RandomLocalCodeSample r A B =>
        sample.HasFullRowRank) :=
  hasPositiveUniformProbability_fullRowRank_of_dependency_bound
    hA hB (rankDependency_count_lt_sampleSpace hr)

/-- A surjective matrix parity-check map has the expected kernel-code
dimension: number of columns minus number of rows. -/
private theorem dimension_parityCheckKernelCode_of_surjective
    {F : Type u} {row col : Type v} [Field F] [Fintype F]
    [Fintype row] [Fintype col]
    (M : Matrix row col F) (hM : Function.Surjective (Matrix.toLin' M)) :
    Dimension (parityCheckKernelCode (Matrix.toLin' M)) =
      Fintype.card col - Fintype.card row := by
  rw [Dimension_eq_finrank_carrier]
  change Module.finrank F (LinearMap.ker (Matrix.toLin' M)) =
    Fintype.card col - Fintype.card row
  have hRange : LinearMap.range (Matrix.toLin' M) = ⊤ :=
    LinearMap.range_eq_top.mpr hM
  have hRankNullity := (Matrix.toLin' M).finrank_range_add_finrank_ker
  rw [hRange, finrank_top, finrank_word_eq_length,
    finrank_word_eq_length] at hRankNullity
  simp only [Length] at hRankNullity
  omega

/-- A surjective matrix map has a row code whose dimension is exactly its
number of rows. -/
private theorem dimension_parityCheckRowCode_of_surjective
    {F : Type u} {row col : Type v} [Field F] [Fintype F] [DecidableEq F]
    [Fintype row] [Fintype col]
    (M : Matrix row col F) (hM : Function.Surjective (Matrix.toLin' M)) :
    Dimension (parityCheckRowCode (Matrix.toLin' M)) = Fintype.card row := by
  let rowCode := parityCheckRowCode (Matrix.toLin' M)
  have hRange : LinearMap.range (Matrix.toLin' M) = ⊤ :=
    LinearMap.range_eq_top.mpr hM
  have hRankNullity := (Matrix.toLin' M).finrank_range_add_finrank_ker
  rw [hRange, finrank_top, finrank_word_eq_length,
    finrank_word_eq_length] at hRankNullity
  simp only [Length] at hRankNullity
  have hRowsLe : Fintype.card row ≤ Fintype.card col := by
    omega
  have hKernel := dimension_parityCheckKernelCode_of_surjective M hM
  have hDual : rowCode.dual = parityCheckKernelCode (Matrix.toLin' M) := by
    exact parityCheckRowCode_dual_eq_kernelCode (Matrix.toLin' M)
  have hDimension := rowCode.dimension_add_dual_dimension_eq_length
  rw [hDual, hKernel] at hDimension
  change Dimension rowCode = Fintype.card row
  simp only [Length] at hDimension
  omega

/-- Full row rank supplies the exact complementary local dimensions in the
successful random event. -/
theorem dimensions_of_fullRowRank
    {r Delta : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (sample : RandomLocalCodeSample r A B)
    (_hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (hFull : sample.HasFullRowRank) :
    Dimension sample.codeA = r ∧ Dimension sample.codeB = Delta - r := by
  constructor
  · simpa [RandomLocalCodeSample.codeA] using
      dimension_parityCheckRowCode_of_surjective sample.1 hFull.1
  · simpa [RandomLocalCodeSample.codeB, hB] using
      dimension_parityCheckKernelCode_of_surjective sample.2 hFull.2

/-- The finite count bound selects one local-code pair with the exact
complementary dimensions and all four primal/dual distance bounds.  The
remaining robustness clauses of `GoodLocalCodeEvent` are not assumed here. -/
theorem hasPositiveUniformProbability_dimensions_and_distances_of_count_bound
    {r Delta distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (hcount :
      2 * (2 ^ r - 1) *
            (2 ^ (r * Delta - Delta) * 2 ^ (r * Delta)) +
          2 * (((2 ^ r - 1) *
              (∑ weight ∈ Finset.range distance,
                Nat.choose Delta weight)) *
            (2 ^ (r * Delta - Delta) * 2 ^ (r * Delta))) +
          2 * ((∑ weight ∈ Finset.range distance,
              Nat.choose Delta weight) *
            (2 ^ (r * Delta) * 2 ^ (r * Delta - r))) <
        2 ^ (r * Delta) * 2 ^ (r * Delta)) :
    HasPositiveUniformProbability
      (fun sample : RandomLocalCodeSample r A B =>
        Dimension sample.codeA = r ∧
          Dimension sample.codeB = Delta - r ∧
          HasMinimumDistanceAtLeast sample.codeA distance ∧
          HasMinimumDistanceAtLeast sample.codeB distance ∧
          HasMinimumDistanceAtLeast sample.codeA.dual distance ∧
          HasMinimumDistanceAtLeast sample.codeB.dual distance) := by
  rw [hasPositiveUniformProbability_iff_exists]
  obtain ⟨sample, hFull, hDistanceA, hDistanceB,
    hDistanceADual, hDistanceBDual⟩ :=
    (hasPositiveUniformProbability_iff_exists _).mp
      (hasPositiveUniformProbability_fullRowRank_and_distances_of_count_bound
        hA hB hcount)
  obtain ⟨hDimensionA, hDimensionB⟩ :=
    dimensions_of_fullRowRank sample hA hB hFull
  exact ⟨sample, hDimensionA, hDimensionB, hDistanceA, hDistanceB,
    hDistanceADual, hDistanceBDual⟩

/-- The source-facing finite volume criterion selects one pair with the exact
local dimensions and the four distance bounds.  Its remaining numerical
input is only the binomial Hamming-ball sum, rather than the cardinality of
the entire matrix-pair sample space. -/
theorem hasPositiveUniformProbability_dimensions_and_distances_of_ball_bound
    {r Delta distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (hr : 0 < r) (hrDelta : r ≤ Delta)
    (hball :
      2 * (2 ^ r - 1) +
          2 * ((2 ^ r - 1) *
            (∑ weight ∈ Finset.range distance,
              Nat.choose Delta weight)) +
          2 * ((∑ weight ∈ Finset.range distance,
              Nat.choose Delta weight) * 2 ^ (Delta - r)) <
        2 ^ Delta) :
    HasPositiveUniformProbability
      (fun sample : RandomLocalCodeSample r A B =>
        Dimension sample.codeA = r ∧
          Dimension sample.codeB = Delta - r ∧
          HasMinimumDistanceAtLeast sample.codeA distance ∧
          HasMinimumDistanceAtLeast sample.codeB distance ∧
          HasMinimumDistanceAtLeast sample.codeA.dual distance ∧
          HasMinimumDistanceAtLeast sample.codeB.dual distance) :=
  hasPositiveUniformProbability_dimensions_and_distances_of_count_bound
    hA hB (simultaneousDistance_count_bound_of_ball_bound hr hrDelta hball)

/-! ## Finite support counting for the robustness experiment -/

private theorem hammingWeight_eq_sum_indicator_local
    {ι : Type v} [Fintype ι] (z : Word (ZMod 2) ι) :
    HammingWeight z = ∑ i, if z i ≠ 0 then 1 else 0 := by
  classical
  rw [HammingWeight, hammingSupport, Finset.card_filter]

/-- Matrix weight decomposes as a sum of column weights.  This is the
counting identity used when the source removes columns that exceed the
light-column cutoff in its punctured robustness argument. -/
private theorem hammingWeight_eq_sum_columns
    {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) :
    HammingWeight x =
      ∑ b : B, HammingWeight (columnRestriction b x) := by
  classical
  calc
    HammingWeight x =
        ∑ coordinate : A × B, if x coordinate ≠ 0 then 1 else 0 :=
      hammingWeight_eq_sum_indicator_local x
    _ = ∑ a : A, ∑ b : B, if x (a, b) ≠ 0 then 1 else 0 :=
      Fintype.sum_prod_type _
    _ = ∑ b : B, ∑ a : A, if x (a, b) ≠ 0 then 1 else 0 :=
      Finset.sum_comm
    _ = ∑ b : B, HammingWeight (columnRestriction b x) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [hammingWeight_eq_sum_indicator_local]
      rfl

/-- The overlap of two supports is the sum of its coordinate indicators. -/
private theorem supportOverlap_eq_sum_indicator
    {ι : Type v} [Fintype ι] [DecidableEq ι] (x y : Word (ZMod 2) ι) :
    (hammingSupport x ∩ hammingSupport y).card =
      ∑ i, if x i ≠ 0 ∧ y i ≠ 0 then 1 else 0 := by
  have hSet : hammingSupport x ∩ hammingSupport y =
      Finset.univ.filter (fun i => x i ≠ 0 ∧ y i ≠ 0) := by
    ext i
    simp [hammingSupport]
  rw [hSet, Finset.card_filter]

/-- Cancellation loses at most twice the overlap, without assuming the two
parts have disjoint supports. -/
private theorem hammingWeight_add_overlap_bound
    {ι : Type v} [Fintype ι] [DecidableEq ι] (x y : Word (ZMod 2) ι) :
    HammingWeight x + HammingWeight y ≤
      HammingWeight (x + y) + 2 * (hammingSupport x ∩ hammingSupport y).card := by
  rw [hammingWeight_eq_sum_indicator_local x,
    hammingWeight_eq_sum_indicator_local y,
    hammingWeight_eq_sum_indicator_local (x + y),
    supportOverlap_eq_sum_indicator]
  rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  by_cases hx : x i = 0 <;> by_cases hy : y i = 0
  · simp [hx, hy]
  · simp [hx, hy]
  · simp [hx, hy]
  · simp only [ne_eq, hx, hy, not_false_eq_true, and_self, ↓reduceIte, Pi.add_apply]
    omega

/-- Count the common support by columns. -/
private theorem supportOverlap_eq_sum_columns
    {A B : Type v} [Fintype A] [Fintype B]
    (x y : Word (ZMod 2) (A × B)) :
    (hammingSupport x ∩ hammingSupport y).card =
      ∑ b : B, (hammingSupport (columnRestriction b x) ∩
        hammingSupport (columnRestriction b y)).card := by
  rw [supportOverlap_eq_sum_indicator]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [supportOverlap_eq_sum_indicator]
  rfl

/-- Count the common support by rows. -/
private theorem supportOverlap_eq_sum_rows
    {A B : Type v} [Fintype A] [Fintype B]
    (x y : Word (ZMod 2) (A × B)) :
    (hammingSupport x ∩ hammingSupport y).card =
      ∑ a : A, (hammingSupport (rowRestriction a x) ∩
        hammingSupport (rowRestriction a y)).card := by
  rw [supportOverlap_eq_sum_indicator, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [supportOverlap_eq_sum_indicator]
  rfl

/-- Matrix weight also decomposes as a sum of row weights. -/
private theorem hammingWeight_eq_sum_rows
    {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) :
    HammingWeight x = ∑ a : A, HammingWeight (rowRestriction a x) := by
  rw [hammingWeight_eq_sum_indicator_local, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [hammingWeight_eq_sum_indicator_local]
  rfl

/-- A half-distance row support can cancel at most half of a column-code word. -/
private theorem two_supportOverlap_le_columnPart_weight
    {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (distance : Nat)
    (hDistance : HasMinimumDistanceAtLeast CA distance)
    (rowPart columnPart : Word (ZMod 2) (A × B))
    (hColumn : columnPart ∈ (columnCode (B := B) CA).carrier)
    (rows : Finset A) (hRows : 2 * rows.card ≤ distance)
    (hRowSupport : ∀ a, a ∉ rows → rowRestriction a rowPart = 0) :
    2 * (hammingSupport rowPart ∩ hammingSupport columnPart).card ≤
      HammingWeight columnPart := by
  rw [supportOverlap_eq_sum_columns, Finset.mul_sum, hammingWeight_eq_sum_columns]
  apply Finset.sum_le_sum
  intro b _
  by_cases hZero : columnRestriction b columnPart = 0
  · simp [hZero, hammingSupport, HammingWeight]
  · have hSubset : hammingSupport (columnRestriction b rowPart) ∩
        hammingSupport (columnRestriction b columnPart) ⊆ rows := by
      intro a ha
      by_contra hOutside
      have hNonzero := (Finset.mem_filter.mp (Finset.mem_inter.mp ha).1).2
      exact hNonzero (congrFun (hRowSupport a hOutside) b)
    have hCard := Finset.card_le_card hSubset
    have hMin := hDistance _ (hColumn b) hZero
    omega

/-- A half-distance column support can cancel at most half of a row-code word. -/
private theorem two_supportOverlap_le_rowPart_weight
    {A B : Type v} [Fintype A] [Fintype B]
    (CB : LinearCode (ZMod 2) B) (distance : Nat)
    (hDistance : HasMinimumDistanceAtLeast CB distance)
    (rowPart columnPart : Word (ZMod 2) (A × B))
    (hRow : rowPart ∈ (rowCode (A := A) CB).carrier)
    (columns : Finset B) (hColumns : 2 * columns.card ≤ distance)
    (hColumnSupport : ∀ b, b ∉ columns → columnRestriction b columnPart = 0) :
    2 * (hammingSupport rowPart ∩ hammingSupport columnPart).card ≤
      HammingWeight rowPart := by
  rw [supportOverlap_eq_sum_rows, Finset.mul_sum, hammingWeight_eq_sum_rows]
  apply Finset.sum_le_sum
  intro a _
  by_cases hZero : rowRestriction a rowPart = 0
  · simp [hZero, hammingSupport, HammingWeight]
  · have hSubset : hammingSupport (rowRestriction a rowPart) ∩
        hammingSupport (rowRestriction a columnPart) ⊆ columns := by
      intro b hb
      by_contra hOutside
      have hNonzero := (Finset.mem_filter.mp (Finset.mem_inter.mp hb).2).2
      exact hNonzero (congrFun (hColumnSupport b hOutside) a)
    have hCard := Finset.card_le_card hSubset
    have hMin := hDistance _ (hRow a) hZero
    omega

/-- Under the source's two half-distance budgets, neither sparse part is heavier
than their sum.  This proves the cancellation claim used by lem:d/2. -/
private theorem hammingWeight_parts_le_of_supported_decomposition
    {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (distanceA distanceB : Nat)
    (hDistanceA : HasMinimumDistanceAtLeast CA distanceA)
    (hDistanceB : HasMinimumDistanceAtLeast CB distanceB)
    (rowPart columnPart : Word (ZMod 2) (A × B))
    (hRow : rowPart ∈ (rowCode (A := A) CB).carrier)
    (hColumn : columnPart ∈ (columnCode (B := B) CA).carrier)
    (rows : Finset A) (columns : Finset B)
    (hRows : 2 * rows.card ≤ distanceA)
    (hColumns : 2 * columns.card ≤ distanceB)
    (hRowSupport : ∀ a, a ∉ rows → rowRestriction a rowPart = 0)
    (hColumnSupport : ∀ b, b ∉ columns → columnRestriction b columnPart = 0) :
    HammingWeight rowPart ≤ HammingWeight (rowPart + columnPart) ∧
      HammingWeight columnPart ≤ HammingWeight (rowPart + columnPart) := by
  have hSum := hammingWeight_add_overlap_bound rowPart columnPart
  have hOverlapColumn := two_supportOverlap_le_columnPart_weight
    CA distanceA hDistanceA rowPart columnPart hColumn rows hRows hRowSupport
  have hOverlapRow := two_supportOverlap_le_rowPart_weight
    CB distanceB hDistanceB rowPart columnPart hRow columns hColumns hColumnSupport
  constructor <;> omega

/-- The heavy columns consume at least `cutoff + 1` support coordinates
each.  This is the exact finite counting step before the source bounds the
number of columns punctured in the robustness experiment. -/
private theorem heavyColumns_card_mul_succ_le_hammingWeight
    {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) (cutoff : Nat) :
    ((Finset.univ.filter fun b : B =>
      cutoff < HammingWeight (columnRestriction b x)).card) *
        (cutoff + 1) ≤ HammingWeight x := by
  classical
  let heavy : Finset B := Finset.univ.filter fun b =>
    cutoff < HammingWeight (columnRestriction b x)
  have hHeavy (b : B) (hb : b ∈ heavy) :
      cutoff + 1 ≤ HammingWeight (columnRestriction b x) := by
    simp only [heavy, Finset.mem_filter, Finset.mem_univ,
      true_and] at hb
    omega
  change heavy.card * (cutoff + 1) ≤ HammingWeight x
  calc
    heavy.card * (cutoff + 1) = ∑ _b ∈ heavy, (cutoff + 1) := by
      simp [mul_comm]
    _ ≤ ∑ b ∈ heavy, HammingWeight (columnRestriction b x) := by
      apply Finset.sum_le_sum
      intro b hb
      exact hHeavy b hb
    _ ≤ ∑ b : B, HammingWeight (columnRestriction b x) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
      intro b _ _
      exact Nat.zero_le _
    _ = HammingWeight x := (hammingWeight_eq_sum_columns x).symm

/-- The heavy-column count is bounded by the total weight divided by the
light-column cutoff plus one. -/
private theorem heavyColumns_card_le_weight_div
    {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) (cutoff : Nat) :
    (Finset.univ.filter fun b : B =>
      cutoff < HammingWeight (columnRestriction b x)).card ≤
        HammingWeight x / (cutoff + 1) := by
  apply (Nat.le_div_iff_mul_le (by omega : 0 < cutoff + 1)).2
  exact heavyColumns_card_mul_succ_le_hammingWeight x cutoff

/-- If `w` is below the capacity of `p + 1` heavy columns, at most `p`
columns need to be punctured before every retained column is light. -/
private theorem heavyColumns_card_le_punctureBudget
    {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) (cutoff w p : Nat)
    (hWeight : HammingWeight x ≤ w)
    (hBudget : w < (p + 1) * (cutoff + 1)) :
    (Finset.univ.filter fun b : B =>
      cutoff < HammingWeight (columnRestriction b x)).card ≤ p := by
  have hHeavyWeight := heavyColumns_card_mul_succ_le_hammingWeight x cutoff
  by_contra h
  have hMany : p + 1 ≤
      (Finset.univ.filter fun b : B =>
        cutoff < HammingWeight (columnRestriction b x)).card := by
    omega
  have hMul := Nat.mul_le_mul_right (cutoff + 1) hMany
  omega

/-- Rows touched by a nonzero entry outside the heavy columns.  These are
the rows that remain after the source's heavy-column puncture. -/
private def lightRows
    {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) (cutoff : Nat) : Finset A := by
  classical
  exact Finset.univ.filter fun a =>
    ∃ b : B,
      b ∉ (Finset.univ.filter fun b : B =>
        cutoff < HammingWeight (columnRestriction b x)) ∧
      x (a, b) ≠ 0

/-- Every support coordinate is in a light row or a heavy column. -/
private theorem supportCovered_lightRows_heavyColumns
    {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) (cutoff : Nat) :
    SupportCovered x (lightRows x cutoff)
      (Finset.univ.filter fun b : B =>
        cutoff < HammingWeight (columnRestriction b x)) := by
  classical
  intro coordinate hcoordinate
  obtain ⟨a, b⟩ := coordinate
  by_cases hb : b ∈ (Finset.univ.filter fun b : B =>
      cutoff < HammingWeight (columnRestriction b x))
  · apply Finset.mem_union.mpr
    right
    exact Finset.mem_product.mpr ⟨Finset.mem_univ a, hb⟩
  · have hx : x (a, b) ≠ 0 := by
      simpa [hammingSupport] using hcoordinate
    have hb' : ¬ cutoff < HammingWeight (columnRestriction b x) := by
      intro h
      exact hb (Finset.mem_filter.mpr ⟨Finset.mem_univ b, h⟩)
    have ha : a ∈ lightRows x cutoff := by
      simp only [lightRows, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨b, hb', hx⟩
    apply Finset.mem_union.mpr
    left
    exact Finset.mem_product.mpr ⟨ha, Finset.mem_univ b⟩

/-- If no `p` rows and `p` columns cover the support, puncturing all heavy
columns (at most `p` of them) leaves more than `p` nonzero rows. -/
private theorem puncture_heavyColumns_has_many_lightRows
    {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) (cutoff w p : Nat)
    (hWeight : HammingWeight x ≤ w)
    (hBudget : w < (p + 1) * (cutoff + 1))
    (hNoCover : ∀ rows : Finset A, ∀ columns : Finset B,
      rows.card ≤ p → columns.card ≤ p →
        ¬ SupportCovered x rows columns) :
    p < (lightRows x cutoff).card := by
  have hHeavy := heavyColumns_card_le_punctureBudget x cutoff w p
    hWeight hBudget
  by_contra h
  have hRows : (lightRows x cutoff).card ≤ p := by omega
  exact hNoCover (lightRows x cutoff)
    (Finset.univ.filter fun b : B =>
      cutoff < HammingWeight (columnRestriction b x))
    hRows hHeavy (supportCovered_lightRows_heavyColumns x cutoff)

/-- Restricting to columns identifies a matrix with a choice of one low-weight
word per column.  This is the finite sample-space bijection behind the
source's count of possible punctured matrices `X_p`. -/
private def lowWeightColumnMatricesEquiv
    (A B : Type v) [Fintype A] [Fintype B] (distance : Nat) :
    {x : Word (ZMod 2) (A × B) //
      ∀ b : B, HammingWeight (columnRestriction b x) < distance} ≃
      (B → BinaryLowWeightWords A distance) where
  toFun x b := ⟨columnRestriction b x.1, x.2 b⟩
  invFun columns := ⟨fun i => (columns i.2).1 i.1, by
    intro b
    exact (columns b).2⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    obtain ⟨a, b⟩ := i
    rfl
  right_inv columns := by
    funext b
    apply Subtype.ext
    funext a
    rfl

/-- The exact number of matrices with every column in the same strict
binary Hamming ball is the ball volume raised to the column count. -/
private theorem card_lowWeightColumnMatrices
    (A B : Type v) [Fintype A] [Fintype B] [DecidableEq A]
    (distance : Nat) :
    Fintype.card {x : Word (ZMod 2) (A × B) //
      ∀ b : B, HammingWeight (columnRestriction b x) < distance} =
      (∑ weight ∈ Finset.range distance,
        Nat.choose (Fintype.card A) weight) ^ Fintype.card B := by
  classical
  rw [Fintype.card_congr (lowWeightColumnMatricesEquiv A B distance),
    Fintype.card_fun, card_binaryLowWeightWords]

/-- Puncturing `removed` leaves exactly the complementary coordinates. -/
private theorem card_keptCoordinate
    (B : Type v) [Fintype B] (removed : Finset B) :
    Fintype.card (KeptCoordinate removed) =
      Fintype.card B - removed.card := by
  classical
  rw [Fintype.card_subtype_compl (fun b : B => b ∈ removed)]
  simp [Fintype.card_subtype]

/-- Index a punctured light matrix by its set of `p` discarded columns.
This is the finite family `X_P` counted in the source's union bound. -/
private abbrev PuncturedLowWeightMatrixFamily
    (A B : Type v) [Fintype A] [Fintype B]
    (p distance : Nat) :=
  Σ removed : (Finset.univ : Finset B).powersetCard p,
    {x : Word (ZMod 2) (A × KeptCoordinate removed.1) //
      ∀ b : KeptCoordinate removed.1,
        HammingWeight (columnRestriction b x) < distance}

/-- The exact number of `p`-punctured light-matrix choices is the number of
puncture sets times the Hamming-ball volume for every retained column. -/
private theorem card_puncturedLowWeightMatrixFamily
    (A B : Type v) [Fintype A] [Fintype B] [DecidableEq A]
    (p distance : Nat) :
    Fintype.card (PuncturedLowWeightMatrixFamily A B p distance) =
      Nat.choose (Fintype.card B) p *
        (∑ weight ∈ Finset.range distance,
          Nat.choose (Fintype.card A) weight) ^ (Fintype.card B - p) := by
  classical
  let volume := ∑ weight ∈ Finset.range distance,
    Nat.choose (Fintype.card A) weight
  let choices : Finset (Finset B) :=
    (Finset.univ : Finset B).powersetCard p
  calc
    Fintype.card (PuncturedLowWeightMatrixFamily A B p distance) =
        ∑ removed : choices,
          Fintype.card {x : Word (ZMod 2)
              (A × KeptCoordinate removed.1) //
            ∀ b : KeptCoordinate removed.1,
              HammingWeight (columnRestriction b x) < distance} := by
        exact Fintype.card_sigma
    _ = ∑ _removed : choices, volume ^ (Fintype.card B - p) := by
      apply Finset.sum_congr rfl
      intro removed _
      have hcard : removed.1.card = p :=
        (Finset.mem_powersetCard.mp removed.2).2
      have hcount := card_lowWeightColumnMatrices A
        (KeptCoordinate removed.1) distance
      rw [card_keptCoordinate B removed.1, hcard] at hcount
      simpa only [volume, Fintype.card_eq_nat_card] using hcount
    _ = Nat.choose (Fintype.card B) p *
        volume ^ (Fintype.card B - p) := by
      simp [choices, Finset.sum_const,
        Finset.card_powersetCard]

/-- The source's coarse union-bound count: choose at most `2^|B|` puncture
sets and at most a full `|B|`-fold Hamming-ball choice for the retained
columns.  The strict radius is positive so the ball volume is at least one. -/
private theorem card_puncturedLowWeightMatrixFamily_le
    (A B : Type v) [Fintype A] [Fintype B] [DecidableEq A]
    (p distance : Nat) (hDistance : 0 < distance) :
    Fintype.card (PuncturedLowWeightMatrixFamily A B p distance) ≤
      2 ^ Fintype.card B *
        (∑ weight ∈ Finset.range distance,
          Nat.choose (Fintype.card A) weight) ^ Fintype.card B := by
  classical
  let volume := ∑ weight ∈ Finset.range distance,
    Nat.choose (Fintype.card A) weight
  have hOne : 1 ≤ volume := by
    have hzero : 0 ∈ Finset.range distance := Finset.mem_range.mpr hDistance
    simpa [volume] using
      (Finset.single_le_sum
        (fun weight _ => Nat.zero_le (Nat.choose (Fintype.card A) weight)) hzero)
  rw [card_puncturedLowWeightMatrixFamily]
  calc
    Nat.choose (Fintype.card B) p *
        volume ^ (Fintype.card B - p) ≤
      2 ^ Fintype.card B * volume ^ (Fintype.card B - p) :=
        Nat.mul_le_mul_right _ (Nat.choose_le_two_pow _ _)
    _ ≤ 2 ^ Fintype.card B * volume ^ Fintype.card B :=
        Nat.mul_le_mul_left _
          (pow_le_pow_right₀ hOne (Nat.sub_le _ _))

/-- Every coordinate in the support of a vector in a finite column span
already appears in the support of one of the spanning columns. -/
private theorem hammingSupport_subset_biUnion_of_mem_span
    {ι : Type v} [Fintype ι]
    (columns : Finset (Word (ZMod 2) ι))
    {x : Word (ZMod 2) ι}
    (hx : x ∈ Submodule.span (ZMod 2) (columns : Set (Word (ZMod 2) ι))) :
    hammingSupport x ⊆ columns.biUnion hammingSupport := by
  classical
  intro coordinate hcoordinate
  by_contra hmissing
  let evaluate : Word (ZMod 2) ι →ₗ[ZMod 2] ZMod 2 := {
    toFun := fun word => word coordinate
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have hspan :
      Submodule.span (ZMod 2) (columns : Set (Word (ZMod 2) ι)) ≤
        LinearMap.ker evaluate := by
    apply Submodule.span_le.mpr
    intro word hword
    change word coordinate = 0
    by_contra hnonzero
    apply hmissing
    exact Finset.mem_biUnion.mpr
      ⟨word, hword, by simpa [hammingSupport] using hnonzero⟩
  have hzero : x coordinate = 0 := by
    have hkernel := hspan hx
    change evaluate x = 0 at hkernel
    exact hkernel
  have hnonzero : x coordinate ≠ 0 := by
    simpa [hammingSupport] using hcoordinate
  exact hnonzero hzero

/-- If each member of a finite column family has weight at most `cutoff`,
the union of all row supports has size at most span rank times `cutoff`.
Choosing an independent spanning subfamily makes the rank factor exact. -/
private theorem card_biUnion_hammingSupport_le_finrank_mul
    {ι : Type v} [Fintype ι]
    (columns : Finset (Word (ZMod 2) ι)) (cutoff : Nat)
    (hLight : ∀ word ∈ columns, HammingWeight word ≤ cutoff) :
    (columns.biUnion hammingSupport).card ≤
      Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2)
          (columns : Set (Word (ZMod 2) ι))) * cutoff := by
  classical
  obtain ⟨basis, hsubset, hcard, hspan, _⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn
      (ZMod 2) (columns : Set (Word (ZMod 2) ι))
  have hcover : columns.biUnion hammingSupport ⊆
      basis.biUnion hammingSupport := by
    intro coordinate hcoordinate
    obtain ⟨word, hword, hsupport⟩ := Finset.mem_biUnion.mp hcoordinate
    have hmem : word ∈ Submodule.span (ZMod 2)
        (columns : Set (Word (ZMod 2) ι)) :=
      Submodule.subset_span hword
    rw [← hspan] at hmem
    exact hammingSupport_subset_biUnion_of_mem_span basis hmem hsupport
  calc
    (columns.biUnion hammingSupport).card ≤
        (basis.biUnion hammingSupport).card := Finset.card_le_card hcover
    _ ≤ basis.card * cutoff := by
      apply Finset.card_biUnion_le_card_mul
      intro word hword
      simpa [HammingWeight_eq_card_hammingSupport] using
        hLight word (hsubset hword)
    _ = Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2)
          (columns : Set (Word (ZMod 2) ι))) * cutoff := by
      rw [hcard]

/-- The rows retained after deleting heavy columns are precisely the union
of supports of the light column words. -/
private theorem lightRows_eq_biUnion_lightColumns
    {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) (cutoff : Nat) :
    lightRows x cutoff =
      ((Finset.univ.filter fun b : B =>
        HammingWeight (columnRestriction b x) ≤ cutoff).image
          (fun b => columnRestriction b x)).biUnion hammingSupport := by
  classical
  ext a
  constructor
  · intro ha
    obtain ⟨b, hb, hx⟩ := by
      simpa only [lightRows, Finset.mem_filter, Finset.mem_univ,
        true_and] using ha
    have hLight : HammingWeight (columnRestriction b x) ≤ cutoff :=
      Nat.le_of_not_gt hb
    apply Finset.mem_biUnion.mpr
    refine ⟨columnRestriction b x, ?_, ?_⟩
    · apply Finset.mem_image.mpr
      exact ⟨b, Finset.mem_filter.mpr
        ⟨Finset.mem_univ b, hLight⟩, rfl⟩
    · change a ∈ (Finset.univ.filter fun i : A =>
        (columnRestriction b x) i ≠ 0)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, hx⟩
  · intro ha
    obtain ⟨word, hword, hsupport⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hword
    have hLight := (Finset.mem_filter.mp hb).2
    have hNotHeavy : b ∉ (Finset.univ.filter fun b : B =>
        cutoff < HammingWeight (columnRestriction b x)) := by
      intro hHeavy
      have hGreater := (Finset.mem_filter.mp hHeavy).2
      omega
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ a, ⟨b, hNotHeavy, ?_⟩⟩
    change a ∈ (Finset.univ.filter fun i : A =>
      (columnRestriction b x) i ≠ 0) at hsupport
    exact (Finset.mem_filter.mp hsupport).2

/-- A retained light-column matrix with many nonzero rows must have large
column-span rank: this is the finite combinatorial half of the source's
rank estimate before applying the parity-check syndrome map. -/
private theorem lightRows_card_le_lightColumnSpan_finrank_mul
    {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) (cutoff : Nat) :
    (lightRows x cutoff).card ≤
      Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2)
          (((Finset.univ.filter fun b : B =>
            HammingWeight (columnRestriction b x) ≤ cutoff).image
              (fun b => columnRestriction b x)) :
                Set (Word (ZMod 2) A))) * cutoff := by
  classical
  rw [lightRows_eq_biUnion_lightColumns]
  apply card_biUnion_hammingSupport_le_finrank_mul
  intro word hword
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hword
  exact (Finset.mem_filter.mp hb).2

/-- Under the source's no-small-cover hypothesis, the light-column span
has rank large enough that `rank * cutoff` exceeds the puncture budget. -/
private theorem puncture_lightColumnSpan_rank_mul_gt_budget
    {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) (cutoff w p : Nat)
    (hWeight : HammingWeight x ≤ w)
    (hBudget : w < (p + 1) * (cutoff + 1))
    (hNoCover : ∀ rows : Finset A, ∀ columns : Finset B,
      rows.card ≤ p → columns.card ≤ p →
        ¬ SupportCovered x rows columns) :
    p < Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2)
        (((Finset.univ.filter fun b : B =>
          HammingWeight (columnRestriction b x) ≤ cutoff).image
            (fun b => columnRestriction b x)) :
              Set (Word (ZMod 2) A))) * cutoff :=
  (puncture_heavyColumns_has_many_lightRows x cutoff w p
    hWeight hBudget hNoCover).trans_le
      (lightRows_card_le_lightColumnSpan_finrank_mul x cutoff)

/-- The source's syndrome-injectivity lemma in its finite-span form.  If the
kernel code has distance at least `distance`, a collection of columns whose
combined support is smaller than `distance` contains no nonzero vector in the
kernel of the syndrome map.  This is the rank-preservation step needed after
the light-column support bound. -/
private theorem syndrome_injective_on_smallSupport_span
    {ι M : Type v} [Fintype ι] [AddCommGroup M] [Module (ZMod 2) M]
    (syndrome : Word (ZMod 2) ι →ₗ[ZMod 2] M)
    (columns : Finset (Word (ZMod 2) ι)) (distance : Nat)
    (hDistance : ∀ word, syndrome word = 0 → word ≠ 0 →
      distance ≤ HammingWeight word)
    (hSupport : (columns.biUnion hammingSupport).card < distance)
    {word : Word (ZMod 2) ι}
    (hWord : word ∈ Submodule.span (ZMod 2)
      (columns : Set (Word (ZMod 2) ι)))
    (hSyndrome : syndrome word = 0) : word = 0 := by
  classical
  by_contra hNonzero
  have hSubset := hammingSupport_subset_biUnion_of_mem_span columns hWord
  have hWeight : HammingWeight word ≤
      (columns.biUnion hammingSupport).card := by
    simpa [HammingWeight_eq_card_hammingSupport] using
      (Finset.card_le_card hSubset)
  have hMin := hDistance word hSyndrome hNonzero
  omega

/-- Applying a parity-check map preserves the rank of a family whose total
support is smaller than the distance of its kernel code. -/
private theorem syndrome_smallSupport_span_finrank_eq
    {ι M : Type v} [Fintype ι] [AddCommGroup M] [Module (ZMod 2) M]
    (syndrome : Word (ZMod 2) ι →ₗ[ZMod 2] M)
    (columns : Finset (Word (ZMod 2) ι)) (distance : Nat)
    (hDistance : ∀ word, syndrome word = 0 → word ≠ 0 →
      distance ≤ HammingWeight word)
    (hSupport : (columns.biUnion hammingSupport).card < distance) :
    Module.finrank (ZMod 2)
      ((Submodule.span (ZMod 2)
        (columns : Set (Word (ZMod 2) ι))).map syndrome) =
      Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2)
          (columns : Set (Word (ZMod 2) ι))) := by
  classical
  let span := Submodule.span (ZMod 2)
    (columns : Set (Word (ZMod 2) ι))
  have hinjective : Function.Injective (syndrome.domRestrict span) := by
    intro x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply syndrome_injective_on_smallSupport_span syndrome columns distance
      hDistance hSupport
    · exact span.sub_mem x.property y.property
    · have heq : syndrome (x : Word (ZMod 2) ι) =
          syndrome (y : Word (ZMod 2) ι) := hxy
      simpa only [map_sub, sub_eq_zero] using heq
  rw [← LinearMap.range_domRestrict]
  exact LinearMap.finrank_range_of_inj hinjective

/-- The quotient by a local code is a canonical syndrome space.  Minimum
distance alone, without choosing a parity-check basis, ensures that this
syndrome preserves the rank of any column family with small total support. -/
private theorem codeQuotient_smallSupport_span_finrank_eq
    {ι : Type v} [Fintype ι]
    (code : LinearCode (ZMod 2) ι)
    (columns : Finset (Word (ZMod 2) ι)) (distance : Nat)
    (hDistance : HasMinimumDistanceAtLeast code distance)
    (hSupport : (columns.biUnion hammingSupport).card < distance) :
    Module.finrank (ZMod 2)
      ((Submodule.span (ZMod 2)
        (columns : Set (Word (ZMod 2) ι))).map code.carrier.mkQ) =
      Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2)
          (columns : Set (Word (ZMod 2) ι))) := by
  apply syndrome_smallSupport_span_finrank_eq code.carrier.mkQ columns distance
  · intro word hKernel hNonzero
    exact hDistance word
      ((Submodule.Quotient.mk_eq_zero code.carrier).mp hKernel) hNonzero
  · exact hSupport

/-- A selected independent subfamily of light columns survives the local
code's syndrome map whenever its total possible support is below the code
distance.  The ambient family may have much larger support: this is the
selection step used in the source's rank corollary. -/
private theorem codeQuotient_lightIndependent_finrank_le
    {ι : Type v} [Fintype ι]
    (code : LinearCode (ZMod 2) ι)
    (columns basis : Finset (Word (ZMod 2) ι))
    (cutoff distance : Nat)
    (hBasis : basis ⊆ columns)
    (hIndependent : LinearIndepOn (ZMod 2) id
      (basis : Set (Word (ZMod 2) ι)))
    (hLight : ∀ word ∈ basis, HammingWeight word ≤ cutoff)
    (hCount : basis.card * cutoff < distance)
    (hDistance : HasMinimumDistanceAtLeast code distance) :
    basis.card ≤ Module.finrank (ZMod 2)
      ((Submodule.span (ZMod 2)
        (columns : Set (Word (ZMod 2) ι))).map code.carrier.mkQ) := by
  classical
  have hSupport : (basis.biUnion hammingSupport).card < distance := by
    apply lt_of_le_of_lt _ hCount
    apply Finset.card_biUnion_le_card_mul
    intro word hword
    simpa [HammingWeight_eq_card_hammingSupport] using hLight word hword
  have hRank := codeQuotient_smallSupport_span_finrank_eq
    code basis distance hDistance hSupport
  calc
    basis.card = Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2)
          (basis : Set (Word (ZMod 2) ι))) :=
      (finrank_span_finset_eq_card hIndependent).symm
    _ = Module.finrank (ZMod 2)
        ((Submodule.span (ZMod 2)
          (basis : Set (Word (ZMod 2) ι))).map code.carrier.mkQ) :=
      hRank.symm
    _ ≤ Module.finrank (ZMod 2)
        ((Submodule.span (ZMod 2)
          (columns : Set (Word (ZMod 2) ι))).map code.carrier.mkQ) :=
      Submodule.finrank_mono
        (Submodule.map_mono (Submodule.span_mono hBasis))

/-- Every requested number of independent light columns up to the column
rank survives in the code quotient, provided its support budget remains below
the local distance.  This is the quantitative form of the source's choice of
independent columns before applying syndrome injectivity. -/
private theorem codeQuotient_lightColumns_rank_le
    {ι : Type v} [Fintype ι]
    (code : LinearCode (ZMod 2) ι)
    (columns : Finset (Word (ZMod 2) ι))
    (cutoff distance rank : Nat)
    (hRank : rank ≤ Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2)
        (columns : Set (Word (ZMod 2) ι))))
    (hLight : ∀ word ∈ columns, HammingWeight word ≤ cutoff)
    (hBudget : rank * cutoff < distance)
    (hDistance : HasMinimumDistanceAtLeast code distance) :
    rank ≤ Module.finrank (ZMod 2)
      ((Submodule.span (ZMod 2)
        (columns : Set (Word (ZMod 2) ι))).map code.carrier.mkQ) := by
  classical
  obtain ⟨basis, hbasis, hcard, _, hindependent⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn
      (ZMod 2) (columns : Set (Word (ZMod 2) ι))
  obtain ⟨chosen, hChosenBasis, hChosenCard⟩ :=
    Finset.exists_subset_card_eq (hcard.symm ▸ hRank)
  have hChosenColumns : chosen ⊆ columns := by
    intro word hword
    exact hbasis (hChosenBasis hword)
  have hChosenIndependent : LinearIndepOn (ZMod 2) id
      (chosen : Set (Word (ZMod 2) ι)) := by
    apply hindependent.mono
    intro word hword
    exact hChosenBasis hword
  have hChosenLight : ∀ word ∈ chosen,
      HammingWeight word ≤ cutoff := by
    intro word hword
    exact hLight word (hChosenColumns hword)
  have hChosenBudget : chosen.card * cutoff < distance := by
    simpa only [hChosenCard] using hBudget
  simpa only [hChosenCard] using
    (codeQuotient_lightIndependent_finrank_le code columns chosen
      cutoff distance hChosenColumns hChosenIndependent hChosenLight
      hChosenBudget hDistance)

/-- After deleting heavy columns, the no-small-cover condition forces more
than `p / cutoff` independent light columns.  Provided that this many light
columns still have total support below the local distance, the same rank
survives in the local code's syndrome space. -/
private theorem puncture_lightColumnSyndrome_rank_gt_budgetDiv
    {A B : Type v} [Fintype A] [Fintype B]
    (code : LinearCode (ZMod 2) A)
    (x : Word (ZMod 2) (A × B))
    (cutoff w p distance : Nat)
    (hCutoff : 0 < cutoff)
    (hWeight : HammingWeight x ≤ w)
    (hHeavyBudget : w < (p + 1) * (cutoff + 1))
    (hNoCover : ∀ rows : Finset A, ∀ columns : Finset B,
      rows.card ≤ p → columns.card ≤ p →
        ¬ SupportCovered x rows columns)
    (hSyndromeBudget : (p / cutoff + 1) * cutoff < distance)
    (hDistance : HasMinimumDistanceAtLeast code distance) :
    p / cutoff + 1 ≤ Module.finrank (ZMod 2)
      ((Submodule.span (ZMod 2)
        (((Finset.univ.filter fun b : B =>
          HammingWeight (columnRestriction b x) ≤ cutoff).image
            (fun b => columnRestriction b x)) :
              Set (Word (ZMod 2) A))).map code.carrier.mkQ) := by
  classical
  let columns : Finset (Word (ZMod 2) A) :=
    (Finset.univ.filter fun b : B =>
      HammingWeight (columnRestriction b x) ≤ cutoff).image
        (fun b => columnRestriction b x)
  have hRank : p / cutoff + 1 ≤ Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2)
        (columns : Set (Word (ZMod 2) A))) := by
    apply Nat.succ_le_iff.mpr
    apply (Nat.div_lt_iff_lt_mul hCutoff).mpr
    exact puncture_lightColumnSpan_rank_mul_gt_budget x cutoff w p
      hWeight hHeavyBudget hNoCover
  apply codeQuotient_lightColumns_rank_le code columns cutoff distance
    (p / cutoff + 1) hRank
  · intro word hword
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hword
    exact (Finset.mem_filter.mp hb).2
  · exact hSyndromeBudget
  · exact hDistance

/-- Restrict a candidate random parity-check map to a fixed subspace of
test words.  The kernel consists exactly of maps that kill every word of that
subspace, which is the event counted in the source's `lem:randomC`. -/
private def restrictCheckMap
    {row col : Type v} [Fintype row] [Fintype col]
    (testSpace : Submodule (ZMod 2) (Word (ZMod 2) col)) :
    (Word (ZMod 2) col →ₗ[ZMod 2] Word (ZMod 2) row) →ₗ[ZMod 2]
      (testSpace →ₗ[ZMod 2] Word (ZMod 2) row) where
  toFun check := check.comp testSpace.subtype
  map_add' _ _ := by ext word coordinate; rfl
  map_smul' _ _ := by ext word coordinate; rfl

/-- Any prescribed syndromes on a subspace extend to a parity-check map on
the whole word space.  Thus restriction to the test subspace is surjective;
this is the linear-algebra source of the independent-syndrome probability. -/
private theorem restrictCheckMap_surjective
    {row col : Type v} [Fintype row] [Fintype col]
    (testSpace : Submodule (ZMod 2) (Word (ZMod 2) col)) :
    Function.Surjective (restrictCheckMap (row := row) testSpace) := by
  intro prescribed
  obtain ⟨check, hcheck⟩ := prescribed.exists_extend
  exact ⟨check, hcheck⟩

/-- The event that a random binary check map vanishes on a fixed test space
has one independent binary equation for every output coordinate and every
dimension of that test space.  This is the exact finite count behind the
source's independent-syndrome probability. -/
private theorem card_ker_restrictCheckMap
    {row col : Type v} [Fintype row] [Fintype col]
    (testSpace : Submodule (ZMod 2) (Word (ZMod 2) col)) :
    Nat.card (LinearMap.ker (restrictCheckMap (row := row) testSpace)) =
      2 ^ ((Fintype.card col - Module.finrank (ZMod 2) testSpace) *
        Fintype.card row) := by
  classical
  let f := restrictCheckMap (row := row) testSpace
  have hRange : LinearMap.range f = ⊤ :=
    LinearMap.range_eq_top.mpr (restrictCheckMap_surjective testSpace)
  have hRankNullity := f.finrank_range_add_finrank_ker
  rw [hRange, finrank_top, Module.finrank_linearMap,
    Module.finrank_linearMap] at hRankNullity
  simp only [finrank_word_eq_length, Length] at hRankNullity
  have hLe : Module.finrank (ZMod 2) testSpace ≤ Fintype.card col := by
    simpa only [finrank_word_eq_length, Length] using testSpace.finrank_le
  have hKer : Module.finrank (ZMod 2) (LinearMap.ker f) =
      (Fintype.card col - Module.finrank (ZMod 2) testSpace) *
        Fintype.card row := by
    rw [Nat.sub_mul]
    have hMul := Nat.mul_le_mul_right (Fintype.card row) hLe
    omega
  haveI : Finite (Word (ZMod 2) col →ₗ[ZMod 2]
      Word (ZMod 2) row) :=
    Finite.of_injective
      (fun check : Word (ZMod 2) col →ₗ[ZMod 2]
        Word (ZMod 2) row =>
          (check : Word (ZMod 2) col → Word (ZMod 2) row))
      (by intro check₁ check₂ h; exact LinearMap.coe_injective h)
  letI : Fintype (LinearMap.ker f) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card,
    @Module.card_eq_pow_finrank (ZMod 2) (LinearMap.ker f)
    _ _ _ _ _]
  have hbase : Fintype.card (ZMod 2) = 2 := ZMod.card 2
  rw [hbase, hKer]

/-- The standard matrix/linear-map equivalence identifies a random binary
matrix with its check map, including the event of vanishing on a fixed test
subspace. -/
private def matrixRestrictCheckKernelEquiv
    {row col : Type v} [Fintype row] [Fintype col]
    (testSpace : Submodule (ZMod 2) (Word (ZMod 2) col)) :
    {matrix : Matrix row col (ZMod 2) //
      restrictCheckMap testSpace (Matrix.toLin' matrix) = 0} ≃
      LinearMap.ker (restrictCheckMap (row := row) testSpace) where
  toFun matrix := ⟨Matrix.toLin' matrix.1, matrix.2⟩
  invFun check := ⟨Matrix.toLin'.symm check.1, by
    simpa only [LinearEquiv.apply_symm_apply, LinearMap.mem_ker] using check.2⟩
  left_inv matrix := by
    apply Subtype.ext
    exact LinearEquiv.symm_apply_apply Matrix.toLin' matrix.1
  right_inv check := by
    apply Subtype.ext
    exact LinearEquiv.apply_symm_apply Matrix.toLin' check.1

/-- Exact random-matrix form of `lem:randomC`: the number of check matrices
vanishing on a fixed `k`-dimensional test space is `2^((n-k)r)`. -/
private theorem card_matrix_restrictCheckKernel
    {row col : Type v} [Fintype row] [Fintype col]
    (testSpace : Submodule (ZMod 2) (Word (ZMod 2) col)) :
    Nat.card {matrix : Matrix row col (ZMod 2) //
      restrictCheckMap testSpace (Matrix.toLin' matrix) = 0} =
      2 ^ ((Fintype.card col - Module.finrank (ZMod 2) testSpace) *
        Fintype.card row) := by
  rw [Nat.card_congr (matrixRestrictCheckKernelEquiv testSpace)]
  exact card_ker_restrictCheckMap testSpace

/-- Integer form of the uniform probability in `lem:randomC`: exactly one
out of `2^(r k)` check matrices annihilates a fixed `k`-dimensional test
space.  This multiplicative identity avoids introducing real-valued
probabilities into the subsequent finite union bound. -/
private theorem card_matrix_restrictCheckKernel_mul_pow_eq_sampleSpace
    {row col : Type v} [Fintype row] [Fintype col]
    (testSpace : Submodule (ZMod 2) (Word (ZMod 2) col)) :
    Nat.card {matrix : Matrix row col (ZMod 2) //
      restrictCheckMap testSpace (Matrix.toLin' matrix) = 0} *
        2 ^ (Module.finrank (ZMod 2) testSpace * Fintype.card row) =
      Fintype.card (Matrix row col (ZMod 2)) := by
  rw [card_matrix_restrictCheckKernel, card_binaryMatrix]
  have hLe : Module.finrank (ZMod 2) testSpace ≤ Fintype.card col := by
    simpa only [finrank_word_eq_length, Length] using testSpace.finrank_le
  rw [← pow_add, ← Nat.add_mul, Nat.sub_add_cancel hLe,
    Nat.mul_comm (Fintype.card col) (Fintype.card row)]

/-- Restrict random check syndromes to a test space and then project away a
fixed space of syndromes supplied by deleted coordinates.  This is the
conditional linear map in the source's punctured-code lemma `lem:randomCp`. -/
private def quotientCheckRestriction
    {row col : Type v} [Fintype row] [Fintype col]
    (testSpace : Submodule (ZMod 2) (Word (ZMod 2) col))
    (deletedSyndromes : Submodule (ZMod 2) (Word (ZMod 2) row)) :
    Matrix row col (ZMod 2) →ₗ[ZMod 2]
      (testSpace →ₗ[ZMod 2] (Word (ZMod 2) row ⧸ deletedSyndromes)) where
  toFun matrix :=
    (deletedSyndromes.mkQ.comp (Matrix.toLin' matrix)).comp testSpace.subtype
  map_add' matrix₁ matrix₂ := by
    ext word
    simp
  map_smul' scalar matrix := by
    ext word
    simp

/-- Every prescribed quotient syndrome on a test space is realized by some
check matrix: lift through the quotient, then extend off the test space. -/
private theorem quotientCheckRestriction_surjective
    {row col : Type v} [Fintype row] [Fintype col]
    (testSpace : Submodule (ZMod 2) (Word (ZMod 2) col))
    (deletedSyndromes : Submodule (ZMod 2) (Word (ZMod 2) row)) :
    Function.Surjective (quotientCheckRestriction testSpace deletedSyndromes) := by
  intro prescribed
  obtain ⟨lifted, hLifted⟩ :=
    deletedSyndromes.mkQ_surjective.surjective_linearMapComp_left prescribed
  obtain ⟨check, hCheck⟩ := lifted.exists_extend
  refine ⟨Matrix.toLin'.symm check, ?_⟩
  change (deletedSyndromes.mkQ.comp
    (Matrix.toLin' (Matrix.toLin'.symm check))).comp testSpace.subtype = prescribed
  rw [LinearEquiv.apply_symm_apply, LinearMap.comp_assoc, hCheck]
  exact hLifted

/-- A projected check vanishes precisely when every tested syndrome can be
supplied by the deleted coordinates. -/
private theorem quotientCheckRestriction_eq_zero_iff
    {row col : Type v} [Fintype row] [Fintype col]
    (testSpace : Submodule (ZMod 2) (Word (ZMod 2) col))
    (deletedSyndromes : Submodule (ZMod 2) (Word (ZMod 2) row))
    (matrix : Matrix row col (ZMod 2)) :
    quotientCheckRestriction testSpace deletedSyndromes matrix = 0 ↔
      ∀ word : testSpace, Matrix.mulVec matrix word.1 ∈ deletedSyndromes := by
  rw [LinearMap.ext_iff]
  change (∀ word : testSpace,
    deletedSyndromes.mkQ (Matrix.toLin' matrix word.1) = 0) ↔ _
  simp only [Matrix.toLin'_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]

/-- With the deleted syndrome space fixed, a `k`-dimensional test space
imposes exactly `k (r-w)` binary equations, where `w` is the dimension of
the deleted syndrome space.  This is the exact conditional count used by
`lem:randomCp`. -/
private theorem card_ker_quotientCheckRestriction_mul_pow
    {row col : Type v} [Fintype row] [Fintype col]
    (testSpace : Submodule (ZMod 2) (Word (ZMod 2) col))
    (deletedSyndromes : Submodule (ZMod 2) (Word (ZMod 2) row)) :
    Fintype.card (LinearMap.ker
      (quotientCheckRestriction testSpace deletedSyndromes)) *
        2 ^ (Module.finrank (ZMod 2) testSpace *
          (Fintype.card row - Module.finrank (ZMod 2) deletedSyndromes)) =
      Fintype.card (Matrix row col (ZMod 2)) := by
  classical
  let f := quotientCheckRestriction testSpace deletedSyndromes
  have hRange : LinearMap.range f = ⊤ :=
    LinearMap.range_eq_top.mpr
      (quotientCheckRestriction_surjective testSpace deletedSyndromes)
  have hRankNullity := f.finrank_range_add_finrank_ker
  rw [hRange, finrank_top, Module.finrank_linearMap,
    Submodule.finrank_quotient, finrank_word_eq_length] at hRankNullity
  norm_num [Length, Module.finrank_matrix] at hRankNullity
  rw [@Module.card_eq_pow_finrank (ZMod 2) (LinearMap.ker f)
    _ _ _ _ _, card_binaryMatrix]
  have hbase : Fintype.card (ZMod 2) = 2 := ZMod.card 2
  rw [hbase, ← pow_add]
  congr 1
  simpa only [Nat.add_comm] using hRankNullity

/-- In particular, if at most `p` independent deleted syndromes are
available, the conditional success count is at most the fraction
`2^(-(r-p)k)` of all retained check matrices. -/
private theorem card_ker_quotientCheckRestriction_mul_pow_le
    {row col : Type v} [Fintype row] [Fintype col]
    (testSpace : Submodule (ZMod 2) (Word (ZMod 2) col))
    (deletedSyndromes : Submodule (ZMod 2) (Word (ZMod 2) row))
    (p : Nat) (hDeleted : Module.finrank (ZMod 2) deletedSyndromes ≤ p) :
    Fintype.card (LinearMap.ker
      (quotientCheckRestriction testSpace deletedSyndromes)) *
        2 ^ (Module.finrank (ZMod 2) testSpace * (Fintype.card row - p)) ≤
      Fintype.card (Matrix row col (ZMod 2)) := by
  calc
    _ ≤ Fintype.card (LinearMap.ker
        (quotientCheckRestriction testSpace deletedSyndromes)) *
          2 ^ (Module.finrank (ZMod 2) testSpace *
            (Fintype.card row - Module.finrank (ZMod 2) deletedSyndromes)) := by
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_right (by omega : 0 < 2)
      exact Nat.mul_le_mul_left _ (Nat.sub_le_sub_left hDeleted _)
    _ = _ := card_ker_quotientCheckRestriction_mul_pow testSpace deletedSyndromes

/-- Split a random check matrix into deleted and retained columns.  For a
fixed deleted block, the event that every retained test syndrome is in its
range is precisely the quotient-restriction kernel counted above. -/
private def splitPunctureCheckEventEquiv
    {row deleted kept : Type v}
    [Fintype row] [Fintype deleted] [Fintype kept]
    (testSpace : Submodule (ZMod 2) (Word (ZMod 2) kept)) :
    {sample : Matrix row deleted (ZMod 2) × Matrix row kept (ZMod 2) //
      ∀ word : testSpace, Matrix.mulVec sample.2 word.1 ∈
        LinearMap.range (Matrix.toLin' sample.1)} ≃
      Σ deletedMatrix : Matrix row deleted (ZMod 2),
        LinearMap.ker (quotientCheckRestriction testSpace
          (LinearMap.range (Matrix.toLin' deletedMatrix))) where
  toFun sample := ⟨sample.1.1, ⟨sample.1.2,
    (quotientCheckRestriction_eq_zero_iff testSpace
      (LinearMap.range (Matrix.toLin' sample.1.1)) sample.1.2).mpr sample.2⟩⟩
  invFun sample := ⟨⟨sample.1, sample.2.1⟩,
    (quotientCheckRestriction_eq_zero_iff testSpace
      (LinearMap.range (Matrix.toLin' sample.1)) sample.2.1).mp sample.2.2⟩
  left_inv sample := by
    apply Subtype.ext
    rfl
  right_inv sample := by
    cases sample
    rfl

/-- Summing the conditional count over every deleted block gives the
unconditional integer bound from `lem:randomCp`.  The number of deleted
coordinates bounds the rank of each block, so no assumption about its
random rank or any conditioning event is needed. -/
private theorem card_splitPunctureCheckEvent_mul_pow_le
    {row deleted kept : Type v}
    [Fintype row] [Fintype deleted] [Fintype kept]
    (testSpace : Submodule (ZMod 2) (Word (ZMod 2) kept)) :
    Fintype.card {sample : Matrix row deleted (ZMod 2) ×
        Matrix row kept (ZMod 2) //
      ∀ word : testSpace, Matrix.mulVec sample.2 word.1 ∈
        LinearMap.range (Matrix.toLin' sample.1)} *
      2 ^ (Module.finrank (ZMod 2) testSpace *
        (Fintype.card row - Fintype.card deleted)) ≤
      Fintype.card (Matrix row deleted (ZMod 2) ×
        Matrix row kept (ZMod 2)) := by
  classical
  rw [Fintype.card_congr (splitPunctureCheckEventEquiv testSpace),
    Fintype.card_sigma, Finset.sum_mul, Fintype.card_prod]
  calc
    _ ≤ ∑ _deletedMatrix : Matrix row deleted (ZMod 2),
        Fintype.card (Matrix row kept (ZMod 2)) := by
      apply Finset.sum_le_sum
      intro deletedMatrix _
      apply card_ker_quotientCheckRestriction_mul_pow_le
      simpa only [finrank_word_eq_length, Length] using
        (Matrix.toLin' deletedMatrix).finrank_range_le
    _ = _ := by simp

/-- A retained syndrome is supplied by deleted columns exactly when the
retained word extends to a zero-syndrome word in the split check matrix. -/
private theorem splitCheck_syndrome_mem_range_iff
    {row deleted kept : Type v}
    [Fintype row] [Fintype deleted] [Fintype kept]
    (deletedMatrix : Matrix row deleted (ZMod 2))
    (keptMatrix : Matrix row kept (ZMod 2)) (word : Word (ZMod 2) kept) :
    Matrix.mulVec keptMatrix word ∈ LinearMap.range (Matrix.toLin' deletedMatrix) ↔
      ∃ deletedWord : Word (ZMod 2) deleted,
        Matrix.mulVec (Matrix.fromCols deletedMatrix keptMatrix)
          (Sum.elim deletedWord word) = 0 := by
  simp only [Matrix.fromCols_mulVec_sumElim]
  constructor
  · rintro ⟨deletedWord, hWord⟩
    refine ⟨-deletedWord, ?_⟩
    change Matrix.mulVec deletedMatrix deletedWord = Matrix.mulVec keptMatrix word at hWord
    rw [Matrix.mulVec_neg, hWord, neg_add_cancel]
  · rintro ⟨deletedWord, hWord⟩
    refine ⟨-deletedWord, ?_⟩
    simpa only [Matrix.toLin'_apply, Matrix.mulVec_neg] using
      (eq_neg_of_add_eq_zero_right hWord).symm

/-- Decompose a check syndrome along an arbitrary finite puncture set. -/
private theorem mulVec_deleted_add_kept
    {row col : Type v} [Fintype row] [Fintype col]
    (matrix : Matrix row col (ZMod 2)) (removed : Finset col)
    (word : Word (ZMod 2) col) :
    Matrix.mulVec matrix word =
      Matrix.mulVec (matrix.submatrix id (fun i : {i // i ∈ removed} => i.1))
        (fun i => word i.1) +
      Matrix.mulVec (matrix.submatrix id (fun i : {i // i ∉ removed} => i.1))
        (fun i => word i.1) := by
  ext r
  simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Matrix.submatrix_apply, id_eq]
  calc
    _ = (∑ i ∈ removed, matrix r i * word i) +
        (∑ i ∈ removedᶜ, matrix r i * word i) :=
      (Finset.sum_add_sum_compl removed (fun i => matrix r i * word i)).symm
    _ = _ := congrArg₂ (· + ·)
      (Finset.sum_subtype removed (by simp) (fun i => matrix r i * word i))
      (Finset.sum_subtype removedᶜ (by simp) (fun i => matrix r i * word i))

/-- The retained word extends to the full kernel exactly when its syndrome
is in the image of the deleted-coordinate check block. -/
private theorem retained_word_exists_zero_syndrome_iff
    {row col : Type v} [Fintype row] [Fintype col]
    (matrix : Matrix row col (ZMod 2)) (removed : Finset col)
    (word : Word (ZMod 2) {i // i ∉ removed}) :
    (∃ fullWord : Word (ZMod 2) col, Matrix.mulVec matrix fullWord = 0 ∧
      (fun i : {i // i ∉ removed} => fullWord i.1) = word) ↔
    Matrix.mulVec (matrix.submatrix id (fun i : {i // i ∉ removed} => i.1)) word ∈
      LinearMap.range (Matrix.toLin'
        (matrix.submatrix id (fun i : {i // i ∈ removed} => i.1))) := by
  constructor
  · rintro ⟨fullWord, hZero, hKept⟩
    rw [mulVec_deleted_add_kept matrix removed, hKept] at hZero
    refine ⟨-(fun i : {i // i ∈ removed} => fullWord i.1), ?_⟩
    simpa only [Matrix.toLin'_apply, Matrix.mulVec_neg] using
      (eq_neg_of_add_eq_zero_right hZero).symm
  · rintro ⟨deletedWord, hDeleted⟩
    let fullWord : Word (ZMod 2) col := fun i =>
      if hi : i ∈ removed then -deletedWord ⟨i, hi⟩ else word ⟨i, hi⟩
    have hKept : (fun i : {i // i ∉ removed} => fullWord i.1) = word := by
      funext i
      simp [fullWord, i.2]
    have hRemoved : (fun i : {i // i ∈ removed} => fullWord i.1) = -deletedWord := by
      funext i
      simp [fullWord, i.2]
    refine ⟨fullWord, ?_, hKept⟩
    rw [mulVec_deleted_add_kept matrix removed, hKept, hRemoved, Matrix.mulVec_neg]
    change -Matrix.toLin' _ deletedWord + _ = 0
    rw [hDeleted, neg_add_cancel]

/-- The semantic carrier form of the punctured random-kernel event in
LZ22's Appendix lemma `lem:randomCp`, for any set of removed coordinates. -/
private theorem mem_punctured_parityCheckKernelCode_iff
    {row col : Type v} [Fintype row] [Fintype col]
    (matrix : Matrix row col (ZMod 2)) (removed : Finset col)
    (word : Word (ZMod 2) (KeptCoordinate removed)) :
    word ∈ (puncturedCode (parityCheckKernelCode (Matrix.toLin' matrix)) removed).carrier ↔
      Matrix.mulVec (matrix.submatrix id (fun i : KeptCoordinate removed => i.1)) word ∈
        LinearMap.range (Matrix.toLin'
          (matrix.submatrix id (fun i : {i // i ∈ removed} => i.1))) := by
  rw [mem_puncturedCode]
  change (∃ fullWord : Word (ZMod 2) col, Matrix.mulVec matrix fullWord = 0 ∧
    (fun i : KeptCoordinate removed => fullWord i.1) = word) ↔ _
  exact retained_word_exists_zero_syndrome_iff matrix removed word

/-- Split the uniform matrix sample space along the actual removed coordinates. -/
private def splitCheckMatrixEquiv
    {row col : Type v} [Fintype row] [Fintype col] (removed : Finset col) :
    Matrix row col (ZMod 2) ≃
      Matrix row {i // i ∈ removed} (ZMod 2) ×
        Matrix row (KeptCoordinate removed) (ZMod 2) where
  toFun matrix := ⟨matrix.submatrix id (fun i => i.1),
    matrix.submatrix id (fun i => i.1)⟩
  invFun blocks r i :=
    if hi : i ∈ removed then blocks.1 r ⟨i, hi⟩ else blocks.2 r ⟨i, hi⟩
  left_inv matrix := by
    funext r i
    by_cases hi : i ∈ removed <;> simp [hi, Matrix.submatrix]
  right_inv blocks := by
    apply Prod.ext
    · funext r i
      simp [Matrix.submatrix, i.2]
    · funext r i
      simp [Matrix.submatrix, i.2]

/-- Identify the actual punctured-kernel containment event with the previously
counted deleted/retained syndrome event, without changing the sample space. -/
private def puncturedCheckMatrixEventEquiv
    {row col : Type v} [Fintype row] [Fintype col]
    (removed : Finset col)
    (testSpace : Submodule (ZMod 2) (Word (ZMod 2) (KeptCoordinate removed))) :
    {matrix : Matrix row col (ZMod 2) // ∀ word : testSpace,
      word.1 ∈ (puncturedCode
        (parityCheckKernelCode (Matrix.toLin' matrix)) removed).carrier} ≃
    {sample : Matrix row {i // i ∈ removed} (ZMod 2) ×
        Matrix row (KeptCoordinate removed) (ZMod 2) //
      ∀ word : testSpace, Matrix.mulVec sample.2 word.1 ∈
        LinearMap.range (Matrix.toLin' sample.1)} := by
  refine (splitCheckMatrixEquiv removed).subtypeEquiv ?_
  intro matrix
  exact forall_congr' fun word => mem_punctured_parityCheckKernelCode_iff matrix removed word.1

/-- Transfer an integer event bound without comparing computed subtype
Fintype instances.  Cardinality is independent of those instances. -/
private theorem card_mul_le_of_equivs
    {α β γ δ : Type*}
    (events : α ≃ β) (samples : γ ≃ δ) (factor scale : Nat)
    (hFactor : factor = scale)
    (h : Nat.card β * factor ≤ Nat.card δ) :
    Nat.card α * scale ≤ Nat.card γ := by
  subst scale
  rw [Nat.card_congr events, Nat.card_congr samples]
  exact h

/-- Instance-independent form of the split-block count, proved before
specializing the coordinate types to finite-set subtypes. -/
private theorem nat_card_splitPunctureCheckEvent_mul_pow_le
    {row deleted kept : Type v}
    [Fintype row] [Fintype deleted] [Fintype kept]
    (testSpace : Submodule (ZMod 2) (Word (ZMod 2) kept)) :
    Nat.card {sample : Matrix row deleted (ZMod 2) × Matrix row kept (ZMod 2) //
      ∀ word : testSpace, Matrix.mulVec sample.2 word.1 ∈
        LinearMap.range (Matrix.toLin' sample.1)} *
      2 ^ (Module.finrank (ZMod 2) testSpace *
        (Fintype.card row - Fintype.card deleted)) ≤
      Nat.card (Matrix row deleted (ZMod 2) × Matrix row kept (ZMod 2)) := by
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact card_splitPunctureCheckEvent_mul_pow_le testSpace

/-- The actual punctured random-kernel containment event satisfies the
integer probability bound in LZ22's Appendix lemma `lem:randomCp`. -/
private theorem card_puncturedCheckMatrixEvent_mul_pow_le
    {row col : Type v} [Fintype row] [Fintype col]
    (removed : Finset col)
    (testSpace : Submodule (ZMod 2) (Word (ZMod 2) (KeptCoordinate removed))) :
    Nat.card {matrix : Matrix row col (ZMod 2) // ∀ word : testSpace,
      word.1 ∈ (puncturedCode
        (parityCheckKernelCode (Matrix.toLin' matrix)) removed).carrier} *
      2 ^ (Module.finrank (ZMod 2) testSpace *
        (Fintype.card row - removed.card)) ≤
      Nat.card (Matrix row col (ZMod 2)) := by
  have hDeleted : Fintype.card {i : col // i ∈ removed} = removed.card :=
    Fintype.card_coe removed
  have hFactor := congrArg
    (fun p => 2 ^ (Module.finrank (ZMod 2) testSpace * (Fintype.card row - p))) hDeleted
  exact card_mul_le_of_equivs
    (puncturedCheckMatrixEventEquiv removed testSpace)
    (splitCheckMatrixEquiv (row := row) removed) _ _ hFactor
    (nat_card_splitPunctureCheckEvent_mul_pow_le
      (row := row) (deleted := {i : col // i ∈ removed})
      (kept := KeptCoordinate removed) testSpace)

/-- A finite local code has a genuine matrix parity check: choose coordinates
on its quotient space and compose them with the quotient projection. -/
private theorem exists_parityCheckMatrix_ker_eq
    {A : Type v} [Fintype A]
    (code : Submodule (ZMod 2) (Word (ZMod 2) A)) :
    ∃ check : Matrix (Fin (Module.finrank (ZMod 2)
        (Word (ZMod 2) A ⧸ code))) A (ZMod 2),
      LinearMap.ker (Matrix.toLin' check) = code := by
  let coordinates := (Module.finBasis (ZMod 2)
    (Word (ZMod 2) A ⧸ code)).equivFun
  let syndrome := coordinates.toLinearMap.comp code.mkQ
  refine ⟨LinearMap.toMatrix' syndrome, ?_⟩
  rw [Matrix.toLin'_toMatrix']
  ext word
  change coordinates (code.mkQ word) = 0 ↔ word ∈ code
  constructor
  · intro h
    apply (Submodule.Quotient.mk_eq_zero code).mp
    apply coordinates.injective
    simpa only [Submodule.mkQ_apply, map_zero] using h
  · intro h
    have hZero := (Submodule.Quotient.mk_eq_zero code).mpr h
    simp only [Submodule.mkQ_apply, hZero, map_zero]

/-- Words supported on a fixed coordinate set form a linear subspace. -/
private def supportedWordSpace
    {A : Type v} [Fintype A] (support : Finset A) :
    Submodule (ZMod 2) (Word (ZMod 2) A) where
  carrier := {word | ∀ a, a ∉ support → word a = 0}
  zero_mem' := by intro a _; rfl
  add_mem' := by
    intro x y hx hy a ha
    simp only [Pi.add_apply, hx a ha, hy a ha, zero_add]
  smul_mem' := by
    intro scalar x hx a ha
    simp only [Pi.smul_apply, hx a ha, smul_zero]

/-- The support budget bounds every word in the coordinate-supported subspace. -/
private theorem hammingWeight_le_of_mem_supportedWordSpace
    {A : Type v} [Fintype A] (support : Finset A)
    {word : Word (ZMod 2) A} (hWord : word ∈ supportedWordSpace support) :
    HammingWeight word ≤ support.card := by
  apply Finset.card_le_card
  intro a ha
  by_contra hOutside
  exact (Finset.mem_filter.mp ha).2 (hWord a hOutside)

/-- A distance larger than the coordinate support makes the restricted check
injective; the conclusion uses the actual kernel condition, not a rank premise. -/
private theorem check_supportedWordSpace_ker_eq_bot
    {A M : Type v} [Fintype A] [AddCommGroup M] [Module (ZMod 2) M]
    (check : Word (ZMod 2) A →ₗ[ZMod 2] M)
    (support : Finset A) (distance : Nat)
    (hDistance : ∀ word, check word = 0 → word ≠ 0 →
      distance ≤ HammingWeight word)
    (hSupport : support.card < distance) :
    LinearMap.ker (check.domRestrict (supportedWordSpace support)) = ⊥ := by
  apply LinearMap.ker_eq_bot.mpr
  intro x y hxy
  apply Subtype.ext
  apply sub_eq_zero.mp
  by_contra hNonzero
  have hZero : check ((x : Word (ZMod 2) A) - y) = 0 := by
    change check (x : Word (ZMod 2) A) = check (y : Word (ZMod 2) A) at hxy
    simpa only [map_sub, sub_eq_zero] using hxy
  have hWeight := hammingWeight_le_of_mem_supportedWordSpace support
    ((supportedWordSpace support).sub_mem x.property y.property)
  have hMin := hDistance _ hZero hNonzero
  omega

/-- The inverse on a supported subspace extends linearly to all syndromes.
Its output remains supported, and it reconstructs every attainable syndrome. -/
private theorem exists_supportedWordRecovery
    {A M : Type v} [Fintype A] [AddCommGroup M] [Module (ZMod 2) M]
    (check : Word (ZMod 2) A →ₗ[ZMod 2] M)
    (support : Finset A)
    (hInjective : LinearMap.ker
      (check.domRestrict (supportedWordSpace support)) = ⊥) :
    ∃ recovery : M →ₗ[ZMod 2] Word (ZMod 2) A,
      LinearMap.range recovery ≤ supportedWordSpace support ∧
      (∀ word ∈ supportedWordSpace support, recovery (check word) = word) ∧
      (∀ syndrome ∈ (supportedWordSpace support).map check,
        check (recovery syndrome) = syndrome) := by
  let space := supportedWordSpace support
  obtain ⟨inverse, hInverse⟩ :=
    (check.domRestrict space).exists_leftInverse_of_injective hInjective
  let recovery := space.subtype.comp inverse
  have hRecover : ∀ word ∈ space, recovery (check word) = word := by
    intro word hWord
    exact congrArg Subtype.val (LinearMap.congr_fun hInverse ⟨word, hWord⟩)
  refine ⟨recovery, ?_, hRecover, ?_⟩
  · rintro _ ⟨syndrome, rfl⟩
    exact (inverse syndrome).property
  · intro syndrome hSyndrome
    obtain ⟨word, hWord, rfl⟩ := hSyndrome
    rw [hRecover word hWord]

/-- A complement projection gives a genuine square parity-check matrix.
Its row index stays `A`, avoiding quotient-dimension-dependent finite instances;
redundant check rows do not change the kernel or the syndrome-rank argument. -/
private theorem exists_squareParityCheckMatrix_ker_eq
    {A : Type v} [Fintype A]
    (code : Submodule (ZMod 2) (Word (ZMod 2) A)) :
    ∃ check : Matrix A A (ZMod 2), LinearMap.ker (Matrix.toLin' check) = code := by
  obtain ⟨complement, hComplement⟩ := code.exists_isCompl
  refine ⟨LinearMap.toMatrix' (complement.projection code hComplement.symm), ?_⟩
  rw [Matrix.toLin'_toMatrix']
  exact Submodule.ker_projection hComplement.symm

/-- Equal kernels make a concrete check and the canonical code quotient preserve
exactly the same dimension on every test subspace. -/
private theorem check_map_finrank_eq_quotient
    {A R : Type v} [Fintype A] [Fintype R]
    (code : Submodule (ZMod 2) (Word (ZMod 2) A))
    (check : Matrix R A (ZMod 2))
    (hKernel : LinearMap.ker (Matrix.toLin' check) = code)
    (space : Submodule (ZMod 2) (Word (ZMod 2) A)) :
    Module.finrank (ZMod 2) (space.map (Matrix.toLin' check)) =
      Module.finrank (ZMod 2) (space.map code.mkQ) := by
  let lifted := code.liftQ (Matrix.toLin' check) hKernel.symm.le
  have hInjective : Function.Injective lifted :=
    LinearMap.ker_eq_bot.mp
      (code.ker_liftQ_eq_bot (Matrix.toLin' check) hKernel.symm.le hKernel.le)
  calc
    Module.finrank (ZMod 2) (space.map (Matrix.toLin' check)) =
        Module.finrank (ZMod 2) ((space.map code.mkQ).map lifted) := by
      rw [← Submodule.map_comp, Submodule.liftQ_mkQ]
    _ = Module.finrank (ZMod 2) (space.map code.mkQ) := by
      rw [← LinearMap.range_domRestrict]
      apply LinearMap.finrank_range_of_inj
      exact hInjective.comp Subtype.val_injective

/-- The syndrome column space has the same dimension as its row space.
This is the row/column-rank bridge in the source's fixed-matrix estimate. -/
private theorem syndrome_columnSpan_finrank_eq_rowSpan
    {A B R : Type v} [Fintype A] [Fintype B] [Fintype R]
    (check : Matrix R A (ZMod 2)) (x : Word (ZMod 2) (A × B)) :
    Module.finrank (ZMod 2)
      ((Submodule.span (ZMod 2) (Set.range fun b : B =>
        columnRestriction b x)).map (Matrix.toLin' check)) =
      Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range fun r : R =>
          (fun b => Matrix.mulVec check (columnRestriction b x) r))) := by
  let syndrome : Matrix R B (ZMod 2) :=
    fun r b => Matrix.mulVec check (columnRestriction b x) r
  have hSpace :
      (Submodule.span (ZMod 2) (Set.range fun b : B =>
        columnRestriction b x)).map (Matrix.toLin' check) =
      Submodule.span (ZMod 2) (Set.range syndrome.col) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [hSpace, ← syndrome.rank_eq_finrank_span_cols,
    syndrome.rank_eq_finrank_span_row]
  rfl

/-- A genuine parity check transports the local code quotient's column rank
to the row space used by the punctured random-code counting bound. -/
private theorem check_columnQuotient_finrank_eq_rowSpan
    {A B R : Type v} [Fintype A] [Fintype B] [Fintype R]
    (code : Submodule (ZMod 2) (Word (ZMod 2) A))
    (check : Matrix R A (ZMod 2))
    (hKernel : LinearMap.ker (Matrix.toLin' check) = code)
    (x : Word (ZMod 2) (A × B)) :
    Module.finrank (ZMod 2)
      ((Submodule.span (ZMod 2) (Set.range fun b : B =>
        columnRestriction b x)).map code.mkQ) =
      Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range fun r : R =>
          (fun b => Matrix.mulVec check (columnRestriction b x) r))) := by
  rw [← check_map_finrank_eq_quotient code check hKernel]
  exact syndrome_columnSpan_finrank_eq_rowSpan check x

/-- Transport a finite-family quotient-rank lower bound to syndrome rows. -/
private theorem check_columnQuotient_rank_le_rowSpan
    {A B R : Type v} [Fintype A] [Fintype B] [Fintype R]
    (code : Submodule (ZMod 2) (Word (ZMod 2) A))
    (check : Matrix R A (ZMod 2))
    (hKernel : LinearMap.ker (Matrix.toLin' check) = code)
    (x : Word (ZMod 2) (A × B)) (rank : Nat)
    (hRank : rank ≤ Module.finrank (ZMod 2)
      ((Submodule.span (ZMod 2)
        ((Finset.univ.image fun b : B => columnRestriction b x) :
          Set (Word (ZMod 2) A))).map code.mkQ)) :
    rank ≤ Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range fun r : R =>
        (fun b => Matrix.mulVec check (columnRestriction b x) r))) := by
  have hColumns :
      ((Finset.univ.image fun b : B => columnRestriction b x) :
        Set (Word (ZMod 2) A)) =
      Set.range (fun b : B => columnRestriction b x) := by
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rw [hColumns, check_columnQuotient_finrank_eq_rowSpan code check hKernel x] at hRank
  exact hRank


/-- Independent light columns below the local-distance support budget force
the same lower bound on the concrete parity-check syndrome's row rank.
The check must have exactly the local code as its kernel. -/
private theorem check_lightColumns_rowSpan_rank_le
    {A B R : Type v} [Fintype A] [Fintype B] [Fintype R]
    (code : LinearCode (ZMod 2) A) (check : Matrix R A (ZMod 2))
    (hKernel : LinearMap.ker (Matrix.toLin' check) = code.carrier)
    (x : Word (ZMod 2) (A × B)) (cutoff distance rank : Nat)
    (hRank : rank ≤ Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2)
        ((Finset.univ.image fun b : B => columnRestriction b x) :
          Set (Word (ZMod 2) A))))
    (hLight : ∀ b : B, HammingWeight (columnRestriction b x) ≤ cutoff)
    (hBudget : rank * cutoff < distance)
    (hDistance : HasMinimumDistanceAtLeast code distance) :
    rank ≤ Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range fun r : R =>
        (fun b => Matrix.mulVec check (columnRestriction b x) r))) := by
  apply check_columnQuotient_rank_le_rowSpan code.carrier check hKernel x rank
  apply codeQuotient_lightColumns_rank_le code _ cutoff distance rank hRank
  · intro word hword
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hword
    exact hLight b
  · exact hBudget
  · exact hDistance

/-- A dual-tensor word has each check-syndrome row in the row code
whenever the check annihilates the column code. -/
private theorem syndrome_row_mem_of_mem_dualTensorCode
    {A B R : Type v} [Fintype A] [Fintype B] [Fintype R]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (check : Matrix R A (ZMod 2))
    (hCheck : CA.carrier ≤ LinearMap.ker (Matrix.toLin' check))
    (x : Word (ZMod 2) (A × B))
    (hx : x ∈ (dualTensorCode CA CB).carrier) (r : R) :
    (fun b => Matrix.mulVec check (columnRestriction b x) r) ∈ CB.carrier := by
  obtain ⟨columnPart, hColumn, rowPart, hRow, hParts⟩ := Submodule.mem_sup.mp hx
  have hZero : ∀ b, Matrix.mulVec check (columnRestriction b columnPart) = 0 := by
    intro b
    exact hCheck (hColumn b)
  have hRows :
      (fun b => Matrix.mulVec check (columnRestriction b x) r) =
        ∑ a : A, check r a • rowRestriction a rowPart := by
    funext b
    rw [← hParts, map_add, Matrix.mulVec_add, hZero, zero_add]
    simp [Matrix.mulVec, dotProduct, rowRestriction, columnRestriction]
  rw [hRows]
  exact CB.carrier.sum_mem fun a _ => CB.carrier.smul_mem (check r a) (hRow a)

/-- Outside a covering column set, each column is supported on the covering rows. -/
private theorem column_mem_supportedWordSpace_of_supportCovered
    {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) (rows : Finset A) (columns : Finset B)
    (hCovered : SupportCovered x rows columns) (b : B) (hb : b ∉ columns) :
    columnRestriction b x ∈ supportedWordSpace rows := by
  intro a ha
  by_contra hNonzero
  have hMem := hCovered (by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hNonzero⟩)
  rcases Finset.mem_union.mp hMem with hRow | hColumn
  · exact ha (Finset.mem_product.mp hRow).1
  · exact hb (Finset.mem_product.mp hColumn).2

/-- Any linear map annihilating the column code preserves the row-code constraint
of a dual-tensor word.  The matrix interface is supplied by the actual map. -/
private theorem linearMap_row_mem_of_mem_dualTensorCode
    {A B R : Type v} [Fintype A] [Fintype B] [Fintype R]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (check : Word (ZMod 2) A →ₗ[ZMod 2] Word (ZMod 2) R)
    (hCheck : CA.carrier ≤ LinearMap.ker check)
    (x : Word (ZMod 2) (A × B))
    (hx : x ∈ (dualTensorCode CA CB).carrier) (r : R) :
    (fun b => check (columnRestriction b x) r) ∈ CB.carrier := by
  have hMatrix : CA.carrier ≤
      LinearMap.ker (Matrix.toLin' (LinearMap.toMatrix' check)) := by
    simpa only [Matrix.toLin'_toMatrix'] using hCheck
  have hRow := syndrome_row_mem_of_mem_dualTensorCode CA CB
    (LinearMap.toMatrix' check) hMatrix x hx r
  change (fun b => Matrix.toLin' (LinearMap.toMatrix' check)
    (columnRestriction b x) r) ∈ CB.carrier at hRow
  simpa only [Matrix.toLin'_toMatrix'] using hRow

/-- A dual-tensor word covered by fewer than the local distances admits a
genuine row-code plus column-code decomposition supported on those same sets.
The check residual proves attainability before recovery is used; no sparse
decomposition is assumed. -/
private theorem exists_supported_dualTensor_decomposition
    {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (distanceA distanceB : Nat)
    (hDistanceA : HasMinimumDistanceAtLeast CA distanceA)
    (hDistanceB : HasMinimumDistanceAtLeast CB distanceB)
    (x : Word (ZMod 2) (A × B))
    (hx : x ∈ (dualTensorCode CA CB).carrier)
    (rows : Finset A) (columns : Finset B)
    (hRows : rows.card < distanceA) (hColumns : columns.card < distanceB)
    (hCovered : SupportCovered x rows columns) :
    ∃ rowPart columnPart : Word (ZMod 2) (A × B),
      rowPart ∈ (rowCode (A := A) CB).carrier ∧
      columnPart ∈ (columnCode (B := B) CA).carrier ∧
      x = rowPart + columnPart ∧
      (∀ a, a ∉ rows → rowRestriction a rowPart = 0) ∧
      (∀ b, b ∉ columns → columnRestriction b columnPart = 0) := by
  obtain ⟨matrix, hKernel⟩ := exists_squareParityCheckMatrix_ker_eq CA.carrier
  let check := Matrix.toLin' matrix
  have hCheckDistance : ∀ word, check word = 0 → word ≠ 0 →
      distanceA ≤ HammingWeight word := by
    intro word hZero hNonzero
    apply hDistanceA word _ hNonzero
    rw [← hKernel]
    exact hZero
  obtain ⟨recovery, hRecoveryRange, hRecover, _⟩ :=
    exists_supportedWordRecovery check rows
      (check_supportedWordSpace_ker_eq_bot check rows distanceA hCheckDistance hRows)
  let corrector := recovery.comp check
  let obstruction := check - check.comp corrector
  have hCheckZero : ∀ word ∈ CA.carrier, check word = 0 := by
    intro word hWord
    have h := hWord
    rw [← hKernel] at h
    exact h
  have hCorrectorKernel : CA.carrier ≤ LinearMap.ker corrector := by
    intro word hWord
    change recovery (check word) = 0
    rw [hCheckZero word hWord, map_zero]
  have hObstructionKernel : CA.carrier ≤ LinearMap.ker obstruction := by
    intro word hWord
    change check word - check (corrector word) = 0
    rw [hCheckZero word hWord, hCorrectorKernel hWord, map_zero, sub_self]
  have hOutside : ∀ b, b ∉ columns →
      columnRestriction b x ∈ supportedWordSpace rows := by
    intro b hb
    exact column_mem_supportedWordSpace_of_supportCovered x rows columns hCovered b hb
  have hObstructionOutside : ∀ b, b ∉ columns →
      obstruction (columnRestriction b x) = 0 := by
    intro b hb
    change check (columnRestriction b x) -
      check (recovery (check (columnRestriction b x))) = 0
    rw [hRecover _ (hOutside b hb), sub_self]
  have hObstructionRowZero : ∀ a : A,
      (fun b => obstruction (columnRestriction b x) a) = 0 := by
    intro a
    have hRow := linearMap_row_mem_of_mem_dualTensorCode CA CB
      obstruction hObstructionKernel x hx a
    have hSupport : (fun b => obstruction (columnRestriction b x) a) ∈
        supportedWordSpace columns := by
      intro b hb
      exact congrFun (hObstructionOutside b hb) a
    have hWeight := hammingWeight_le_of_mem_supportedWordSpace columns hSupport
    by_contra hNonzero
    have hMin := hDistanceB _ hRow hNonzero
    omega
  have hCheckCorrect : ∀ b, check (corrector (columnRestriction b x)) =
      check (columnRestriction b x) := by
    intro b
    have hZero : obstruction (columnRestriction b x) = 0 := by
      funext a
      exact congrFun (hObstructionRowZero a) b
    exact (sub_eq_zero.mp hZero).symm
  let rowPart : Word (ZMod 2) (A × B) :=
    fun ab => corrector (columnRestriction ab.2 x) ab.1
  let columnPart := x - rowPart
  have hRowPart : rowPart ∈ (rowCode (A := A) CB).carrier := by
    intro a
    exact linearMap_row_mem_of_mem_dualTensorCode CA CB
      corrector hCorrectorKernel x hx a
  have hColumnPart : columnPart ∈ (columnCode (B := B) CA).carrier := by
    intro b
    rw [← hKernel]
    change check (columnRestriction b x - corrector (columnRestriction b x)) = 0
    rw [map_sub, hCheckCorrect b, sub_self]
  refine ⟨rowPart, columnPart, hRowPart, hColumnPart, ?_, ?_, ?_⟩
  · exact (sub_add_cancel x rowPart).symm.trans (add_comm _ _)
  · intro a ha
    funext b
    have hSupport := hRecoveryRange
      (LinearMap.mem_range.mpr ⟨check (columnRestriction b x), rfl⟩)
    exact hSupport a ha
  · intro b hb
    funext a
    change x (a, b) - recovery (check (columnRestriction b x)) a = 0
    rw [hRecover _ (hOutside b hb)]
    exact sub_self _

/-- An actual small support cover yields row/column-code parts supported on
those same sets, as used in [LZ22, Lemma lem:d/2 and proof of thm:main]. -/
theorem exists_supported_decomposition_of_cover
    {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (distanceA distanceB : Nat)
    (hDistanceA : HasMinimumDistanceAtLeast CA distanceA)
    (hDistanceB : HasMinimumDistanceAtLeast CB distanceB)
    (x : Word (ZMod 2) (A × B)) (hx : x ∈ (dualTensorCode CA CB).carrier)
    (rows : Finset A) (columns : Finset B)
    (hRows : rows.card < distanceA) (hColumns : columns.card < distanceB)
    (hCovered : SupportCovered x rows columns) :
    ∃ rowPart columnPart : Word (ZMod 2) (A × B),
      rowPart ∈ (rowCode (A := A) CB).carrier ∧
      columnPart ∈ (columnCode (B := B) CA).carrier ∧
      x = rowPart + columnPart ∧
      (∀ a, a ∉ rows → rowRestriction a rowPart = 0) ∧
      (∀ b, b ∉ columns → columnRestriction b columnPart = 0) :=
  exists_supported_dualTensor_decomposition CA CB distanceA distanceB
    hDistanceA hDistanceB x hx rows columns hRows hColumns hCovered

/-- A half-distance support cover gives an actual row/column decomposition,
with neither part heavier than the original word. This exposes the attained
decomposition used in [LZ22, Proposition prop:tensor], not an assumed decoder. -/
theorem exists_weight_bounded_decomposition_of_half_distance_cover
    {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (distanceA distanceB : Nat)
    (hDistanceA : HasMinimumDistanceAtLeast CA distanceA)
    (hDistanceB : HasMinimumDistanceAtLeast CB distanceB)
    (hPositiveA : 0 < distanceA) (hPositiveB : 0 < distanceB)
    (x : Word (ZMod 2) (A × B))
    (hx : x ∈ (dualTensorCode CA CB).carrier)
    (rows : Finset A) (columns : Finset B)
    (hRows : 2 * rows.card ≤ distanceA)
    (hColumns : 2 * columns.card ≤ distanceB)
    (hCovered : SupportCovered x rows columns) :
    ∃ rowPart columnPart : Word (ZMod 2) (A × B),
      rowPart ∈ (rowCode (A := A) CB).carrier ∧
      columnPart ∈ (columnCode (B := B) CA).carrier ∧
      x = rowPart + columnPart ∧
      HammingWeight rowPart ≤ HammingWeight x ∧
      HammingWeight columnPart ≤ HammingWeight x := by
  obtain ⟨r, c, hr, hc, hParts, hRowSupport, hColumnSupport⟩ :=
    exists_supported_dualTensor_decomposition CA CB distanceA distanceB
      hDistanceA hDistanceB x hx rows columns (by omega) (by omega) hCovered
  have hWeights := hammingWeight_parts_le_of_supported_decomposition
    CA CB distanceA distanceB hDistanceA hDistanceB r c hr hc rows columns
      hRows hColumns hRowSupport hColumnSupport
  rw [← hParts] at hWeights
  exact ⟨r, c, hr, hc, hParts, hWeights.1, hWeights.2⟩

/-- The rows that are genuinely nonzero, rather than a supplied support cover. -/
private def activeRowSet
    {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) : Finset A :=
  Finset.univ.filter fun a => rowRestriction a x ≠ 0

/-- The columns that are genuinely nonzero. -/
private def activeColumnSet
    {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) : Finset B :=
  Finset.univ.filter fun b => columnRestriction b x ≠ 0

/-- Every active row of a row-code word contributes at least the local distance. -/
private theorem activeRowSet_card_mul_distance_le
    {A B : Type v} [Fintype A] [Fintype B]
    (CB : LinearCode (ZMod 2) B) (distance : Nat)
    (hDistance : HasMinimumDistanceAtLeast CB distance)
    (x : Word (ZMod 2) (A × B))
    (hx : x ∈ (rowCode (A := A) CB).carrier) :
    (activeRowSet x).card * distance ≤ HammingWeight x := by
  rw [activeRowSet, Finset.card_filter, Finset.sum_mul, hammingWeight_eq_sum_rows]
  apply Finset.sum_le_sum
  intro a _
  by_cases hZero : rowRestriction a x = 0
  · simp [hZero]
  · simpa [hZero] using hDistance _ (hx a) hZero

/-- Every active column of a column-code word contributes its local distance. -/
private theorem activeColumnSet_card_mul_distance_le
    {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (distance : Nat)
    (hDistance : HasMinimumDistanceAtLeast CA distance)
    (x : Word (ZMod 2) (A × B))
    (hx : x ∈ (columnCode (B := B) CA).carrier) :
    (activeColumnSet x).card * distance ≤ HammingWeight x := by
  rw [activeColumnSet, Finset.card_filter, Finset.sum_mul, hammingWeight_eq_sum_columns]
  apply Finset.sum_le_sum
  intro b _
  by_cases hZero : columnRestriction b x = 0
  · simp [hZero]
  · simpa [hZero] using hDistance _ (hx b) hZero

/-- The actual active rows and columns of any two parts cover their sum. -/
private theorem supportCovered_add_activeParts
    {A B : Type v} [Fintype A] [Fintype B]
    (rowPart columnPart : Word (ZMod 2) (A × B)) :
    SupportCovered (rowPart + columnPart)
      (activeRowSet rowPart) (activeColumnSet columnPart) := by
  intro ab hMem
  by_cases hRow : rowRestriction ab.1 rowPart = 0
  · have hRowZero : rowPart ab = 0 := congrFun hRow ab.2
    have hColumn : columnRestriction ab.2 columnPart ≠ 0 := by
      intro hZero
      have hColumnZero : columnPart ab = 0 := congrFun hZero ab.1
      exact (Finset.mem_filter.mp hMem).2
        (by simp [Pi.add_apply, hRowZero, hColumnZero])
    apply Finset.mem_union.mpr
    right
    simp [Finset.mem_product, activeColumnSet, hColumn]
  · apply Finset.mem_union.mpr
    left
    simp [Finset.mem_product, activeRowSet, hRow]

/-- Source lem:d/2 with the sparse decomposition and cancellation proved,
not supplied as hypotheses: half-distance covers yield normalized covers. -/
private theorem exists_distanceNormalized_supportCover
    {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (distanceA distanceB : Nat)
    (hDistanceA : HasMinimumDistanceAtLeast CA distanceA)
    (hDistanceB : HasMinimumDistanceAtLeast CB distanceB)
    (hPositiveA : 0 < distanceA) (hPositiveB : 0 < distanceB)
    (x : Word (ZMod 2) (A × B))
    (hx : x ∈ (dualTensorCode CA CB).carrier)
    (rows : Finset A) (columns : Finset B)
    (hRows : 2 * rows.card ≤ distanceA)
    (hColumns : 2 * columns.card ≤ distanceB)
    (hCovered : SupportCovered x rows columns) :
    ∃ normalizedRows : Finset A, ∃ normalizedColumns : Finset B,
      SupportCovered x normalizedRows normalizedColumns ∧
        normalizedRows.card ≤ HammingWeight x / distanceB ∧
        normalizedColumns.card ≤ HammingWeight x / distanceA := by
  obtain ⟨rowPart, columnPart, hRow, hColumn, hParts, hRowSupport, hColumnSupport⟩ :=
    exists_supported_dualTensor_decomposition CA CB distanceA distanceB
      hDistanceA hDistanceB x hx rows columns (by omega) (by omega) hCovered
  have hWeights := hammingWeight_parts_le_of_supported_decomposition
    CA CB distanceA distanceB hDistanceA hDistanceB rowPart columnPart
      hRow hColumn rows columns hRows hColumns hRowSupport hColumnSupport
  rw [← hParts] at hWeights
  refine ⟨activeRowSet rowPart, activeColumnSet columnPart, ?_, ?_, ?_⟩
  · rw [hParts]
    exact supportCovered_add_activeParts rowPart columnPart
  · apply (Nat.le_div_iff_mul_le hPositiveB).mpr
    exact (activeRowSet_card_mul_distance_le CB distanceB hDistanceB rowPart hRow).trans
      hWeights.1
  · apply (Nat.le_div_iff_mul_le hPositiveA).mpr
    exact (activeColumnSet_card_mul_distance_le CA distanceA hDistanceA
      columnPart hColumn).trans hWeights.2

/-- Core minimum distance is necessarily positive because it has a nonzero
attaining word; the zero code has no such witness. -/
private theorem minimumDistance_positive
    {A : Type v} [Fintype A] (code : LinearCode (ZMod 2) A)
    {distance : Nat} (hDistance : MinimumDistance code distance) : 0 < distance := by
  obtain ⟨word, _, hNonzero, hWeight, _⟩ := hDistance
  rw [← hWeight]
  exact Nat.pos_of_ne_zero fun hZero =>
    hNonzero ((HammingWeight_eq_zero_iff word).mp hZero)

/-- A common small-cover budget implies Core robustness using its actual
minimum-distance witnesses, including its zero-code quantifier boundary. -/
private theorem isRobust_of_supportCover_budget
    {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (distanceA distanceB p w : Nat)
    (hDistanceA : HasMinimumDistanceAtLeast CA distanceA)
    (hDistanceB : HasMinimumDistanceAtLeast CB distanceB)
    (hRows : 2 * p ≤ distanceA) (hColumns : 2 * p ≤ distanceB)
    (hCovers : ∀ x, x ∈ (dualTensorCode CA CB).carrier → HammingWeight x ≤ w →
      ∃ rows : Finset A, ∃ columns : Finset B,
        SupportCovered x rows columns ∧ rows.card ≤ p ∧ columns.card ≤ p) :
    IsRobust CA CB w := by
  intro dA dB hMinimumA hMinimumB x hx hWeight
  have hPositiveA := minimumDistance_positive CA hMinimumA
  have hPositiveB := minimumDistance_positive CB hMinimumB
  obtain ⟨wordA, hWordA, hNonzeroA, hWeightA, hMinA⟩ := hMinimumA
  obtain ⟨wordB, hWordB, hNonzeroB, hWeightB, hMinB⟩ := hMinimumB
  have hLowerA : distanceA ≤ dA := by
    rw [← hWeightA]
    exact hDistanceA wordA hWordA hNonzeroA
  have hLowerB : distanceB ≤ dB := by
    rw [← hWeightB]
    exact hDistanceB wordB hWordB hNonzeroB
  obtain ⟨rows, columns, hCovered, hRowCard, hColumnCard⟩ := hCovers x hx hWeight
  exact exists_distanceNormalized_supportCover CA CB dA dB hMinA hMinB
    hPositiveA hPositiveB x hx rows columns (by omega) (by omega) hCovered

/-- A failure of Core robustness on distance-good local codes has an actual
low-weight dual-tensor witness with no budget-sized support cover. -/
private theorem not_isRobust_imp_noSmallCover
    {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (distanceA distanceB p w : Nat)
    (hDistanceA : HasMinimumDistanceAtLeast CA distanceA)
    (hDistanceB : HasMinimumDistanceAtLeast CB distanceB)
    (hRows : 2 * p ≤ distanceA) (hColumns : 2 * p ≤ distanceB)
    (hNotRobust : ¬ IsRobust CA CB w) :
    ∃ x : Word (ZMod 2) (A × B),
      x ∈ (dualTensorCode CA CB).carrier ∧ HammingWeight x ≤ w ∧
        ∀ rows : Finset A, ∀ columns : Finset B,
          rows.card ≤ p → columns.card ≤ p → ¬ SupportCovered x rows columns := by
  by_contra hNoWitness
  apply hNotRobust
  apply isRobust_of_supportCover_budget CA CB distanceA distanceB p w
    hDistanceA hDistanceB hRows hColumns
  intro x hx hWeight
  by_contra hNoCover
  apply hNoWitness
  refine ⟨x, hx, hWeight, ?_⟩
  intro rows columns hRowCard hColumnCard hCovered
  exact hNoCover ⟨rows, columns, hCovered, hRowCard, hColumnCard⟩


/-- The retained support is exactly the original support minus the deleted coordinates. -/
private theorem hammingSupport_puncture_image
    {ι : Type v} [Fintype ι] (removed : Finset ι) (x : Word (ZMod 2) ι) :
    (hammingSupport (punctureMap removed x)).image Subtype.val =
      hammingSupport x \ removed := by
  classical
  ext i
  constructor
  · intro hi
    rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, j.2⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
  · intro hi
    rcases Finset.mem_sdiff.mp hi with ⟨hSupport, hKept⟩
    apply Finset.mem_image.mpr
    refine ⟨⟨i, hKept⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hSupport).2⟩

/-- Puncturing splits weight into retained and deleted nonzero coordinates. -/
private theorem hammingWeight_eq_puncture_add_deleted
    {ι : Type v} [Fintype ι] (removed : Finset ι) (x : Word (ZMod 2) ι) :
    HammingWeight x = HammingWeight (punctureMap removed x) +
      (hammingSupport x ∩ removed).card := by
  classical
  have hCard := congrArg Finset.card (hammingSupport_puncture_image removed x)
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hCard
  exact (Finset.card_sdiff_add_card_inter (hammingSupport x) removed).symm.trans
    (congrArg (fun n => n + (hammingSupport x ∩ removed).card) hCard.symm)

/-- Puncturing cannot increase Hamming weight. -/
private theorem hammingWeight_puncture_le
    {ι : Type v} [Fintype ι] (removed : Finset ι) (x : Word (ZMod 2) ι) :
    HammingWeight (punctureMap removed x) ≤ HammingWeight x := by
  have h := hammingWeight_eq_puncture_add_deleted removed x
  omega

/-- Deleting coordinates loses at most their number in Hamming weight. -/
private theorem hammingWeight_puncture_loss_le
    {ι : Type v} [Fintype ι] (removed : Finset ι) (x : Word (ZMod 2) ι) :
    HammingWeight x ≤ HammingWeight (punctureMap removed x) + removed.card := by
  classical
  rw [hammingWeight_eq_puncture_add_deleted removed x]
  exact Nat.add_le_add_left (Finset.card_le_card Finset.inter_subset_right) _

/-- Every actual punctured codeword inherits the distance loss bound. -/
private theorem hasMinimumDistanceAtLeast_puncturedCode
    {ι : Type v} [Fintype ι] (code : LinearCode (ZMod 2) ι)
    (distance : Nat) (removed : Finset ι)
    (hDistance : HasMinimumDistanceAtLeast code distance) :
    HasMinimumDistanceAtLeast (puncturedCode code removed) (distance - removed.card) := by
  intro x hx hNonzero
  rcases (mem_puncturedCode code removed x).mp hx with ⟨y, hy, rfl⟩
  have hY : y ≠ 0 := by
    intro hZero
    apply hNonzero
    simp [hZero]
  have hLower := hDistance y hy hY
  have hLoss := hammingWeight_puncture_loss_le removed y
  omega

/-- A common puncture budget gives one lower bound for every deleted set. -/
private theorem hasMinimumDistanceAtLeast_puncturedCode_of_card_le
    {ι : Type v} [Fintype ι] (code : LinearCode (ZMod 2) ι)
    (distance budget : Nat) (removed : Finset ι)
    (hDistance : HasMinimumDistanceAtLeast code distance)
    (hCard : removed.card ≤ budget) :
    HasMinimumDistanceAtLeast (puncturedCode code removed) (distance - budget) := by
  intro x hx hNonzero
  have h := hasMinimumDistanceAtLeast_puncturedCode code distance removed
    hDistance x hx hNonzero
  omega

/-- Puncturing a generator combination is the same combination of the retained columns. -/
private theorem puncture_wordLinearMapTranspose_matrix
    {row col : Type v} [Fintype row] [Fintype col]
    (matrix : Matrix row col (ZMod 2)) (removed : Finset col)
    (coefficients : Word (ZMod 2) row) :
    punctureMap removed (wordLinearMapTranspose (Matrix.toLin' matrix) coefficients) =
      wordLinearMapTranspose
        (Matrix.toLin' (matrix.submatrix id (fun i : KeptCoordinate removed => i.1)))
        coefficients := by
  classical
  ext i
  simp [punctureMap, wordLinearMapTranspose, Matrix.toLin'_apply,
    Matrix.mulVec_single_one, Matrix.submatrix]

/-- The actual punctured generator code is the row code of the retained random block. -/
private theorem punctured_generatorCode_carrier_eq
    {row col : Type v} [Fintype row] [Fintype col]
    (matrix : Matrix row col (ZMod 2)) (removed : Finset col) :
    (puncturedCode (parityCheckRowCode (Matrix.toLin' matrix)) removed).carrier =
      (parityCheckRowCode
        (Matrix.toLin' (matrix.submatrix id (fun i : KeptCoordinate removed => i.1)))).carrier := by
  ext x
  rw [mem_puncturedCode, mem_parityCheckRowCode]
  constructor
  · rintro ⟨y, hy, hPuncture⟩
    rcases (mem_parityCheckRowCode _ y).mp hy with ⟨coefficients, rfl⟩
    exact ⟨coefficients,
      (puncture_wordLinearMapTranspose_matrix matrix removed coefficients).symm.trans hPuncture⟩
  · rintro ⟨coefficients, hRetained⟩
    refine ⟨wordLinearMapTranspose (Matrix.toLin' matrix) coefficients,
      (mem_parityCheckRowCode _ _).mpr ⟨coefficients, rfl⟩, ?_⟩
    exact (puncture_wordLinearMapTranspose_matrix matrix removed coefficients).trans hRetained

/-- An event on retained generator entries is a product with the freely deleted entries. -/
private def retainedMatrixEventEquiv
    {row col : Type v} [Fintype row] [Fintype col] (removed : Finset col)
    (event : Matrix row (KeptCoordinate removed) (ZMod 2) → Prop) :
    {matrix : Matrix row col (ZMod 2) //
      event (matrix.submatrix id (fun i : KeptCoordinate removed => i.1))} ≃
      Matrix row {i // i ∈ removed} (ZMod 2) ×
        {retained : Matrix row (KeptCoordinate removed) (ZMod 2) // event retained} where
  toFun matrix := ⟨(splitCheckMatrixEquiv removed matrix.1).1,
    ⟨(splitCheckMatrixEquiv removed matrix.1).2, matrix.2⟩⟩
  invFun blocks := ⟨(splitCheckMatrixEquiv removed).symm (blocks.1, blocks.2.1), by
    change event ((splitCheckMatrixEquiv removed)
      ((splitCheckMatrixEquiv removed).symm (blocks.1, blocks.2.1))).2
    rw [Equiv.apply_symm_apply]
    exact blocks.2.2⟩
  left_inv matrix := by
    apply Subtype.ext
    exact (splitCheckMatrixEquiv removed).symm_apply_apply matrix.1
  right_inv blocks := by
    apply Prod.ext
    · change ((splitCheckMatrixEquiv removed)
        ((splitCheckMatrixEquiv removed).symm (blocks.1, blocks.2.1))).1 = blocks.1
      exact congrArg Prod.fst
        ((splitCheckMatrixEquiv removed).apply_symm_apply (blocks.1, blocks.2.1))
    · apply Subtype.ext
      change ((splitCheckMatrixEquiv removed)
        ((splitCheckMatrixEquiv removed).symm (blocks.1, blocks.2.1))).2 = blocks.2.1
      exact congrArg Prod.snd
        ((splitCheckMatrixEquiv removed).apply_symm_apply (blocks.1, blocks.2.1))

/-- Exact event count: every retained matrix has the same number of completions. -/
private theorem card_retainedMatrixEvent
    {row col : Type v} [Fintype row] [Fintype col] (removed : Finset col)
    (event : Matrix row (KeptCoordinate removed) (ZMod 2) → Prop) :
    Nat.card {matrix : Matrix row col (ZMod 2) //
      event (matrix.submatrix id (fun i : KeptCoordinate removed => i.1))} =
      Nat.card (Matrix row {i // i ∈ removed} (ZMod 2)) *
        Nat.card {retained : Matrix row (KeptCoordinate removed) (ZMod 2) // event retained} := by
  rw [Nat.card_congr (retainedMatrixEventEquiv removed event), Nat.card_prod]

/-- Retained-block events have exactly the same uniform fraction in the original sample space. -/
private theorem card_retainedMatrixEvent_mul_eq
    {row col : Type v} [Fintype row] [Fintype col] (removed : Finset col)
    (event : Matrix row (KeptCoordinate removed) (ZMod 2) → Prop) :
    Nat.card {matrix : Matrix row col (ZMod 2) //
      event (matrix.submatrix id (fun i : KeptCoordinate removed => i.1))} *
        Nat.card (Matrix row (KeptCoordinate removed) (ZMod 2)) =
      Nat.card (Matrix row col (ZMod 2)) *
        Nat.card {retained : Matrix row (KeptCoordinate removed) (ZMod 2) // event retained} := by
  rw [card_retainedMatrixEvent,
    Nat.card_congr (splitCheckMatrixEquiv removed), Nat.card_prod]
  ac_rfl

/-- Uniform retained-block transport for events on the actual punctured generator code. -/
private theorem card_puncturedGeneratorCodeEvent_mul_eq
    {row col : Type v} [Fintype row] [Fintype col] (removed : Finset col)
    (event : Submodule (ZMod 2) (Word (ZMod 2) (KeptCoordinate removed)) → Prop) :
    Nat.card {matrix : Matrix row col (ZMod 2) //
      event (puncturedCode (parityCheckRowCode (Matrix.toLin' matrix)) removed).carrier} *
        Nat.card (Matrix row (KeptCoordinate removed) (ZMod 2)) =
      Nat.card (Matrix row col (ZMod 2)) *
        Nat.card {retained : Matrix row (KeptCoordinate removed) (ZMod 2) //
          event (parityCheckRowCode (Matrix.toLin' retained)).carrier} := by
  simp_rw [punctured_generatorCode_carrier_eq]
  exact card_retainedMatrixEvent_mul_eq removed
    (fun retained => event (parityCheckRowCode (Matrix.toLin' retained)).carrier)


/-- Leaving out columns of a dual-tensor word leaves every retained
syndrome row in the corresponding punctured row code. -/
private theorem retained_syndrome_row_mem_puncturedCode
    {A B R : Type v} [Fintype A] [Fintype B] [Fintype R]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (check : Matrix R A (ZMod 2))
    (hCheck : CA.carrier ≤ LinearMap.ker (Matrix.toLin' check))
    (removed : Finset B)
    (retained : Word (ZMod 2) (A × KeptCoordinate removed))
    (x : Word (ZMod 2) (A × B))
    (hx : x ∈ (dualTensorCode CA CB).carrier)
    (hRetained : (fun ab : A × KeptCoordinate removed => x (ab.1, ab.2.1)) = retained)
    (r : R) :
    (fun b => Matrix.mulVec check (columnRestriction b retained) r) ∈
      (puncturedCode CB removed).carrier := by
  apply (mem_puncturedCode CB removed _).mpr
  refine ⟨(fun b => Matrix.mulVec check (columnRestriction b x) r),
    syndrome_row_mem_of_mem_dualTensorCode CA CB check hCheck x hx r, ?_⟩
  funext b
  change Matrix.mulVec check (fun a => x (a, b.1)) r =
    Matrix.mulVec check (columnRestriction b retained) r
  have hColumn : (fun a => x (a, b.1)) = columnRestriction b retained := by
    funext a
    exact congrFun hRetained (a, b)
  rw [hColumn]

/-- Containment of every fixed row is equivalent to containment of its
linear span; the latter is the test-space event counted by randomCp. -/
private theorem rows_mem_iff_span_contained
    {R B : Type v} [Fintype B]
    (rows : R → Word (ZMod 2) B) (code : Submodule (ZMod 2) (Word (ZMod 2) B)) :
    (∀ r, rows r ∈ code) ↔
      ∀ word : Submodule.span (ZMod 2) (Set.range rows), word.1 ∈ code := by
  constructor
  · intro hRows word
    apply (Submodule.span_le.mpr ?_) word.2
    rintro _ ⟨r, rfl⟩
    exact hRows r
  · intro hSpan r
    exact hSpan ⟨rows r, Submodule.subset_span (Set.mem_range_self r)⟩

/-- Replace fixed-row membership by the span-containment event without
changing either the random check matrix or its distribution. -/
private def puncturedCheckRowsEventEquiv
    {R B T : Type v} [Fintype B] [Fintype T]
    (removed : Finset B) (rows : R → Word (ZMod 2) (KeptCoordinate removed)) :
    {matrix : Matrix T B (ZMod 2) // ∀ r, rows r ∈
      (puncturedCode (parityCheckKernelCode (Matrix.toLin' matrix)) removed).carrier} ≃
    {matrix : Matrix T B (ZMod 2) //
      ∀ word : Submodule.span (ZMod 2) (Set.range rows), word.1 ∈
        (puncturedCode (parityCheckKernelCode (Matrix.toLin' matrix)) removed).carrier} := by
  refine (Equiv.refl (Matrix T B (ZMod 2))).subtypeEquiv ?_
  intro matrix
  exact rows_mem_iff_span_contained rows _

/-- The source randomCp bound applied to the fixed syndrome row span. -/
private theorem card_puncturedCheckRowsEvent_mul_pow_le
    {R B T : Type v} [Fintype B] [Fintype T]
    (removed : Finset B) (rows : R → Word (ZMod 2) (KeptCoordinate removed)) :
    Nat.card {matrix : Matrix T B (ZMod 2) // ∀ r, rows r ∈
      (puncturedCode (parityCheckKernelCode (Matrix.toLin' matrix)) removed).carrier} *
      2 ^ (Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range rows)) *
        (Fintype.card T - removed.card)) ≤ Nat.card (Matrix T B (ZMod 2)) := by
  rw [Nat.card_congr (puncturedCheckRowsEventEquiv removed rows)]
  exact card_puncturedCheckMatrixEvent_mul_pow_le removed
    (Submodule.span (ZMod 2) (Set.range rows))

/-- A lower bound on the fixed syndrome rank gives the corresponding
integer rarity bound for its punctured-kernel containment event. -/
private theorem card_puncturedCheckRowsEvent_mul_pow_le_of_rank_le
    {R B T : Type v} [Fintype B] [Fintype T]
    (removed : Finset B) (rows : R → Word (ZMod 2) (KeptCoordinate removed))
    (rank : Nat)
    (hRank : rank ≤ Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range rows))) :
    Nat.card {matrix : Matrix T B (ZMod 2) // ∀ r, rows r ∈
      (puncturedCode (parityCheckKernelCode (Matrix.toLin' matrix)) removed).carrier} *
      2 ^ (rank * (Fintype.card T - removed.card)) ≤
      Nat.card (Matrix T B (ZMod 2)) := by
  apply le_trans _ (card_puncturedCheckRowsEvent_mul_pow_le removed rows)
  apply Nat.mul_le_mul_left
  exact pow_le_pow_right₀ (by decide : 1 ≤ (2 : Nat))
    (Nat.mul_le_mul_right _ hRank)

/-- Finite event inclusion can be counted with instance-independent
cardinalities before multiplying by the common probability denominator. -/
private theorem nat_card_event_le_of_imp
    {α : Type*} [Finite α] (P Q : α → Prop) (h : ∀ a, P a → Q a) :
    Nat.card {a : α // P a} ≤ Nat.card {a : α // Q a} := by
  apply Nat.card_le_card_of_injective (fun a => ⟨a.1, h a.1 a.2⟩)
  intro a b hab
  apply Subtype.ext
  exact congrArg (fun c : {a : α // Q a} => c.1) hab

/-- A fixed retained matrix can extend to the dual-tensor code only if
all of its fixed check-syndrome rows enter the random punctured kernel.
Together with a syndrome-rank bound, this is the integer form of lem:XP. -/
private theorem card_dualTensorRetainedEvent_mul_pow_le
    {A B R T : Type v} [Fintype A] [Fintype B] [Fintype R] [Fintype T]
    (CA : LinearCode (ZMod 2) A) (check : Matrix R A (ZMod 2))
    (hCheck : CA.carrier ≤ LinearMap.ker (Matrix.toLin' check))
    (removed : Finset B) (retained : Word (ZMod 2) (A × KeptCoordinate removed))
    (rank : Nat)
    (hRank : rank ≤ Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range fun r : R =>
        (fun b => Matrix.mulVec check (columnRestriction b retained) r)))) :
    Nat.card {matrix : Matrix T B (ZMod 2) //
      ∃ x : Word (ZMod 2) (A × B),
        x ∈ (dualTensorCode CA (parityCheckKernelCode (Matrix.toLin' matrix))).carrier ∧
        (fun ab : A × KeptCoordinate removed => x (ab.1, ab.2.1)) = retained} *
      2 ^ (rank * (Fintype.card T - removed.card)) ≤
      Nat.card (Matrix T B (ZMod 2)) := by
  apply le_trans _ (card_puncturedCheckRowsEvent_mul_pow_le_of_rank_le
    removed (fun r b => Matrix.mulVec check (columnRestriction b retained) r) rank hRank)
  apply Nat.mul_le_mul_right
  apply nat_card_event_le_of_imp
  intro matrix hEvent
  obtain ⟨x, hx, hRetained⟩ := hEvent
  intro r
  exact retained_syndrome_row_mem_puncturedCode CA
    (parityCheckKernelCode (Matrix.toLin' matrix)) check hCheck
    removed retained x hx hRetained r


/-- For a fixed light retained matrix, local distance preserves the requested
column rank in a genuine check syndrome.  The random completion event therefore
satisfies the source's integer rarity bound without an assumed check or syndrome
rank.  The raw column-rank and local support-budget hypotheses remain explicit. -/
private theorem card_dualTensorLightRetainedEvent_mul_pow_le
    {A B T : Type v} [Fintype A] [Fintype B] [Fintype T]
    (CA : LinearCode (ZMod 2) A) (removed : Finset B)
    (retained : Word (ZMod 2) (A × KeptCoordinate removed))
    (cutoff distance rank : Nat)
    (hRank : rank ≤ Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2)
        ((Finset.univ.image fun b : KeptCoordinate removed => columnRestriction b retained) :
          Set (Word (ZMod 2) A))))
    (hLight : ∀ b : KeptCoordinate removed,
      HammingWeight (columnRestriction b retained) ≤ cutoff)
    (hBudget : rank * cutoff < distance)
    (hDistance : HasMinimumDistanceAtLeast CA distance) :
    Nat.card {matrix : Matrix T B (ZMod 2) //
      ∃ x : Word (ZMod 2) (A × B),
        x ∈ (dualTensorCode CA (parityCheckKernelCode (Matrix.toLin' matrix))).carrier ∧
        (fun ab : A × KeptCoordinate removed => x (ab.1, ab.2.1)) = retained} *
      2 ^ (rank * (Fintype.card T - removed.card)) ≤
      Nat.card (Matrix T B (ZMod 2)) := by
  obtain ⟨check, hKernel⟩ := exists_squareParityCheckMatrix_ker_eq CA.carrier
  exact card_dualTensorRetainedEvent_mul_pow_le CA check hKernel.symm.le removed retained rank
    (check_lightColumns_rowSpan_rank_le CA check hKernel retained cutoff distance rank hRank hLight hBudget hDistance)

/-- Combine external punctures with deletions among their retained coordinates. -/
private def combinedPuncture {B : Type v} [Fintype B]
    (removed : Finset B) (more : Finset (KeptCoordinate removed)) : Finset B :=
  removed ∪ more.image Subtype.val

private theorem mem_combinedPuncture_iff
    {B : Type v} [Fintype B] (removed : Finset B)
    (more : Finset (KeptCoordinate removed)) (b : KeptCoordinate removed) :
    b.1 ∈ combinedPuncture removed more ↔ b ∈ more := by
  classical
  simp only [combinedPuncture, Finset.mem_union, b.2, false_or]
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨c, hc, hcb⟩
    have hEq : c = b := Subtype.ext hcb
    simpa only [hEq] using hc
  · intro h
    exact Finset.mem_image.mpr ⟨b, h, rfl⟩

/-- External and retained-coordinate deletions are disjoint, so their sizes add. -/
private theorem card_combinedPuncture
    {B : Type v} [Fintype B] (removed : Finset B)
    (more : Finset (KeptCoordinate removed)) :
    (combinedPuncture removed more).card = removed.card + more.card := by
  classical
  have hDisjoint : Disjoint removed (more.image Subtype.val) := by
    apply Finset.disjoint_left.mpr
    intro b hb hImage
    rcases Finset.mem_image.mp hImage with ⟨c, hc, rfl⟩
    exact c.2 hb
  rw [combinedPuncture, Finset.card_union_of_disjoint hDisjoint,
    Finset.card_image_of_injective _ Subtype.val_injective]

/-- Nested retained coordinates are the actual coordinates left after the combined deletion. -/
private def nestedKeptCoordinateEquiv
    {B : Type v} [Fintype B] (removed : Finset B)
    (more : Finset (KeptCoordinate removed)) :
    KeptCoordinate more ≃ KeptCoordinate (combinedPuncture removed more) where
  toFun b := ⟨b.1.1, by
    intro h
    exact b.2 ((mem_combinedPuncture_iff removed more b.1).mp h)⟩
  invFun b := ⟨⟨b.1, by
    intro h
    exact b.2 (Finset.mem_union_left _ h)⟩, by
    intro h
    apply b.2
    exact (mem_combinedPuncture_iff removed more _).mpr h⟩
  left_inv b := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv b := by
    apply Subtype.ext
    rfl

private theorem punctureMap_nested_apply
    {B : Type v} [Fintype B] (removed : Finset B)
    (more : Finset (KeptCoordinate removed)) (x : Word (ZMod 2) B)
    (b : KeptCoordinate more) :
    punctureMap more (punctureMap removed x) b =
      punctureMap (combinedPuncture removed more) x
        (nestedKeptCoordinateEquiv removed more b) := by
  rfl

/-- Membership after two actual image punctures agrees with one combined puncture. -/
private theorem mem_nestedPuncturedCode_iff
    {B : Type v} [Fintype B] (code : LinearCode (ZMod 2) B)
    (removed : Finset B) (more : Finset (KeptCoordinate removed))
    (x : Word (ZMod 2) (KeptCoordinate (combinedPuncture removed more))) :
    (fun b => x (nestedKeptCoordinateEquiv removed more b)) ∈
      ((puncturedCode code removed).carrier.map (punctureMap more)) ↔
      x ∈ (puncturedCode code (combinedPuncture removed more)).carrier := by
  change (∃ y, y ∈ (puncturedCode code removed).carrier ∧
    punctureMap more y = (fun b => x (nestedKeptCoordinateEquiv removed more b))) ↔ _
  simp only [mem_puncturedCode]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, hPuncture⟩
    refine ⟨z, hz, ?_⟩
    funext b
    rcases (nestedKeptCoordinateEquiv removed more).surjective b with ⟨c, rfl⟩
    exact congrFun hPuncture c
  · rintro ⟨z, hz, hPuncture⟩
    refine ⟨punctureMap removed z, ⟨z, hz, rfl⟩, ?_⟩
    funext b
    rw [punctureMap_nested_apply, hPuncture]

/-- Lift an actual dual-tensor word from a punctured row code to the original row code. -/
private theorem exists_dualTensor_lift_punctured_right
    {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (removed : Finset B) (x : Word (ZMod 2) (A × KeptCoordinate removed))
    (hx : x ∈ (dualTensorCode CA (puncturedCode CB removed)).carrier) :
    ∃ y : Word (ZMod 2) (A × B), y ∈ (dualTensorCode CA CB).carrier ∧
      (fun ab : A × KeptCoordinate removed => y (ab.1, ab.2.1)) = x := by
  classical
  obtain ⟨columnPart, hColumn, rowPart, hRow, hParts⟩ := Submodule.mem_sup.mp hx
  have hPreimage : ∀ a : A, ∃ word : Word (ZMod 2) B,
      word ∈ CB.carrier ∧ punctureMap removed word = rowRestriction a rowPart := by
    intro a
    exact (mem_puncturedCode CB removed _).mp (hRow a)
  choose rowWord hRowWord hRowPuncture using hPreimage
  let liftedColumn : Word (ZMod 2) (A × B) := fun ab =>
    if hb : ab.2 ∈ removed then 0 else columnPart (ab.1, ⟨ab.2, hb⟩)
  let liftedRow : Word (ZMod 2) (A × B) := fun ab => rowWord ab.1 ab.2
  have hColumnLift : liftedColumn ∈ (columnCode (B := B) CA).carrier := by
    intro b
    by_cases hb : b ∈ removed
    · have hZero : columnRestriction b liftedColumn = 0 := by
        ext a
        simp [columnRestriction, liftedColumn, hb]
      rw [hZero]
      exact CA.carrier.zero_mem
    · have hKept : columnRestriction b liftedColumn =
        columnRestriction ⟨b, hb⟩ columnPart := by
        ext a
        simp [columnRestriction, liftedColumn, hb]
      rw [hKept]
      exact hColumn ⟨b, hb⟩
  have hRowLift : liftedRow ∈ (rowCode (A := A) CB).carrier := by
    intro a
    exact hRowWord a
  refine ⟨liftedColumn + liftedRow, ?_, ?_⟩
  · exact (dualTensorCode CA CB).carrier.add_mem
      (Submodule.mem_sup_left hColumnLift) (Submodule.mem_sup_right hRowLift)
  · funext ab
    have hRowValue := congrFun (hRowPuncture ab.1) ab.2
    change rowWord ab.1 ab.2.1 = rowPart ab at hRowValue
    change liftedColumn (ab.1, ab.2.1) + rowWord ab.1 ab.2.1 = x ab
    simp only [liftedColumn, dif_neg ab.2.2, hRowValue]
    exact congrFun hParts ab

/-- Count a fixed retained cylinder of the actual punctured dual-tensor experiment. -/
private theorem card_puncturedDualTensorLightRetainedEvent_mul_pow_le
    {A B T : Type v} [Fintype A] [Fintype B] [Fintype T]
    (CA : LinearCode (ZMod 2) A) (removed : Finset B)
    (more : Finset (KeptCoordinate removed))
    (retained : Word (ZMod 2) (A × KeptCoordinate (combinedPuncture removed more)))
    (cutoff distance rank : Nat)
    (hRank : rank ≤ Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2)
        ((Finset.univ.image fun b : KeptCoordinate (combinedPuncture removed more) =>
          columnRestriction b retained) : Set (Word (ZMod 2) A))))
    (hLight : ∀ b : KeptCoordinate (combinedPuncture removed more),
      HammingWeight (columnRestriction b retained) ≤ cutoff)
    (hBudget : rank * cutoff < distance)
    (hDistance : HasMinimumDistanceAtLeast CA distance) :
    Nat.card {matrix : Matrix T B (ZMod 2) //
      ∃ x : Word (ZMod 2) (A × KeptCoordinate removed),
        x ∈ (dualTensorCode CA
          (puncturedCode (parityCheckKernelCode (Matrix.toLin' matrix)) removed)).carrier ∧
        (fun ab : A × KeptCoordinate (combinedPuncture removed more) =>
          x (ab.1, ((nestedKeptCoordinateEquiv removed more).symm ab.2).1)) = retained} *
      2 ^ (rank * (Fintype.card T - (removed.card + more.card))) ≤
      Nat.card (Matrix T B (ZMod 2)) := by
  rw [← card_combinedPuncture removed more]
  apply le_trans _ (card_dualTensorLightRetainedEvent_mul_pow_le
    CA (combinedPuncture removed more) retained cutoff distance rank
    hRank hLight hBudget hDistance)
  apply Nat.mul_le_mul_right
  apply nat_card_event_le_of_imp
  intro matrix hEvent
  rcases hEvent with ⟨x, hx, hRetained⟩
  obtain ⟨y, hy, hLift⟩ := exists_dualTensor_lift_punctured_right
    CA (parityCheckKernelCode (Matrix.toLin' matrix)) removed x hx
  refine ⟨y, hy, ?_⟩
  funext ab
  have hLiftValue := congrFun hLift
    (ab.1, ((nestedKeptCoordinateEquiv removed more).symm ab.2).1)
  exact hLiftValue.trans (congrFun hRetained ab)


/-- Reindex a nested retained word onto the coordinates left by the combined deletion. -/
private def canonicalNestedRetainedWord
    {A B : Type v} [Fintype A] [Fintype B]
    (removed : Finset B) (more : Finset (KeptCoordinate removed))
    (retained : Word (ZMod 2) (A × KeptCoordinate more)) :
    Word (ZMod 2) (A × KeptCoordinate (combinedPuncture removed more)) :=
  fun ab => retained (ab.1, (nestedKeptCoordinateEquiv removed more).symm ab.2)

private theorem columnRestriction_canonicalNestedRetainedWord
    {A B : Type v} [Fintype A] [Fintype B]
    (removed : Finset B) (more : Finset (KeptCoordinate removed))
    (retained : Word (ZMod 2) (A × KeptCoordinate more))
    (b : KeptCoordinate (combinedPuncture removed more)) :
    columnRestriction b (canonicalNestedRetainedWord removed more retained) =
      columnRestriction ((nestedKeptCoordinateEquiv removed more).symm b) retained := by
  rfl

/-- The canonical reindexing preserves the actual column family, including repeats. -/
private theorem canonicalNestedRetainedWord_columnFamily_eq
    {A B : Type v} [Fintype A] [Fintype B]
    (removed : Finset B) (more : Finset (KeptCoordinate removed))
    (retained : Word (ZMod 2) (A × KeptCoordinate more)) :
    (Finset.univ.image fun b : KeptCoordinate (combinedPuncture removed more) =>
      columnRestriction b (canonicalNestedRetainedWord removed more retained)) =
    (Finset.univ.image fun b : KeptCoordinate more => columnRestriction b retained) := by
  classical
  ext word
  constructor
  · intro hword
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hword
    exact Finset.mem_image.mpr
      ⟨(nestedKeptCoordinateEquiv removed more).symm b, Finset.mem_univ _, rfl⟩
  · intro hword
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hword
    refine Finset.mem_image.mpr
      ⟨nestedKeptCoordinateEquiv removed more b, Finset.mem_univ _, ?_⟩
    simp only [columnRestriction_canonicalNestedRetainedWord, Equiv.symm_apply_apply]

private theorem canonicalNestedRetainedWord_columnSpan_rank_eq
    {A B : Type v} [Fintype A] [Fintype B]
    (removed : Finset B) (more : Finset (KeptCoordinate removed))
    (retained : Word (ZMod 2) (A × KeptCoordinate more)) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
      ((Finset.univ.image fun b : KeptCoordinate (combinedPuncture removed more) =>
        columnRestriction b (canonicalNestedRetainedWord removed more retained)) :
          Set (Word (ZMod 2) A))) =
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
      ((Finset.univ.image fun b : KeptCoordinate more => columnRestriction b retained) :
        Set (Word (ZMod 2) A))) := by
  rw [canonicalNestedRetainedWord_columnFamily_eq]

private theorem canonicalNestedRetainedWord_light
    {A B : Type v} [Fintype A] [Fintype B]
    (removed : Finset B) (more : Finset (KeptCoordinate removed))
    (retained : Word (ZMod 2) (A × KeptCoordinate more)) (cutoff : Nat)
    (hLight : ∀ b, HammingWeight (columnRestriction b retained) ≤ cutoff) :
    ∀ b, HammingWeight
      (columnRestriction b (canonicalNestedRetainedWord removed more retained)) ≤ cutoff := by
  intro b
  rw [columnRestriction_canonicalNestedRetainedWord]
  exact hLight _

/-- Count a concrete nested retained cylinder before introducing any dependent index. -/
private theorem card_nestedPuncturedDualTensorLightRetainedEvent_mul_pow_le
    {A B T : Type v} [Fintype A] [Fintype B] [Fintype T]
    (CA : LinearCode (ZMod 2) A) (removed : Finset B)
    (more : Finset (KeptCoordinate removed))
    (retained : Word (ZMod 2) (A × KeptCoordinate more))
    (cutoff distance rank : Nat)
    (hRank : rank ≤ Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2)
        ((Finset.univ.image fun b : KeptCoordinate more =>
          columnRestriction b retained) : Set (Word (ZMod 2) A))))
    (hLight : ∀ b : KeptCoordinate more,
      HammingWeight (columnRestriction b retained) ≤ cutoff)
    (hBudget : rank * cutoff < distance)
    (hDistance : HasMinimumDistanceAtLeast CA distance) :
    Nat.card {matrix : Matrix T B (ZMod 2) //
      ∃ x : Word (ZMod 2) (A × KeptCoordinate removed),
        x ∈ (dualTensorCode CA
          (puncturedCode (parityCheckKernelCode (Matrix.toLin' matrix)) removed)).carrier ∧
        (fun ab : A × KeptCoordinate more => x (ab.1, ab.2.1)) = retained} *
      2 ^ (rank * (Fintype.card T - (removed.card + more.card))) ≤
      Nat.card (Matrix T B (ZMod 2)) := by
  have hCanonicalRank : rank ≤ Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2)
        ((Finset.univ.image fun b : KeptCoordinate (combinedPuncture removed more) =>
          columnRestriction b (canonicalNestedRetainedWord removed more retained)) :
            Set (Word (ZMod 2) A))) := by
    rw [canonicalNestedRetainedWord_columnSpan_rank_eq]
    exact hRank
  apply le_trans _ (card_puncturedDualTensorLightRetainedEvent_mul_pow_le
    CA removed more (canonicalNestedRetainedWord removed more retained)
    cutoff distance rank hCanonicalRank
    (canonicalNestedRetainedWord_light removed more retained cutoff hLight) hBudget hDistance)
  apply Nat.mul_le_mul_right
  apply nat_card_event_le_of_imp
  intro matrix hEvent
  obtain ⟨x, hx, hRetained⟩ := hEvent
  refine ⟨x, hx, ?_⟩
  funext ab
  exact congrFun hRetained
    (ab.1, (nestedKeptCoordinateEquiv removed more).symm ab.2)


/-- Retaining the complement of a deletion set gives exactly the original
column family filtered by that complement, including repeated columns. -/
private theorem retainedColumnFamily_eq
    {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) (removed : Finset B) :
    (Finset.univ.image fun b : KeptCoordinate removed =>
      columnRestriction b (fun ab : A × KeptCoordinate removed => x (ab.1, ab.2.1))) =
      (Finset.univ.filter fun b : B => b ∉ removed).image
        (fun b => columnRestriction b x) := by
  classical
  ext word
  constructor
  · intro hword
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hword
    exact Finset.mem_image.mpr
      ⟨b.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.2⟩, rfl⟩
  · intro hword
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hword
    exact Finset.mem_image.mpr
      ⟨⟨b, (Finset.mem_filter.mp hb).2⟩, Finset.mem_univ _, rfl⟩

/-- Deleting exactly the heavy columns realizes the light-column family used
by the combinatorial no-small-cover rank estimate. -/
private theorem retainedLightColumnFamily_eq
    {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) (cutoff : Nat) :
    (Finset.univ.image fun b : KeptCoordinate
        (Finset.univ.filter fun b : B => cutoff < HammingWeight (columnRestriction b x)) =>
      columnRestriction b (fun ab => x (ab.1, ab.2.1))) =
      (Finset.univ.filter fun b : B =>
        HammingWeight (columnRestriction b x) ≤ cutoff).image
          (fun b => columnRestriction b x) := by
  classical
  rw [retainedColumnFamily_eq]
  congr 1
  ext b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]

/-- No cover by at most `p` rows and `p` columns forces the actual retained
matrix to have at least `p / cutoff + 1` independent columns. -/
private theorem retainedLightColumnSpan_rank_le
    {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) (cutoff w p : Nat)
    (hCutoff : 0 < cutoff) (hWeight : HammingWeight x ≤ w)
    (hHeavyBudget : w < (p + 1) * (cutoff + 1))
    (hNoCover : ∀ rows : Finset A, ∀ columns : Finset B,
      rows.card ≤ p → columns.card ≤ p → ¬ SupportCovered x rows columns) :
    p / cutoff + 1 ≤ Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2)
        ((Finset.univ.image fun b : KeptCoordinate
          (Finset.univ.filter fun b : B =>
            cutoff < HammingWeight (columnRestriction b x)) =>
          columnRestriction b (fun ab => x (ab.1, ab.2.1))) :
            Set (Word (ZMod 2) A))) := by
  rw [retainedLightColumnFamily_eq]
  apply Nat.succ_le_iff.mpr
  apply (Nat.div_lt_iff_lt_mul hCutoff).mpr
  exact puncture_lightColumnSpan_rank_mul_gt_budget x cutoff w p
    hWeight hHeavyBudget hNoCover

/-- Replacing an actual puncture cardinality by its common budget weakens
the integer rarity denominator monotonically. -/
private theorem card_mul_two_pow_le_of_puncture_le
    {eventCard rank checkRows removed budget sampleCard : Nat}
    (hRemoved : removed ≤ budget)
    (hCount : eventCard * 2 ^ (rank * (checkRows - removed)) ≤ sampleCard) :
    eventCard * 2 ^ (rank * (checkRows - budget)) ≤ sampleCard := by
  apply le_trans _ hCount
  apply Nat.mul_le_mul_left
  exact pow_le_pow_right₀ (by decide : 1 ≤ (2 : Nat))
    (Nat.mul_le_mul_left rank (Nat.sub_le_sub_left hRemoved checkRows))

/-- For a fixed word with no small support cover, puncturing its heavy
columns supplies the rank hypothesis for the actual random completion count.
This is a fixed-cylinder estimate, not yet a union over all such words. -/
private theorem card_noSmallCoverRetainedEvent_mul_pow_le
    {A B T : Type v} [Fintype A] [Fintype B] [Fintype T]
    (CA : LinearCode (ZMod 2) A) (x : Word (ZMod 2) (A × B))
    (cutoff w p distance : Nat)
    (hCutoff : 0 < cutoff) (hWeight : HammingWeight x ≤ w)
    (hHeavyBudget : w < (p + 1) * (cutoff + 1))
    (hNoCover : ∀ rows : Finset A, ∀ columns : Finset B,
      rows.card ≤ p → columns.card ≤ p → ¬ SupportCovered x rows columns)
    (hSyndromeBudget : (p / cutoff + 1) * cutoff < distance)
    (hDistance : HasMinimumDistanceAtLeast CA distance) :
    let removed := Finset.univ.filter fun b : B =>
      cutoff < HammingWeight (columnRestriction b x)
    Nat.card {matrix : Matrix T B (ZMod 2) //
      ∃ y : Word (ZMod 2) (A × B),
        y ∈ (dualTensorCode CA (parityCheckKernelCode (Matrix.toLin' matrix))).carrier ∧
        (fun ab : A × KeptCoordinate removed => y (ab.1, ab.2.1)) =
          (fun ab : A × KeptCoordinate removed => x (ab.1, ab.2.1))} *
      2 ^ ((p / cutoff + 1) * (Fintype.card T - p)) ≤
      Nat.card (Matrix T B (ZMod 2)) := by
  classical
  let removed := Finset.univ.filter fun b : B =>
    cutoff < HammingWeight (columnRestriction b x)
  apply card_mul_two_pow_le_of_puncture_le (removed := removed.card)
    (heavyColumns_card_le_punctureBudget x cutoff w p hWeight hHeavyBudget)
  apply card_dualTensorLightRetainedEvent_mul_pow_le CA removed
    (fun ab => x (ab.1, ab.2.1)) cutoff distance (p / cutoff + 1)
  · exact retainedLightColumnSpan_rank_le x cutoff w p
      hCutoff hWeight hHeavyBudget hNoCover
  · intro b
    have hNotHeavy : ¬ cutoff < HammingWeight (columnRestriction b.1 x) := by
      intro hHeavy
      exact b.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hHeavy⟩)
    exact Nat.le_of_not_gt hNotHeavy
  · exact hSyndromeBudget
  · exact hDistance

/-- A finite existential event is bounded by the sum of its indexed event sizes. -/
private theorem nat_card_exists_le_sum
    {ι α : Type v} [Fintype ι] [Finite α] (event : ι → α → Prop) :
    Nat.card {a : α // ∃ i, event i a} ≤ ∑ i, Nat.card {a : α // event i a} := by
  classical
  let project : (Σ i, {a : α // event i a}) → {a : α // ∃ i, event i a} :=
    fun x => ⟨x.2.1, x.1, x.2.2⟩
  have hSurj : Function.Surjective project := by
    intro a
    obtain ⟨i, hi⟩ := a.2
    exact ⟨⟨i, a.1, hi⟩, Subtype.ext rfl⟩
  calc
    _ ≤ Nat.card (Σ i, {a : α // event i a}) :=
      Nat.card_le_card_of_surjective project hSurj
    _ = _ := Nat.card_sigma

/-- Summing integer rarity bounds preserves a common denominator without division. -/
private theorem nat_card_exists_mul_le
    {ι α : Type v} [Fintype ι] [Finite α] (event : ι → α → Prop)
    (factor bound : Nat) (hCount : ∀ i, Nat.card {a : α // event i a} * factor ≤ bound) :
    Nat.card {a : α // ∃ i, event i a} * factor ≤ Nat.card ι * bound := by
  classical
  calc
    _ ≤ (∑ i, Nat.card {a : α // event i a}) * factor :=
      Nat.mul_le_mul_right factor (nat_card_exists_le_sum event)
    _ = ∑ i, Nat.card {a : α // event i a} * factor := by rw [Finset.sum_mul]
    _ ≤ ∑ _i : ι, bound := Finset.sum_le_sum fun i _ => hCount i
    _ = Nat.card ι * bound := by simp [Nat.card_eq_fintype_card]

/-- Indices outside a deterministic admissibility predicate contribute no samples. -/
private theorem nat_card_exists_valid_mul_le
    {ι α : Type v} [Fintype ι] [Finite α] (valid : ι → Prop) (event : ι → α → Prop)
    (factor bound : Nat)
    (hCount : ∀ i, valid i → Nat.card {a : α // event i a} * factor ≤ bound) :
    Nat.card {a : α // ∃ i, valid i ∧ event i a} * factor ≤ Nat.card ι * bound := by
  classical
  apply nat_card_exists_mul_le (fun i a => valid i ∧ event i a)
  intro i
  by_cases hi : valid i
  · exact le_trans (Nat.mul_le_mul_right factor
      (nat_card_event_le_of_imp _ _ fun _ h => h.2)) (hCount i hi)
  · have hEmpty : IsEmpty {a : α // valid i ∧ event i a} :=
      ⟨fun a => hi a.2.1⟩
    have hZero : Nat.card {a : α // valid i ∧ event i a} = 0 :=
      Nat.card_eq_zero.mpr (Or.inl hEmpty)
    rw [hZero, Nat.zero_mul]
    exact Nat.zero_le _

/-- Index every deleted-column set and every light retained matrix, without counting deleted entries. -/
private abbrev AllPuncturedLightMatrixFamily
    (A B : Type v) [Fintype A] [Fintype B] (cutoff : Nat) :=
  Σ removed : Finset B, {x : Word (ZMod 2) (A × KeptCoordinate removed) //
    ∀ b : KeptCoordinate removed, HammingWeight (columnRestriction b x) < cutoff + 1}

/-- All puncture sets and retained light matrices obey the source's coarse Hamming-ball index bound. -/
private theorem card_allPuncturedLightMatrixFamily_le
    (A B : Type v) [Fintype A] [Fintype B] [DecidableEq A] (cutoff : Nat) :
    Nat.card (AllPuncturedLightMatrixFamily A B cutoff) ≤
      2 ^ Fintype.card B *
        (∑ weight ∈ Finset.range (cutoff + 1),
          Nat.choose (Fintype.card A) weight) ^ Fintype.card B := by
  classical
  let volume := ∑ weight ∈ Finset.range (cutoff + 1),
    Nat.choose (Fintype.card A) weight
  have hOne : 1 ≤ volume := by
    have hzero : 0 ∈ Finset.range (cutoff + 1) := Finset.mem_range.mpr (Nat.zero_lt_succ _)
    simpa [volume] using (Finset.single_le_sum
      (fun weight _ => Nat.zero_le (Nat.choose (Fintype.card A) weight)) hzero)
  calc
    _ = ∑ removed : Finset B,
        Nat.card {x : Word (ZMod 2) (A × KeptCoordinate removed) //
          ∀ b : KeptCoordinate removed, HammingWeight (columnRestriction b x) < cutoff + 1} :=
      Nat.card_sigma
    _ = ∑ removed : Finset B, volume ^ (Fintype.card B - removed.card) := by
      apply Finset.sum_congr rfl
      intro removed _
      have h := card_lowWeightColumnMatrices A (KeptCoordinate removed) (cutoff + 1)
      rw [card_keptCoordinate] at h
      rw [Fintype.card_eq_nat_card] at h
      exact h
    _ ≤ ∑ _removed : Finset B, volume ^ Fintype.card B :=
      Finset.sum_le_sum fun removed _ => pow_le_pow_right₀ hOne (Nat.sub_le _ _)
    _ = 2 ^ Fintype.card B * volume ^ Fintype.card B := by
      simp [Fintype.card_finset]

/-- The actual dual-tensor completion cylinder belonging to one retained-matrix index. -/
private abbrev LightRetainedCompletionEvent
    {A B T : Type v} [Fintype A] [Fintype B] [Fintype T]
    (CA : LinearCode (ZMod 2) A) (cutoff : Nat)
    (i : AllPuncturedLightMatrixFamily A B cutoff) (matrix : Matrix T B (ZMod 2)) : Prop :=
  ∃ x : Word (ZMod 2) (A × B),
    x ∈ (dualTensorCode CA (parityCheckKernelCode (Matrix.toLin' matrix))).carrier ∧
    (fun ab : A × KeptCoordinate i.1 => x (ab.1, ab.2.1)) = i.2.1

/-- Keep only deletion sets within budget and retained matrices of sufficient raw column rank. -/
private abbrev ValidLightRetainedIndex
    {A B : Type v} [Fintype A] [Fintype B] (cutoff p rank : Nat)
    (i : AllPuncturedLightMatrixFamily A B cutoff) : Prop :=
  i.1.card ≤ p ∧ rank ≤ Module.finrank (ZMod 2)
    (Submodule.span (ZMod 2)
      ((Finset.univ.image fun b : KeptCoordinate i.1 => columnRestriction b i.2.1) :
        Set (Word (ZMod 2) A)))

/-- Union the actual completion cylinders over all admissible light retained matrices and puncture sets. -/
private theorem card_lightRetainedUnionEvent_mul_pow_le
    {A B T : Type v} [Fintype A] [Fintype B] [Fintype T]
    (CA : LinearCode (ZMod 2) A) (cutoff p distance rank : Nat)
    (hBudget : rank * cutoff < distance) (hDistance : HasMinimumDistanceAtLeast CA distance) :
    Nat.card {matrix : Matrix T B (ZMod 2) //
      ∃ i : AllPuncturedLightMatrixFamily A B cutoff,
        ValidLightRetainedIndex cutoff p rank i ∧ LightRetainedCompletionEvent CA cutoff i matrix} *
      2 ^ (rank * (Fintype.card T - p)) ≤
      (2 ^ Fintype.card B * (∑ weight ∈ Finset.range (cutoff + 1),
        Nat.choose (Fintype.card A) weight) ^ Fintype.card B) *
          Nat.card (Matrix T B (ZMod 2)) := by
  classical
  apply le_trans _ (Nat.mul_le_mul_right _ (card_allPuncturedLightMatrixFamily_le A B cutoff))
  apply nat_card_exists_valid_mul_le (ValidLightRetainedIndex cutoff p rank)
    (LightRetainedCompletionEvent CA cutoff)
  intro i hi
  apply card_mul_two_pow_le_of_puncture_le hi.1
  exact card_dualTensorLightRetainedEvent_mul_pow_le CA i.1 i.2.1 cutoff distance rank hi.2
    (fun b => Nat.le_of_lt_succ (i.2.2 b)) hBudget hDistance

/-- Bound all low-weight dual-tensor words with no small support cover by
retained cylinders. This proves the finite bad-word count, not yet
puncture-resistant robustness or final goodness. -/
private theorem card_noSmallCoverDualTensorEvent_mul_pow_le
    {A B T : Type v} [Fintype A] [Fintype B] [Fintype T]
    (CA : LinearCode (ZMod 2) A) (cutoff w p distance : Nat)
    (hCutoff : 0 < cutoff) (hHeavyBudget : w < (p + 1) * (cutoff + 1))
    (hSyndromeBudget : (p / cutoff + 1) * cutoff < distance)
    (hDistance : HasMinimumDistanceAtLeast CA distance) :
    Nat.card {matrix : Matrix T B (ZMod 2) //
      ∃ x : Word (ZMod 2) (A × B),
        x ∈ (dualTensorCode CA (parityCheckKernelCode (Matrix.toLin' matrix))).carrier ∧
        HammingWeight x ≤ w ∧
        ∀ rows : Finset A, ∀ columns : Finset B,
          rows.card ≤ p → columns.card ≤ p → ¬ SupportCovered x rows columns} *
      2 ^ ((p / cutoff + 1) * (Fintype.card T - p)) ≤
      (2 ^ Fintype.card B * (∑ weight ∈ Finset.range (cutoff + 1),
        Nat.choose (Fintype.card A) weight) ^ Fintype.card B) *
          Nat.card (Matrix T B (ZMod 2)) := by
  classical
  apply le_trans _ (card_lightRetainedUnionEvent_mul_pow_le
    CA cutoff p distance (p / cutoff + 1) hSyndromeBudget hDistance)
  apply Nat.mul_le_mul_right
  apply nat_card_event_le_of_imp
  intro matrix hBad
  obtain ⟨x, hx, hWeight, hNoCover⟩ := hBad
  let removed := Finset.univ.filter fun b : B =>
    cutoff < HammingWeight (columnRestriction b x)
  have hLight : ∀ b : KeptCoordinate removed,
      HammingWeight (columnRestriction b (fun ab => x (ab.1, ab.2.1))) < cutoff + 1 := by
    intro b
    apply Nat.lt_succ_of_le
    apply Nat.le_of_not_gt
    intro hHeavy
    exact b.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hHeavy⟩)
  let i : AllPuncturedLightMatrixFamily A B cutoff :=
    ⟨removed, (fun ab => x (ab.1, ab.2.1)), hLight⟩
  refine ⟨i, ⟨?_, ?_⟩, x, hx, rfl⟩
  · exact heavyColumns_card_le_punctureBudget x cutoff w p hWeight hHeavyBudget
  · exact retainedLightColumnSpan_rank_le x cutoff w p hCutoff hWeight hHeavyBudget hNoCover

/-- Count actual failures of distance-normalized Core robustness among
distance-good random kernels, using the genuinely proved bad-cover estimate. -/
private theorem card_notRobust_distanceGoodKernel_mul_pow_le
    {A B T : Type v} [Fintype A] [Fintype B] [Fintype T]
    (CA : LinearCode (ZMod 2) A) (cutoff w p distanceA distanceB : Nat)
    (hCutoff : 0 < cutoff) (hHeavyBudget : w < (p + 1) * (cutoff + 1))
    (hSyndromeBudget : (p / cutoff + 1) * cutoff < distanceA)
    (hDistance : HasMinimumDistanceAtLeast CA distanceA)
    (hRows : 2 * p ≤ distanceA) (hColumns : 2 * p ≤ distanceB) :
    Nat.card {matrix : Matrix T B (ZMod 2) //
      HasMinimumDistanceAtLeast (parityCheckKernelCode (Matrix.toLin' matrix)) distanceB ∧
        ¬ IsRobust CA (parityCheckKernelCode (Matrix.toLin' matrix)) w} *
      2 ^ ((p / cutoff + 1) * (Fintype.card T - p)) ≤
      (2 ^ Fintype.card B * (∑ weight ∈ Finset.range (cutoff + 1),
        Nat.choose (Fintype.card A) weight) ^ Fintype.card B) *
          Nat.card (Matrix T B (ZMod 2)) := by
  apply le_trans _ (card_noSmallCoverDualTensorEvent_mul_pow_le
    CA cutoff w p distanceA hCutoff hHeavyBudget hSyndromeBudget hDistance)
  apply Nat.mul_le_mul_right
  apply nat_card_event_le_of_imp
  intro matrix hBad
  exact not_isRobust_imp_noSmallCover CA (parityCheckKernelCode (Matrix.toLin' matrix))
    distanceA distanceB p w hDistance hBad.1 hRows hColumns hBad.2

/-- A concrete light nested-retained matrix index with frozen projection types. -/
private structure NestedLightRetainedIndex
    (A B : Type v) [Fintype A] [Fintype B] (removed : Finset B) (cutoff : Nat) where
  more : Finset (KeptCoordinate removed)
  retained : Word (ZMod 2) (A × KeptCoordinate more)
  light : ∀ b : KeptCoordinate more, HammingWeight (columnRestriction b retained) < cutoff + 1

private def nestedLightRetainedIndexEquiv
    (A B : Type v) [Fintype A] [Fintype B] (removed : Finset B) (cutoff : Nat) :
    NestedLightRetainedIndex A B removed cutoff ≃
      AllPuncturedLightMatrixFamily A (KeptCoordinate removed) cutoff where
  toFun i := ⟨i.more, i.retained, i.light⟩
  invFun i := ⟨i.1, i.2.1, i.2.2⟩
  left_inv i := by cases i; rfl
  right_inv i := by rcases i with ⟨more, retained, light⟩; rfl

private instance nestedLightRetainedIndexFinite
    (A B : Type v) [Fintype A] [Fintype B] (removed : Finset B) (cutoff : Nat) :
    Finite (NestedLightRetainedIndex A B removed cutoff) :=
  Finite.of_equiv _ (nestedLightRetainedIndexEquiv A B removed cutoff).symm

private theorem card_nestedLightRetainedIndex_eq
    (A B : Type v) [Fintype A] [Fintype B] (removed : Finset B) (cutoff : Nat) :
    Nat.card (NestedLightRetainedIndex A B removed cutoff) =
      Nat.card (AllPuncturedLightMatrixFamily A (KeptCoordinate removed) cutoff) :=
  Nat.card_congr (nestedLightRetainedIndexEquiv A B removed cutoff)

private abbrev ValidNestedLightRetainedIndex
    {A B : Type v} [Fintype A] [Fintype B] (removed : Finset B) (cutoff p rank : Nat)
    (i : NestedLightRetainedIndex A B removed cutoff) : Prop :=
  i.more.card ≤ p ∧ rank ≤ Module.finrank (ZMod 2)
    (Submodule.span (ZMod 2)
      ((Finset.univ.image fun b : KeptCoordinate i.more => columnRestriction b i.retained) :
        Set (Word (ZMod 2) A)))

/-- A retained cylinder for the actual externally punctured sampled kernel. -/
private abbrev PuncturedLightRetainedCompletionEvent
    {A B T : Type v} [Fintype A] [Fintype B] [Fintype T]
    (CA : LinearCode (ZMod 2) A) (removed : Finset B) (cutoff : Nat)
    (i : NestedLightRetainedIndex A B removed cutoff)
    (matrix : Matrix T B (ZMod 2)) : Prop :=
  ∃ x : Word (ZMod 2) (A × KeptCoordinate removed),
    x ∈ (dualTensorCode CA
      (puncturedCode (parityCheckKernelCode (Matrix.toLin' matrix)) removed)).carrier ∧
    (fun ab : A × KeptCoordinate i.more => x (ab.1, ab.2.1)) = i.retained

/-- Union genuine punctured cylinders in the original matrix experiment,
using the common external-plus-internal deletion budget. -/
private theorem card_puncturedLightRetainedUnionEvent_mul_pow_le
    {A B T : Type v} [Fintype A] [Fintype B] [Fintype T]
    (CA : LinearCode (ZMod 2) A) (removed : Finset B)
    (cutoff p distance rank : Nat)
    (hBudget : rank * cutoff < distance) (hDistance : HasMinimumDistanceAtLeast CA distance) :
    Nat.card {matrix : Matrix T B (ZMod 2) //
      ∃ i : NestedLightRetainedIndex A B removed cutoff,
        ValidNestedLightRetainedIndex removed cutoff p rank i ∧
          PuncturedLightRetainedCompletionEvent CA removed cutoff i matrix} *
      2 ^ (rank * (Fintype.card T - (removed.card + p))) ≤
      (2 ^ Fintype.card (KeptCoordinate removed) *
        (∑ weight ∈ Finset.range (cutoff + 1),
          Nat.choose (Fintype.card A) weight) ^ Fintype.card (KeptCoordinate removed)) *
          Nat.card (Matrix T B (ZMod 2)) := by
  classical
  letI : Fintype (NestedLightRetainedIndex A B removed cutoff) := Fintype.ofFinite _
  have hIndex : Nat.card (NestedLightRetainedIndex A B removed cutoff) ≤
      2 ^ Fintype.card (KeptCoordinate removed) *
        (∑ weight ∈ Finset.range (cutoff + 1),
          Nat.choose (Fintype.card A) weight) ^ Fintype.card (KeptCoordinate removed) := by
    rw [card_nestedLightRetainedIndex_eq]
    exact card_allPuncturedLightMatrixFamily_le A (KeptCoordinate removed) cutoff
  apply le_trans _ (Nat.mul_le_mul_right _ hIndex)
  apply nat_card_exists_valid_mul_le (ValidNestedLightRetainedIndex removed cutoff p rank)
    (PuncturedLightRetainedCompletionEvent CA removed cutoff)
  intro i hi
  apply card_mul_two_pow_le_of_puncture_le
    (removed := removed.card + i.more.card) (Nat.add_le_add_left hi.1 removed.card)
  exact card_nestedPuncturedDualTensorLightRetainedEvent_mul_pow_le
    CA removed i.more i.retained cutoff distance rank hi.2
    (fun b => Nat.le_of_lt_succ (i.light b)) hBudget hDistance



/-- The raw column span can be represented without a coordinate enumeration. -/
private theorem rawColumnSpanRank_eq_range
    {A C : Type v} [Fintype A] [Fintype C] (x : Word (ZMod 2) (A × C)) :
    Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2)
        ((Finset.univ.image fun c : C => columnRestriction c x) : Set (Word (ZMod 2) A))) =
    Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range fun c : C => fun a : A => x (a, c))) := by
  have hFamily :
      ((Finset.univ.image fun c : C => columnRestriction c x) : Set (Word (ZMod 2) A)) =
        Set.range (fun c : C => fun a : A => x (a, c)) := by
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    rfl
  exact congrArg (fun s : Set (Word (ZMod 2) A) =>
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) s)) hFamily

/-- Freeze the retained-coordinate type before forming the geometric union. -/
private theorem card_noSmallCoverCompletionEvent_mul_le
    {A C α : Type v} [Fintype A] [Fintype C] [Finite α]
    (membership : Word (ZMod 2) (A × C) → α → Prop)
    (cutoff w p factor : Nat)
    (hCutoff : 0 < cutoff) (hHeavyBudget : w < (p + 1) * (cutoff + 1))
    (hCount : ∀ more : Finset C,
      ∀ retained : Word (ZMod 2) (A × KeptCoordinate more),
      (∀ b : KeptCoordinate more, HammingWeight (columnRestriction b retained) < cutoff + 1) →
      more.card ≤ p →
      p / cutoff + 1 ≤ Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2)
          (Set.range fun b : KeptCoordinate more => fun a : A => retained (a, b))) →
      Nat.card {a : α // ∃ x, membership x a ∧
        (fun ab : A × KeptCoordinate more => x (ab.1, ab.2.1)) = retained} * factor ≤
          Nat.card α) :
    Nat.card {a : α // ∃ x, membership x a ∧ HammingWeight x ≤ w ∧
      ∀ rows : Finset A, ∀ columns : Finset C,
        rows.card ≤ p → columns.card ≤ p → ¬ SupportCovered x rows columns} * factor ≤
      (2 ^ Fintype.card C * (∑ weight ∈ Finset.range (cutoff + 1),
        Nat.choose (Fintype.card A) weight) ^ Fintype.card C) * Nat.card α := by
  classical
  let valid : AllPuncturedLightMatrixFamily A C cutoff → Prop := fun i =>
    i.1.card ≤ p ∧ p / cutoff + 1 ≤ Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range fun b : KeptCoordinate i.1 => fun a : A => i.2.1 (a, b)))
  let completion : AllPuncturedLightMatrixFamily A C cutoff → α → Prop :=
    fun i a => ∃ x, membership x a ∧
      (fun ab : A × KeptCoordinate i.1 => x (ab.1, ab.2.1)) = i.2.1
  have hUnion : Nat.card {a : α // ∃ i : AllPuncturedLightMatrixFamily A C cutoff,
      valid i ∧ completion i a} * factor ≤
      (2 ^ Fintype.card C * (∑ weight ∈ Finset.range (cutoff + 1),
        Nat.choose (Fintype.card A) weight) ^ Fintype.card C) * Nat.card α := by
    apply le_trans _ (Nat.mul_le_mul_right _ (card_allPuncturedLightMatrixFamily_le A C cutoff))
    apply nat_card_exists_valid_mul_le
      valid completion
    intro i hi
    exact hCount i.1 i.2.1 i.2.2 hi.1 hi.2
  apply le_trans _ hUnion
  apply Nat.mul_le_mul_right
  apply nat_card_event_le_of_imp
  intro a hBad
  obtain ⟨x, hx, hWeight, hNoCover⟩ := hBad
  let more := Finset.univ.filter fun b : C => cutoff < HammingWeight (columnRestriction b x)
  have hLight : ∀ b : KeptCoordinate more,
      HammingWeight (columnRestriction b (fun ab => x (ab.1, ab.2.1))) < cutoff + 1 := by
    intro b
    apply Nat.lt_succ_of_le
    apply Nat.le_of_not_gt
    intro hHeavy
    exact b.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hHeavy⟩)
  let i : AllPuncturedLightMatrixFamily A C cutoff :=
    ⟨more, (fun ab => x (ab.1, ab.2.1)), hLight⟩
  refine ⟨i, ⟨?_, ?_⟩, x, hx, rfl⟩
  · exact heavyColumns_card_le_punctureBudget x cutoff w p hWeight hHeavyBudget
  · have hRank := retainedLightColumnSpan_rank_le x cutoff w p hCutoff hWeight hHeavyBudget hNoCover
    rw [rawColumnSpanRank_eq_range] at hRank
    exact hRank

private theorem card_budgetedNestedRetainedEvent_mul_pow_le
    {A B T : Type v} [Fintype A] [Fintype B] [Fintype T]
    (CA : LinearCode (ZMod 2) A) (removed : Finset B)
    (more : Finset (KeptCoordinate removed))
    (retained : Word (ZMod 2) (A × KeptCoordinate more))
    (cutoff p distance rank : Nat)
    (hLight : ∀ b : KeptCoordinate more, HammingWeight (columnRestriction b retained) < cutoff + 1)
    (hCard : more.card ≤ p)
    (hRank : rank ≤ Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2)
        (Set.range fun b : KeptCoordinate more => fun a : A => retained (a, b))))
    (hBudget : rank * cutoff < distance) (hDistance : HasMinimumDistanceAtLeast CA distance) :
    Nat.card {matrix : Matrix T B (ZMod 2) //
      ∃ x : Word (ZMod 2) (A × KeptCoordinate removed),
        x ∈ (dualTensorCode CA
          (puncturedCode (parityCheckKernelCode (Matrix.toLin' matrix)) removed)).carrier ∧
        (fun ab : A × KeptCoordinate more => x (ab.1, ab.2.1)) = retained} *
      2 ^ (rank * (Fintype.card T - (removed.card + p))) ≤
      Nat.card (Matrix T B (ZMod 2)) := by
  apply card_mul_two_pow_le_of_puncture_le
    (removed := removed.card + more.card) (Nat.add_le_add_left hCard removed.card)
  exact card_nestedPuncturedDualTensorLightRetainedEvent_mul_pow_le
    CA removed more retained cutoff distance rank
    (by rw [rawColumnSpanRank_eq_range]; exact hRank)
    (fun b => Nat.le_of_lt_succ (hLight b)) hBudget hDistance

/-- Count actual punctured bad words in the original random matrix experiment. -/
private theorem card_puncturedNoSmallCoverDualTensorEvent_mul_pow_le
    {A B T : Type v} [Fintype A] [Fintype B] [Fintype T]
    (CA : LinearCode (ZMod 2) A) (removed : Finset B) (cutoff w p distance : Nat)
    (hCutoff : 0 < cutoff) (hHeavyBudget : w < (p + 1) * (cutoff + 1))
    (hSyndromeBudget : (p / cutoff + 1) * cutoff < distance)
    (hDistance : HasMinimumDistanceAtLeast CA distance) :
    Nat.card {matrix : Matrix T B (ZMod 2) //
      ∃ x : Word (ZMod 2) (A × KeptCoordinate removed),
        x ∈ (dualTensorCode CA
          (puncturedCode (parityCheckKernelCode (Matrix.toLin' matrix)) removed)).carrier ∧
        HammingWeight x ≤ w ∧
        ∀ rows : Finset A, ∀ columns : Finset (KeptCoordinate removed),
          rows.card ≤ p → columns.card ≤ p → ¬ SupportCovered x rows columns} *
      2 ^ ((p / cutoff + 1) * (Fintype.card T - (removed.card + p))) ≤
      (2 ^ Fintype.card (KeptCoordinate removed) *
        (∑ weight ∈ Finset.range (cutoff + 1),
          Nat.choose (Fintype.card A) weight) ^ Fintype.card (KeptCoordinate removed)) *
          Nat.card (Matrix T B (ZMod 2)) := by
  apply card_noSmallCoverCompletionEvent_mul_le
    (fun x matrix => x ∈ (dualTensorCode CA
      (puncturedCode (parityCheckKernelCode (Matrix.toLin' matrix)) removed)).carrier)
    cutoff w p _ hCutoff hHeavyBudget
  intro more retained hLight hCard hRank
  exact card_budgetedNestedRetainedEvent_mul_pow_le
    CA removed more retained cutoff p distance (p / cutoff + 1)
    hLight hCard hRank hSyndromeBudget hDistance

/-- Robustness failure after actual puncturing, conditioned on the original distance. -/
private theorem card_notRobust_distanceGoodPuncturedKernel_mul_pow_le
    {A B T : Type v} [Fintype A] [Fintype B] [Fintype T]
    (CA : LinearCode (ZMod 2) A) (removed : Finset B)
    (cutoff w p distanceA distanceB : Nat)
    (hCutoff : 0 < cutoff) (hHeavyBudget : w < (p + 1) * (cutoff + 1))
    (hSyndromeBudget : (p / cutoff + 1) * cutoff < distanceA)
    (hDistance : HasMinimumDistanceAtLeast CA distanceA)
    (hRows : 2 * p ≤ distanceA) (hColumns : 2 * p ≤ distanceB - removed.card) :
    Nat.card {matrix : Matrix T B (ZMod 2) //
      HasMinimumDistanceAtLeast (parityCheckKernelCode (Matrix.toLin' matrix)) distanceB ∧
        ¬ IsRobust CA
          (puncturedCode (parityCheckKernelCode (Matrix.toLin' matrix)) removed) w} *
      2 ^ ((p / cutoff + 1) * (Fintype.card T - (removed.card + p))) ≤
      (2 ^ Fintype.card (KeptCoordinate removed) *
        (∑ weight ∈ Finset.range (cutoff + 1),
          Nat.choose (Fintype.card A) weight) ^ Fintype.card (KeptCoordinate removed)) *
          Nat.card (Matrix T B (ZMod 2)) := by
  apply le_trans _ (card_puncturedNoSmallCoverDualTensorEvent_mul_pow_le
    CA removed cutoff w p distanceA hCutoff hHeavyBudget hSyndromeBudget hDistance)
  apply Nat.mul_le_mul_right
  apply nat_card_event_le_of_imp
  intro matrix hBad
  exact not_isRobust_imp_noSmallCover CA
    (puncturedCode (parityCheckKernelCode (Matrix.toLin' matrix)) removed)
    distanceA (distanceB - removed.card) p w hDistance
    (hasMinimumDistanceAtLeast_puncturedCode _ distanceB removed hBad.1)
    hRows hColumns hBad.2


/-- Retained coordinate Hamming-ball indices admit one ambient-size bound. -/
private theorem puncturedLightIndexBound_le
    {A B : Type v} [Fintype A] [Fintype B]
    (removedA : Finset A) (removedB : Finset B) (cutoff : Nat) :
    (2 ^ Fintype.card (KeptCoordinate removedB) *
      (∑ weight ∈ Finset.range (cutoff + 1),
        Nat.choose (Fintype.card (KeptCoordinate removedA)) weight) ^
          Fintype.card (KeptCoordinate removedB)) ≤
      2 ^ Fintype.card B *
        (∑ weight ∈ Finset.range (cutoff + 1),
          Nat.choose (Fintype.card A) weight) ^ Fintype.card B := by
  classical
  let volume := ∑ weight ∈ Finset.range (cutoff + 1),
    Nat.choose (Fintype.card A) weight
  have hA : Fintype.card (KeptCoordinate removedA) ≤ Fintype.card A := by
    rw [card_keptCoordinate]
    exact Nat.sub_le _ _
  have hB : Fintype.card (KeptCoordinate removedB) ≤ Fintype.card B := by
    rw [card_keptCoordinate]
    exact Nat.sub_le _ _
  have hOne : 1 ≤ volume := by
    have hzero : 0 ∈ Finset.range (cutoff + 1) := Finset.mem_range.mpr (Nat.zero_lt_succ _)
    simpa [volume] using (Finset.single_le_sum
      (fun weight _ => Nat.zero_le (Nat.choose (Fintype.card A) weight)) hzero)
  apply Nat.mul_le_mul
  · exact pow_le_pow_right₀ (by decide : 1 ≤ (2 : Nat)) hB
  · apply le_trans (Nat.pow_le_pow_left
      (Finset.sum_le_sum fun weight _ => Nat.choose_le_choose weight hA) _)
    exact pow_le_pow_right₀ hOne hB

/-- A matching external deletion pair has an actual robustness-failure bound
in the original check-matrix experiment, with one common puncture budget. -/
private theorem card_matchingPuncturedRobustFailure_mul_pow_le
    {A B T : Type v} [Fintype A] [Fintype B] [Fintype T]
    (CA : LinearCode (ZMod 2) A) (removedA : Finset A) (removedB : Finset B)
    (cutoff w p q distanceA distanceB : Nat)
    (hMatching : removedA.card = removedB.card) (hCard : removedA.card ≤ q)
    (hCutoff : 0 < cutoff) (hHeavyBudget : w < (p + 1) * (cutoff + 1))
    (hSyndromeBudget : (p / cutoff + 1) * cutoff < distanceA - q)
    (hDistance : HasMinimumDistanceAtLeast CA distanceA)
    (hRows : 2 * p ≤ distanceA - q) (hColumns : 2 * p ≤ distanceB - q) :
    Nat.card {matrix : Matrix T B (ZMod 2) //
      HasMinimumDistanceAtLeast (parityCheckKernelCode (Matrix.toLin' matrix)) distanceB ∧
        ¬ IsRobust (puncturedCode CA removedA)
          (puncturedCode (parityCheckKernelCode (Matrix.toLin' matrix)) removedB) w} *
      2 ^ ((p / cutoff + 1) * (Fintype.card T - (q + p))) ≤
      (2 ^ Fintype.card B *
        (∑ weight ∈ Finset.range (cutoff + 1),
          Nat.choose (Fintype.card A) weight) ^ Fintype.card B) *
            Nat.card (Matrix T B (ZMod 2)) := by
  have hBCard : removedB.card ≤ q := by omega
  have hCount := card_notRobust_distanceGoodPuncturedKernel_mul_pow_le (T := T)
    (puncturedCode CA removedA) removedB cutoff w p (distanceA - q) distanceB
    hCutoff hHeavyBudget hSyndromeBudget
    (hasMinimumDistanceAtLeast_puncturedCode_of_card_le CA distanceA q removedA hDistance hCard)
    hRows (by omega)
  have hBudgeted := card_mul_two_pow_le_of_puncture_le
    (removed := removedB.card + p) (budget := q + p)
    (Nat.add_le_add_right hBCard p) hCount
  exact le_trans hBudgeted (Nat.mul_le_mul_right _
    (puncturedLightIndexBound_le removedA removedB cutoff))


/-- Enumerate matching punctures by their actual common size and deletion sets. -/
private abbrev MatchingPunctureIndex
    (A B : Type v) [Fintype A] [Fintype B] (q : Nat) :=
  Σ size : Fin (q + 1),
    {removedA : Finset A // removedA.card = size.1} ×
      {removedB : Finset B // removedB.card = size.1}

/-- The source's exact matching-puncture multiplicity, with no deleted values. -/
private theorem card_matchingPunctureIndex
    (A B : Type v) [Fintype A] [Fintype B] (q : Nat) :
    Nat.card (MatchingPunctureIndex A B q) =
      ∑ size ∈ Finset.range (q + 1),
        Nat.choose (Fintype.card A) size * Nat.choose (Fintype.card B) size := by
  classical
  simp [MatchingPunctureIndex, Nat.card_eq_fintype_card,
    Fintype.card_sigma, Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro size hSize
  simp [Nat.lt_succ_iff.mp (Finset.mem_range.mp hSize)]

/-- Union every actual matching external puncture pair without replacing
punctured kernels by fresh random kernels. This is a finite conditional bound. -/
private theorem card_notPunctureResistant_distanceGoodKernel_mul_pow_le
    {A B T : Type v} [Fintype A] [Fintype B] [Fintype T]
    (CA : LinearCode (ZMod 2) A) (cutoff w p q distanceA distanceB : Nat)
    (hCutoff : 0 < cutoff) (hHeavyBudget : w < (p + 1) * (cutoff + 1))
    (hSyndromeBudget : (p / cutoff + 1) * cutoff < distanceA - q)
    (hDistance : HasMinimumDistanceAtLeast CA distanceA)
    (hRows : 2 * p ≤ distanceA - q) (hColumns : 2 * p ≤ distanceB - q) :
    Nat.card {matrix : Matrix T B (ZMod 2) //
      HasMinimumDistanceAtLeast (parityCheckKernelCode (Matrix.toLin' matrix)) distanceB ∧
        ¬ IsRobustWithPunctureResistance CA
          (parityCheckKernelCode (Matrix.toLin' matrix)) w q} *
      2 ^ ((p / cutoff + 1) * (Fintype.card T - (q + p))) ≤
      (∑ size ∈ Finset.range (q + 1),
        Nat.choose (Fintype.card A) size * Nat.choose (Fintype.card B) size) *
        ((2 ^ Fintype.card B *
          (∑ weight ∈ Finset.range (cutoff + 1),
            Nat.choose (Fintype.card A) weight) ^ Fintype.card B) *
              Nat.card (Matrix T B (ZMod 2))) := by
  classical
  let event : MatchingPunctureIndex A B q → Matrix T B (ZMod 2) → Prop :=
    fun i matrix =>
      HasMinimumDistanceAtLeast (parityCheckKernelCode (Matrix.toLin' matrix)) distanceB ∧
        ¬ IsRobust (puncturedCode CA i.2.1.1)
          (puncturedCode (parityCheckKernelCode (Matrix.toLin' matrix)) i.2.2.1) w
  have hUnion := nat_card_exists_mul_le event
    (2 ^ ((p / cutoff + 1) * (Fintype.card T - (q + p))))
    ((2 ^ Fintype.card B *
      (∑ weight ∈ Finset.range (cutoff + 1),
        Nat.choose (Fintype.card A) weight) ^ Fintype.card B) *
          Nat.card (Matrix T B (ZMod 2)))
    (fun i => card_matchingPuncturedRobustFailure_mul_pow_le
      CA i.2.1.1 i.2.2.1 cutoff w p q distanceA distanceB
      (i.2.1.2.trans i.2.2.2.symm) (by have h := i.1.2; have hA := i.2.1.2; omega)
      hCutoff hHeavyBudget hSyndromeBudget hDistance hRows hColumns)
  rw [card_matchingPunctureIndex] at hUnion
  apply le_trans _ hUnion
  apply Nat.mul_le_mul_right
  apply nat_card_event_le_of_imp
  intro matrix hBad
  have hNot := hBad.2
  simp only [IsRobustWithPunctureResistance] at hNot
  push Not at hNot
  obtain ⟨removedA, removedB, hMatching, hCard, hFail⟩ := hNot
  let i : MatchingPunctureIndex A B q :=
    ⟨⟨removedA.card, Nat.lt_succ_of_le hCard⟩,
      ⟨removedA, rfl⟩, ⟨removedB, hMatching.symm⟩⟩
  exact ⟨i, hBad.1, hFail⟩

/-- Product-event fibers preserve the actual two-matrix sample, without
resampling either coordinate. -/
private def productEventFiberEquiv
    {α β : Type v} (event : α × β → Prop) :
    {sample : α × β // event sample} ≃
      Σ first : α, {second : β // event (first, second)} where
  toFun sample := ⟨sample.1.1, sample.1.2, sample.2⟩
  invFun sample := ⟨(sample.1, sample.2.1), sample.2.2⟩
  left_inv sample := by
    apply Subtype.ext
    rfl
  right_inv sample := by
    cases sample
    rfl

/-- A common integer bound on each true conditional fiber bounds the joint
event. No independence of the good events is asserted. -/
private theorem nat_card_product_event_mul_le
    {α β : Type v} [Fintype α] [Finite β]
    (event : α × β → Prop) (factor bound : Nat)
    (hCount : ∀ first, Nat.card {second : β // event (first, second)} *
      factor ≤ bound) :
    Nat.card {sample : α × β // event sample} * factor ≤
      Nat.card α * bound := by
  classical
  rw [Nat.card_congr (productEventFiberEquiv event),
    Nat.card_sigma, Finset.sum_mul]
  calc
    _ ≤ ∑ _first : α, bound := Finset.sum_le_sum fun first _ => hCount first
    _ = Nat.card α * bound := by simp [Nat.card_eq_fintype_card]

/-- Integrate the proved fixed-code puncture-failure bound over the actual
first generator matrix, retaining both distance conditions on the joint draw. -/
private theorem card_jointPrimalPunctureFailure_mul_pow_le
    {A B T : Type v} [Fintype A] [Fintype B] [Fintype T]
    (cutoff w p q distanceA distanceB : Nat)
    (hCutoff : 0 < cutoff) (hHeavyBudget : w < (p + 1) * (cutoff + 1))
    (hSyndromeBudget : (p / cutoff + 1) * cutoff < distanceA - q)
    (hRows : 2 * p ≤ distanceA - q) (hColumns : 2 * p ≤ distanceB - q) :
    Nat.card {sample : Matrix T A (ZMod 2) × Matrix T B (ZMod 2) //
      HasMinimumDistanceAtLeast (parityCheckRowCode (Matrix.toLin' sample.1)) distanceA ∧
      HasMinimumDistanceAtLeast (parityCheckKernelCode (Matrix.toLin' sample.2)) distanceB ∧
      ¬ IsRobustWithPunctureResistance
        (parityCheckRowCode (Matrix.toLin' sample.1))
        (parityCheckKernelCode (Matrix.toLin' sample.2)) w q} *
      2 ^ ((p / cutoff + 1) * (Fintype.card T - (q + p))) ≤
      ((∑ size ∈ Finset.range (q + 1),
        Nat.choose (Fintype.card A) size * Nat.choose (Fintype.card B) size) *
        (2 ^ Fintype.card B *
          (∑ weight ∈ Finset.range (cutoff + 1),
            Nat.choose (Fintype.card A) weight) ^ Fintype.card B)) *
              Nat.card (Matrix T A (ZMod 2) × Matrix T B (ZMod 2)) := by
  classical
  let numerator :=
    (∑ size ∈ Finset.range (q + 1),
      Nat.choose (Fintype.card A) size * Nat.choose (Fintype.card B) size) *
        (2 ^ Fintype.card B *
          (∑ weight ∈ Finset.range (cutoff + 1),
            Nat.choose (Fintype.card A) weight) ^ Fintype.card B)
  apply le_trans (nat_card_product_event_mul_le _
    (2 ^ ((p / cutoff + 1) * (Fintype.card T - (q + p))))
    (numerator * Nat.card (Matrix T B (ZMod 2))) ?_)
  · rw [Nat.card_prod]
    change Nat.card (Matrix T A (ZMod 2)) *
      (numerator * Nat.card (Matrix T B (ZMod 2))) ≤
        numerator * (Nat.card (Matrix T A (ZMod 2)) * Nat.card (Matrix T B (ZMod 2)))
    exact le_of_eq (by ring)
  · intro first
    by_cases hFirst :
        HasMinimumDistanceAtLeast (parityCheckRowCode (Matrix.toLin' first)) distanceA
    · have hCount := card_notPunctureResistant_distanceGoodKernel_mul_pow_le (B := B) (T := T)
        (parityCheckRowCode (Matrix.toLin' first)) cutoff w p q distanceA distanceB
        hCutoff hHeavyBudget hSyndromeBudget hFirst hRows hColumns
      apply le_trans (Nat.mul_le_mul_right _
        (nat_card_event_le_of_imp _ _ fun _ h => h.2))
      simpa [numerator, Nat.mul_assoc] using hCount
    · have hEmpty : IsEmpty {second : Matrix T B (ZMod 2) //
          HasMinimumDistanceAtLeast (parityCheckRowCode (Matrix.toLin' first)) distanceA ∧
          HasMinimumDistanceAtLeast (parityCheckKernelCode (Matrix.toLin' second)) distanceB ∧
          ¬ IsRobustWithPunctureResistance
            (parityCheckRowCode (Matrix.toLin' first))
            (parityCheckKernelCode (Matrix.toLin' second)) w q} :=
        ⟨fun second => hFirst second.2.1⟩
      rw [Nat.card_eq_zero.mpr (Or.inl hEmpty), Nat.zero_mul]
      exact Nat.zero_le _

/-- Exchange the tensor coordinates without changing the represented values. -/
private def transposeTensorWord
    {A B : Type v} (x : Word (ZMod 2) (A × B)) : Word (ZMod 2) (B × A) :=
  fun coordinate => x (coordinate.2, coordinate.1)

private theorem transposeTensorWord_involutive
    {A B : Type v} (x : Word (ZMod 2) (A × B)) :
    transposeTensorWord (transposeTensorWord x) = x := rfl

private theorem hammingWeight_transposeTensorWord
    {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) :
    HammingWeight (transposeTensorWord x) = HammingWeight x := by
  classical
  unfold HammingWeight
  apply Finset.card_bij (fun coordinate _ => (coordinate.2, coordinate.1))
  · intro coordinate hCoordinate
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hCoordinate).2⟩
  · intro first hFirst second hSecond hEqual
    exact Prod.ext (congrArg Prod.snd hEqual) (congrArg Prod.fst hEqual)
  · intro coordinate hCoordinate
    exact ⟨(coordinate.2, coordinate.1),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hCoordinate).2⟩, rfl⟩

/-- Transposition exchanges the actual column and row summands. -/
private theorem mem_dualTensorCode_transposeTensorWord
    {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    {x : Word (ZMod 2) (A × B)} (hx : x ∈ (dualTensorCode CA CB).carrier) :
    transposeTensorWord x ∈ (dualTensorCode CB CA).carrier := by
  rcases Submodule.mem_sup.mp hx with ⟨columnPart, hColumn, rowPart, hRow, hSum⟩
  apply Submodule.mem_sup.mpr
  refine ⟨transposeTensorWord rowPart, ?_, transposeTensorWord columnPart, ?_, ?_⟩
  · change ∀ a, columnRestriction a (transposeTensorWord rowPart) ∈ CB.carrier
    intro a
    exact hRow a
  · change ∀ b, rowRestriction b (transposeTensorWord columnPart) ∈ CA.carrier
    intro b
    exact hColumn b
  · ext coordinate
    simpa [transposeTensorWord, add_comm] using
      congrArg (fun z : Word (ZMod 2) (A × B) => z (coordinate.2, coordinate.1)) hSum

/-- An actual support cover transposes with its row and column sets. -/
private theorem supportCovered_transposeTensorWord
    {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) (rows : Finset A) (columns : Finset B)
    (hCover : SupportCovered x rows columns) :
    SupportCovered (transposeTensorWord x) columns rows := by
  intro coordinate hCoordinate
  have hOriginal : (coordinate.2, coordinate.1) ∈ hammingSupport x := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hCoordinate).2⟩
  have hCovered := hCover hOriginal
  rcases Finset.mem_union.mp hCovered with hRows | hColumns
  · exact Finset.mem_union.mpr (Or.inr
      (Finset.mem_product.mpr ⟨Finset.mem_univ _, (Finset.mem_product.mp hRows).1⟩))
  · exact Finset.mem_union.mpr (Or.inl
      (Finset.mem_product.mpr ⟨(Finset.mem_product.mp hColumns).2, Finset.mem_univ _⟩))

/-- Distance-normalized robustness is genuinely symmetric in the two local codes. -/
private theorem isRobust_swap
    {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B) (w : Nat)
    (hRobust : IsRobust CA CB w) : IsRobust CB CA w := by
  intro distanceB distanceA hB hA x hx hWeight
  have hTransposed := mem_dualTensorCode_transposeTensorWord CB CA hx
  have hTransposedWeight := hammingWeight_transposeTensorWord x
  obtain ⟨rows, columns, hCover, hRows, hColumns⟩ :=
    hRobust distanceA distanceB hA hB (transposeTensorWord x) hTransposed
      (by simpa only [hTransposedWeight] using hWeight)
  refine ⟨columns, rows, ?_, ?_, ?_⟩
  · simpa only [transposeTensorWord_involutive] using
      supportCovered_transposeTensorWord (transposeTensorWord x) rows columns hCover
  · simpa only [hTransposedWeight] using hColumns
  · simpa only [hTransposedWeight] using hRows

private theorem isRobustWithPunctureResistance_swap
    {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B) (w q : Nat)
    (hRobust : IsRobustWithPunctureResistance CA CB w q) :
    IsRobustWithPunctureResistance CB CA w q := by
  intro removedB removedA hMatching hCard
  exact isRobust_swap (puncturedCode CA removedA) (puncturedCode CB removedB) w
    (hRobust removedA removedB hMatching.symm (by omega))

/-- The failure event swaps both sample coordinates, preserving the same draw. -/
private def robustFailureSwapEquiv
    {α β : Type u} {A B : Type v} [Fintype A] [Fintype B]
    (CA : α → LinearCode (ZMod 2) A) (CB : β → LinearCode (ZMod 2) B)
    (distanceA distanceB w q : Nat) :
    {sample : α × β //
      HasMinimumDistanceAtLeast (CA sample.1) distanceA ∧
      HasMinimumDistanceAtLeast (CB sample.2) distanceB ∧
      ¬ IsRobustWithPunctureResistance (CA sample.1) (CB sample.2) w q} ≃
    {sample : β × α //
      HasMinimumDistanceAtLeast (CB sample.1) distanceB ∧
      HasMinimumDistanceAtLeast (CA sample.2) distanceA ∧
      ¬ IsRobustWithPunctureResistance (CB sample.1) (CA sample.2) w q} where
  toFun sample := ⟨(sample.1.2, sample.1.1),
    sample.2.2.1, sample.2.1, fun hRobust =>
      sample.2.2.2 (isRobustWithPunctureResistance_swap _ _ w q hRobust)⟩
  invFun sample := ⟨(sample.1.2, sample.1.1),
    sample.2.2.1, sample.2.1, fun hRobust =>
      sample.2.2.2 (isRobustWithPunctureResistance_swap _ _ w q hRobust)⟩
  left_inv sample := by
    apply Subtype.ext
    rfl
  right_inv sample := by
    apply Subtype.ext
    rfl


/-- The swapped-side bound is transported on the same two-matrix experiment. -/
private theorem card_jointSwappedPunctureFailure_mul_pow_le
    {A B T : Type v} [Fintype A] [Fintype B] [Fintype T]
    (cutoff w p q distanceA distanceB : Nat)
    (hCutoff : 0 < cutoff) (hHeavyBudget : w < (p + 1) * (cutoff + 1))
    (hSyndromeBudget : (p / cutoff + 1) * cutoff < distanceB - q)
    (hRows : 2 * p ≤ distanceB - q) (hColumns : 2 * p ≤ distanceA - q) :
    Nat.card {sample : Matrix T A (ZMod 2) × Matrix T B (ZMod 2) //
      HasMinimumDistanceAtLeast (parityCheckKernelCode (Matrix.toLin' sample.1)) distanceA ∧
      HasMinimumDistanceAtLeast (parityCheckRowCode (Matrix.toLin' sample.2)) distanceB ∧
      ¬ IsRobustWithPunctureResistance
        (parityCheckKernelCode (Matrix.toLin' sample.1))
        (parityCheckRowCode (Matrix.toLin' sample.2)) w q} *
      2 ^ ((p / cutoff + 1) * (Fintype.card T - (q + p))) ≤
      ((∑ size ∈ Finset.range (q + 1),
        Nat.choose (Fintype.card B) size * Nat.choose (Fintype.card A) size) *
        (2 ^ Fintype.card A *
          (∑ weight ∈ Finset.range (cutoff + 1),
            Nat.choose (Fintype.card B) weight) ^ Fintype.card A)) *
              Nat.card (Matrix T A (ZMod 2) × Matrix T B (ZMod 2)) := by
  classical
  have hCount := card_jointPrimalPunctureFailure_mul_pow_le (A := B) (B := A) (T := T)
    cutoff w p q distanceB distanceA hCutoff hHeavyBudget hSyndromeBudget hRows hColumns
  rw [Nat.card_congr (robustFailureSwapEquiv
    (fun first : Matrix T A (ZMod 2) => parityCheckKernelCode (Matrix.toLin' first))
    (fun second : Matrix T B (ZMod 2) => parityCheckRowCode (Matrix.toLin' second))
    distanceA distanceB w q)]
  simpa only [Nat.card_prod, Nat.mul_comm] using hCount


private theorem linearCode_eq_of_carrier_eq
    {F : Type u} {I : Type v} [Field F] [Fintype F] [Fintype I]
    {first second : LinearCode F I} (hCarrier : first.carrier = second.carrier) :
    first = second := by
  cases first
  cases second
  cases hCarrier
  rfl

private theorem parityCheckKernelCode_dual_eq_rowCode
    {I K : Type v} [Fintype I] [Fintype K]
    (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K) :
    (parityCheckKernelCode P).dual = parityCheckRowCode P := by
  apply linearCode_eq_of_carrier_eq
  rw [← parityCheckRowCode_dual_eq_kernelCode P]
  exact dual_dual_carrier_eq _


/-- The actual local-code dual failure event uses the same pair of matrices. -/
private theorem card_jointDualPunctureFailure_mul_pow_le
    {A B T : Type v} [Fintype A] [Fintype B] [Fintype T]
    (cutoff w p q distanceA distanceB : Nat)
    (hCutoff : 0 < cutoff) (hHeavyBudget : w < (p + 1) * (cutoff + 1))
    (hSyndromeBudget : (p / cutoff + 1) * cutoff < distanceB - q)
    (hRows : 2 * p ≤ distanceB - q) (hColumns : 2 * p ≤ distanceA - q) :
    Nat.card {sample : Matrix T A (ZMod 2) × Matrix T B (ZMod 2) //
      HasMinimumDistanceAtLeast (parityCheckRowCode (Matrix.toLin' sample.1)).dual distanceA ∧
      HasMinimumDistanceAtLeast (parityCheckKernelCode (Matrix.toLin' sample.2)).dual distanceB ∧
      ¬ IsRobustWithPunctureResistance
        ((parityCheckRowCode (Matrix.toLin' sample.1)).dual)
        ((parityCheckKernelCode (Matrix.toLin' sample.2)).dual) w q} *
      2 ^ ((p / cutoff + 1) * (Fintype.card T - (q + p))) ≤
      ((∑ size ∈ Finset.range (q + 1),
        Nat.choose (Fintype.card B) size * Nat.choose (Fintype.card A) size) *
        (2 ^ Fintype.card A *
          (∑ weight ∈ Finset.range (cutoff + 1),
            Nat.choose (Fintype.card B) weight) ^ Fintype.card A)) *
              Nat.card (Matrix T A (ZMod 2) × Matrix T B (ZMod 2)) := by
  have hCount := card_jointSwappedPunctureFailure_mul_pow_le (A := A) (B := B) (T := T)
    cutoff w p q distanceA distanceB hCutoff hHeavyBudget hSyndromeBudget hRows hColumns
  simpa only [parityCheckRowCode_dual_eq_kernelCode, parityCheckKernelCode_dual_eq_rowCode] using hCount

/-- Robustness bad events are conditioned on the same draw's four distance clauses. -/
private def distanceGoodPunctureFailure
    {r : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (distance w q : Nat) (dualSide : Bool) (sample : RandomLocalCodeSample r A B) : Prop :=
  HasMinimumDistanceAtLeast sample.codeA distance ∧
    HasMinimumDistanceAtLeast sample.codeB distance ∧
    HasMinimumDistanceAtLeast sample.codeA.dual distance ∧
    HasMinimumDistanceAtLeast sample.codeB.dual distance ∧
    match dualSide with
    | false => ¬ IsRobustWithPunctureResistance sample.codeA sample.codeB w q
    | true => ¬ IsRobustWithPunctureResistance sample.codeA.dual sample.codeB.dual w q

private theorem card_distanceGoodPunctureFailure_primal_mul_pow_le
    {r : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (cutoff w p q distance : Nat)
    (hCutoff : 0 < cutoff) (hHeavyBudget : w < (p + 1) * (cutoff + 1))
    (hSyndromeBudget : (p / cutoff + 1) * cutoff < distance - q)
    (hDistanceBudget : 2 * p ≤ distance - q) :
    Nat.card {sample : RandomLocalCodeSample r A B //
      distanceGoodPunctureFailure distance w q false sample} *
      2 ^ ((p / cutoff + 1) * (r - (q + p))) ≤
      ((∑ size ∈ Finset.range (q + 1),
        Nat.choose (Fintype.card A) size * Nat.choose (Fintype.card B) size) *
        (2 ^ Fintype.card B *
          (∑ weight ∈ Finset.range (cutoff + 1),
            Nat.choose (Fintype.card A) weight) ^ Fintype.card B)) *
              Nat.card (RandomLocalCodeSample r A B) := by
  have hSubset : Nat.card {sample : RandomLocalCodeSample r A B //
      distanceGoodPunctureFailure distance w q false sample} ≤
      Nat.card {sample : RandomLocalCodeSample r A B //
        HasMinimumDistanceAtLeast sample.codeA distance ∧
        HasMinimumDistanceAtLeast sample.codeB distance ∧
        ¬ IsRobustWithPunctureResistance sample.codeA sample.codeB w q} := by
    apply nat_card_event_le_of_imp
    intro sample h
    exact ⟨h.1, h.2.1, h.2.2.2.2⟩
  apply le_trans (Nat.mul_le_mul_right _ hSubset)
  have hCount := card_jointPrimalPunctureFailure_mul_pow_le (A := A) (B := B) (T := ULift.{v} (Fin r))
    cutoff w p q distance distance hCutoff hHeavyBudget
    hSyndromeBudget hDistanceBudget hDistanceBudget
  simpa only [RandomLocalCodeSample.codeA, RandomLocalCodeSample.codeB,
    RandomLocalCodeSample, Fintype.card_ulift, Fintype.card_fin] using hCount

private theorem card_distanceGoodPunctureFailure_dual_mul_pow_le
    {r : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (cutoff w p q distance : Nat)
    (hCutoff : 0 < cutoff) (hHeavyBudget : w < (p + 1) * (cutoff + 1))
    (hSyndromeBudget : (p / cutoff + 1) * cutoff < distance - q)
    (hDistanceBudget : 2 * p ≤ distance - q) :
    Nat.card {sample : RandomLocalCodeSample r A B //
      distanceGoodPunctureFailure distance w q true sample} *
      2 ^ ((p / cutoff + 1) * (r - (q + p))) ≤
      ((∑ size ∈ Finset.range (q + 1),
        Nat.choose (Fintype.card B) size * Nat.choose (Fintype.card A) size) *
        (2 ^ Fintype.card A *
          (∑ weight ∈ Finset.range (cutoff + 1),
            Nat.choose (Fintype.card B) weight) ^ Fintype.card A)) *
              Nat.card (RandomLocalCodeSample r A B) := by
  have hSubset : Nat.card {sample : RandomLocalCodeSample r A B //
      distanceGoodPunctureFailure distance w q true sample} ≤
      Nat.card {sample : RandomLocalCodeSample r A B //
        HasMinimumDistanceAtLeast sample.codeA.dual distance ∧
        HasMinimumDistanceAtLeast sample.codeB.dual distance ∧
        ¬ IsRobustWithPunctureResistance sample.codeA.dual sample.codeB.dual w q} := by
    apply nat_card_event_le_of_imp
    intro sample h
    exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  apply le_trans (Nat.mul_le_mul_right _ hSubset)
  have hCount := card_jointDualPunctureFailure_mul_pow_le (A := A) (B := B) (T := ULift.{v} (Fin r))
    cutoff w p q distance distance hCutoff hHeavyBudget
    hSyndromeBudget hDistanceBudget hDistanceBudget
  simpa only [RandomLocalCodeSample.codeA, RandomLocalCodeSample.codeB,
    RandomLocalCodeSample, Fintype.card_ulift, Fintype.card_fin] using hCount

/-- The two conditional failures are counted together, not on separately chosen draws. -/
private theorem card_distanceGoodPunctureFailures_mul_pow_le
    {r Delta : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (cutoff w p q distance : Nat)
    (hCutoff : 0 < cutoff) (hHeavyBudget : w < (p + 1) * (cutoff + 1))
    (hSyndromeBudget : (p / cutoff + 1) * cutoff < distance - q)
    (hDistanceBudget : 2 * p ≤ distance - q) :
    (∑ dualSide : Bool, Nat.card {sample : RandomLocalCodeSample r A B //
      distanceGoodPunctureFailure distance w q dualSide sample}) *
      2 ^ ((p / cutoff + 1) * (r - (q + p))) ≤
      2 * ((∑ size ∈ Finset.range (q + 1),
        Nat.choose Delta size * Nat.choose Delta size) *
        (2 ^ Delta * (∑ weight ∈ Finset.range (cutoff + 1),
          Nat.choose Delta weight) ^ Delta)) *
              Nat.card (RandomLocalCodeSample r A B) := by
  have hP := card_distanceGoodPunctureFailure_primal_mul_pow_le
    (r := r) (A := A) (B := B) cutoff w p q distance
    hCutoff hHeavyBudget hSyndromeBudget hDistanceBudget
  have hD := card_distanceGoodPunctureFailure_dual_mul_pow_le
    (r := r) (A := A) (B := B) cutoff w p q distance
    hCutoff hHeavyBudget hSyndromeBudget hDistanceBudget
  rw [hA, hB] at hP hD
  rw [Fintype.sum_bool, Nat.add_mul]
  exact (Nat.add_le_add hD hP).trans_eq (by ring)

/-- The same joint draw has an explicit binary-exponent bound for both failures,
using the actual matching-puncture and light-column multiplicities. -/
private theorem card_distanceGoodPunctureFailures_mul_pow_le_pow_clog
    {r Delta : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (cutoff w p q distance : Nat) (hq : q ≤ Delta) (hc : cutoff ≤ Delta)
    (hCutoff : 0 < cutoff) (hHeavyBudget : w < (p + 1) * (cutoff + 1))
    (hSyndromeBudget : (p / cutoff + 1) * cutoff < distance - q)
    (hDistanceBudget : 2 * p ≤ distance - q) :
    (∑ dualSide : Bool, Nat.card {sample : RandomLocalCodeSample r A B //
      distanceGoodPunctureFailure distance w q dualSide sample}) *
      2 ^ ((p / cutoff + 1) * (r - (q + p))) ≤
      2 ^ (Delta + 1 + Nat.clog 2 (Delta + 1) *
        (2 * q + 1 + (cutoff + 1) * Delta)) *
          Nat.card (RandomLocalCodeSample r A B) := by
  have hCount := card_distanceGoodPunctureFailures_mul_pow_le
    (r := r) hA hB cutoff w p q distance
    hCutoff hHeavyBudget hSyndromeBudget hDistanceBudget
  exact hCount.trans (Nat.mul_le_mul_right _
    (robustIndexNumerator_le_pow_clog Delta q cutoff hq hc))

/-- A two-bit gap between the actual index and syndrome exponents bounds the
two distance-conditioned robustness failures by one quarter of the same draw. -/
private theorem four_mul_card_distanceGoodPunctureFailures_le
    {r Delta : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (cutoff w p q distance : Nat) (hq : q ≤ Delta) (hc : cutoff ≤ Delta)
    (hCutoff : 0 < cutoff) (hHeavyBudget : w < (p + 1) * (cutoff + 1))
    (hSyndromeBudget : (p / cutoff + 1) * cutoff < distance - q)
    (hDistanceBudget : 2 * p ≤ distance - q)
    (hGap : Delta + 1 + Nat.clog 2 (Delta + 1) *
      (2 * q + 1 + (cutoff + 1) * Delta) + 2 ≤
        (p / cutoff + 1) * (r - (q + p))) :
    4 * (∑ dualSide : Bool, Nat.card {sample : RandomLocalCodeSample r A B //
      distanceGoodPunctureFailure distance w q dualSide sample}) ≤
        Nat.card (RandomLocalCodeSample r A B) := by
  let E := Delta + 1 + Nat.clog 2 (Delta + 1) *
    (2 * q + 1 + (cutoff + 1) * Delta)
  let D := (p / cutoff + 1) * (r - (q + p))
  let C := ∑ dualSide : Bool, Nat.card {sample : RandomLocalCodeSample r A B //
    distanceGoodPunctureFailure distance w q dualSide sample}
  let S := Nat.card (RandomLocalCodeSample r A B)
  have hCount : C * 2 ^ D ≤ 2 ^ E * S :=
    card_distanceGoodPunctureFailures_mul_pow_le_pow_clog
      hA hB cutoff w p q distance hq hc hCutoff hHeavyBudget
      hSyndromeBudget hDistanceBudget
  have hPow : 4 * 2 ^ E ≤ 2 ^ D := by
    have h := pow_le_pow_right' (by decide : 1 ≤ (2 : Nat)) hGap
    simpa only [E, D, pow_add, show (2 : Nat) ^ 2 = 4 by norm_num,
      Nat.mul_comm] using h
  have hScaled : (4 * C) * 2 ^ D ≤ S * 2 ^ D := by
    calc
      (4 * C) * 2 ^ D = 4 * (C * 2 ^ D) := by ring
      _ ≤ 4 * (2 ^ E * S) := Nat.mul_le_mul_left 4 hCount
      _ = (4 * 2 ^ E) * S := by ring
      _ ≤ 2 ^ D * S := Nat.mul_le_mul_right S hPow
      _ = S * 2 ^ D := by ring
  exact Nat.le_of_mul_le_mul_right hScaled (by positivity : 0 < 2 ^ D)

/-- The actual source row count and floored weight/puncture choices leave a
quarter-sample budget for the two conditioned robustness failures together.
The rank/four-distance union margin is not supplied by this theorem. -/
private theorem exists_eventual_source_conditionedRobustness_quarter
    (epsilon gamma delta rho : ℝ) (hEpsilon : 0 < epsilon)
    (hEpsilonUpper : epsilon < 1 / 2) (hGamma : gamma < 1)
    (hDelta : 0 < delta) (hRho : 0 < rho) :
    ∃ threshold : Nat, ∀ n : Nat, threshold ≤ n →
      ∀ (A B : Type v) [Fintype A] [Fintype B],
        Fintype.card A = n → Fintype.card B = n →
          4 * (∑ dualSide : Bool,
            Nat.card {sample : RandomLocalCodeSample (randomRowCount rho n) A B //
              distanceGoodPunctureFailure (Nat.floor (delta * n))
                (Nat.floor ((n : ℝ) ^ ((3 : ℝ) / 2 - epsilon)))
                (Nat.floor ((n : ℝ) ^ gamma)) dualSide sample}) ≤
            Nat.card (RandomLocalCodeSample (randomRowCount rho n) A B) := by
  have hBeta : 0 < min delta rho / 8 :=
    div_pos (lt_min hDelta hRho) (by norm_num)
  have hBetaRho : min delta rho / 8 ≤ rho / 4 := by
    have h := min_le_right delta rho
    linarith
  obtain ⟨tB, htB⟩ := exists_eventual_source_robustness_floor_budgets
    epsilon gamma delta rho hEpsilon hEpsilonUpper hGamma hDelta hRho
  obtain ⟨tG, htG⟩ := exists_eventual_robustIndexExponent_add_two_le_syndrome
    ((1 : ℝ) / 2 - epsilon / 2) gamma (min delta rho / 8) rho
    (by linarith) (by linarith) hGamma hBeta hRho hBetaRho
  refine ⟨max tB tG, ?_⟩
  intro n hn A B _ _ hA hB
  obtain ⟨hK, hQ, hKN, hW, hRank, hCover⟩ :=
    htB n ((Nat.le_max_left _ _).trans hn)
  exact four_mul_card_distanceGoodPunctureFailures_le
    (r := randomRowCount rho n) hA hB
    (Nat.floor ((n : ℝ) ^ ((1 : ℝ) / 2 - epsilon / 2)))
    (Nat.floor ((n : ℝ) ^ ((3 : ℝ) / 2 - epsilon)))
    (Nat.floor ((min delta rho / 8) * n))
    (Nat.floor ((n : ℝ) ^ gamma)) (Nat.floor (delta * n))
    hQ hKN hK hW hRank hCover
    (htG n ((Nat.le_max_right _ _).trans hn))


/-- The simultaneous local event used in LZ22 Theorem `thm:goodcodes`.
It includes the two local codes and their duals because the global distance
argument is applied symmetrically to the X and Z sectors. -/
def GoodLocalCodeEvent
    {r : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (dimensionA dimensionB distanceThreshold robustness punctures : Nat)
    (sample : RandomLocalCodeSample r A B) : Prop :=
  Dimension sample.codeA = dimensionA ∧
    Dimension sample.codeB = dimensionB ∧
    HasMinimumDistanceAtLeast sample.codeA distanceThreshold ∧
    HasMinimumDistanceAtLeast sample.codeB distanceThreshold ∧
    HasMinimumDistanceAtLeast sample.codeA.dual distanceThreshold ∧
    HasMinimumDistanceAtLeast sample.codeB.dual distanceThreshold ∧
    IsRobustWithPunctureResistance
      sample.codeA sample.codeB robustness punctures ∧
    IsRobustWithPunctureResistance
      sample.codeA.dual sample.codeB.dual robustness punctures

/-- Full row rank discharges both dimension clauses of the successful event;
the remaining hypotheses are precisely the primal/dual GV-distance and
puncture-resistant robustness estimates proved by the source's probabilistic
argument. -/
theorem goodLocalCodeEvent_of_fullRowRank
    {r Delta distanceThreshold robustness punctures : Nat}
    {A B : Type v} [Fintype A] [Fintype B]
    {sample : RandomLocalCodeSample r A B}
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (hFull : sample.HasFullRowRank)
    (hDistanceA : HasMinimumDistanceAtLeast sample.codeA distanceThreshold)
    (hDistanceB : HasMinimumDistanceAtLeast sample.codeB distanceThreshold)
    (hDistanceADual :
      HasMinimumDistanceAtLeast sample.codeA.dual distanceThreshold)
    (hDistanceBDual :
      HasMinimumDistanceAtLeast sample.codeB.dual distanceThreshold)
    (hRobust : IsRobustWithPunctureResistance
      sample.codeA sample.codeB robustness punctures)
    (hRobustDual : IsRobustWithPunctureResistance
      sample.codeA.dual sample.codeB.dual robustness punctures) :
    GoodLocalCodeEvent
      r (Delta - r) distanceThreshold robustness punctures sample := by
  obtain ⟨hDimensionA, hDimensionB⟩ :=
    dimensions_of_fullRowRank sample hA hB hFull
  exact ⟨hDimensionA, hDimensionB, hDistanceA, hDistanceB,
    hDistanceADual, hDistanceBDual, hRobust, hRobustDual⟩

/-- The full local-code event follows from one finite union bound that includes
the already-counted rank/distance failures and both puncture-resistant
robustness failures.  The source's remaining probabilistic task is to bound
the two robustness event cardinalities, not to assume their conclusions. -/
private def goodLocalCodeBad
    {r : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (distanceThreshold robustness punctures : Nat)
    (index : Sum (SimultaneousDistanceBadIndex r distanceThreshold A B) Bool)
    (sample : RandomLocalCodeSample r A B) : Prop :=
  match index with
  | .inl i => simultaneousDistanceBad i sample
  | .inr dualSide =>
      distanceGoodPunctureFailure distanceThreshold robustness punctures dualSide sample

private theorem hasPositiveUniformProbability_goodLocalCodeEvent_of_count_bound
    {r Delta distanceThreshold robustness punctures : Nat}
    {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (hcount :
      (∑ index : Sum
          (SimultaneousDistanceBadIndex r distanceThreshold A B) Bool,
        (eventFinset (goodLocalCodeBad
          distanceThreshold robustness punctures index)).card) <
      Fintype.card (RandomLocalCodeSample r A B)) :
    HasPositiveUniformProbability (Ω := RandomLocalCodeSample r A B)
      (GoodLocalCodeEvent (r := r) (A := A) (B := B)
        r (Delta - r) distanceThreshold robustness punctures) := by
  apply hasPositiveUniformProbability_of_union_bound
    (good := GoodLocalCodeEvent (r := r) (A := A) (B := B)
      r (Delta - r) distanceThreshold robustness punctures)
    (bad := goodLocalCodeBad distanceThreshold robustness punctures)
  · intro sample hnot
    by_cases hbase : sample.HasFullRowRank ∧
        HasMinimumDistanceAtLeast sample.codeA distanceThreshold ∧
        HasMinimumDistanceAtLeast sample.codeB distanceThreshold ∧
        HasMinimumDistanceAtLeast sample.codeA.dual distanceThreshold ∧
        HasMinimumDistanceAtLeast sample.codeB.dual distanceThreshold
    · obtain ⟨hFull, hDistanceA, hDistanceB, hDistanceADual,
        hDistanceBDual⟩ := hbase
      by_cases hRobust : IsRobustWithPunctureResistance
          sample.codeA sample.codeB robustness punctures
      · have hRobustDual : ¬ IsRobustWithPunctureResistance
            sample.codeA.dual sample.codeB.dual robustness punctures := by
          intro hDual
          exact hnot (goodLocalCodeEvent_of_fullRowRank hA hB hFull
            hDistanceA hDistanceB hDistanceADual hDistanceBDual hRobust hDual)
        exact ⟨.inr true, hDistanceA, hDistanceB, hDistanceADual,
          hDistanceBDual, hRobustDual⟩
      · exact ⟨.inr false, hDistanceA, hDistanceB, hDistanceADual,
          hDistanceBDual, hRobust⟩
    · obtain ⟨index, hindex⟩ :=
        simultaneousDistanceBad_covers sample hbase
      exact ⟨.inl index, hindex⟩
  · exact hcount

/-- The already-counted rank and four-distance failures have this explicit finite bound. -/
private def distanceFailureCountBound (r Delta distance : Nat) : Nat :=
  2 * (2 ^ r - 1) * (2 ^ (r * Delta - Delta) * 2 ^ (r * Delta)) +
    2 * (((2 ^ r - 1) * (∑ weight ∈ Finset.range distance,
      Nat.choose Delta weight)) * (2 ^ (r * Delta - Delta) * 2 ^ (r * Delta))) +
    2 * ((∑ weight ∈ Finset.range distance, Nat.choose Delta weight) *
      (2 ^ (r * Delta) * 2 ^ (r * Delta - r)))

/-- Twelvefold finite margins reserve a strict half-space budget for the
rank and four-distance event family. -/
private theorem simultaneousDistance_twelvefold_bounds_of_real_margins
    (Delta r distance : Nat) (delta : ℝ)
    (hDelta : 0 < Delta) (hrDelta : r ≤ Delta) (hDistance : 0 < distance)
    (hdeltaPositive : 0 < delta) (hdeltaHalf : delta < 1 / 2)
    (hDistanceCeil : distance = Nat.ceil (delta * Delta))
    (hceil : 2 ≤ distance)
    (hGeneratorMargin :
      12 * (((2 ^ r : Nat) : ℝ) *
        Real.exp ((Delta : ℝ) * Real.binEntropy delta)) <
        ((2 ^ Delta : Nat) : ℝ))
    (hKernelMargin :
      12 * Real.exp ((Delta : ℝ) * Real.binEntropy delta) <
        ((2 ^ r : Nat) : ℝ)) :
    12 * (2 ^ r - 1) < 2 ^ Delta ∧
      12 * ((2 ^ r - 1) *
        (∑ weight ∈ Finset.range distance, Nat.choose Delta weight)) <
        2 ^ Delta ∧
      12 * ((∑ weight ∈ Finset.range distance,
        Nat.choose Delta weight) * 2 ^ (Delta - r)) <
        2 ^ Delta := by
  let volume := ∑ weight ∈ Finset.range distance, Nat.choose Delta weight
  have hVolume : (volume : ℝ) ≤
      Real.exp ((Delta : ℝ) * Real.binEntropy delta) := by
    subst distance
    exact binaryHammingBall_le_exp_binEntropy_ceilRadius
      Delta delta hDelta hdeltaPositive hdeltaHalf hceil
  have hOne : 1 ≤ volume := by
    have hzero : 0 ∈ Finset.range distance := Finset.mem_range.mpr hDistance
    simpa [volume] using
      (Finset.single_le_sum
        (fun weight _ => Nat.zero_le (Nat.choose Delta weight)) hzero)
  have hGenerator : 12 * ((2 ^ r - 1) * volume) < 2 ^ Delta := by
    have hSub : (((2 ^ r - 1 : Nat) : ℝ)) ≤ ((2 ^ r : Nat) : ℝ) := by
      exact_mod_cast Nat.sub_le (2 ^ r) 1
    have hReal : (((12 * ((2 ^ r - 1) * volume) : Nat) : ℝ)) <
        ((2 ^ Delta : Nat) : ℝ) := by
      calc
        (((12 * ((2 ^ r - 1) * volume) : Nat) : ℝ)) =
            12 * ((2 ^ r - 1 : Nat) : ℝ) * (volume : ℝ) := by
              norm_cast
              ring
        _ ≤ 12 * ((2 ^ r : Nat) : ℝ) * (volume : ℝ) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hSub (by norm_num))
            (Nat.cast_nonneg _)
        _ ≤ 12 * ((2 ^ r : Nat) : ℝ) *
            Real.exp ((Delta : ℝ) * Real.binEntropy delta) := by
          exact mul_le_mul_of_nonneg_left hVolume (by positivity)
        _ < ((2 ^ Delta : Nat) : ℝ) := by
          simpa only [mul_assoc] using hGeneratorMargin
    exact_mod_cast hReal
  have hRank : 12 * (2 ^ r - 1) < 2 ^ Delta := by
    have hLe : (2 ^ r - 1) ≤ (2 ^ r - 1) * volume := by
      calc
        2 ^ r - 1 = (2 ^ r - 1) * 1 := by omega
        _ ≤ (2 ^ r - 1) * volume :=
          Nat.mul_le_mul_left _ hOne
    exact (Nat.mul_le_mul_left 12 hLe).trans_lt hGenerator
  have hKernelSmall : 12 * volume < 2 ^ r := by
    have hReal : (((12 * volume : Nat) : ℝ)) < ((2 ^ r : Nat) : ℝ) := by
      calc
        (((12 * volume : Nat) : ℝ)) = 12 * (volume : ℝ) := by norm_cast
        _ ≤ 12 * Real.exp ((Delta : ℝ) * Real.binEntropy delta) := by
          exact mul_le_mul_of_nonneg_left hVolume (by norm_num)
        _ < ((2 ^ r : Nat) : ℝ) := hKernelMargin
    exact_mod_cast hReal
  have hKernel : 12 * (volume * 2 ^ (Delta - r)) < 2 ^ Delta := by
    calc
      12 * (volume * 2 ^ (Delta - r)) =
          (12 * volume) * 2 ^ (Delta - r) := by ring
      _ < 2 ^ r * 2 ^ (Delta - r) :=
        Nat.mul_lt_mul_of_pos_right hKernelSmall (by positivity)
      _ = 2 ^ Delta := by
        rw [← pow_add]
        congr 1
        omega
  exact ⟨hRank, hGenerator, hKernel⟩

/-- The generator and kernel exponential margins follow from the two
entropy gaps after accounting for the single row lost when `rho * Delta` is
floored.  The kernel bound therefore reserves one extra `log 2` of margin. -/
private theorem simultaneousDistance_twelvefold_real_margins_of_entropy_gaps
    (rho delta : ℝ) (Delta : Nat) (hRhoNonnegative : 0 ≤ rho)
    (hGeneratorGap :
      Real.log 12 <
        ((1 - rho) * Real.log 2 - Real.binEntropy delta) * (Delta : ℝ))
    (hKernelGap :
      Real.log 12 + Real.log 2 <
        (rho * Real.log 2 - Real.binEntropy delta) * (Delta : ℝ)) :
    12 * (((2 ^ randomRowCount rho Delta : Nat) : ℝ) *
      Real.exp ((Delta : ℝ) * Real.binEntropy delta)) <
        ((2 ^ Delta : Nat) : ℝ) ∧
      12 * Real.exp ((Delta : ℝ) * Real.binEntropy delta) <
        ((2 ^ randomRowCount rho Delta : Nat) : ℝ) := by
  let r := randomRowCount rho Delta
  have hlog : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hRows : (r : ℝ) ≤ rho * Delta :=
    randomRowCount_cast_le hRhoNonnegative
  have hRowsLog := mul_le_mul_of_nonneg_right hRows hlog.le
  have hFloor : rho * Delta < (r : ℝ) + 1 :=
    randomRowCount_lt_add_one rho Delta
  have hFloorLog := mul_lt_mul_of_pos_right hFloor hlog
  have hGeneratorExponent :
      Real.log 12 +
          ((r : ℝ) * Real.log 2 +
            (Delta : ℝ) * Real.binEntropy delta) <
        (Delta : ℝ) * Real.log 2 := by
    nlinarith [hGeneratorGap, hRowsLog]
  have hKernelExponent :
      Real.log 12 + (Delta : ℝ) * Real.binEntropy delta <
        (r : ℝ) * Real.log 2 := by
    nlinarith [hKernelGap, hFloorLog]
  have hPow (k : Nat) :
      ((2 ^ k : Nat) : ℝ) =
        Real.exp ((k : ℝ) * Real.log 2) := by
    calc
      ((2 ^ k : Nat) : ℝ) = (2 : ℝ) ^ k := by norm_cast
      _ = (Real.exp (Real.log (2 : ℝ))) ^ k := by
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ = Real.exp ((k : ℝ) * Real.log 2) :=
        (Real.exp_nat_mul (Real.log (2 : ℝ)) k).symm
  constructor
  · change 12 * (((2 ^ r : Nat) : ℝ) *
        Real.exp ((Delta : ℝ) * Real.binEntropy delta)) <
      ((2 ^ Delta : Nat) : ℝ)
    calc
      12 * (((2 ^ r : Nat) : ℝ) *
          Real.exp ((Delta : ℝ) * Real.binEntropy delta)) =
          Real.exp (Real.log 12 +
            ((r : ℝ) * Real.log 2 +
              (Delta : ℝ) * Real.binEntropy delta)) := by
        rw [Real.exp_add, Real.exp_add,
          Real.exp_log (by norm_num : (0 : ℝ) < 12), ← hPow r]
      _ < Real.exp ((Delta : ℝ) * Real.log 2) :=
        Real.exp_lt_exp.mpr hGeneratorExponent
      _ = ((2 ^ Delta : Nat) : ℝ) := (hPow Delta).symm
  · change 12 * Real.exp ((Delta : ℝ) * Real.binEntropy delta) <
      ((2 ^ r : Nat) : ℝ)
    calc
      12 * Real.exp ((Delta : ℝ) * Real.binEntropy delta) =
          Real.exp (Real.log 12 +
            (Delta : ℝ) * Real.binEntropy delta) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 12)]
      _ < Real.exp ((r : ℝ) * Real.log 2) :=
        Real.exp_lt_exp.mpr hKernelExponent
      _ = ((2 ^ r : Nat) : ℝ) := (hPow r).symm

/-- Under the corrected source hypotheses `rho < 1/2` and
`h₂(delta) < rho`, both finite-degree margins needed for simultaneous
rank and distance hold once the fixed local degree is large enough. -/
private theorem exists_eventual_simultaneousDistance_twelvefold_entropy_margins
    (rho delta : ℝ) (hRhoHalf : rho < 1 / 2)
    (hEntropy : Real.binEntropy delta < rho * Real.log 2) :
    ∃ threshold : Nat, ∀ Delta : Nat, threshold ≤ Delta →
      Real.log 12 <
          ((1 - rho) * Real.log 2 - Real.binEntropy delta) *
            (Delta : ℝ) ∧
        Real.log 12 + Real.log 2 <
          (rho * Real.log 2 - Real.binEntropy delta) *
            (Delta : ℝ) := by
  have hlog : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hRhoLog : rho * Real.log 2 < (1 / 2 : ℝ) * Real.log 2 :=
    mul_lt_mul_of_pos_right hRhoHalf hlog
  have hGeneratorSlope :
      0 < (1 - rho) * Real.log 2 - Real.binEntropy delta := by
    nlinarith [hEntropy, hRhoLog]
  have hKernelSlope :
      0 < rho * Real.log 2 - Real.binEntropy delta := by
    linarith
  obtain ⟨generatorThreshold, hGeneratorThreshold⟩ :=
    exists_nat_gt
      (Real.log 12 /
        ((1 - rho) * Real.log 2 - Real.binEntropy delta))
  obtain ⟨kernelThreshold, hKernelThreshold⟩ :=
    exists_nat_gt
      ((Real.log 12 + Real.log 2) /
        (rho * Real.log 2 - Real.binEntropy delta))
  refine ⟨max generatorThreshold kernelThreshold, ?_⟩
  intro Delta hThreshold
  have hGeneratorLe : generatorThreshold ≤ Delta :=
    (Nat.le_max_left _ _).trans hThreshold
  have hKernelLe : kernelThreshold ≤ Delta :=
    (Nat.le_max_right _ _).trans hThreshold
  have hGeneratorCast :
      (generatorThreshold : ℝ) ≤ Delta := by
    exact_mod_cast hGeneratorLe
  have hKernelCast :
      (kernelThreshold : ℝ) ≤ Delta := by
    exact_mod_cast hKernelLe
  have hGeneratorAtThreshold :
      Real.log 12 <
        ((1 - rho) * Real.log 2 - Real.binEntropy delta) *
          (generatorThreshold : ℝ) := by
    have h := (div_lt_iff₀ hGeneratorSlope).mp hGeneratorThreshold
    nlinarith [h]
  have hKernelAtThreshold :
      Real.log 12 + Real.log 2 <
        (rho * Real.log 2 - Real.binEntropy delta) *
          (kernelThreshold : ℝ) := by
    have h := (div_lt_iff₀ hKernelSlope).mp hKernelThreshold
    nlinarith [h]
  constructor
  · have hScaled :=
      mul_le_mul_of_nonneg_left hGeneratorCast hGeneratorSlope.le
    nlinarith [hGeneratorAtThreshold, hScaled]
  · have hScaled :=
      mul_le_mul_of_nonneg_left hKernelCast hKernelSlope.le
    nlinarith [hKernelAtThreshold, hScaled]

/-- Twelvefold component margins reserve strictly more than half the matrix
sample space for the already counted rank and four-distance failures. -/
private theorem simultaneousDistance_twice_count_bound_of_twelvefold_components
    {r Delta distance : Nat} (hr : 0 < r) (hrDelta : r ≤ Delta)
    (hRank : 12 * (2 ^ r - 1) < 2 ^ Delta)
    (hGenerator :
      12 * ((2 ^ r - 1) *
        (∑ weight ∈ Finset.range distance, Nat.choose Delta weight)) < 2 ^ Delta)
    (hKernel :
      12 * ((∑ weight ∈ Finset.range distance, Nat.choose Delta weight) *
        2 ^ (Delta - r)) < 2 ^ Delta) :
    2 * distanceFailureCountBound r Delta distance <
      2 ^ (r * Delta) * 2 ^ (r * Delta) := by
  have hDeltaLe : Delta ≤ r * Delta := by
    calc
      Delta = 1 * Delta := by omega
      _ ≤ r * Delta := Nat.mul_le_mul_right Delta hr
  have hSplitDelta :
      2 ^ (r * Delta) = 2 ^ (r * Delta - Delta) * 2 ^ Delta := by
    rw [← pow_add, Nat.sub_add_cancel hDeltaLe]
  have hSplitR :
      2 ^ (r * Delta - r) =
        2 ^ (r * Delta - Delta) * 2 ^ (Delta - r) := by
    rw [← pow_add]
    congr 1
    omega
  let volume := ∑ weight ∈ Finset.range distance, Nat.choose Delta weight
  let common := 2 ^ (r * Delta - Delta) * 2 ^ (r * Delta)
  have hcommon : 0 < common := by dsimp [common]; positivity
  have hball :
      2 * (2 * (2 ^ r - 1) + 2 * ((2 ^ r - 1) * volume) +
        2 * (volume * 2 ^ (Delta - r))) < 2 ^ Delta := by
    dsimp [volume]
    omega
  change 2 * (2 * (2 ^ r - 1) * common +
    2 * (((2 ^ r - 1) * volume) * common) +
    2 * (volume * (2 ^ (r * Delta) * 2 ^ (r * Delta - r)))) < _
  calc
    2 * (2 * (2 ^ r - 1) * common +
        2 * (((2 ^ r - 1) * volume) * common) +
        2 * (volume * (2 ^ (r * Delta) * 2 ^ (r * Delta - r)))) =
      (2 * (2 * (2 ^ r - 1) + 2 * ((2 ^ r - 1) * volume) +
        2 * (volume * 2 ^ (Delta - r)))) * common := by
      rw [hSplitR]
      ring
    _ < 2 ^ Delta * common :=
      Nat.mul_lt_mul_of_pos_right hball hcommon
    _ = 2 ^ (r * Delta) * 2 ^ (r * Delta) := by
      dsimp [common]
      calc
        2 ^ Delta * (2 ^ (r * Delta - Delta) * 2 ^ (r * Delta)) =
          (2 ^ (r * Delta - Delta) * 2 ^ Delta) * 2 ^ (r * Delta) := by ring
        _ = 2 ^ (r * Delta) * 2 ^ (r * Delta) := by rw [← hSplitDelta]

/-- The genuine source entropy gap supplies a strict half-space bound at the
ceiling distance radius, not merely at a floored approximation. -/
private theorem exists_eventual_simultaneousDistance_twice_count_bound
    (rho delta : ℝ) (hRhoPositive : 0 < rho) (hRhoHalf : rho < 1 / 2)
    (hdeltaPositive : 0 < delta) (hdeltaHalf : delta < 1 / 2)
    (hEntropy : Real.binEntropy delta < rho * Real.log 2) :
    ∃ threshold : Nat, ∀ Delta : Nat, threshold ≤ Delta →
      let r := randomRowCount rho Delta
      let distance := Nat.ceil (delta * Delta)
      2 * distanceFailureCountBound r Delta distance <
        2 ^ (r * Delta) * 2 ^ (r * Delta) := by
  obtain ⟨baseThreshold, hBase⟩ :=
    exists_eventual_simultaneousDistance_parameters
      rho delta hRhoPositive hRhoHalf hdeltaPositive hEntropy
  obtain ⟨marginThreshold, hMargin⟩ :=
    exists_eventual_simultaneousDistance_twelvefold_entropy_margins
      rho delta hRhoHalf hEntropy
  refine ⟨max baseThreshold marginThreshold, ?_⟩
  intro Delta hThreshold
  obtain ⟨hDelta, hr, hrDelta, hCeil, _, _⟩ :=
    hBase Delta ((Nat.le_max_left _ _).trans hThreshold)
  obtain ⟨hGeneratorGap, hKernelGap⟩ :=
    hMargin Delta ((Nat.le_max_right _ _).trans hThreshold)
  obtain ⟨hGeneratorMargin, hKernelMargin⟩ :=
    simultaneousDistance_twelvefold_real_margins_of_entropy_gaps
      rho delta Delta hRhoPositive.le hGeneratorGap hKernelGap
  obtain ⟨hRank, hGenerator, hKernel⟩ :=
    simultaneousDistance_twelvefold_bounds_of_real_margins
      Delta (randomRowCount rho Delta) (Nat.ceil (delta * Delta)) delta
      hDelta hrDelta.le (by omega) hdeltaPositive hdeltaHalf rfl hCeil
      hGeneratorMargin hKernelMargin
  exact simultaneousDistance_twice_count_bound_of_twelvefold_components
    hr hrDelta.le hRank hGenerator hKernel


private theorem nat_card_event_eq_card_eventFinset
    {Ω : Type u} [Fintype Ω] (event : Ω → Prop) :
    Nat.card {sample : Ω // event sample} = (eventFinset event).card := by
  rw [Nat.card_eq_fintype_card, eventFinset, Fintype.card_subtype]

/-- One numerical finite bound supplies all clauses of the actual local-code
event on the same draw.  Deriving this strict inequality from the source's
asymptotic parameters remains a separate obligation. -/
private theorem hasPositiveUniformProbability_goodLocalCodeEvent_of_numeric_bound
    {r Delta : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (cutoff w p q distance : Nat)
    (hCutoff : 0 < cutoff) (hHeavyBudget : w < (p + 1) * (cutoff + 1))
    (hSyndromeBudget : (p / cutoff + 1) * cutoff < distance - q)
    (hDistanceBudget : 2 * p ≤ distance - q)
    (hNumeric :
      distanceFailureCountBound r Delta distance *
          2 ^ ((p / cutoff + 1) * (r - (q + p))) +
        2 * ((∑ size ∈ Finset.range (q + 1),
          Nat.choose Delta size * Nat.choose Delta size) *
          (2 ^ Delta * (∑ weight ∈ Finset.range (cutoff + 1),
            Nat.choose Delta weight) ^ Delta)) *
              Fintype.card (RandomLocalCodeSample r A B) <
        Fintype.card (RandomLocalCodeSample r A B) *
          2 ^ ((p / cutoff + 1) * (r - (q + p)))) :
    HasPositiveUniformProbability
      (GoodLocalCodeEvent (r := r) (A := A) (B := B)
        r (Delta - r) distance w q) := by
  apply hasPositiveUniformProbability_goodLocalCodeEvent_of_count_bound hA hB
  have hBase := sum_card_simultaneousDistanceBad_le
    (r := r) (distance := distance) hA hB
  change (∑ index : SimultaneousDistanceBadIndex r distance A B,
      (eventFinset (simultaneousDistanceBad index)).card) ≤
    distanceFailureCountBound r Delta distance at hBase
  have hRobust := card_distanceGoodPunctureFailures_mul_pow_le
    (r := r) hA hB cutoff w p q distance
    hCutoff hHeavyBudget hSyndromeBudget hDistanceBudget
  simp_rw [nat_card_event_eq_card_eventFinset] at hRobust
  rw [Nat.card_eq_fintype_card] at hRobust
  have hBoth := (Nat.add_le_add
    (Nat.mul_le_mul_right
      (2 ^ ((p / cutoff + 1) * (r - (q + p)))) hBase) hRobust).trans_lt hNumeric
  rw [← Nat.add_mul] at hBoth
  have hStrict := (Nat.mul_lt_mul_right
    (by positivity : 0 < 2 ^ ((p / cutoff + 1) * (r - (q + p))))).mp hBoth
  rw [Fintype.sum_sum_type]
  change (∑ index : SimultaneousDistanceBadIndex r distance A B,
      (eventFinset (simultaneousDistanceBad index)).card) +
    (∑ dualSide : Bool,
      (eventFinset (distanceGoodPunctureFailure distance w q dualSide)).card) <
        Fintype.card (RandomLocalCodeSample r A B)
  exact hStrict

/-- Increasing the common distance threshold shrinks each conditioned
robustness failure event; the robustness parameters and matrix draw stay fixed. -/
private theorem card_distanceGoodPunctureFailure_antitone
    {r : Nat} {A B : Type v} [Fintype A] [Fintype B]
    {distance distance' : Nat} (hDistance : distance ≤ distance')
    (w q : Nat) (dualSide : Bool) :
    Nat.card {sample : RandomLocalCodeSample r A B //
      distanceGoodPunctureFailure distance' w q dualSide sample} ≤
    Nat.card {sample : RandomLocalCodeSample r A B //
      distanceGoodPunctureFailure distance w q dualSide sample} := by
  apply nat_card_event_le_of_imp
  intro sample h
  obtain ⟨hA, hB, hADual, hBDual, hFailure⟩ := h
  exact ⟨fun word hw hn => hDistance.trans (hA word hw hn),
    fun word hw hn => hDistance.trans (hB word hw hn),
    fun word hw hn => hDistance.trans (hADual word hw hn),
    fun word hw hn => hDistance.trans (hBDual word hw hn), hFailure⟩

/-- A strict half-space rank/distance budget and a quarter-space conditioned
robustness budget give the complete local event on the same draw.  The latter
budget may be counted at a smaller distance threshold. -/
private theorem hasPositiveUniformProbability_goodLocalCodeEvent_of_half_quarter_bounds
    {r Delta distance distance' w q : Nat}
    {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (hDistance : distance ≤ distance')
    (hHalf : 2 * distanceFailureCountBound r Delta distance' <
      2 ^ (r * Delta) * 2 ^ (r * Delta))
    (hQuarter : 4 * (∑ dualSide : Bool,
      Nat.card {sample : RandomLocalCodeSample r A B //
        distanceGoodPunctureFailure distance w q dualSide sample}) ≤
      Nat.card (RandomLocalCodeSample r A B)) :
    HasPositiveUniformProbability
      (GoodLocalCodeEvent (r := r) (A := A) (B := B)
        r (Delta - r) distance' w q) := by
  apply hasPositiveUniformProbability_goodLocalCodeEvent_of_count_bound hA hB
  have hBase := sum_card_simultaneousDistanceBad_le
    (r := r) (distance := distance') hA hB
  change (∑ index : SimultaneousDistanceBadIndex r distance' A B,
    (eventFinset (simultaneousDistanceBad index)).card) ≤
      distanceFailureCountBound r Delta distance' at hBase
  have hRobust :
      (∑ dualSide : Bool,
        Nat.card {sample : RandomLocalCodeSample r A B //
          distanceGoodPunctureFailure distance' w q dualSide sample}) ≤
      (∑ dualSide : Bool,
        Nat.card {sample : RandomLocalCodeSample r A B //
          distanceGoodPunctureFailure distance w q dualSide sample}) := by
    apply Finset.sum_le_sum
    intro dualSide _
    exact card_distanceGoodPunctureFailure_antitone hDistance w q dualSide
  rw [← card_randomLocalCodeSample hA hB] at hHalf
  simp_rw [nat_card_event_eq_card_eventFinset] at hQuarter hRobust
  rw [Nat.card_eq_fintype_card] at hQuarter
  rw [Fintype.sum_sum_type]
  change (∑ index : SimultaneousDistanceBadIndex r distance' A B,
      (eventFinset (simultaneousDistanceBad index)).card) +
    (∑ dualSide : Bool,
      (eventFinset (distanceGoodPunctureFailure distance' w q dualSide)).card) <
        Fintype.card (RandomLocalCodeSample r A B)
  omega

/-- The source entropy gap and sublinear puncture parameters yield a positive
complete local-code event at the ceiling distance, without a numerical-bound
hypothesis or a second matrix sample. -/
private theorem exists_eventual_source_goodLocalCodeEvent_positive
    (epsilon gamma delta rho : ℝ) (hEpsilon : 0 < epsilon)
    (hEpsilonUpper : epsilon < 1 / 2) (hGamma : gamma < 1)
    (hDelta : 0 < delta) (hDeltaHalf : delta < 1 / 2)
    (hRho : 0 < rho) (hRhoHalf : rho < 1 / 2)
    (hEntropy : Real.binEntropy delta < rho * Real.log 2) :
    ∃ threshold : Nat, ∀ n : Nat, threshold ≤ n →
      ∀ (A B : Type v) [Fintype A] [Fintype B],
        Fintype.card A = n → Fintype.card B = n →
          HasPositiveUniformProbability
            (GoodLocalCodeEvent (r := randomRowCount rho n) (A := A) (B := B)
              (randomRowCount rho n) (n - randomRowCount rho n)
              (Nat.ceil (delta * n))
              (Nat.floor ((n : ℝ) ^ ((3 : ℝ) / 2 - epsilon)))
              (Nat.floor ((n : ℝ) ^ gamma))) := by
  obtain ⟨tH, htH⟩ := exists_eventual_simultaneousDistance_twice_count_bound
    rho delta hRho hRhoHalf hDelta hDeltaHalf hEntropy
  obtain ⟨tQ, htQ⟩ := exists_eventual_source_conditionedRobustness_quarter
    epsilon gamma delta rho hEpsilon hEpsilonUpper hGamma hDelta hRho
  refine ⟨max tH tQ, ?_⟩
  intro n hn A B _ _ hA hB
  exact hasPositiveUniformProbability_goodLocalCodeEvent_of_half_quarter_bounds
    hA hB (Nat.floor_le_ceil (delta * n))
    (htH n ((Nat.le_max_left _ _).trans hn))
    (htQ n ((Nat.le_max_right _ _).trans hn) A B hA hB)

/-- Choose one joint generator/check sample with the source local conditions.
The robustness theorem is applied at epsilon/2 to obtain the larger weight
required by LZ22 Theorem thm:123; no square-complex or global-distance conclusion
is asserted here.  The distance parameter is in the explicit lower GV branch. -/
theorem exists_eventual_source_goodLocalCodeSample
    (epsilon gamma delta rho : ℝ) (hEpsilon : 0 < epsilon)
    (hEpsilonUpper : epsilon < 1 / 2)
    (_hGammaLower : 1 / 2 + epsilon < gamma) (hGamma : gamma < 1)
    (hDelta : 0 < delta) (hDeltaHalf : delta < 1 / 2)
    (hRho : 0 < rho) (hRhoHalf : rho < 1 / 2)
    (hEntropy : Real.binEntropy delta < rho * Real.log 2) :
    ∃ threshold : Nat, ∀ n : Nat, threshold ≤ n →
      ∀ (A B : Type v) [Fintype A] [Fintype B],
        Fintype.card A = n → Fintype.card B = n →
          ∃ sample : RandomLocalCodeSample (randomRowCount rho n) A B,
            GoodLocalCodeEvent
              (randomRowCount rho n) (n - randomRowCount rho n)
              (Nat.ceil (delta * n))
              (Nat.floor ((n : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2)))
              (Nat.floor ((n : ℝ) ^ gamma)) sample := by
  obtain ⟨threshold, hThreshold⟩ := exists_eventual_source_goodLocalCodeEvent_positive
    (epsilon / 2) gamma delta rho (by linarith) (by linarith)
    hGamma hDelta hDeltaHalf hRho hRhoHalf hEntropy
  refine ⟨threshold, ?_⟩
  intro n hn A B _ _ hA hB
  exact (hasPositiveUniformProbability_iff_exists _).mp
    (hThreshold n hn A B hA hB)


/-- A real distance budget on the actual words of a binary local code. -/
private def HasRealMinimumDistanceAtLeast
    {I : Type v} [Fintype I] (C : LinearCode (ZMod 2) I) (distance : ℝ) : Prop :=
  ∀ x, x ∈ C.carrier → x ≠ 0 → distance ≤ (HammingWeight x : ℝ)

/-- The concrete robustness predicate with a real word-weight budget.
The distance-normalized support bounds remain those of the actual code. -/
private def IsRealRobust
    {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B) (weight : ℝ) : Prop :=
  ∀ dA dB, MinimumDistance CA dA → MinimumDistance CB dB →
    ∀ x, x ∈ (dualTensorCode CA CB).carrier → (HammingWeight x : ℝ) ≤ weight →
      ∃ rows : Finset A, ∃ columns : Finset B,
        SupportCovered x rows columns ∧
          rows.card ≤ HammingWeight x / dB ∧
          columns.card ≤ HammingWeight x / dA

/-- Matching deletion sets are bounded by their actual real cardinalities. -/
private def IsRealRobustWithPunctureResistance
    {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (weight punctures : ℝ) : Prop :=
  ∀ removedA : Finset A, ∀ removedB : Finset B,
    removedA.card = removedB.card → (removedA.card : ℝ) ≤ punctures →
      IsRealRobust (puncturedCode CA removedA) (puncturedCode CB removedB) weight

private theorem hasMinimumDistanceAtLeast_ceil_iff
    {I : Type v} [Fintype I] (C : LinearCode (ZMod 2) I) (distance : ℝ) :
    HasMinimumDistanceAtLeast C (Nat.ceil distance) ↔
      HasRealMinimumDistanceAtLeast C distance := by
  constructor
  · intro h x hx hx0
    exact Nat.ceil_le.mp (h x hx hx0)
  · intro h x hx hx0
    exact Nat.ceil_le.mpr (h x hx hx0)

private theorem isRobust_floor_iff
    {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (weight : ℝ) (hWeight : 0 ≤ weight) :
    IsRobust CA CB (Nat.floor weight) ↔ IsRealRobust CA CB weight := by
  constructor
  · intro h dA dB hA hB x hx hw
    exact h dA dB hA hB x hx (Nat.le_floor hw)
  · intro h dA dB hA hB x hx hw
    exact h dA dB hA hB x hx ((Nat.le_floor_iff hWeight).mp hw)

private theorem isRobustWithPunctureResistance_floor_iff
    {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (weight punctures : ℝ) (hWeight : 0 ≤ weight) (hPunctures : 0 ≤ punctures) :
    IsRobustWithPunctureResistance CA CB (Nat.floor weight) (Nat.floor punctures) ↔
      IsRealRobustWithPunctureResistance CA CB weight punctures := by
  constructor
  · intro h removedA removedB hCard hp
    exact (isRobust_floor_iff _ _ weight hWeight).mp
      (h removedA removedB hCard (Nat.le_floor hp))
  · intro h removedA removedB hCard hp
    exact (isRobust_floor_iff _ _ weight hWeight).mpr
      (h removedA removedB hCard ((Nat.le_floor_iff hPunctures).mp hp))

/-- Real source thresholds and the rate budget for one fixed matrix draw.
This is a local event, not a selected complex or a global code family. -/
private def SourceRealLocalCodeEvent
    {r : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (rho : ℝ) (n : Nat) (distance weight punctures : ℝ)
    (sample : RandomLocalCodeSample r A B) : Prop :=
  0 < Dimension sample.codeA ∧
    (Dimension sample.codeA : ℝ) ≤ rho * n ∧
    Dimension sample.codeB = n - Dimension sample.codeA ∧
    HasRealMinimumDistanceAtLeast sample.codeA distance ∧
    HasRealMinimumDistanceAtLeast sample.codeB distance ∧
    HasRealMinimumDistanceAtLeast sample.codeA.dual distance ∧
    HasRealMinimumDistanceAtLeast sample.codeB.dual distance ∧
    IsRealRobustWithPunctureResistance sample.codeA sample.codeB weight punctures ∧
    IsRealRobustWithPunctureResistance sample.codeA.dual sample.codeB.dual weight punctures

private theorem sourceRealLocalCodeEvent_of_goodLocalCodeEvent
    {r n : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (sample : RandomLocalCodeSample r A B)
    (rho distance weight punctures : ℝ)
    (hr : 0 < r) (hRate : (r : ℝ) ≤ rho * n)
    (hWeight : 0 ≤ weight) (hPunctures : 0 ≤ punctures)
    (hGood : GoodLocalCodeEvent r (n - r)
      (Nat.ceil distance) (Nat.floor weight) (Nat.floor punctures) sample) :
    SourceRealLocalCodeEvent rho n distance weight punctures sample := by
  obtain ⟨hDimA, hDimB, hDA, hDB, hDADual, hDBDual, hRobust, hRobustDual⟩ := hGood
  refine ⟨?_, ?_, ?_,
    (hasMinimumDistanceAtLeast_ceil_iff _ _).mp hDA,
    (hasMinimumDistanceAtLeast_ceil_iff _ _).mp hDB,
    (hasMinimumDistanceAtLeast_ceil_iff _ _).mp hDADual,
    (hasMinimumDistanceAtLeast_ceil_iff _ _).mp hDBDual,
    (isRobustWithPunctureResistance_floor_iff _ _ _ _ hWeight hPunctures).mp hRobust,
    (isRobustWithPunctureResistance_floor_iff _ _ _ _ hWeight hPunctures).mp hRobustDual⟩
  · simpa only [hDimA] using hr
  · simpa only [hDimA] using hRate
  · simpa only [hDimA] using hDimB

/-- A common degree threshold gives positive row count, fewer rows than
columns, and the real local source event on the same selected matrix sample. -/
private theorem exists_eventual_source_realLocalCodeSample
    (epsilon gamma delta rho : ℝ) (hEpsilon : 0 < epsilon)
    (hEpsilonUpper : epsilon < 1 / 2)
    (hGammaLower : 1 / 2 + epsilon < gamma) (hGamma : gamma < 1)
    (hDelta : 0 < delta) (hDeltaHalf : delta < 1 / 2)
    (hRho : 0 < rho) (hRhoHalf : rho < 1 / 2)
    (hEntropy : Real.binEntropy delta < rho * Real.log 2) :
    ∃ threshold : Nat, ∀ n : Nat, threshold ≤ n →
      0 < randomRowCount rho n ∧ randomRowCount rho n < n ∧
        ∀ (A B : Type v) [Fintype A] [Fintype B],
          Fintype.card A = n → Fintype.card B = n →
            ∃ sample : RandomLocalCodeSample (randomRowCount rho n) A B,
              SourceRealLocalCodeEvent rho n (delta * n)
                ((n : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2))
                ((n : ℝ) ^ gamma) sample := by
  obtain ⟨t, ht⟩ := exists_eventual_source_goodLocalCodeSample
    epsilon gamma delta rho hEpsilon hEpsilonUpper hGammaLower hGamma
    hDelta hDeltaHalf hRho hRhoHalf hEntropy
  refine ⟨max t (max 1 (Nat.ceil (2 / rho))), ?_⟩
  intro n hn
  have hnOne : 1 ≤ n := (Nat.le_max_left 1 _).trans
    ((Nat.le_max_right t _).trans hn)
  have hnTwo : Nat.ceil (2 / rho) ≤ n := (Nat.le_max_right 1 _).trans
    ((Nat.le_max_right t _).trans hn)
  have hRealTwo : (2 : ℝ) ≤ rho * n := by
    have hDiv : (2 : ℝ) / rho ≤ n := Nat.ceil_le.mp hnTwo
    have hMul := (div_le_iff₀ hRho).mp hDiv
    nlinarith
  have hrPositive : 0 < randomRowCount rho n := by
    have hFloor : rho * n < (randomRowCount rho n : ℝ) + 1 :=
      randomRowCount_lt_add_one rho n
    have hPositive : (0 : ℝ) < randomRowCount rho n := by linarith
    exact_mod_cast hPositive
  refine ⟨hrPositive, randomRowCount_lt_degree hRho.le (by linarith) (by omega), ?_⟩
  intro A B _ _ hA hB
  obtain ⟨sample, hGood⟩ := ht n ((Nat.le_max_left _ _).trans hn) A B hA hB
  refine ⟨sample, sourceRealLocalCodeEvent_of_goodLocalCodeEvent
    sample rho _ _ _ hrPositive (randomRowCount_cast_le hRho.le)
    (Real.rpow_nonneg (Nat.cast_nonneg n) _) (Real.rpow_nonneg (Nat.cast_nonneg n) _) hGood⟩

/-! ## Actual Cayley-square geometry and CSS commutation

The square type consists only of realized four-corner squares.  Generator
injectivity, inverse laws and total no-conjugacy supply the incidence and
overlap proofs; no check-orthogonality hypothesis is used in the constructor.
-/

private def square {G A B : Type v} [Group G]
    (L : A → G) (R : B → G) (g : G) (side : Bool) (a : A) (b : B) :
    Finset (G × Bool) :=
  {(g, side), (L a * g, !side), (g * R b, !side), (L a * g * R b, side)}

private theorem square_opposite_vertex {G A B : Type v} [Group G]
    (L : A → G) (R : B → G) (g h : G) (a : A) (b : B) :
    (h, true) ∈ square L R g false a b ↔ h = L a * g ∨ h = g * R b := by
  simp [square]

private theorem square_base_vertex {G A B : Type v} [Group G]
    (L : A → G) (R : B → G) (g h : G) (a : A) (b : B) :
    (g, false) ∈ square L R h true a b ↔ g = L a * h ∨ g = h * R b := by
  simp [square]

private theorem square_opposite_vertex_general {G A B : Type v} [Group G]
    (L : A → G) (R : B → G) (g h : G) (side : Bool) (a : A) (b : B) :
    (h, !side) ∈ square L R g side a b ↔ h = L a * g ∨ h = g * R b := by
  cases side <;> simp [square]

private theorem square_link_injective {G A B : Type v} [Group G]
    (L : A → G) (R : B → G)
    (hL : Function.Injective L) (hR : Function.Injective R)
    (hTNC : ∀ g a b, L a * g ≠ g * R b)
    (g : G) (side : Bool) :
    Function.Injective (fun ab : A × B => square L R g side ab.1 ab.2) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ hs
  change square L R g side a b = square L R g side c d at hs
  have ha : (L a * g, !side) ∈ square L R g side c d := by
    rw [← hs]
    exact (square_opposite_vertex_general L R g (L a * g) side a b).2 (Or.inl rfl)
  have hb : (g * R b, !side) ∈ square L R g side c d := by
    rw [← hs]
    exact (square_opposite_vertex_general L R g (g * R b) side a b).2 (Or.inr rfl)
  have hac : a = c := by
    rcases (square_opposite_vertex_general L R g (L a * g) side c d).1 ha with h | h
    · exact hL (mul_right_cancel h)
    · exact (hTNC g a d h).elim
  have hbd : b = d := by
    rcases (square_opposite_vertex_general L R g (g * R b) side c d).1 hb with h | h
    · exact (hTNC g c b h.symm).elim
    · exact hR (mul_left_cancel h)
  exact Prod.ext hac hbd

private theorem square_rebase_left {G A B : Type v} [Group G]
    (L : A → G) (R : B → G) (invA : Equiv.Perm A)
    (hLA : ∀ a, L (invA a) = (L a)⁻¹)
    (g : G) (side : Bool) (a : A) (b : B) :
    square L R g side a b = square L R (L a * g) (!side) (invA a) b := by
  ext vertex
  cases side <;>
    simp only [square, hLA, inv_mul_cancel_left, Bool.not_false, Bool.not_true,
      Finset.mem_insert, Finset.mem_singleton] <;> tauto

private theorem square_rebase_right {G A B : Type v} [Group G]
    (L : A → G) (R : B → G) (invB : Equiv.Perm B)
    (hRB : ∀ b, R (invB b) = (R b)⁻¹)
    (g : G) (side : Bool) (a : A) (b : B) :
    square L R g side a b = square L R (g * R b) (!side) a (invB b) := by
  ext vertex
  cases side <;>
    simp only [square, hRB, mul_assoc, mul_inv_cancel, mul_one,
      Bool.not_false, Bool.not_true, Finset.mem_insert, Finset.mem_singleton] <;> tauto

private theorem square_same_side_vertices {G A B : Type v} [Group G]
    (L : A → G) (R : B → G) (g : G) (side : Bool) (a : A) (b : B) :
    (square L R g side a b).filter (fun vertex => vertex.2 = side) =
      {(g, side), (L a * g * R b, side)} := by
  ext ⟨h, t⟩
  cases side <;> cases t <;> simp [square]

private theorem square_opposite_side_vertices {G A B : Type v} [Group G]
    (L : A → G) (R : B → G) (g : G) (side : Bool) (a : A) (b : B) :
    (square L R g side a b).filter (fun vertex => vertex.2 = !side) =
      {(L a * g, !side), (g * R b, !side)} := by
  ext ⟨h, t⟩
  cases side <;> cases t <;> simp [square]

private theorem square_each_side_card {G A B : Type v} [Group G]
    (L : A → G) (R : B → G) (invB : Equiv.Perm B)
    (hRB : ∀ b, R (invB b) = (R b)⁻¹)
    (hTNC : ∀ g a b, L a * g ≠ g * R b)
    (g : G) (side t : Bool) (a : A) (b : B) :
    ((square L R g side a b).filter (fun vertex => vertex.2 = t)).card = 2 := by
  have hdiag : g ≠ L a * g * R b := by
    intro heq
    apply hTNC g a (invB b)
    rw [hRB]
    calc
      L a * g = (L a * g * R b) * (R b)⁻¹ := by simp [mul_assoc]
      _ = g * (R b)⁻¹ := by rw [← heq]
  have hsame : ((square L R g side a b).filter (fun vertex => vertex.2 = side)).card = 2 := by
    rw [square_same_side_vertices]
    apply Finset.card_pair
    intro heq
    exact hdiag (congrArg Prod.fst heq)
  have hopposite : ((square L R g side a b).filter (fun vertex => vertex.2 = !side)).card = 2 := by
    rw [square_opposite_side_vertices]
    apply Finset.card_pair
    intro heq
    exact hTNC g a b (congrArg Prod.fst heq)
  cases side <;> cases t
  · exact hsame
  · exact hopposite
  · exact hopposite
  · exact hsame

-- Source Section 3.1: actual four-corner equality, not an assumed check pairing.
private theorem square_overlap_iff {G A B : Type v} [Group G]
    (L : A → G) (R : B → G)
    (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hL : Function.Injective L) (hR : Function.Injective R)
    (hLA : ∀ a, L (invA a) = (L a)⁻¹)
    (hRB : ∀ b, R (invB b) = (R b)⁻¹)
    (hTNC : ∀ g a b, L a * g ≠ g * R b)
    (g h : G) (a c : A) (b d : B) :
    square L R g false a b = square L R h true c d ↔
      (h = L a * g ∧ c = invA a ∧ d = b) ∨
      (h = g * R b ∧ c = a ∧ d = invB b) := by
  constructor
  · intro hs
    have hh : (h, true) ∈ square L R g false a b := by
      rw [hs]
      simp [square]
    have hg : (g, false) ∈ square L R h true c d := by
      rw [← hs]
      simp [square]
    rcases (square_opposite_vertex L R g h a b).mp hh with ha | hb
    · subst h
      have hcg : g = L c * (L a * g) := by
        rcases (square_base_vertex L R g (L a * g) c d).mp hg with hc | hd
        · exact hc
        · have hbad : L a * g = g * R (invB d) := by
            rw [hRB]
            calc
              L a * g = ((L a * g) * R d) * (R d)⁻¹ := by simp [mul_assoc]
              _ = g * (R d)⁻¹ := by rw [← hd]
          exact (hTNC g a (invB d) hbad).elim
      have hc : c = invA a := by
        apply hL
        rw [hLA]
        calc
          L c = (L c * (L a * g)) * g⁻¹ * (L a)⁻¹ := by simp [mul_assoc]
          _ = (L a)⁻¹ := by rw [← hcg]; simp
      have hgb : (g * R b, true) ∈ square L R (L a * g) true c d := by
        rw [← hs]
        simp [square]
      have hbd : g * R b = g * R d := by
        have hmem := hgb
        rw [hc] at hmem
        simp only [square, hLA, inv_mul_cancel_left, Bool.not_true,
          Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq,
          Bool.true_eq_false, and_false, false_or, and_true] at hmem
        rcases hmem with hbad | heq
        · exact (hTNC g a b hbad.symm).elim
        · exact heq
      exact Or.inl ⟨rfl, hc, (hR (mul_left_cancel hbd)).symm⟩
    · subst h
      have hgd : g = (g * R b) * R d := by
        rcases (square_base_vertex L R g (g * R b) c d).mp hg with hc | hd
        · have hbad : L c * g = g * R (invB b) := by
            rw [hRB]
            calc
              L c * g = (L c * (g * R b)) * (R b)⁻¹ := by simp [mul_assoc]
              _ = g * (R b)⁻¹ := by rw [← hc]
          exact (hTNC g c (invB b) hbad).elim
        · exact hd
      have hd : d = invB b := by
        apply hR
        rw [hRB]
        calc
          R d = (R b)⁻¹ * g⁻¹ * ((g * R b) * R d) := by simp [mul_assoc]
          _ = (R b)⁻¹ := by rw [← hgd]; simp [mul_assoc]
      have hag : (L a * g, true) ∈ square L R (g * R b) true c d := by
        rw [← hs]
        simp [square]
      have hac : L a * g = L c * g := by
        have hmem := hag
        rw [hd] at hmem
        simp only [square, hRB, mul_assoc, mul_inv_cancel, mul_one, Bool.not_true,
          Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq,
          Bool.true_eq_false, and_false, false_or, and_true] at hmem
        rcases hmem with hbad | heq
        · exact (hTNC g a b hbad).elim
        · exact heq
      exact Or.inr ⟨rfl, (hL (mul_right_cancel hac)).symm, hd⟩
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · ext vertex
      simp only [square, hLA, inv_mul_cancel_left, Bool.not_false, Bool.not_true,
        Finset.mem_insert, Finset.mem_singleton]
      tauto
    · ext vertex
      simp only [square, hRB, mul_assoc, mul_inv_cancel, mul_one,
        Bool.not_false, Bool.not_true, Finset.mem_insert, Finset.mem_singleton]
      tauto


private abbrev CanonicalSquare {G A B : Type v} [Group G]
    (L : A → G) (R : B → G) :=
  {q : Finset (G × Bool) // ∃ g side a b, q = square L R g side a b}

/-- A shared finite enumeration for the realized four-corner square type.
Keeping this instance named avoids expanding a classical filtered powerset
when downstream arithmetic constructions compare square-complex types. -/
noncomputable instance cayleySquareFintype {G A B : Type v} [Group G] [Fintype G]
    (L : A → G) (R : B → G) : Fintype (CanonicalSquare L R) := by
  classical
  infer_instance

private def canonicalLink {G A B : Type v} [Group G]
    (L : A → G) (R : B → G) (vertex : G × Bool) (ab : A × B) :
    CanonicalSquare L R :=
  ⟨square L R vertex.1 vertex.2 ab.1 ab.2,
    ⟨vertex.1, vertex.2, ab.1, ab.2, rfl⟩⟩

private theorem canonicalLink_injective {G A B : Type v} [Group G]
    (L : A → G) (R : B → G)
    (hL : Function.Injective L) (hR : Function.Injective R)
    (hTNC : ∀ g a b, L a * g ≠ g * R b) (vertex : G × Bool) :
    Function.Injective (canonicalLink L R vertex) := by
  intro ab cd h
  exact square_link_injective L R hL hR hTNC vertex.1 vertex.2
    (congrArg Subtype.val h)

private theorem canonicalLink_incident_iff {G A B : Type v} [Group G]
    (L : A → G) (R : B → G)
    (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hLA : ∀ a, L (invA a) = (L a)⁻¹)
    (hRB : ∀ b, R (invB b) = (R b)⁻¹)
    (vertex : G × Bool) (q : CanonicalSquare L R) :
    (∃ ab, canonicalLink L R vertex ab = q) ↔ vertex ∈ q.val := by
  constructor
  · rintro ⟨ab, rfl⟩
    simp [canonicalLink, square]
  · obtain ⟨g, side, a, b, hq⟩ := q.property
    rw [hq]
    intro hv
    simp only [square, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with hv | hv | hv | hv
    · subst vertex
      refine ⟨(a, b), Subtype.ext ?_⟩
      exact hq.symm
    · subst vertex
      refine ⟨(invA a, b), Subtype.ext ?_⟩
      exact (square_rebase_left L R invA hLA g side a b).symm.trans hq.symm
    · subst vertex
      refine ⟨(a, invB b), Subtype.ext ?_⟩
      exact (square_rebase_right L R invB hRB g side a b).symm.trans hq.symm
    · subst vertex
      refine ⟨(invA a, invB b), Subtype.ext ?_⟩
      have hreb := (square_rebase_left L R invA hLA g side a b).trans
        (square_rebase_right L R invB hRB (L a * g) (!side) (invA a) b)
      simpa only [Bool.not_not, canonicalLink] using hreb.symm.trans hq.symm

private theorem canonicalLink_side_degree {G A B : Type v} [Group G] [Fintype G]
    (L : A → G) (R : B → G)
    (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hLA : ∀ a, L (invA a) = (L a)⁻¹)
    (hRB : ∀ b, R (invB b) = (R b)⁻¹)
    (hTNC : ∀ g a b, L a * g ≠ g * R b)
    (q : CanonicalSquare L R) (side : Bool) :
    (Finset.univ.filter fun g => ∃ ab, canonicalLink L R (g, side) ab = q).card = 2 := by
  let vertices := Finset.univ.filter fun g => ∃ ab, canonicalLink L R (g, side) ab = q
  have himage : vertices.image (fun g => (g, side)) =
      q.val.filter (fun vertex => vertex.2 = side) := by
    ext ⟨g, t⟩
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      vertices, Prod.mk.injEq]
    constructor
    · rintro ⟨h, hi, rfl, rfl⟩
      exact ⟨(canonicalLink_incident_iff L R invA invB hLA hRB _ q).1 hi, rfl⟩
    · rintro ⟨hi, rfl⟩
      exact ⟨g, (canonicalLink_incident_iff L R invA invB hLA hRB _ q).2 hi,
        rfl, rfl⟩
  have hinj : Function.Injective (fun g : G => (g, side)) :=
    fun _ _ h => congrArg Prod.fst h
  have hcard := Finset.card_image_of_injective vertices hinj
  rw [himage] at hcard
  obtain ⟨g, t, a, b, hq⟩ := q.property
  rw [← hcard, hq]
  exact square_each_side_card L R invB hRB hTNC g t side a b


private def canonicalSquareComplex {G A B : Type v} [Group G]
    [Fintype G] [Fintype A] [Fintype B]
    (L : A → G) (R : B → G)
    (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hL : Function.Injective L) (hR : Function.Injective R)
    (hLA : ∀ a, L (invA a) = (L a)⁻¹)
    (hRB : ∀ b, R (invB b) = (R b)⁻¹)
    (hTNC : ∀ g a b, L a * g ≠ g * R b) :
    LeftRightCayleySquareComplex G A B (CanonicalSquare L R) where
  leftGenerator := L
  rightGenerator := R
  leftInverse := invA
  rightInverse := invB
  leftGenerator_inverse := hLA
  rightGenerator_inverse := hRB
  noConjugacy := hTNC
  link := canonicalLink L R
  link_injective := canonicalLink_injective L R hL hR hTNC
  square_side_degree := by
    intro q side
    have hcard := canonicalLink_side_degree L R invA invB hLA hRB hTNC q side
    convert hcard using 1
    congr 1
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]


/-- Actual four-corner square coordinates from [LZ22, Section 3.1]. -/
abbrev CayleySquare {G A B : Type v} [Group G] (L : A → G) (R : B → G) :=
  CanonicalSquare L R

/-- The realized square complex, with no spectral or distance claim assumed. -/
def cayleySquareComplex {G A B : Type v} [Group G]
    [Fintype G] [Fintype A] [Fintype B]
    (L : A → G) (R : B → G)
    (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hL : Function.Injective L) (hR : Function.Injective R)
    (hLA : ∀ a, L (invA a) = (L a)⁻¹)
    (hRB : ∀ b, R (invB b) = (R b)⁻¹)
    (hTNC : ∀ g a b, L a * g ≠ g * R b) :
    LeftRightCayleySquareComplex G A B (CayleySquare L R) :=
  canonicalSquareComplex L R invA invB hL hR hLA hRB hTNC

/-- The canonical realization satisfies both link transport identities;
they are proved from its four corners rather than added as input laws. -/
theorem cayleySquareComplex_hasCayleyLinkIdentities
    {G A B : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
    (L : A → G) (R : B → G)
    (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hL : Function.Injective L) (hR : Function.Injective R)
    (hLA : ∀ a, L (invA a) = (L a)⁻¹)
    (hRB : ∀ b, R (invB b) = (R b)⁻¹)
    (hTNC : ∀ g a b, L a * g ≠ g * R b) :
    (cayleySquareComplex L R invA invB hL hR hLA hRB hTNC).HasCayleyLinkIdentities := by
  constructor
  · intro g side a b
    apply Subtype.ext
    exact square_rebase_left L R invA hLA g side a b
  · intro g side a b
    apply Subtype.ext
    exact square_rebase_right L R invB hRB g side a b

private theorem canonicalLink_overlap_iff {G A B : Type v} [Group G]
    (L : A → G) (R : B → G)
    (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hL : Function.Injective L) (hR : Function.Injective R)
    (hLA : ∀ a, L (invA a) = (L a)⁻¹)
    (hRB : ∀ b, R (invB b) = (R b)⁻¹)
    (hTNC : ∀ g a b, L a * g ≠ g * R b)
    (g h : G) (a c : A) (b d : B) :
    canonicalLink L R (g, false) (a, b) = canonicalLink L R (h, true) (c, d) ↔
      (h = L a * g ∧ c = invA a ∧ d = b) ∨
      (h = g * R b ∧ c = a ∧ d = invB b) := by
  rw [Subtype.ext_iff]
  exact square_overlap_iff L R invA invB hL hR hLA hRB hTNC g h a c b d

private theorem canonicalLink_left_overlap_iff {G A B : Type v} [Group G]
    (L : A → G) (R : B → G)
    (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hL : Function.Injective L) (hR : Function.Injective R)
    (hLA : ∀ a, L (invA a) = (L a)⁻¹)
    (hRB : ∀ b, R (invB b) = (R b)⁻¹)
    (hTNC : ∀ g a b, L a * g ≠ g * R b)
    (g : G) (a₀ a c : A) (b d : B) :
    canonicalLink L R (g, false) (a, b) =
      canonicalLink L R (L a₀ * g, true) (c, d) ↔
      a = a₀ ∧ c = invA a₀ ∧ d = b := by
  rw [canonicalLink_overlap_iff L R invA invB hL hR hLA hRB hTNC]
  constructor
  · rintro (⟨h, hc, hd⟩ | ⟨h, _, _⟩)
    · have ha : a = a₀ := (hL (mul_right_cancel h)).symm
      subst a
      exact ⟨rfl, hc, hd⟩
    · exact (hTNC g a₀ b h).elim
  · rintro ⟨rfl, hc, hd⟩
    exact Or.inl ⟨rfl, hc, hd⟩

private theorem canonicalLink_right_overlap_iff {G A B : Type v} [Group G]
    (L : A → G) (R : B → G)
    (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hL : Function.Injective L) (hR : Function.Injective R)
    (hLA : ∀ a, L (invA a) = (L a)⁻¹)
    (hRB : ∀ b, R (invB b) = (R b)⁻¹)
    (hTNC : ∀ g a b, L a * g ≠ g * R b)
    (g : G) (b₀ b d : B) (a c : A) :
    canonicalLink L R (g, false) (a, b) =
      canonicalLink L R (g * R b₀, true) (c, d) ↔
      b = b₀ ∧ c = a ∧ d = invB b₀ := by
  rw [canonicalLink_overlap_iff L R invA invB hL hR hLA hRB hTNC]
  constructor
  · rintro (⟨h, _, _⟩ | ⟨h, hc, hd⟩)
    · exact (hTNC g a b₀ h.symm).elim
    · have hb : b = b₀ := (hR (mul_left_cancel h)).symm
      subst b
      exact ⟨rfl, hc, hd⟩
  · rintro ⟨rfl, hc, hd⟩
    exact Or.inr ⟨rfl, hc, hd⟩


private theorem canonicalLink_left_pairing_sum {G A B : Type v} {F : Type u}
    [Group G] [Fintype A] [Fintype B] [Semiring F]
    (L : A → G) (R : B → G)
    (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hL : Function.Injective L) (hR : Function.Injective R)
    (hLA : ∀ a, L (invA a) = (L a)⁻¹)
    (hRB : ∀ b, R (invB b) = (R b)⁻¹)
    (hTNC : ∀ g a b, L a * g ≠ g * R b)
    (g : G) (a₀ : A) (z x : A × B → F) :
    (∑ ab : A × B, ∑ cd : A × B,
      if canonicalLink L R (g, false) ab = canonicalLink L R (L a₀ * g, true) cd
      then z ab * x cd else 0) =
      ∑ b : B, z (a₀, b) * x (invA a₀, b) := by
  simp only [Fintype.sum_prod_type]
  simp_rw [canonicalLink_left_overlap_iff L R invA invB hL hR hLA hRB hTNC]
  simp [ite_and]

private theorem canonicalLink_right_pairing_sum {G A B : Type v} {F : Type u}
    [Group G] [Fintype A] [Fintype B] [Semiring F]
    (L : A → G) (R : B → G)
    (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hL : Function.Injective L) (hR : Function.Injective R)
    (hLA : ∀ a, L (invA a) = (L a)⁻¹)
    (hRB : ∀ b, R (invB b) = (R b)⁻¹)
    (hTNC : ∀ g a b, L a * g ≠ g * R b)
    (g : G) (b₀ : B) (z x : A × B → F) :
    (∑ ab : A × B, ∑ cd : A × B,
      if canonicalLink L R (g, false) ab = canonicalLink L R (g * R b₀, true) cd
      then z ab * x cd else 0) =
      ∑ a : A, z (a, b₀) * x (a, invB b₀) := by
  simp only [Fintype.sum_prod_type]
  simp_rw [canonicalLink_right_overlap_iff L R invA invB hL hR hLA hRB hTNC]
  simp [ite_and]


private def localExtensionWord {F : Type u} {I Q : Type v} [Semiring F] [Fintype I]
    (link : I → Q) (x : I → F) : Q → F :=
  ∑ i : I, x i • Pi.single (link i) 1

private theorem localExtensionWord_pairing {F : Type u} {I J Q : Type v}
    [CommSemiring F] [Fintype I] [Fintype J] [Fintype Q]
    (link₁ : I → Q) (link₂ : J → Q) (z : I → F) (x : J → F) :
    dotProduct (localExtensionWord link₁ z) (localExtensionWord link₂ x) =
      ∑ i : I, ∑ j : J, if link₁ i = link₂ j then z i * x j else 0 := by
  unfold localExtensionWord
  simp_rw [sum_dotProduct, dotProduct_sum, smul_dotProduct, dotProduct_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : link₁ i = link₂ j
  · simp [h]
  · simp [h, Ne.symm h]

private theorem canonicalLink_nonadjacent_pairing_sum {G A B : Type v} {F : Type u}
    [Group G] [Fintype A] [Fintype B] [Semiring F]
    (L : A → G) (R : B → G)
    (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hL : Function.Injective L) (hR : Function.Injective R)
    (hLA : ∀ a, L (invA a) = (L a)⁻¹)
    (hRB : ∀ b, R (invB b) = (R b)⁻¹)
    (hTNC : ∀ g a b, L a * g ≠ g * R b)
    (g h : G) (hNoL : ∀ a, h ≠ L a * g) (hNoR : ∀ b, h ≠ g * R b)
    (z x : A × B → F) :
    (∑ ab : A × B, ∑ cd : A × B,
      if canonicalLink L R (g, false) ab = canonicalLink L R (h, true) cd
      then z ab * x cd else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro ab _
  apply Finset.sum_eq_zero
  intro cd _
  have hne : canonicalLink L R (g, false) ab ≠ canonicalLink L R (h, true) cd := by
    intro heq
    rcases (canonicalLink_overlap_iff L R invA invB hL hR hLA hRB hTNC
      g h ab.1 cd.1 ab.2 cd.2).1 heq with ⟨ha, _, _⟩ | ⟨hb, _, _⟩
    · exact hNoL ab.1 ha
    · exact hNoR ab.2 hb
  exact if_neg hne


private theorem canonicalLocalChecks_orthogonal {G A B : Type v} {F : Type u}
    [Group G] [Fintype G] [Fintype A] [Fintype B] [Field F] [Fintype F]
    (L : A → G) (R : B → G)
    (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hL : Function.Injective L) (hR : Function.Injective R)
    (hLA : ∀ a, L (invA a) = (L a)⁻¹)
    (hRB : ∀ b, R (invB b) = (R b)⁻¹)
    (hTNC : ∀ g a b, L a * g ≠ g * R b)
    (CA : LinearCode F A) (CB : LinearCode F B)
    (g h : G) (z x : Word F (A × B))
    (hz : z ∈ (tensorCode CA CB).carrier)
    (hx : x ∈ (tensorCode CA.dual CB.dual).carrier) :
    wordPairing (localExtensionWord (canonicalLink L R (g, false)) z)
      (localExtensionWord (canonicalLink L R (h, true)) x) = 0 := by
  rw [wordPairing_apply, localExtensionWord_pairing]
  have hz' := (mem_tensorCode CA CB z).1 hz
  have hx' := (mem_tensorCode CA.dual CB.dual x).1 hx
  by_cases hleft : ∃ a, h = L a * g
  · obtain ⟨a₀, rfl⟩ := hleft
    have ho := CB.dual_orthogonal (hz'.2 a₀) (hx'.2 (invA a₀))
    change (∑ b : B, z (a₀, b) * x (invA a₀, b)) = 0 at ho
    simp only [Fintype.sum_prod_type]
    simp_rw [canonicalLink_left_overlap_iff L R invA invB hL hR hLA hRB hTNC]
    simp [ite_and]
    exact ho
  · by_cases hright : ∃ b, h = g * R b
    · obtain ⟨b₀, rfl⟩ := hright
      have ho := CA.dual_orthogonal (hz'.1 b₀) (hx'.1 (invB b₀))
      change (∑ a : A, z (a, b₀) * x (a, invB b₀)) = 0 at ho
      simp only [Fintype.sum_prod_type]
      simp_rw [canonicalLink_right_overlap_iff L R invA invB hL hR hLA hRB hTNC]
      simp [ite_and]
      exact ho
    · apply Finset.sum_eq_zero
      intro ab _
      apply Finset.sum_eq_zero
      intro cd _
      have hne : canonicalLink L R (g, false) ab ≠ canonicalLink L R (h, true) cd := by
        intro heq
        rcases (canonicalLink_overlap_iff L R invA invB hL hR hLA hRB hTNC
          g h ab.1 cd.1 ab.2 cd.2).1 heq with ⟨ha, _, _⟩ | ⟨hb, _, _⟩
        · exact hleft ⟨ab.1, ha⟩
        · exact hright ⟨ab.2, hb⟩
      exact if_neg hne


private theorem linearMapOfGenerators_single {F : Type u} {ι κ : Type v}
    [Field F] [Fintype ι] [Fintype κ] (generator : κ → Word F ι) (i : κ) :
    linearMapOfGenerators generator (Pi.single i 1) = generator i := by
  simp [linearMapOfGenerators]

private theorem transposeGenerators_apply {F : Type u} {ι κ : Type v}
    [Field F] [Fintype F] [Fintype ι] [Fintype κ]
    (generator : κ → Word F ι) (y : Word F ι) (i : κ) :
    wordLinearMapTranspose (linearMapOfGenerators generator) y i =
      dotProduct y (generator i) := by
  change (∑ q : ι, y q * (linearMapOfGenerators generator (Pi.single i 1)) q) =
    dotProduct y (generator i)
  rw [linearMapOfGenerators_single]
  rfl

private theorem generators_comp_zero {F : Type u} {ι κ ζ : Type v}
    [Field F] [Fintype F] [Fintype ι] [Fintype κ] [Fintype ζ]
    (gx : κ → Word F ι) (gz : ζ → Word F ι)
    (hOrth : ∀ i j, dotProduct (gz j) (gx i) = 0) :
    (wordLinearMapTranspose (linearMapOfGenerators gx)).comp
      (linearMapOfGenerators gz) = 0 := by
  apply LinearMap.ext
  intro c
  funext i
  change wordLinearMapTranspose (linearMapOfGenerators gx)
    (linearMapOfGenerators gz c) i = 0
  rw [transposeGenerators_apply]
  change dotProduct (∑ j : ζ, c j • gz j) (gx i) = 0
  simp_rw [sum_dotProduct, smul_dotProduct, hOrth]
  simp

private def canonicalRawData {G A B XBasis ZBasis : Type v}
    [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype XBasis] [Fintype ZBasis]
    (L : A → G) (R : B → G) (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hL : Function.Injective L) (hR : Function.Injective R)
    (hLA : ∀ a, L (invA a) = (L a)⁻¹)
    (hRB : ∀ b, R (invB b) = (R b)⁻¹)
    (hTNC : ∀ g a b, L a * g ≠ g * R b)
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (xb : Module.Basis XBasis (ZMod 2) (tensorCode CA.dual CB.dual).carrier)
    (zb : Module.Basis ZBasis (ZMod 2) (tensorCode CA CB).carrier) :
    RawData G A B (CanonicalSquare L R) XBasis ZBasis where
  complex := canonicalSquareComplex L R invA invB hL hR hLA hRB hTNC
  codeA := CA
  codeB := CB
  xBasis := xb
  zBasis := zb

private theorem canonicalRawData_boundary_squared {G A B XBasis ZBasis : Type v}
    [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype XBasis] [Fintype ZBasis]
    (L : A → G) (R : B → G) (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hL : Function.Injective L) (hR : Function.Injective R)
    (hLA : ∀ a, L (invA a) = (L a)⁻¹)
    (hRB : ∀ b, R (invB b) = (R b)⁻¹)
    (hTNC : ∀ g a b, L a * g ≠ g * R b)
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (xb : Module.Basis XBasis (ZMod 2) (tensorCode CA.dual CB.dual).carrier)
    (zb : Module.Basis ZBasis (ZMod 2) (tensorCode CA CB).carrier) :
    let D := canonicalRawData L R invA invB hL hR hLA hRB hTNC CA CB xb zb
    D.boundary1.comp D.boundary2 = 0 := by
  dsimp only
  apply generators_comp_zero
  intro i j
  change dotProduct
    (localExtensionWord (canonicalLink L R (j.1, false)) (zb j.2).1)
    (localExtensionWord (canonicalLink L R (i.1, true)) (xb i.2).1) = 0
  exact canonicalLocalChecks_orthogonal L R invA invB hL hR hLA hRB hTNC
    CA CB j.1 i.1 (zb j.2).1 (xb i.2).1 (zb j.2).2 (xb i.2).2

/-- Actual commuting Quantum Tanner data with caller-selected bases of the
two local tensor codes. The CSS law is proved from the four-corner geometry. -/
def canonicalData {G A B XBasis ZBasis : Type v}
    [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype XBasis] [Fintype ZBasis]
    (L : A → G) (R : B → G) (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hL : Function.Injective L) (hR : Function.Injective R)
    (hLA : ∀ a, L (invA a) = (L a)⁻¹)
    (hRB : ∀ b, R (invB b) = (R b)⁻¹)
    (hTNC : ∀ g a b, L a * g ≠ g * R b)
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (xb : Module.Basis XBasis (ZMod 2) (tensorCode CA.dual CB.dual).carrier)
    (zb : Module.Basis ZBasis (ZMod 2) (tensorCode CA CB).carrier) :
    Data G A B (CanonicalSquare L R) XBasis ZBasis where
  toRawData := canonicalRawData L R invA invB hL hR hLA hRB hTNC CA CB xb zb
  boundary_squared :=
    canonicalRawData_boundary_squared L R invA invB hL hR hLA hRB hTNC CA CB xb zb


/-- A finite tensor-code basis index in the coordinate universe. -/
abbrev TensorBasisIndex
    {A : Type v} [Fintype A] (C : LinearCode (ZMod 2) A) :=
  ULift.{v} (Fin (Dimension C))

/-- Choose a genuine basis of the actual code carrier, not an assumed family
of local checks.  The universe lift changes only the index type. -/
private noncomputable def finiteLocalCodeBasis
    {A : Type v} [Fintype A] (C : LinearCode (ZMod 2) A) :
    Module.Basis (TensorBasisIndex C) (ZMod 2) C.carrier :=
  (Module.finBasis (ZMod 2) C.carrier).reindex Equiv.ulift.symm

/-- Both tensor bases are constructed from one fixed generator/check-matrix
sample.  This is raw data only: the geometric CSS commutation proof is not
supplied by choosing bases. -/
private noncomputable def rawDataOfLocalCodeSample
    {r : Nat} {G A B Square : Type v}
    [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
    (X : LeftRightCayleySquareComplex G A B Square)
    (sample : RandomLocalCodeSample r A B) :
    RawData G A B Square
      (TensorBasisIndex (tensorCode sample.codeA.dual sample.codeB.dual))
      (TensorBasisIndex (tensorCode sample.codeA sample.codeB)) where
  complex := X
  codeA := sample.codeA
  codeB := sample.codeB
  xBasis := finiteLocalCodeBasis (tensorCode sample.codeA.dual sample.codeB.dual)
  zBasis := finiteLocalCodeBasis (tensorCode sample.codeA sample.codeB)

/-- The constructed raw data retain exactly the two codes of the original
sample; neither code is reselected when a complex is introduced. -/
private theorem rawDataOfLocalCodeSample_codes
    {r : Nat} {G A B Square : Type v}
    [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
    (X : LeftRightCayleySquareComplex G A B Square)
    (sample : RandomLocalCodeSample r A B) :
    (rawDataOfLocalCodeSample X sample).codeA = sample.codeA ∧
      (rawDataOfLocalCodeSample X sample).codeB = sample.codeB :=
  ⟨rfl, rfl⟩

/-- The chosen finite index has the actual carrier dimension. -/
private theorem card_tensorBasisIndex
    {A : Type v} [Fintype A] (C : LinearCode (ZMod 2) A) :
    Fintype.card (TensorBasisIndex C) = Dimension C := by
  simp only [TensorBasisIndex, Fintype.card_ulift, Fintype.card_fin]

/-- A witness is selected before the complex; its two carrier bases can then
be constructed without resampling or postulating any check family. -/
private theorem exists_rawData_of_localCodeSample_event
    {r : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (event : RandomLocalCodeSample r A B → Prop)
    (hSample : ∃ sample, event sample) :
    ∃ sample : RandomLocalCodeSample r A B, event sample ∧
      ∀ (G Square : Type v) [Group G] [Fintype G] [Fintype Square]
        (X : LeftRightCayleySquareComplex G A B Square),
        ∃ D : RawData G A B Square
            (TensorBasisIndex (tensorCode sample.codeA.dual sample.codeB.dual))
            (TensorBasisIndex (tensorCode sample.codeA sample.codeB)),
          D.complex = X ∧ D.codeA = sample.codeA ∧ D.codeB = sample.codeB := by
  obtain ⟨sample, hEvent⟩ := hSample
  refine ⟨sample, hEvent, ?_⟩
  intro G Square _ _ _ X
  exact ⟨rawDataOfLocalCodeSample X sample, rfl,
    (rawDataOfLocalCodeSample_codes X sample).1,
    (rawDataOfLocalCodeSample_codes X sample).2⟩

/-- Select the real local-code witness once, then construct its actual tensor
bases over every supplied complex.  The conclusion deliberately contains
`RawData`, not `Data`: CSS commutation and the selected expanding family are
separate geometric obligations. -/
private theorem exists_eventual_source_realLocalRawData
    (epsilon gamma delta rho : ℝ) (hEpsilon : 0 < epsilon)
    (hEpsilonUpper : epsilon < 1 / 2)
    (hGammaLower : 1 / 2 + epsilon < gamma) (hGamma : gamma < 1)
    (hDelta : 0 < delta) (hDeltaHalf : delta < 1 / 2)
    (hRho : 0 < rho) (hRhoHalf : rho < 1 / 2)
    (hEntropy : Real.binEntropy delta < rho * Real.log 2) :
    ∃ threshold : Nat, ∀ n : Nat, threshold ≤ n →
      0 < randomRowCount rho n ∧ randomRowCount rho n < n ∧
        ∀ (A B : Type v) [Fintype A] [Fintype B],
          Fintype.card A = n → Fintype.card B = n →
            ∃ sample : RandomLocalCodeSample (randomRowCount rho n) A B,
              SourceRealLocalCodeEvent rho n (delta * n)
                ((n : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2))
                ((n : ℝ) ^ gamma) sample ∧
              ∀ (G Square : Type v) [Group G] [Fintype G] [Fintype Square]
                (X : LeftRightCayleySquareComplex G A B Square),
                ∃ D : RawData G A B Square
                    (TensorBasisIndex (tensorCode sample.codeA.dual sample.codeB.dual))
                    (TensorBasisIndex (tensorCode sample.codeA sample.codeB)),
                  D.complex = X ∧ D.codeA = sample.codeA ∧ D.codeB = sample.codeB := by
  obtain ⟨threshold, hThreshold⟩ := exists_eventual_source_realLocalCodeSample
    epsilon gamma delta rho hEpsilon hEpsilonUpper hGammaLower hGamma
    hDelta hDeltaHalf hRho hRhoHalf hEntropy
  refine ⟨threshold, ?_⟩
  intro n hn
  obtain ⟨hrPositive, hrDegree, hSample⟩ := hThreshold n hn
  refine ⟨hrPositive, hrDegree, ?_⟩
  intro A B _ _ hA hB
  exact exists_rawData_of_localCodeSample_event _ (hSample A B hA hB)

/-- Extend the two tensor bases of one fixed sample across the actual
four-corner Cayley complex.  CSS commutation is proved from the geometry,
rather than supplied as a sample-selection hypothesis. -/
def canonicalDataOfLocalCodeSample
    {r : Nat} {G A B : Type v}
    [Group G] [Fintype G] [Fintype A] [Fintype B]
    (L : A → G) (R : B → G) (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hL : Function.Injective L) (hR : Function.Injective R)
    (hLA : ∀ a, L (invA a) = (L a)⁻¹)
    (hRB : ∀ b, R (invB b) = (R b)⁻¹)
    (hTNC : ∀ g a b, L a * g ≠ g * R b)
    (sample : RandomLocalCodeSample r A B) :
    Data G A B (CanonicalSquare L R)
      (TensorBasisIndex (tensorCode sample.codeA.dual sample.codeB.dual))
      (TensorBasisIndex (tensorCode sample.codeA sample.codeB)) :=
  canonicalData L R invA invB hL hR hLA hRB hTNC sample.codeA sample.codeB
    (finiteLocalCodeBasis (tensorCode sample.codeA.dual sample.codeB.dual))
    (finiteLocalCodeBasis (tensorCode sample.codeA sample.codeB))

/-- Supplying the geometric boundary law leaves the raw data, including both
selected bases, definitionally unchanged. -/
private theorem canonicalDataOfLocalCodeSample_toRawData
    {r : Nat} {G A B : Type v}
    [Group G] [Fintype G] [Fintype A] [Fintype B]
    (L : A → G) (R : B → G) (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hL : Function.Injective L) (hR : Function.Injective R)
    (hLA : ∀ a, L (invA a) = (L a)⁻¹)
    (hRB : ∀ b, R (invB b) = (R b)⁻¹)
    (hTNC : ∀ g a b, L a * g ≠ g * R b)
    (sample : RandomLocalCodeSample r A B) :
    (canonicalDataOfLocalCodeSample L R invA invB hL hR hLA hRB hTNC sample).toRawData =
      rawDataOfLocalCodeSample
        (canonicalSquareComplex L R invA invB hL hR hLA hRB hTNC) sample :=
  rfl

/-- Select the local event witness once, before any admissible group geometry.
The same sample and the same two bases then give genuine commuting data. -/
private theorem exists_canonicalData_of_localCodeSample_event
    {r : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (event : RandomLocalCodeSample r A B → Prop)
    (hSample : ∃ sample, event sample) :
    ∃ sample : RandomLocalCodeSample r A B, event sample ∧
      ∀ (G : Type v) [Group G] [Fintype G]
        (L : A → G) (R : B → G) (invA : Equiv.Perm A) (invB : Equiv.Perm B)
        (hL : Function.Injective L) (hR : Function.Injective R)
        (hLA : ∀ a, L (invA a) = (L a)⁻¹)
        (hRB : ∀ b, R (invB b) = (R b)⁻¹)
        (hTNC : ∀ g a b, L a * g ≠ g * R b),
        ∃ D : Data G A B (CanonicalSquare L R)
            (TensorBasisIndex (tensorCode sample.codeA.dual sample.codeB.dual))
            (TensorBasisIndex (tensorCode sample.codeA sample.codeB)),
          D.toRawData = rawDataOfLocalCodeSample
            (canonicalSquareComplex L R invA invB hL hR hLA hRB hTNC) sample := by
  obtain ⟨sample, hEvent⟩ := hSample
  refine ⟨sample, hEvent, ?_⟩
  intro G _ _ L R invA invB hL hR hLA hRB hTNC
  exact ⟨canonicalDataOfLocalCodeSample L R invA invB hL hR hLA hRB hTNC sample,
    canonicalDataOfLocalCodeSample_toRawData L R invA invB hL hR hLA hRB hTNC sample⟩

/-- The source local-code event yields actual commuting data on every
admissible four-corner geometry, with one fixed sample and its original bases.
Choosing an expanding PSL2 family and proving global distance remain separate. -/
private theorem exists_eventual_source_realLocalCanonicalData
    (epsilon gamma delta rho : ℝ) (hEpsilon : 0 < epsilon)
    (hEpsilonUpper : epsilon < 1 / 2)
    (hGammaLower : 1 / 2 + epsilon < gamma) (hGamma : gamma < 1)
    (hDelta : 0 < delta) (hDeltaHalf : delta < 1 / 2)
    (hRho : 0 < rho) (hRhoHalf : rho < 1 / 2)
    (hEntropy : Real.binEntropy delta < rho * Real.log 2) :
    ∃ threshold : Nat, ∀ n : Nat, threshold ≤ n →
      0 < randomRowCount rho n ∧ randomRowCount rho n < n ∧
        ∀ (A B : Type v) [Fintype A] [Fintype B],
          Fintype.card A = n → Fintype.card B = n →
            ∃ sample : RandomLocalCodeSample (randomRowCount rho n) A B,
              SourceRealLocalCodeEvent rho n (delta * n)
                ((n : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2))
                ((n : ℝ) ^ gamma) sample ∧
              ∀ (G : Type v) [Group G] [Fintype G]
                (L : A → G) (R : B → G) (invA : Equiv.Perm A) (invB : Equiv.Perm B)
                (hL : Function.Injective L) (hR : Function.Injective R)
                (hLA : ∀ a, L (invA a) = (L a)⁻¹)
                (hRB : ∀ b, R (invB b) = (R b)⁻¹)
                (hTNC : ∀ g a b, L a * g ≠ g * R b),
                ∃ D : Data G A B (CanonicalSquare L R)
                    (TensorBasisIndex (tensorCode sample.codeA.dual sample.codeB.dual))
                    (TensorBasisIndex (tensorCode sample.codeA sample.codeB)),
                  D.toRawData = rawDataOfLocalCodeSample
                    (canonicalSquareComplex L R invA invB hL hR hLA hRB hTNC) sample := by
  obtain ⟨threshold, hThreshold⟩ := exists_eventual_source_realLocalCodeSample
    epsilon gamma delta rho hEpsilon hEpsilonUpper hGammaLower hGamma
    hDelta hDeltaHalf hRho hRhoHalf hEntropy
  refine ⟨threshold, ?_⟩
  intro n hn
  obtain ⟨hrPositive, hrDegree, hSample⟩ := hThreshold n hn
  refine ⟨hrPositive, hrDegree, ?_⟩
  intro A B _ _ hA hB
  exact exists_canonicalData_of_localCodeSample_event _ (hSample A B hA hB)


/-- Positive probability of the simultaneous LZ22 local-code event fixes one
actual generator/check-matrix sample satisfying every clause of the event.
The witness is selected once, before any square-complex family is introduced. -/
theorem exists_goodLocalCodeSample_of_positive
    {r dimensionA dimensionB distanceThreshold robustness punctures : Nat}
    {A B : Type v} [Fintype A] [Fintype B]
    [DecidablePred (GoodLocalCodeEvent
      (r := r) (A := A) (B := B)
      dimensionA dimensionB distanceThreshold robustness punctures)]
    (hpositive : HasPositiveUniformProbability
      (GoodLocalCodeEvent
        (r := r) (A := A) (B := B)
        dimensionA dimensionB distanceThreshold robustness punctures)) :
    ∃ sample : RandomLocalCodeSample r A B,
      GoodLocalCodeEvent
        dimensionA dimensionB distanceThreshold robustness punctures sample := by
  exact (hasPositiveUniformProbability_iff_exists _).mp hpositive

/-- The successful event records the exact dimension of the generator-code
half of the local pair. -/
theorem dimension_codeA_of_goodLocalCodeEvent
    {r dimensionA dimensionB distanceThreshold robustness punctures : Nat}
    {A B : Type v} [Fintype A] [Fintype B]
    {sample : RandomLocalCodeSample r A B}
    (hgood : GoodLocalCodeEvent
      dimensionA dimensionB distanceThreshold robustness punctures sample) :
    Dimension sample.codeA = dimensionA :=
  hgood.1

/-- The successful event records the exact dimension of the parity-check
kernel half of the local pair. -/
theorem dimension_codeB_of_goodLocalCodeEvent
    {r dimensionA dimensionB distanceThreshold robustness punctures : Nat}
    {A B : Type v} [Fintype A] [Fintype B]
    {sample : RandomLocalCodeSample r A B}
    (hgood : GoodLocalCodeEvent
      dimensionA dimensionB distanceThreshold robustness punctures sample) :
    Dimension sample.codeB = dimensionB :=
  hgood.2.1

/-! ## Algebraic-to-semantic CSS distance -/

/-- An attained minimum over the union of the two nontrivial algebraic CSS
sectors is the semantic Pauli distance of the source-valid stabilizer built
from the same parity checks.  This form is the one produced by the Quantum
Tanner global-distance argument; unlike the sectorwise API, it does not assume
that each logical sector is separately nonempty. -/
theorem semanticStabilizerDistance_of_algebraicCSSMinimumDistance
    {iota kappaP kappaQ : Type v}
    [Fintype iota] [DecidableEq iota] [Fintype kappaP] [Fintype kappaQ]
    (P : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaP)
    (Q : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaQ)
    (horth : ∀ p q,
      wordPairing (parityCheckRow P p)
        (parityCheckRow Q q) = 0)
    {distance : Nat}
    (hDistance : AlgebraicCSSMinimumDistance
      (parityCheckRowCode Q)
      (parityCheckRowCode P) distance) :
    StabilizerCode.SemanticStabilizerDistance
      (PauliSymplectic.binaryCSSSourceValidStabilizerOfParityChecks
        P Q horth) distance := by
  rw [StabilizerCode.semanticStabilizerDistance_iff_minWeight_inBinaryNormalizer_diff]
  rcases hDistance with ⟨word, hword, hweight, hleast⟩
  rcases hword with hX | hZ
  · refine ⟨PauliSymplectic.cssXCheck word, ?_, ?_, ?_, ?_⟩
    have hXKernel := hX.1
    rw [parityCheckRowCode_dual_eq_kernelCode] at hXKernel
    · exact
        (PauliSymplectic.inBinaryNormalizer_binaryCSSStabilizerCodeOfParityChecks_iff
          P Q horth (PauliSymplectic.cssXCheck word)).2
          ⟨by simpa using hXKernel,
            (parityCheckKernelCode Q).carrier.zero_mem⟩
    · intro hgenerated
      have hcomponents :=
        (PauliSymplectic.inGeneratedGroupUpToSign_binaryCSSStabilizerCodeOfParityChecks_iff
          P Q horth (PauliSymplectic.cssXCheck word)).1 hgenerated
      exact hX.2 hcomponents.1
    · simpa using
        (PauliSymplectic.weight_cssXCheck_eq_hammingWeight word).trans hweight
    · intro error hnormalizer houtside
      have hnormalizerComponents :=
        (PauliSymplectic.inBinaryNormalizer_binaryCSSStabilizerCodeOfParityChecks_iff
          P Q horth error).1 hnormalizer
      have houtsideComponents :
          error.vector.xPart ∉
              (parityCheckRowCode Q).carrier ∨
            error.vector.zPart ∉
              (parityCheckRowCode P).carrier := by
        by_contra hnot
        push_neg at hnot
        exact houtside
          ((PauliSymplectic.inGeneratedGroupUpToSign_binaryCSSStabilizerCodeOfParityChecks_iff
            P Q horth error).2 hnot)
      rcases houtsideComponents with hxOutside | hzOutside
      · have hxDual := hnormalizerComponents.1
        rw [← parityCheckRowCode_dual_eq_kernelCode] at hxDual
        exact (hleast error.vector.xPart (Or.inl
          ⟨hxDual, hxOutside⟩)).trans
          (PauliSymplectic.hammingWeight_xPart_le_weight error)
      · have hzDual := hnormalizerComponents.2
        rw [← parityCheckRowCode_dual_eq_kernelCode] at hzDual
        exact (hleast error.vector.zPart (Or.inr
          ⟨hzDual, hzOutside⟩)).trans
          (PauliSymplectic.hammingWeight_zPart_le_weight error)
  · refine ⟨PauliSymplectic.cssZCheck word, ?_, ?_, ?_, ?_⟩
    have hZKernel := hZ.1
    rw [parityCheckRowCode_dual_eq_kernelCode] at hZKernel
    · exact
        (PauliSymplectic.inBinaryNormalizer_binaryCSSStabilizerCodeOfParityChecks_iff
          P Q horth (PauliSymplectic.cssZCheck word)).2
          ⟨(parityCheckKernelCode P).carrier.zero_mem,
            by simpa using hZKernel⟩
    · intro hgenerated
      have hcomponents :=
        (PauliSymplectic.inGeneratedGroupUpToSign_binaryCSSStabilizerCodeOfParityChecks_iff
          P Q horth (PauliSymplectic.cssZCheck word)).1 hgenerated
      exact hZ.2 hcomponents.2
    · simpa using
        (PauliSymplectic.weight_cssZCheck_eq_hammingWeight word).trans hweight
    · intro error hnormalizer houtside
      have hnormalizerComponents :=
        (PauliSymplectic.inBinaryNormalizer_binaryCSSStabilizerCodeOfParityChecks_iff
          P Q horth error).1 hnormalizer
      have houtsideComponents :
          error.vector.xPart ∉
              (parityCheckRowCode Q).carrier ∨
            error.vector.zPart ∉
              (parityCheckRowCode P).carrier := by
        by_contra hnot
        push_neg at hnot
        exact houtside
          ((PauliSymplectic.inGeneratedGroupUpToSign_binaryCSSStabilizerCodeOfParityChecks_iff
            P Q horth error).2 hnot)
      rcases houtsideComponents with hxOutside | hzOutside
      · have hxDual := hnormalizerComponents.1
        rw [← parityCheckRowCode_dual_eq_kernelCode] at hxDual
        exact (hleast error.vector.xPart (Or.inl
          ⟨hxDual, hxOutside⟩)).trans
          (PauliSymplectic.hammingWeight_xPart_le_weight error)
      · have hzDual := hnormalizerComponents.2
        rw [← parityCheckRowCode_dual_eq_kernelCode] at hzDual
        exact (hleast error.vector.zPart (Or.inr
          ⟨hzDual, hzOutside⟩)).trans
          (PauliSymplectic.hammingWeight_zPart_le_weight error)

/-- A binary semantic stabilizer distance controls arbitrary operators, not
only Pauli errors: every operator supported on fewer than `distance` qubits is
detectable on the same source-valid code.  The proof passes through the
repository's concrete erasure-recovery theorem and then uses exact erasure
recovery to detect every operator on the erased subsystem. -/
theorem semanticStabilizerDistance_detectable_of_card_lt
    {iota : Type v} [Fintype iota] [DecidableEq iota]
    (Q : StabilizerCode.SourceValidBinary iota) {distance : Nat}
    (hDistance : StabilizerCode.SemanticStabilizerDistance Q distance)
    (region : Semantics.QuditSubsystem
      (QEC.QLDPC.uniformQuditDimensions (ι := iota) 2))
    (hcard : Fintype.card region.SelectedCoordinates < distance)
    (localOperator : Semantics.Operator region.selectedSystem) :
    Semantics.DetectableOn Q.1.code
      (region.extendLocalToRegister localOperator) := by
  rcases region with ⟨selected⟩
  let S : Semantics.FiniteSubsystem iota := ⟨selected⟩
  have hSelected : S.selected.card < distance := by
    simpa [S, Semantics.QuditSubsystem.SelectedCoordinates] using hcard
  obtain ⟨recovery, hcorrect⟩ :=
    QEC.Locality.semanticStabilizerDistance_erasureRecoverableFromRegister
      Q distance hDistance S hSelected
  have hInformation :=
    QEC.Locality.erasureCorrectableFromRegister_noInformation
      S Q.1.code recovery hcorrect
  have hAll :=
    ((QEC.Locality.quditSubsystemOfFinite S).noInformationOn_iff_allLocalScalarCompression
      Q.1.code).mp hInformation
  have hScalar := hAll localOperator
  apply (Semantics.QuditSubsystem.scalarCompression_iff_detectableOn Q.1.code _).mp
  exact hScalar

/-- Every concrete region supporting a nondetectable local operator has at
least the binary semantic stabilizer distance. -/
theorem semanticStabilizerDistance_le_card_of_nondetectable
    {iota : Type v} [Fintype iota] [DecidableEq iota]
    (Q : StabilizerCode.SourceValidBinary iota) {distance : Nat}
    (hDistance : StabilizerCode.SemanticStabilizerDistance Q distance)
    (region : Semantics.QuditSubsystem
      (QEC.QLDPC.uniformQuditDimensions (ι := iota) 2))
    (hregion : QEC.QLDPC.SupportsNondetectableLocalOperator Q.1.code region) :
    distance ≤ Fintype.card region.SelectedCoordinates := by
  by_contra hnot
  have hcard : Fintype.card region.SelectedCoordinates < distance := by omega
  rcases hregion with ⟨localOperator, hlocal⟩
  exact hlocal
    (semanticStabilizerDistance_detectable_of_card_lt
      Q hDistance region hcard localOperator)

/-- When the repository's finite-region semantic distance is attained, the
binary semantic stabilizer distance lower-bounds it on the same code.  The
explicit nonemptiness premise is necessary because `semanticQuditDistance`
is defined to be zero when no nondetectable region exists. -/
theorem semanticStabilizerDistance_le_semanticQuditDistance_of_nonempty
    {iota : Type v} [Fintype iota] [DecidableEq iota]
    (Q : StabilizerCode.SourceValidBinary iota) {distance : Nat}
    (hDistance : StabilizerCode.SemanticStabilizerDistance Q distance)
    (hnonempty : {weight : Nat |
      ∃ region : Semantics.QuditSubsystem
          (fun _ : iota => 2),
        Fintype.card region.SelectedCoordinates = weight ∧
          QEC.QLDPC.SupportsNondetectableLocalOperator Q.1.code region}.Nonempty) :
    distance ≤ QEC.QLDPC.semanticQuditDistance
      (fun _ : iota => 2) Q.1.code := by
  rcases QEC.QLDPC.semanticQuditDistance_attained Q.1.code hnonempty with
    ⟨region, hcard, hregion⟩
  rw [← hcard]
  exact semanticStabilizerDistance_le_card_of_nondetectable
    Q hDistance region hregion

/-- An attained binary semantic stabilizer distance supplies a genuine
nondetectable finite-region operator for the repository's general qudit
distance.  The Pauli witness is pulled back along the full-region local
extension, whose surjectivity is proved for positive local dimensions. -/
theorem semanticQuditDistance_logicalRegions_nonempty
    {iota : Type v} [Fintype iota] [DecidableEq iota]
    (Q : StabilizerCode.SourceValidBinary iota) {distance : Nat}
    (hDistance : StabilizerCode.SemanticStabilizerDistance Q distance) :
    {weight : Nat |
      ∃ region : Semantics.QuditSubsystem (fun _ : iota => 2),
        Fintype.card region.SelectedCoordinates = weight ∧
          QEC.QLDPC.SupportsNondetectableLocalOperator Q.1.code region}.Nonempty := by
  obtain ⟨error, herror, _hweight, _hleast⟩ := hDistance
  let region : Semantics.QuditSubsystem (fun _ : iota => 2) :=
    Semantics.QuditSubsystem.fullRegion (fun _ : iota => 2)
  obtain ⟨localOperator, hlocal⟩ :=
    Semantics.QuditSubsystem.fullRegion_extension_surjective
      (fun _ : iota => 2) (fun _ => by decide)
      (PauliSymplectic.toQubitOperator error)
  refine ⟨Fintype.card region.SelectedCoordinates, region, rfl,
    localOperator, ?_⟩
  rw [hlocal]
  exact herror

/-- The binary semantic stabilizer distance lower-bounds the repository's
general local-operator semantic distance on the same qubit code.  Unlike the
attained-infimum helper above, this bridge needs no separate nonemptiness
hypothesis: the attained Pauli witness supplies it on the full region. -/
theorem semanticStabilizerDistance_le_semanticQuditDistance
    {iota : Type v} [Fintype iota] [DecidableEq iota]
    (Q : StabilizerCode.SourceValidBinary iota) {distance : Nat}
    (hDistance : StabilizerCode.SemanticStabilizerDistance Q distance) :
    distance ≤ QEC.QLDPC.semanticQuditDistance
      (fun _ : iota => 2) Q.1.code :=
  semanticStabilizerDistance_le_semanticQuditDistance_of_nonempty
    Q hDistance (semanticQuditDistance_logicalRegions_nonempty Q hDistance)

/-! ## Exact finite-region realizations of binary CSS row checks -/

/-- The finite qubit subsystem consisting exactly of the nonzero coordinates
of a binary word. -/
private def wordSupportSubsystem
    {iota : Type v} [Fintype iota] [DecidableEq iota]
    (word : Word (ZMod 2) iota) : Semantics.FiniteSubsystem iota :=
  ⟨hammingSupport word⟩

/-- Restrict a binary word to a selected coordinate subsystem. -/
private def restrictWordToSubsystem
    {iota : Type v} [Fintype iota] [DecidableEq iota]
    (S : Semantics.FiniteSubsystem iota) (word : Word (ZMod 2) iota) :
    Word (ZMod 2) S.SelectedCoordinates :=
  fun i => word i

/-- Restricting a word to a region containing its support and extending by
zero recovers the original ambient word. -/
private theorem embedSelectedWord_restrictWordToSubsystem
    {iota : Type v} [Fintype iota] [DecidableEq iota]
    (S : Semantics.FiniteSubsystem iota) (word : Word (ZMod 2) iota)
    (hsupport : hammingSupport word ⊆ S.selected) :
    QEC.Locality.embedSelectedWord S (restrictWordToSubsystem S word) = word := by
  funext i
  by_cases hi : i ∈ S.selected
  · simp [QEC.Locality.embedSelectedWord, restrictWordToSubsystem, hi]
  · have hzero : word i = 0 := by
      by_contra hnonzero
      exact hi (hsupport (by simp [hammingSupport, hnonzero]))
    simp [QEC.Locality.embedSelectedWord, hi, hzero]

/-- A pure binary X check as an actual operator on its exact finite support. -/
noncomputable def cssXFiniteQuditCheck
    {iota : Type v} [Fintype iota] [DecidableEq iota]
    (word : Word (ZMod 2) iota) : QEC.QLDPC.FiniteQuditCheck iota 2 := by
  let S := wordSupportSubsystem word
  exact
    { region := QEC.Locality.quditSubsystemOfFinite S
      localOperator := PauliSymplectic.toQubitOperator
        (QEC.Locality.wordBinaryPauli S
          (restrictWordToSubsystem S word, 0)) }

/-- A pure binary Z check as an actual operator on its exact finite support. -/
noncomputable def cssZFiniteQuditCheck
    {iota : Type v} [Fintype iota] [DecidableEq iota]
    (word : Word (ZMod 2) iota) : QEC.QLDPC.FiniteQuditCheck iota 2 := by
  let S := wordSupportSubsystem word
  exact
    { region := QEC.Locality.quditSubsystemOfFinite S
      localOperator := PauliSymplectic.toQubitOperator
        (QEC.Locality.wordBinaryPauli S
          (0, restrictWordToSubsystem S word)) }

/-- Extending the exact-support X check gives the original global CSS Pauli
operator. -/
theorem cssXFiniteQuditCheck_globalOperator
    {iota : Type v} [Fintype iota] [DecidableEq iota]
    (word : Word (ZMod 2) iota) :
    (cssXFiniteQuditCheck word).globalOperator =
      PauliSymplectic.toQubitOperator (PauliSymplectic.cssXCheck word) := by
  let S := wordSupportSubsystem word
  have hembed : QEC.Locality.embedSelectedWord S
      (restrictWordToSubsystem S word) = word :=
    embedSelectedWord_restrictWordToSubsystem S word (by rfl)
  have hzero : QEC.Locality.embedSelectedWord S
      (0 : Word (ZMod 2) S.SelectedCoordinates) = 0 := by
    funext i
    simp [QEC.Locality.embedSelectedWord]
  rw [show (cssXFiniteQuditCheck word).globalOperator =
      S.extendLocalToRegister
        (PauliSymplectic.toQubitOperator
          (QEC.Locality.wordBinaryPauli S
            (restrictWordToSubsystem S word, 0))) by rfl]
  rw [← QEC.Locality.toQubitOperator_embeddedLocalPauli_eq_extendLocalToRegister]
  congr 1
  apply (PauliSymplectic.binaryEquivPhaseXPartZPart (ι := iota)).injective <;>
    simp [QEC.Locality.embeddedLocalPauli, hembed, hzero]

/-- Extending the exact-support Z check gives the original global CSS Pauli
operator. -/
theorem cssZFiniteQuditCheck_globalOperator
    {iota : Type v} [Fintype iota] [DecidableEq iota]
    (word : Word (ZMod 2) iota) :
    (cssZFiniteQuditCheck word).globalOperator =
      PauliSymplectic.toQubitOperator (PauliSymplectic.cssZCheck word) := by
  let S := wordSupportSubsystem word
  have hembed : QEC.Locality.embedSelectedWord S
      (restrictWordToSubsystem S word) = word :=
    embedSelectedWord_restrictWordToSubsystem S word (by rfl)
  have hzero : QEC.Locality.embedSelectedWord S
      (0 : Word (ZMod 2) S.SelectedCoordinates) = 0 := by
    funext i
    simp [QEC.Locality.embedSelectedWord]
  rw [show (cssZFiniteQuditCheck word).globalOperator =
      S.extendLocalToRegister
        (PauliSymplectic.toQubitOperator
          (QEC.Locality.wordBinaryPauli S
            (0, restrictWordToSubsystem S word))) by rfl]
  rw [← QEC.Locality.toQubitOperator_embeddedLocalPauli_eq_extendLocalToRegister]
  congr 1
  apply (PauliSymplectic.binaryEquivPhaseXPartZPart (ι := iota)).injective <;>
    simp [QEC.Locality.embeddedLocalPauli, hembed, hzero]

@[simp]
theorem cssXFiniteQuditCheck_region_selected
    {iota : Type v} [Fintype iota] [DecidableEq iota]
    (word : Word (ZMod 2) iota) :
    (cssXFiniteQuditCheck word).region.selected = hammingSupport word :=
  rfl

@[simp]
theorem cssZFiniteQuditCheck_region_selected
    {iota : Type v} [Fintype iota] [DecidableEq iota]
    (word : Word (ZMod 2) iota) :
    (cssZFiniteQuditCheck word).region.selected = hammingSupport word :=
  rfl

namespace ChainComplexData

/-! ## Finite-qudit presentations of binary chain-complex CSS codes -/

/-- Realize every basis-row CSS check of a binary chain complex as an operator
on exactly the coordinates in that row's support. -/
noncomputable def finiteQuditRowCheck
    {iota kappa lambda : Type v}
    [Fintype iota] [DecidableEq iota] [Fintype kappa] [Fintype lambda]
    (K : ChainComplexData
      (ZMod 2) (Word (ZMod 2) kappa) (Word (ZMod 2) iota)
        (Word (ZMod 2) lambda)) :
    Sum kappa lambda → QEC.QLDPC.FiniteQuditCheck iota 2
  | Sum.inl k => cssXFiniteQuditCheck
      (wordLinearMapTranspose K.boundary1
        (canonicalBasisWord (F := ZMod 2) k))
  | Sum.inr l => cssZFiniteQuditCheck
      (K.boundary2 (canonicalBasisWord (F := ZMod 2) l))

/-- The global extension of a finite row check is the corresponding binary
Pauli row check used by the chain-complex CSS construction. -/
theorem finiteQuditRowCheck_globalOperator
    {iota kappa lambda : Type v}
    [Fintype iota] [DecidableEq iota] [Fintype kappa] [Fintype lambda]
    (K : ChainComplexData
      (ZMod 2) (Word (ZMod 2) kappa) (Word (ZMod 2) iota)
        (Word (ZMod 2) lambda))
    (c : Sum kappa lambda) :
    (finiteQuditRowCheck K c).globalOperator =
      PauliSymplectic.toQubitOperator
        (QEC.QLDPC.chainComplexCSSRowCheck K c) := by
  cases c with
  | inl k =>
      simpa [finiteQuditRowCheck, QEC.QLDPC.chainComplexCSSRowCheck] using
        cssXFiniteQuditCheck_globalOperator
          (wordLinearMapTranspose K.boundary1
            (canonicalBasisWord (F := ZMod 2) k))
  | inr l =>
      simpa [finiteQuditRowCheck, QEC.QLDPC.chainComplexCSSRowCheck] using
        cssZFiniteQuditCheck_globalOperator
          (K.boundary2 (canonicalBasisWord (F := ZMod 2) l))

/-- The selected region of a finite row check is exactly the check support in
the canonical chain-complex boundary incidence. -/
theorem finiteQuditRowCheck_region_selected
    {iota kappa lambda : Type v}
    [Fintype iota] [DecidableEq iota] [Fintype kappa] [Fintype lambda]
    (K : ChainComplexData
      (ZMod 2) (Word (ZMod 2) kappa) (Word (ZMod 2) iota)
        (Word (ZMod 2) lambda))
    (c : Sum kappa lambda) :
    (finiteQuditRowCheck K c).region.selected =
      (QEC.QLDPC.chainComplexBoundaryIncidence K).checkSupport c := by
  ext q
  cases c <;>
    simp [finiteQuditRowCheck, QEC.QLDPC.chainComplexBoundaryIncidence,
      hammingSupport]

/-- The semantic CSS carrier together with the exact-support basis-row checks
is an honest finite-qubit check presentation. -/
noncomputable def finiteQuditCheckPresentation
    {iota kappa lambda : Type v}
    [Fintype iota] [DecidableEq iota] [Fintype kappa] [Fintype lambda]
    (K : ChainComplexData
      (ZMod 2) (Word (ZMod 2) kappa) (Word (ZMod 2) iota)
        (Word (ZMod 2) lambda))
    (encodedQudits : Nat)
    (hdimension :
      Module.finrank Complex (K.binaryCSSCode).stabilizer.code.carrier =
        2 ^ encodedQudits) :
    QEC.QLDPC.FiniteQuditCheckPresentation iota (Sum kappa lambda) where
  alphabetSize := 2
  alphabetSize_ge_two := by decide
  code := (K.binaryCSSCode).stabilizer.code
  checks := finiteQuditRowCheck K
  carrier_iff_fixed := by
    intro psi
    have hsource := K.binaryCSSCode_stabilizer_isSourceValidBinary.2 psi
    have hgenerate :=
      QEC.QLDPC.chainComplexCSSRowChecks_generate_stabilizerGroup K
    rw [QEC.QLDPC.FinsetGenerates] at hgenerate
    constructor
    · intro hpsi c
      rw [finiteQuditRowCheck_globalOperator]
      apply (hsource.mp hpsi)
      have hrow : QEC.QLDPC.chainComplexCSSRowCheck K c ∈
          QEC.QLDPC.chainComplexCSSRowChecks K :=
        (QEC.QLDPC.mem_chainComplexCSSRowChecks K _).2 ⟨c, rfl⟩
      have hgenerated : PauliSymplectic.GeneratedStabilizer
          (fun g : {P : PauliSymplectic.Binary iota //
            P ∈ QEC.QLDPC.chainComplexCSSRowChecks K} => g.1)
          (QEC.QLDPC.chainComplexCSSRowCheck K c) :=
        PauliSymplectic.GeneratedStabilizer.generator
          (⟨QEC.QLDPC.chainComplexCSSRowCheck K c, hrow⟩ :
            {P : PauliSymplectic.Binary iota //
              P ∈ QEC.QLDPC.chainComplexCSSRowChecks K})
      rw [← hgenerate]
      exact hgenerated
    · intro hfixed
      apply hsource.mpr
      intro P hP
      have hgenerated : P ∈ PauliSymplectic.generatedStabilizerSet
          (fun g : {Q : PauliSymplectic.Binary iota //
            Q ∈ QEC.QLDPC.chainComplexCSSRowChecks K} => g.1) := by
        rw [hgenerate]
        exact hP
      change PauliSymplectic.GeneratedStabilizer
        (fun g : {Q : PauliSymplectic.Binary iota //
          Q ∈ QEC.QLDPC.chainComplexCSSRowChecks K} => g.1) P at hgenerated
      apply PauliSymplectic.toQubitOperator_fixed_of_generatedStabilizer
        _ _ hgenerated
      intro g
      rcases (QEC.QLDPC.mem_chainComplexCSSRowChecks K g.1).1 g.2 with
        ⟨c, hc⟩
      rw [← hc, ← finiteQuditRowCheck_globalOperator]
      exact hfixed c
  encodedQudits := encodedQudits
  dimension_eq := by
    change Module.finrank Complex
      (K.binaryCSSCode).stabilizer.code.carrier = 2 ^ encodedQudits
    exact hdimension

/-- The incidence extracted from the finite-qudit presentation is definitionally
the chain complex's boundary-row incidence, including repeated row indices. -/
theorem finiteQuditCheckPresentation_incidence
    {iota kappa lambda : Type v}
    [Fintype iota] [DecidableEq iota] [Fintype kappa] [Fintype lambda]
    (K : ChainComplexData
      (ZMod 2) (Word (ZMod 2) kappa) (Word (ZMod 2) iota)
        (Word (ZMod 2) lambda))
    (encodedQudits : Nat)
    (hdimension :
      Module.finrank Complex (K.binaryCSSCode).stabilizer.code.carrier =
        2 ^ encodedQudits) :
    (finiteQuditCheckPresentation K encodedQudits hdimension).incidence =
      QEC.QLDPC.chainComplexBoundaryIncidence K := by
  have hincident :
      (finiteQuditCheckPresentation K encodedQudits hdimension).incidence.incident =
        (QEC.QLDPC.chainComplexBoundaryIncidence K).incident := by
    funext c q
    apply propext
    change q ∈ (finiteQuditRowCheck K c).region.selected ↔
      (QEC.QLDPC.chainComplexBoundaryIncidence K).incident c q
    rw [finiteQuditRowCheck_region_selected]
    exact QEC.QLDPC.CheckIncidence.mem_checkSupport _ _ _
  exact congrArg (fun incident => QEC.QLDPC.CheckIncidence.mk incident) hincident

/-- Consequently the presentation's semantic locality profile is exactly the
already bounded boundary-incidence locality profile. -/
theorem finiteQuditCheckPresentation_localityProfile
    {iota kappa lambda : Type v}
    [Fintype iota] [DecidableEq iota] [Fintype kappa] [Fintype lambda]
    (K : ChainComplexData
      (ZMod 2) (Word (ZMod 2) kappa) (Word (ZMod 2) iota)
        (Word (ZMod 2) lambda))
    (encodedQudits : Nat)
    (hdimension :
      Module.finrank Complex (K.binaryCSSCode).stabilizer.code.carrier =
        2 ^ encodedQudits) :
    (finiteQuditCheckPresentation K encodedQudits hdimension).localityProfile =
      (QEC.QLDPC.chainComplexBoundaryIncidence K).localityProfile := by
  change
    (finiteQuditCheckPresentation K encodedQudits hdimension).incidence.localityProfile =
      (QEC.QLDPC.chainComplexBoundaryIncidence K).localityProfile
  rw [finiteQuditCheckPresentation_incidence]

/-- An attained algebraic CSS minimum for a finite binary chain complex is the
semantic Pauli distance of the repository's source-valid chain-complex CSS
stabilizer.  The parity-check presentation uses `boundary1` for the X checks
and the transpose of `boundary2` for the Z checks. -/
theorem semanticStabilizerDistance_of_algebraicCSSMinimumDistance
    {iota kappa lambda : Type v}
    [Fintype iota] [DecidableEq iota] [Fintype kappa] [Fintype lambda]
    (K : ChainComplexData
      (ZMod 2) (Word (ZMod 2) kappa) (Word (ZMod 2) iota)
        (Word (ZMod 2) lambda))
    {distance : Nat}
    (hDistance : AlgebraicCSSMinimumDistance
      K.firstCoboundaryCheckCode K.middleBoundaryCode distance) :
    StabilizerCode.SemanticStabilizerDistance
      K.binaryCSSSourceValidStabilizer distance := by
  let P := wordLinearMapTranspose K.boundary2
  let Q := K.boundary1
  have hP : parityCheckRowCode P = K.middleBoundaryCode := by
    unfold parityCheckRowCode ChainComplexData.middleBoundaryCode
    simp only [P, wordLinearMapTranspose_transpose]
  have hQ : parityCheckRowCode Q = K.firstCoboundaryCheckCode := by
    rfl
  have horth : ∀ p q,
      wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0 := by
    apply (parityCheckRows_orthogonal_iff_rowCode_le_dual P Q).2
    simpa [hP, hQ] using K.middleBoundaryCode_le_firstCoboundaryCheckCode_dual
  have hDistance' : AlgebraicCSSMinimumDistance
      (parityCheckRowCode Q) (parityCheckRowCode P) distance := by
    simpa [hP, hQ] using hDistance
  have hSemantic :=
    QEC.Coding.QuantumTanner.semanticStabilizerDistance_of_algebraicCSSMinimumDistance
      P Q horth hDistance'
  simpa [P, Q, PauliSymplectic.binaryCSSSourceValidStabilizerOfParityChecks,
    PauliSymplectic.binaryCSSStabilizerCodeOfParityChecks,
    PauliSymplectic.binaryCSSStabilizerCodeOfDualLe,
    ChainComplexData.binaryCSSSourceValidStabilizer,
    ChainComplexData.binaryCSSCode, hP, hQ] using hSemantic

end ChainComplexData

namespace LeftRightCayleySquareComplex

/-- Extending a local link word by zero cannot increase its support beyond
the `|A| |B|` squares in that link. -/
theorem HammingWeight_localExtension_le
    {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
    [Fintype Square]
    (X : LeftRightCayleySquareComplex G A B Square)
    (vertex : G × Bool) (x : Word (ZMod 2) (A × B)) :
    HammingWeight (X.localExtension vertex x) ≤
      Fintype.card A * Fintype.card B := by
  rw [HammingWeight_eq_card_hammingSupport]
  exact (Finset.card_le_card (X.localExtension_support_subset vertex x)).trans_eq
    (X.incidentSquares_card vertex)

end LeftRightCayleySquareComplex

namespace RawData

variable {G A B Square XBasis ZBasis : Type v}
variable [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
variable [Fintype XBasis] [Fintype ZBasis]

/-- The selected X-check basis has exactly the dimension of the dual local
tensor code it indexes. -/
theorem card_xBasis_eq
    (D : RawData G A B Square XBasis ZBasis) :
    Fintype.card XBasis =
      Dimension (tensorCode D.codeA.dual D.codeB.dual) := by
  rw [Dimension_eq_finrank_carrier,
    Module.finrank_eq_card_basis D.xBasis]

/-- The selected Z-check basis has exactly the dimension of the primal local
tensor code it indexes. -/
theorem card_zBasis_eq
    (D : RawData G A B Square XBasis ZBasis) :
    Fintype.card ZBasis = Dimension (tensorCode D.codeA D.codeB) := by
  rw [Dimension_eq_finrank_carrier,
    Module.finrank_eq_card_basis D.zBasis]

/-- Each selected X generator is supported inside one vertex link. -/
theorem HammingWeight_xGenerator_le
    (D : RawData G A B Square XBasis ZBasis) (check : G × XBasis) :
    HammingWeight (D.xGenerator check) ≤
      Fintype.card A * Fintype.card B := by
  exact D.complex.HammingWeight_localExtension_le
    (check.1, true) (D.xBasis check.2).1

/-- Each selected Z generator is supported inside one vertex link. -/
theorem HammingWeight_zGenerator_le
    (D : RawData G A B Square XBasis ZBasis) (check : G × ZBasis) :
    HammingWeight (D.zGenerator check) ≤
      Fintype.card A * Fintype.card B := by
  exact D.complex.HammingWeight_localExtension_le
    (check.1, false) (D.zBasis check.2).1

@[simp]
theorem linearMapOfGenerators_canonicalBasis
    {F : Type u} {ι κ : Type v} [Field F] [Fintype ι] [Fintype κ]
    (generator : κ → Word F ι) (k : κ) :
    linearMapOfGenerators generator (canonicalBasisWord k) = generator k := by
  classical
  funext i
  unfold linearMapOfGenerators canonicalBasisWord
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [Fintype.sum_eq_single k]
  · simp
  · intro k' hne
    simp [hne]

private theorem wordLinearMapTranspose_canonicalBasis_apply
    {F : Type u} {ι κ : Type v} [Field F] [Fintype F] [Fintype ι] [Fintype κ]
    (map : Word F ι →ₗ[F] Word F κ) (k : κ) (i : ι) :
    wordLinearMapTranspose map (canonicalBasisWord k) i =
      map (canonicalBasisWord i) k := by
  classical
  unfold wordLinearMapTranspose canonicalBasisWord
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Fintype.sum_eq_single k]
  · simp
  · intro k' hne
    simp [hne]

/-- A boundary-one column can meet only X checks based at the two side-one
vertices incident to the square. -/
theorem boundary1_basis_support_subset
    (D : RawData G A B Square XBasis ZBasis) (square : Square) :
    hammingSupport
        (D.boundary1 (canonicalBasisWord (F := ZMod 2) square)) ⊆
      ((Finset.univ.filter fun g => D.complex.Incident (g, true) square).product
        (Finset.univ : Finset XBasis)) := by
  intro check hcheck
  apply Finset.mem_product.mpr
  refine ⟨?_, Finset.mem_univ _⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  have hnonzero :
      D.boundary1 (canonicalBasisWord (F := ZMod 2) square) check ≠ 0 :=
    (Finset.mem_filter.mp hcheck).2
  have hcoordinate :
      D.boundary1 (canonicalBasisWord (F := ZMod 2) square) check =
        D.xGenerator check square := by
    rw [RawData.boundary1,
      wordLinearMapTranspose_canonicalBasis_apply,
      RawData.xGeneratorMap,
      linearMapOfGenerators_canonicalBasis]
  have hxnonzero : D.xGenerator check square ≠ 0 := by
    intro hzero
    apply hnonzero
    rw [hcoordinate, hzero]
  have hsquare : square ∈ hammingSupport (D.xGenerator check) := by
    unfold hammingSupport
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hxnonzero⟩
  have himage := D.complex.localExtension_support_subset
    (check.1, true) (D.xBasis check.2).1 hsquare
  rcases Finset.mem_image.mp himage with ⟨ab, _hab, hab⟩
  exact ⟨ab, hab⟩

/-- A transposed boundary-two column can meet only Z checks based at the two
side-zero vertices incident to the square. -/
theorem transpose_boundary2_basis_support_subset
    (D : RawData G A B Square XBasis ZBasis) (square : Square) :
    hammingSupport
        (wordLinearMapTranspose D.boundary2
          (canonicalBasisWord (F := ZMod 2) square)) ⊆
      ((Finset.univ.filter fun g => D.complex.Incident (g, false) square).product
        (Finset.univ : Finset ZBasis)) := by
  intro check hcheck
  apply Finset.mem_product.mpr
  refine ⟨?_, Finset.mem_univ _⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  have hnonzero :
      wordLinearMapTranspose D.boundary2
          (canonicalBasisWord (F := ZMod 2) square) check ≠ 0 :=
    (Finset.mem_filter.mp hcheck).2
  have hcoordinate :
      wordLinearMapTranspose D.boundary2
          (canonicalBasisWord (F := ZMod 2) square) check =
        D.zGenerator check square := by
    rw [RawData.boundary2,
      wordLinearMapTranspose_canonicalBasis_apply,
      RawData.zGeneratorMap,
      linearMapOfGenerators_canonicalBasis]
  have hznonzero : D.zGenerator check square ≠ 0 := by
    intro hzero
    apply hnonzero
    rw [hcoordinate, hzero]
  have hsquare : square ∈ hammingSupport (D.zGenerator check) := by
    unfold hammingSupport
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hznonzero⟩
  have himage := D.complex.localExtension_support_subset
    (check.1, false) (D.zBasis check.2).1 hsquare
  rcases Finset.mem_image.mp himage with ⟨ab, _hab, hab⟩
  exact ⟨ab, hab⟩

/-- Each square is incident to at most two copies of every selected X-basis
check. -/
theorem HammingWeight_boundary1_basis_le
    (D : RawData G A B Square XBasis ZBasis) (square : Square) :
    HammingWeight (D.boundary1 (canonicalBasisWord (F := ZMod 2) square)) ≤
      2 * Fintype.card XBasis := by
  rw [HammingWeight_eq_card_hammingSupport]
  refine (Finset.card_le_card (D.boundary1_basis_support_subset square)).trans ?_
  calc
    ((Finset.univ.filter fun g => D.complex.Incident (g, true) square).product
        (Finset.univ : Finset XBasis)).card =
        (Finset.univ.filter fun g =>
          D.complex.Incident (g, true) square).card *
          (Finset.univ : Finset XBasis).card := Finset.card_product _ _
    _ ≤ 2 * Fintype.card XBasis := by
      rw [D.complex.incidentVerticesOnSide_card]
      simpa using (Nat.le_refl (2 * Fintype.card XBasis))

/-- Each square is incident to at most two copies of every selected Z-basis
check. -/
theorem HammingWeight_transpose_boundary2_basis_le
    (D : RawData G A B Square XBasis ZBasis) (square : Square) :
    HammingWeight
        (wordLinearMapTranspose D.boundary2
          (canonicalBasisWord (F := ZMod 2) square)) ≤
      2 * Fintype.card ZBasis := by
  rw [HammingWeight_eq_card_hammingSupport]
  refine (Finset.card_le_card
    (D.transpose_boundary2_basis_support_subset square)).trans ?_
  calc
    ((Finset.univ.filter fun g => D.complex.Incident (g, false) square).product
        (Finset.univ : Finset ZBasis)).card =
        (Finset.univ.filter fun g =>
          D.complex.Incident (g, false) square).card *
          (Finset.univ : Finset ZBasis).card := Finset.card_product _ _
    _ ≤ 2 * Fintype.card ZBasis := by
      rw [D.complex.incidentVerticesOnSide_card]
      simpa using (Nat.le_refl (2 * Fintype.card ZBasis))

end RawData

namespace Data

variable {G A B Square XBasis ZBasis : Type v}
variable [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
variable [Fintype XBasis] [Fintype ZBasis]

/-- The actual Quantum Tanner boundary incidence has the source-local variable
degree bound obtained by counting the two incident vertices on each side. -/
theorem boundaryIncidence_variableSupport_card_le
    (D : Data G A B Square XBasis ZBasis) (square : Square) :
    ((QEC.QLDPC.chainComplexBoundaryIncidence D.chainComplex).variableSupport
      square).card ≤
        2 * Fintype.card XBasis + 2 * Fintype.card ZBasis := by
  rw [QEC.QLDPC.chainComplexBoundaryIncidence_variableSupport_card_eq_boundary_columns]
  exact Nat.add_le_add
    (D.toRawData.HammingWeight_boundary1_basis_le square)
    (D.toRawData.HammingWeight_transpose_boundary2_basis_le square)

/-- The variable-degree estimate expressed intrinsically through the two
local tensor-code dimensions, independent of the chosen basis index types. -/
theorem boundaryIncidence_variableSupport_card_le_dimensions
    (D : Data G A B Square XBasis ZBasis) (square : Square) :
    ((QEC.QLDPC.chainComplexBoundaryIncidence D.chainComplex).variableSupport
      square).card ≤
        2 * Dimension (tensorCode D.codeA.dual D.codeB.dual) +
        2 * Dimension (tensorCode D.codeA D.codeB) := by
  simpa [D.toRawData.card_xBasis_eq, D.toRawData.card_zBasis_eq] using
    D.boundaryIncidence_variableSupport_card_le square

/-- The arithmetic core of the LZ22 variable-incidence estimate.  When the
two local codes have complementary dimensions `r` and `Delta - r`, both
selected tensor-code bases have size `r * (Delta - r)`, so the two incident
vertices on each side contribute at most `4 * r * (Delta - r) ≤ Delta²`.

The tensor-code dimension equalities are discharged here from the source
dimensions of the two local codes. -/
theorem boundaryIncidence_variableSupport_card_le_degreeSquared
    (D : Data G A B Square XBasis ZBasis) (Delta r : Nat)
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (hr : r ≤ Delta)
    (hCodeA : Dimension D.codeA = r)
    (hCodeB : Dimension D.codeB = Delta - r)
    (square : Square) :
    ((QEC.QLDPC.chainComplexBoundaryIncidence D.chainComplex).variableSupport
      square).card ≤ Delta * Delta := by
  have hX : Dimension (tensorCode D.codeA.dual D.codeB.dual) =
      (Delta - r) * r := by
    rw [Dimension_tensorCode,
      LinearCode.dual_dimension_eq_length_sub_dimension,
      LinearCode.dual_dimension_eq_length_sub_dimension,
      Length, Length, hA, hB, hCodeA, hCodeB,
      Nat.sub_sub_self hr]
  have hZ : Dimension (tensorCode D.codeA D.codeB) =
      r * (Delta - r) := by
    rw [Dimension_tensorCode, hCodeA, hCodeB]
  have hIncidence := D.boundaryIncidence_variableSupport_card_le_dimensions square
  rw [hX, hZ] at hIncidence
  have hArithmetic :
      2 * ((Delta - r) * r) + 2 * (r * (Delta - r)) ≤ Delta * Delta := by
    have hSub : Delta - r + r = Delta := Nat.sub_add_cancel hr
    have hSubInt :
        ((Delta - r : Nat) : Int) + (r : Int) = (Delta : Int) := by
      exact_mod_cast hSub
    have hArithmeticInt :
        (2 : Int) * ((Delta - r : Nat) : Int) * (r : Int) +
            2 * (r : Int) * ((Delta - r : Nat) : Int) ≤
          (Delta : Int) * (Delta : Int) := by
      nlinarith [sq_nonneg (((Delta - r : Nat) : Int) - (r : Int))]
    have hArithmeticNat :
        2 * (Delta - r) * r + 2 * r * (Delta - r) ≤ Delta * Delta := by
      exact_mod_cast hArithmeticInt
    simpa [Nat.mul_assoc] using hArithmeticNat
  exact hIncidence.trans hArithmetic

/-- The finite Quantum Tanner presentation has locality controlled by the
link size and by the exact number of selected local-basis checks meeting a
square.  This is the construction-level input to the uniform family bound. -/
theorem boundaryIncidence_boundedLocality
    (D : Data G A B Square XBasis ZBasis) :
    QEC.Coding.BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence D.chainComplex).localityProfile
      (max (Fintype.card A * Fintype.card B)
        (2 * Fintype.card XBasis + 2 * Fintype.card ZBasis)) := by
  apply QEC.QLDPC.chainComplexBoundaryIncidence_boundedLocality_of_boundary_bounds
  · intro check
    change HammingWeight
      (wordLinearMapTranspose D.toRawData.boundary1
        (canonicalBasisWord (F := ZMod 2) check)) ≤ _
    rw [RawData.boundary1,
      wordLinearMapTranspose_transpose, RawData.xGeneratorMap,
      RawData.linearMapOfGenerators_canonicalBasis]
    exact D.toRawData.HammingWeight_xGenerator_le check
  · intro check
    change HammingWeight
      (D.toRawData.boundary2
        (canonicalBasisWord (F := ZMod 2) check)) ≤ _
    rw [RawData.boundary2, RawData.zGeneratorMap,
      RawData.linearMapOfGenerators_canonicalBasis]
    exact D.toRawData.HammingWeight_zGenerator_le check
  · exact D.boundaryIncidence_variableSupport_card_le

/-- With a `Delta × Delta` vertex link and the source local-code dimensions,
the actual Quantum Tanner boundary presentation has the uniform locality bound
`Delta²` stated in LZ22. -/
theorem boundaryIncidence_boundedLocality_degreeSquared
    (D : Data G A B Square XBasis ZBasis) (Delta r : Nat)
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (hr : r ≤ Delta)
    (hCodeA : Dimension D.codeA = r)
    (hCodeB : Dimension D.codeB = Delta - r) :
    QEC.Coding.BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence D.chainComplex).localityProfile
      (Delta * Delta) := by
  have hLocality := D.boundaryIncidence_boundedLocality
  have hX : Dimension (tensorCode D.codeA.dual D.codeB.dual) =
      (Delta - r) * r := by
    rw [Dimension_tensorCode,
      LinearCode.dual_dimension_eq_length_sub_dimension,
      LinearCode.dual_dimension_eq_length_sub_dimension,
      Length, Length, hA, hB, hCodeA, hCodeB,
      Nat.sub_sub_self hr]
  have hZ : Dimension (tensorCode D.codeA D.codeB) =
      r * (Delta - r) := by
    rw [Dimension_tensorCode, hCodeA, hCodeB]
  have hXCard : Fintype.card XBasis = (Delta - r) * r := by
    rw [D.toRawData.card_xBasis_eq, hX]
  have hZCard : Fintype.card ZBasis = r * (Delta - r) := by
    rw [D.toRawData.card_zBasis_eq, hZ]
  have hVariableBound :
      2 * Fintype.card XBasis + 2 * Fintype.card ZBasis ≤ Delta * Delta := by
    rw [hXCard, hZCard]
    have hSub : Delta - r + r = Delta := Nat.sub_add_cancel hr
    have hSubInt :
        ((Delta - r : Nat) : Int) + (r : Int) = (Delta : Int) := by
      exact_mod_cast hSub
    have hArithmeticInt :
        (2 : Int) * ((Delta - r : Nat) : Int) * (r : Int) +
            2 * (r : Int) * ((Delta - r : Nat) : Int) ≤
          (Delta : Int) * (Delta : Int) := by
      nlinarith [sq_nonneg (((Delta - r : Nat) : Int) - (r : Int))]
    have hArithmeticNat :
        2 * (Delta - r) * r + 2 * r * (Delta - r) ≤ Delta * Delta := by
      exact_mod_cast hArithmeticInt
    simpa [Nat.mul_assoc] using hArithmeticNat
  have hMax :
      max (Fintype.card A * Fintype.card B)
          (2 * Fintype.card XBasis + 2 * Fintype.card ZBasis) ≤
        Delta * Delta := by
    rw [Nat.max_le]
    constructor
    · simp [hA, hB]
    · exact hVariableBound
  exact ⟨hLocality.1.trans hMax, hLocality.2.trans hMax⟩

/-- A successful LZ22 local-code draw supplies the dimension hypotheses needed
for the construction's exact `Delta²` locality bound.  The equalities below
identify the fixed draw with the two local codes stored by the concrete
Quantum Tanner data; no conclusion about an unselected complex is used. -/
theorem boundaryIncidence_boundedLocality_degreeSquared_of_goodLocalCodeEvent
    (D : Data G A B Square XBasis ZBasis)
    {Delta r distanceThreshold robustness punctures : Nat}
    (sample : RandomLocalCodeSample r A B)
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (hr : r ≤ Delta)
    (hCodeA : D.codeA = sample.codeA)
    (hCodeB : D.codeB = sample.codeB)
    (hgood : GoodLocalCodeEvent
      r (Delta - r) distanceThreshold robustness punctures sample) :
    QEC.Coding.BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence D.chainComplex).localityProfile
      (Delta * Delta) := by
  apply D.boundaryIncidence_boundedLocality_degreeSquared Delta r hA hB hr
  · rw [hCodeA]
    exact dimension_codeA_of_goodLocalCodeEvent hgood
  · rw [hCodeB]
    exact dimension_codeB_of_goodLocalCodeEvent hgood

/-- A family of Quantum Tanner data at one fixed degree, with the source's
complementary local-code dimensions, is an LDPC family of source-valid
stabilizer codes with the uniform bound `Delta²`. -/
theorem boundaryStabilizerFamily_isLDPC_degreeSquared
    {Index : Type u}
    {Gf Af Bf Squaref XBasisf ZBasisf : Index → Type v}
    [∀ i, Group (Gf i)] [∀ i, Fintype (Gf i)]
    [∀ i, Fintype (Af i)] [∀ i, Fintype (Bf i)]
    [∀ i, Fintype (Squaref i)]
    [∀ i, Fintype (XBasisf i)] [∀ i, Fintype (ZBasisf i)]
    (family : ∀ i, Data (Gf i) (Af i) (Bf i) (Squaref i)
      (XBasisf i) (ZBasisf i))
    (Delta r : Nat)
    (hA : ∀ i, Fintype.card (Af i) = Delta)
    (hB : ∀ i, Fintype.card (Bf i) = Delta)
    (hr : r ≤ Delta)
    (hCodeA : ∀ i, Dimension (family i).codeA = r)
    (hCodeB : ∀ i, Dimension (family i).codeB = Delta - r) :
    QEC.QLDPC.IsLDPCStabilizerFamily
      (fun i => (family i).chainComplex.binaryCSSSourceValidStabilizer) := by
  apply QEC.QLDPC.chainComplexCSSFamily_isLDPC_of_uniform_row_bounds
    (K := fun i => (family i).chainComplex) (w := Delta * Delta)
  · intro i check
    change HammingWeight
      (wordLinearMapTranspose (family i).toRawData.boundary1
        (canonicalBasisWord (F := ZMod 2) check)) ≤ _
    rw [RawData.boundary1, wordLinearMapTranspose_transpose,
      RawData.xGeneratorMap, RawData.linearMapOfGenerators_canonicalBasis]
    simpa [hA i, hB i] using
      (family i).toRawData.HammingWeight_xGenerator_le check
  · intro i check
    change HammingWeight
      ((family i).toRawData.boundary2
        (canonicalBasisWord (F := ZMod 2) check)) ≤ _
    rw [RawData.boundary2, RawData.zGeneratorMap,
      RawData.linearMapOfGenerators_canonicalBasis]
    simpa [hA i, hB i] using
      (family i).toRawData.HammingWeight_zGenerator_le check
  · intro i square
    exact (family i).boundaryIncidence_variableSupport_card_le_degreeSquared
      Delta r (hA i) (hB i) hr (hCodeA i) (hCodeB i) square

/-! ## Semantic parameters of one Quantum Tanner code -/

variable [DecidableEq Square]

/-- The algebraic distance component of `Data.HasParameters` is the semantic
Pauli distance of the source-valid stabilizer extracted from the same Quantum
Tanner chain complex. -/
theorem semanticStabilizerDistance_of_hasParameters
    (D : Data G A B Square XBasis ZBasis) {n k distance : Nat}
    (hParameters : D.HasParameters n k distance) :
    StabilizerCode.SemanticStabilizerDistance
      D.chainComplex.binaryCSSSourceValidStabilizer distance :=
  ChainComplexData.semanticStabilizerDistance_of_algebraicCSSMinimumDistance
    D.chainComplex hParameters.2.2

/-- The distance component of `Data.HasParameters` is also a lower bound for
the repository's general local-operator semantic distance.  This is the
finite-code distance bridge needed by the eventual Quantum Tanner family:
the algebraic CSS minimum first gives the attained Pauli distance, and the
full-region argument above supplies attainment for arbitrary local
operators. -/
theorem semanticQuditDistance_ge_of_hasParameters
    (D : Data G A B Square XBasis ZBasis) {n k distance : Nat}
    (hParameters : D.HasParameters n k distance) :
    distance ≤ QEC.QLDPC.semanticQuditDistance
      (fun _ : Square => 2)
      D.chainComplex.binaryCSSSourceValidStabilizer.1.code := by
  exact semanticStabilizerDistance_le_semanticQuditDistance
    D.chainComplex.binaryCSSSourceValidStabilizer
    (D.semanticStabilizerDistance_of_hasParameters hParameters)

/-- The semantic common-fixed carrier of the Quantum Tanner stabilizer has the
dimension recorded by `Data.encodedDimension`. -/
theorem finrank_binaryCSSCode_carrier_eq_pow_encodedDimension
    (D : Data G A B Square XBasis ZBasis) :
    Module.finrank Complex (D.chainComplex.binaryCSSCode).stabilizer.code.carrier =
      2 ^ D.encodedDimension := by
  simpa [Data.encodedDimension] using
    D.chainComplex.binaryCSSCode_finrank_stabilizer_code_carrier_eq_pow_finrank_middleHomology

/-- `Data.HasParameters` identifies its recorded `k` with the actual complex
dimension of the semantic common-fixed carrier.  This discharges the
dimension field required by a finite-qudit check presentation without storing
an independent numerical dimension certificate. -/
theorem finrank_binaryCSSCode_carrier_eq_pow_of_hasParameters
    (D : Data G A B Square XBasis ZBasis) {n k distance : Nat}
    (hParameters : D.HasParameters n k distance) :
    Module.finrank Complex (D.chainComplex.binaryCSSCode).stabilizer.code.carrier =
      2 ^ k := by
  rw [hParameters.2.1]
  exact D.finrank_binaryCSSCode_carrier_eq_pow_encodedDimension

/-! ## Concrete semantic presentations of Quantum Tanner data -/

/-- The actual finite-qubit local-check presentation carried by one Quantum
Tanner datum.  Its checks, code carrier, and encoded dimension are all derived
from the same chain complex. -/
noncomputable def finiteQuditCheckPresentation
    (D : Data G A B Square XBasis ZBasis) :
    QEC.QLDPC.FiniteQuditCheckPresentation Square
      (Sum (G × XBasis) (G × ZBasis)) :=
  ChainComplexData.finiteQuditCheckPresentation
    D.chainComplex D.encodedDimension
      D.finrank_binaryCSSCode_carrier_eq_pow_encodedDimension

@[simp]
theorem finiteQuditCheckPresentation_blockLength
    (D : Data G A B Square XBasis ZBasis) :
    D.finiteQuditCheckPresentation.blockLength = D.blockLength :=
  rfl

@[simp]
theorem finiteQuditCheckPresentation_encodedQudits
    (D : Data G A B Square XBasis ZBasis) :
    D.finiteQuditCheckPresentation.encodedQudits = D.encodedDimension :=
  rfl

/-- The local-check presentation retains exactly the boundary-row incidence
used by the construction-owned locality estimates. -/
theorem finiteQuditCheckPresentation_localityProfile
    (D : Data G A B Square XBasis ZBasis) :
    D.finiteQuditCheckPresentation.localityProfile =
      (QEC.QLDPC.chainComplexBoundaryIncidence D.chainComplex).localityProfile := by
  exact ChainComplexData.finiteQuditCheckPresentation_localityProfile
    D.chainComplex D.encodedDimension
      D.finrank_binaryCSSCode_carrier_eq_pow_encodedDimension

/-- Exact Tanner parameters give the same semantic distance lower bound on the
concrete finite-qudit presentation. -/
theorem finiteQuditCheckPresentation_distance_ge_of_hasParameters
    (D : Data G A B Square XBasis ZBasis) {n k distance : Nat}
    (hParameters : D.HasParameters n k distance) :
    distance ≤ D.finiteQuditCheckPresentation.distance := by
  change distance ≤ QEC.QLDPC.semanticQuditDistance
    (fun _ : Square => 2)
      D.chainComplex.binaryCSSSourceValidStabilizer.1.code
  exact D.semanticQuditDistance_ge_of_hasParameters hParameters

end Data

/-! ## Families of concrete Quantum Tanner presentations -/

namespace Family

variable {Index : Type u}
variable {G A B Square XBasis ZBasis : Index → Type v}
variable [∀ i, Group (G i)] [∀ i, Fintype (G i)]
variable [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
variable [∀ i, Fintype (Square i)] [∀ i, DecidableEq (Square i)]
variable [∀ i, Fintype (XBasis i)] [∀ i, Fintype (ZBasis i)]

/-- A cofinal indexed family of honest Quantum Tanner data determines a family
of the repository's finite-qudit local-check presentations.  This constructor
only packages already constructed data; it does not assume the source's
probabilistic existence or distance conclusion. -/
noncomputable def ofData
    (family : ∀ i, Data (G i) (A i) (B i) (Square i) (XBasis i) (ZBasis i))
    (hcofinal : ∀ N : Nat, ∃ i, N ≤ (family i).blockLength) :
    QEC.QLDPC.QuantumCodeFamily Index Square
      (fun i => Sum (G i × XBasis i) (G i × ZBasis i)) where
  presentation i := (family i).finiteQuditCheckPresentation
  cofinal_blockLength N := by
    obtain ⟨i, hi⟩ := hcofinal N
    exact ⟨i, by simpa using hi⟩

@[simp]
theorem ofData_blockLength
    (family : ∀ i, Data (G i) (A i) (B i) (Square i) (XBasis i) (ZBasis i))
    (hcofinal : ∀ N : Nat, ∃ i, N ≤ (family i).blockLength) (i : Index) :
    (ofData family hcofinal).blockLength i = (family i).blockLength :=
  rfl

@[simp]
theorem ofData_encodedDimension
    (family : ∀ i, Data (G i) (A i) (B i) (Square i) (XBasis i) (ZBasis i))
    (hcofinal : ∀ N : Nat, ∃ i, N ≤ (family i).blockLength) (i : Index) :
    (ofData family hcofinal).encodedDimension i = (family i).encodedDimension :=
  rfl

/-- The semantic distance observation of the packaged family retains every
per-member lower bound proved through `Data.HasParameters`. -/
theorem ofData_distance_ge_of_hasParameters
    (family : ∀ i, Data (G i) (A i) (B i) (Square i) (XBasis i) (ZBasis i))
    (hcofinal : ∀ N : Nat, ∃ i, N ≤ (family i).blockLength)
    (i : Index) {n k distance : Nat}
    (hParameters : (family i).HasParameters n k distance) :
    distance ≤ (ofData family hcofinal).distance i := by
  exact (family i).finiteQuditCheckPresentation_distance_ge_of_hasParameters
    hParameters

/-- The family observation uses exactly the boundary incidence of the member's
Quantum Tanner chain complex. -/
theorem ofData_localityProfile
    (family : ∀ i, Data (G i) (A i) (B i) (Square i) (XBasis i) (ZBasis i))
    (hcofinal : ∀ N : Nat, ∃ i, N ≤ (family i).blockLength) (i : Index) :
    (ofData family hcofinal).localityProfile i =
      (QEC.QLDPC.chainComplexBoundaryIncidence
        (family i).chainComplex).localityProfile := by
  exact (family i).finiteQuditCheckPresentation_localityProfile

/-- Eventual algebraic dimension estimates on actual Tanner parameters become
eventual rate estimates for the semantic presentation family. -/
theorem ofData_hasEventualRateAtLeast_of_hasParameters
    (family : ∀ i, Data (G i) (A i) (B i) (Square i) (XBasis i) (ZBasis i))
    (hcofinal : ∀ N : Nat, ∃ i, N ≤ (family i).blockLength)
    (encoded distance : Index → Nat)
    (hParameters : ∀ i, (family i).HasParameters
      (family i).blockLength (encoded i) (distance i))
    (rate : ℝ)
    (hRate : ∃ N : Nat, ∀ i, N ≤ (family i).blockLength →
      rate * ((family i).blockLength : ℝ) ≤ (encoded i : ℝ)) :
    QEC.QLDPC.HasEventualRateAtLeast (ofData family hcofinal) rate := by
  obtain ⟨N, hN⟩ := hRate
  refine ⟨N, ?_⟩
  intro i hi
  rw [ofData_blockLength] at hi ⊢
  rw [ofData_encodedDimension]
  simpa [(hParameters i).2.1] using hN i hi

/-- Eventual algebraic distance estimates on actual Tanner parameters become
eventual relative-distance estimates for the semantic presentation family. -/
theorem ofData_hasEventualRelativeDistanceAtLeast_of_hasParameters
    (family : ∀ i, Data (G i) (A i) (B i) (Square i) (XBasis i) (ZBasis i))
    (hcofinal : ∀ N : Nat, ∃ i, N ≤ (family i).blockLength)
    (encoded distance : Index → Nat)
    (hParameters : ∀ i, (family i).HasParameters
      (family i).blockLength (encoded i) (distance i))
    (relativeDistance : ℝ)
    (hDistance : ∃ N : Nat, ∀ i, N ≤ (family i).blockLength →
      relativeDistance * ((family i).blockLength : ℝ) ≤ (distance i : ℝ)) :
    QEC.QLDPC.HasEventualRelativeDistanceAtLeast
      (ofData family hcofinal) relativeDistance := by
  obtain ⟨N, hN⟩ := hDistance
  refine ⟨N, ?_⟩
  intro i hi
  rw [ofData_blockLength] at hi ⊢
  have hSemantic : distance i ≤ (ofData family hcofinal).distance i :=
    ofData_distance_ge_of_hasParameters family hcofinal i (hParameters i)
  exact (hN i hi).trans (by exact_mod_cast hSemantic)

/-- Fixed degree and complementary local-code dimensions give the packaged
semantic family the uniform `Delta²` qLDPC bound. -/
theorem ofData_hasUniformLDPC_degreeSquared
    (family : ∀ i, Data (G i) (A i) (B i) (Square i) (XBasis i) (ZBasis i))
    (hcofinal : ∀ N : Nat, ∃ i, N ≤ (family i).blockLength)
    (Delta r : Nat)
    (hA : ∀ i, Fintype.card (A i) = Delta)
    (hB : ∀ i, Fintype.card (B i) = Delta)
    (hr : r ≤ Delta)
    (hCodeA : ∀ i, Dimension (family i).codeA = r)
    (hCodeB : ∀ i, Dimension (family i).codeB = Delta - r) :
    QEC.QLDPC.HasUniformLDPC (ofData family hcofinal) := by
  refine ⟨Delta * Delta, ?_⟩
  intro i
  rw [ofData_localityProfile]
  exact (family i).boundaryIncidence_boundedLocality_degreeSquared
    Delta r (hA i) (hB i) hr (hCodeA i) (hCodeB i)

end Family

end QEC.Coding.QuantumTanner
