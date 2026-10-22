import QEC.Coding.ExpanderCodes.TannerSemanticDistance
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Replicated PK22 numerical schedules

Explicit arithmetic bounds connect finite local-code bad-event estimates to
Tanner distance, graph-expansion, and semantic-rate thresholds. This module
only proves inequalities; it does not select matrices or graphs.
-/

namespace QEC.Coding.TannerLiftedProduct

universe u

variable {F G W R R' : Type u}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']

noncomputable local instance : DecidableEq F := Classical.decEq F
noncomputable local instance : DecidableEq
    (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G) :=
  Classical.decEq _

/-- Elementary upper bound for the low-weight word count appearing in all
four kernel/image bad events. -/
def coarseLowWeightFactor (w d q : Nat) : Nat :=
  d * (w + 1) ^ d * q ^ d

/-- Elementary upper bound for either sparse-rectangle bad event.  The
binomial coefficient is bounded by `2^w`, and the exact rectangle side by
`w`; these losses are only exponential-linear in the fixed local length. -/
def coarseRectangleFactor (w m s q : Nat) : Nat :=
  4 ^ w *
    (s * ((w * w + 1) ^ s) * q ^ (4 * m * w + s))

/-- Base-`q` exponent controlling `coarseRectangleFactor`. -/
def coarseRectangleExponent (w m s q : Nat) : Nat :=
  2 * w + (Nat.log q s + 1) +
    (Nat.log q (w * w + 1) + 1) * s + (4 * m * w + s)

/-- Every natural number is bounded by the corresponding power of any base
at least two. -/
theorem self_le_base_pow (q n : Nat) (hq : 2 ≤ q) : n ≤ q ^ n := by
  calc
    n ≤ 2 * n := by omega
    _ ≤ 2 ^ n := Nat.mul_le_pow (by decide) n
    _ ≤ q ^ n := Nat.pow_le_pow_left hq n

/-- Polynomial powers can be absorbed into an exponential with a linear
exponent. -/
theorem self_pow_le_base_pow_mul (q n a : Nat) (hq : 2 ≤ q) :
    n ^ a ≤ q ^ (n * a) := by
  calc
    n ^ a ≤ (q ^ n) ^ a :=
      Nat.pow_le_pow_left (self_le_base_pow q n hq) a
    _ = q ^ (n * a) := by rw [← pow_mul]

/-- A power upper bound turns directly into an upper bound on the natural
logarithm. -/
theorem log_le_exponent_of_le_pow
    (q x e : Nat) (hq : 1 < q) (hPower : x ≤ q ^ e) :
    Nat.log q x ≤ e := by
  calc
    Nat.log q x ≤ Nat.log q (q ^ e) := Nat.log_mono_right hPower
    _ = e := Nat.log_pow hq e

/-- Logarithm of a fixed polynomial power grows at most linearly. -/
theorem log_self_pow_le_mul
    (q n a : Nat) (hq : 2 ≤ q) :
    Nat.log q (n ^ a) ≤ n * a :=
  log_le_exponent_of_le_pow q (n ^ a) (n * a) (by omega)
    (self_pow_le_base_pow_mul q n a hq)

/-- A constant coefficient and a polynomial power have a logarithm bounded
by the sum of their linear exponential budgets. -/
theorem log_mul_self_pow_le_add
    (q C n a : Nat) (hq : 2 ≤ q) :
    Nat.log q (C * n ^ a) ≤ C + n * a := by
  apply log_le_exponent_of_le_pow q _ _ (by omega)
  calc
    C * n ^ a ≤ q ^ C * q ^ (n * a) :=
      Nat.mul_le_mul (self_le_base_pow q C hq)
        (self_pow_le_base_pow_mul q n a hq)
    _ = q ^ (C + n * a) := by rw [pow_add]

/-- The logarithm of the squared local length `(A * n^e)^2 + 1` has an
explicit linear bound in `A` and `n`. -/
theorem log_sq_mul_pow_add_one_le
    (q A n e : Nat) (hq : 2 ≤ q) (hA : 0 < A) (hn : 0 < n) :
    Nat.log q ((A * n ^ e) * (A * n ^ e) + 1) ≤
      2 * (A + n * e) + 1 := by
  have hLocal : A * n ^ e ≤ q ^ (A + n * e) := by
    calc
      A * n ^ e ≤ q ^ A * q ^ (n * e) :=
        Nat.mul_le_mul (self_le_base_pow q A hq)
          (self_pow_le_base_pow_mul q n e hq)
      _ = q ^ (A + n * e) := by rw [pow_add]
  have hLocalPositive : 0 < A * n ^ e :=
    Nat.mul_pos hA (Nat.pow_pos hn)
  have hSquare : (A * n ^ e) * (A * n ^ e) ≤
      q ^ (2 * (A + n * e)) := by
    calc
      (A * n ^ e) * (A * n ^ e) ≤
          q ^ (A + n * e) * q ^ (A + n * e) :=
        Nat.mul_le_mul hLocal hLocal
      _ = q ^ (2 * (A + n * e)) := by
        rw [← pow_add]
        congr 1
        omega
  have hSquarePositive : 0 < (A * n ^ e) * (A * n ^ e) :=
    Nat.mul_pos hLocalPositive hLocalPositive
  have hWithOne : (A * n ^ e) * (A * n ^ e) + 1 ≤
      q ^ (2 * (A + n * e) + 1) := by
    calc
      (A * n ^ e) * (A * n ^ e) + 1 ≤
          2 * ((A * n ^ e) * (A * n ^ e)) := by omega
      _ ≤ q * ((A * n ^ e) * (A * n ^ e)) :=
        Nat.mul_le_mul_right _ hq
      _ ≤ q * q ^ (2 * (A + n * e)) :=
        Nat.mul_le_mul_left q hSquare
      _ = q ^ (2 * (A + n * e) + 1) := by
        rw [pow_succ', Nat.mul_comm]
  exact log_le_exponent_of_le_pow q _ _ (by omega) hWithOne

/-- The coarse sparse-rectangle exponent is monotone in the local-code
width.  This lets an arbitrary block quotient be rounded up to the next
controlled sixth-power scale. -/
theorem coarseRectangleExponent_mono_width
    (w w' m s q : Nat) (hWidth : w ≤ w') :
    coarseRectangleExponent w m s q ≤
      coarseRectangleExponent w' m s q := by
  have hSquare : w * w + 1 ≤ w' * w' + 1 := by gcongr
  have hLog : Nat.log q (w * w + 1) ≤ Nat.log q (w' * w' + 1) :=
    Nat.log_mono_right hSquare
  unfold coarseRectangleExponent
  gcongr

/-- For the PK22 polynomial schedule `w = A n^6`, `m = n^4`, `s = n^7`,
the rectangle exponent is bounded by a constant times `n^10`. -/
theorem coarseRectangleExponent_polynomial_le
    (A n q : Nat) (hq : 2 ≤ q) (hA : 0 < A) (hn : 0 < n) :
    coarseRectangleExponent (A * n ^ 6) (n ^ 4) (n ^ 7) q + 3 ≤
      (8 * A + 26) * n ^ 10 := by
  have hLogS : Nat.log q (n ^ 7) ≤ n * 7 :=
    log_self_pow_le_mul q n 7 hq
  have hLogSide :
      Nat.log q ((A * n ^ 6) * (A * n ^ 6) + 1) ≤
        2 * (A + n * 6) + 1 :=
    log_sq_mul_pow_add_one_le q A n 6 hq hA hn
  have hOne : 1 ≤ n ^ 10 := Nat.one_le_pow 10 n hn
  have hPowOne : n ≤ n ^ 10 := by
    simpa using Nat.pow_le_pow_right hn (by norm_num : 1 ≤ 10)
  have hPowSix : n ^ 6 ≤ n ^ 10 :=
    Nat.pow_le_pow_right hn (by norm_num)
  have hPowSeven : n ^ 7 ≤ n ^ 10 :=
    Nat.pow_le_pow_right hn (by norm_num)
  have hPowEight : n ^ 8 ≤ n ^ 10 :=
    Nat.pow_le_pow_right hn (by norm_num)
  unfold coarseRectangleExponent
  calc
    2 * (A * n ^ 6) + (Nat.log q (n ^ 7) + 1) +
          (Nat.log q ((A * n ^ 6) * (A * n ^ 6) + 1) + 1) * n ^ 7 +
          (4 * n ^ 4 * (A * n ^ 6) + n ^ 7) + 3 ≤
        2 * (A * n ^ 6) + (n * 7 + 1) +
          ((2 * (A + n * 6) + 1) + 1) * n ^ 7 +
          (4 * n ^ 4 * (A * n ^ 6) + n ^ 7) + 3 := by
      gcongr
    _ = 2 * A * n ^ 6 + 7 * n + 1 +
        2 * A * n ^ 7 + 12 * n ^ 8 + 2 * n ^ 7 +
        4 * A * n ^ 10 + n ^ 7 + 3 := by ring
    _ ≤ 2 * A * n ^ 10 + 7 * n ^ 10 + n ^ 10 +
        2 * A * n ^ 10 + 12 * n ^ 10 + 2 * n ^ 10 +
        4 * A * n ^ 10 + n ^ 10 + 3 * n ^ 10 := by
      gcongr
      exact Nat.mul_le_mul_left 3 hOne
    _ = (8 * A + 26) * n ^ 10 := by ring

/-- Coefficient-bearing version of the PK22 polynomial schedule:
`w = A n^6`, `m = M n^4`, and `s = S n^7`. -/
theorem coarseRectangleExponent_polynomial_coeff_le
    (A M S n q : Nat) (hq : 2 ≤ q) (hA : 0 < A) (hn : 0 < n) :
    coarseRectangleExponent
        (A * n ^ 6) (M * n ^ 4) (S * n ^ 7) q + 3 ≤
      (2 * A + 2 * A * S + 4 * M * A + 16 * S + 11) * n ^ 10 := by
  have hLogS : Nat.log q (S * n ^ 7) ≤ S + n * 7 :=
    log_mul_self_pow_le_add q S n 7 hq
  have hLogSide :
      Nat.log q ((A * n ^ 6) * (A * n ^ 6) + 1) ≤
        2 * (A + n * 6) + 1 :=
    log_sq_mul_pow_add_one_le q A n 6 hq hA hn
  have hOne : 1 ≤ n ^ 10 := Nat.one_le_pow 10 n hn
  have hPowOne : n ≤ n ^ 10 := by
    simpa using Nat.pow_le_pow_right hn (by norm_num : 1 ≤ 10)
  have hPowSix : n ^ 6 ≤ n ^ 10 :=
    Nat.pow_le_pow_right hn (by norm_num)
  have hPowSeven : n ^ 7 ≤ n ^ 10 :=
    Nat.pow_le_pow_right hn (by norm_num)
  have hPowEight : n ^ 8 ≤ n ^ 10 :=
    Nat.pow_le_pow_right hn (by norm_num)
  unfold coarseRectangleExponent
  calc
    2 * (A * n ^ 6) + (Nat.log q (S * n ^ 7) + 1) +
          (Nat.log q ((A * n ^ 6) * (A * n ^ 6) + 1) + 1) *
              (S * n ^ 7) +
          (4 * (M * n ^ 4) * (A * n ^ 6) + S * n ^ 7) + 3 ≤
        2 * (A * n ^ 6) + (S + n * 7 + 1) +
          ((2 * (A + n * 6) + 1) + 1) * (S * n ^ 7) +
          (4 * (M * n ^ 4) * (A * n ^ 6) + S * n ^ 7) + 3 := by
      gcongr
    _ = 2 * A * n ^ 6 + S + 7 * n + 1 +
        2 * A * S * n ^ 7 + 12 * S * n ^ 8 + 2 * S * n ^ 7 +
        4 * M * A * n ^ 10 + S * n ^ 7 + 3 := by ring
    _ ≤ 2 * A * n ^ 10 + S * n ^ 10 + 7 * n ^ 10 + n ^ 10 +
        2 * A * S * n ^ 10 + 12 * S * n ^ 10 + 2 * S * n ^ 10 +
        4 * M * A * n ^ 10 + S * n ^ 10 + 3 * n ^ 10 := by
      gcongr
      · simpa using Nat.mul_le_mul_left S hOne
      · simpa using Nat.mul_le_mul_left 3 hOne
    _ = (2 * A + 2 * A * S + 4 * M * A + 16 * S + 11) * n ^ 10 := by
      ring

/-- A linear threshold on `n` makes the polynomial rectangle exponent
strictly smaller than the PK22 rank budget `k r = n^5 * (B n^6)`. -/
theorem coarseRectangleExponent_polynomial_lt_rank
    (A B n q : Nat) (hq : 2 ≤ q) (hA : 0 < A) (hn : 0 < n)
    (hThreshold : 8 * A + 26 < B * n) :
    coarseRectangleExponent (A * n ^ 6) (n ^ 4) (n ^ 7) q + 3 <
      n ^ 5 * (B * n ^ 6) := by
  calc
    coarseRectangleExponent (A * n ^ 6) (n ^ 4) (n ^ 7) q + 3 ≤
        (8 * A + 26) * n ^ 10 :=
      coarseRectangleExponent_polynomial_le A n q hq hA hn
    _ < (B * n) * n ^ 10 :=
      (Nat.mul_lt_mul_right (Nat.pow_pos hn)).2 hThreshold
    _ = n ^ 5 * (B * n ^ 6) := by ring

/-- Coefficient-bearing strict rectangle/rank comparison. -/
theorem coarseRectangleExponent_polynomial_coeff_lt_rank
    (A M S K B n q : Nat) (hq : 2 ≤ q) (hA : 0 < A) (hn : 0 < n)
    (hThreshold :
      2 * A + 2 * A * S + 4 * M * A + 16 * S + 11 < K * B * n) :
    coarseRectangleExponent
        (A * n ^ 6) (M * n ^ 4) (S * n ^ 7) q + 3 <
      (K * n ^ 5) * (B * n ^ 6) := by
  calc
    coarseRectangleExponent
        (A * n ^ 6) (M * n ^ 4) (S * n ^ 7) q + 3 ≤
        (2 * A + 2 * A * S + 4 * M * A + 16 * S + 11) * n ^ 10 :=
      coarseRectangleExponent_polynomial_coeff_le A M S n q hq hA hn
    _ < (K * B * n) * n ^ 10 :=
      (Nat.mul_lt_mul_right (Nat.pow_pos hn)).2 hThreshold
    _ = (K * n ^ 5) * (B * n ^ 6) := by ring

/-- Rectangle/rank comparison for an arbitrary block quotient `N`.  If
`x^6 ≤ N ≤ 64 x^6`, the existing polynomial estimate applies after widening
the local length from `A N` to `(64 A) x^6`. -/
theorem coarseRectangleExponent_rootSchedule_coeff_lt_rank
    (A M S K B N x q : Nat)
    (hq : 2 ≤ q) (hA : 0 < A) (hx : 0 < x)
    (hLower : x ^ 6 ≤ N) (hUpper : N ≤ 64 * x ^ 6)
    (hThreshold :
      2 * (64 * A) + 2 * (64 * A) * S + 4 * M * (64 * A) +
          16 * S + 11 < K * B * x) :
    coarseRectangleExponent (A * N) (M * x ^ 4) (S * x ^ 7) q + 3 <
      (K * x ^ 5) * (B * N) := by
  have hWidth : A * N ≤ (64 * A) * x ^ 6 := by
    calc
      A * N ≤ A * (64 * x ^ 6) := Nat.mul_le_mul_left A hUpper
      _ = (64 * A) * x ^ 6 := by ring
  have hCoarse :
      coarseRectangleExponent (A * N) (M * x ^ 4) (S * x ^ 7) q + 3 ≤
        (2 * (64 * A) + 2 * (64 * A) * S + 4 * M * (64 * A) +
          16 * S + 11) * x ^ 10 := by
    calc
      coarseRectangleExponent (A * N) (M * x ^ 4) (S * x ^ 7) q + 3 ≤
          coarseRectangleExponent
              ((64 * A) * x ^ 6) (M * x ^ 4) (S * x ^ 7) q + 3 := by
        exact Nat.add_le_add_right
          (coarseRectangleExponent_mono_width
            (A * N) ((64 * A) * x ^ 6) (M * x ^ 4) (S * x ^ 7) q hWidth) 3
      _ ≤ (2 * (64 * A) + 2 * (64 * A) * S + 4 * M * (64 * A) +
          16 * S + 11) * x ^ 10 :=
        coarseRectangleExponent_polynomial_coeff_le
          (64 * A) M S x q hq (Nat.mul_pos (by norm_num) hA) hx
  have hStrict :
      (2 * (64 * A) + 2 * (64 * A) * S + 4 * M * (64 * A) +
          16 * S + 11) * x ^ 10 <
        (K * B * x) * x ^ 10 :=
    (Nat.mul_lt_mul_right (Nat.pow_pos hx)).2 hThreshold
  calc
    coarseRectangleExponent (A * N) (M * x ^ 4) (S * x ^ 7) q + 3 <
        (K * B * x) * x ^ 10 := hCoarse.trans_lt hStrict
    _ = (K * x ^ 5) * (B * x ^ 6) := by ring
    _ ≤ (K * x ^ 5) * (B * N) := by gcongr

/-- The elementary size conditions required by the deterministic and random
local-code theorems for the polynomial schedule reduce to three small
coefficient inequalities. -/
theorem polynomialSchedule_sizeBounds
    (A D n : Nat) (hD : D ≤ A) (hDPositive : 0 < D) (hn : 0 < n)
    (hSmall : 12 ≤ D * n ^ 2)
    (hRank : 36 ≤ 5 * D ^ 2)
    (hRectangle : 4 ≤ D * n ^ 3) :
    0 < D * n ^ 6 ∧
    D * n ^ 6 ≤ A * n ^ 6 ∧
    6 * (2 * n ^ 4) ≤ D * n ^ 6 ∧
    36 * n ^ 5 * n ^ 7 ≤ 5 * (D * n ^ 6) * (D * n ^ 6) ∧
    4 ≤ D * n ^ 6 ∧
    4 * n ^ 4 ≤ D * n ^ 6 ∧
    4 * n ^ 7 ≤ n ^ 4 * (D * n ^ 6) := by
  have hN4 : 0 < n ^ 4 := Nat.pow_pos hn
  have hN6 : 0 < n ^ 6 := Nat.pow_pos hn
  have hDistancePositive : 0 < D * n ^ 6 := Nat.mul_pos hDPositive hN6
  have hLength : D * n ^ 6 ≤ A * n ^ 6 := Nat.mul_le_mul_right _ hD
  have hSmallScaled : 6 * (2 * n ^ 4) ≤ D * n ^ 6 := by
    calc
      6 * (2 * n ^ 4) = 12 * n ^ 4 := by ring
      _ ≤ (D * n ^ 2) * n ^ 4 := Nat.mul_le_mul_right _ hSmall
      _ = D * n ^ 6 := by ring
  have hRankScaled :
      36 * n ^ 5 * n ^ 7 ≤ 5 * (D * n ^ 6) * (D * n ^ 6) := by
    calc
      36 * n ^ 5 * n ^ 7 = 36 * n ^ 12 := by ring
      _ ≤ (5 * D ^ 2) * n ^ 12 := Nat.mul_le_mul_right _ hRank
      _ = 5 * (D * n ^ 6) * (D * n ^ 6) := by ring
  have hFour : 4 ≤ D * n ^ 6 := by
    calc
      4 ≤ 12 * n ^ 4 := by nlinarith [hN4]
      _ = 6 * (2 * n ^ 4) := by ring
      _ ≤ D * n ^ 6 := hSmallScaled
  have hDistanceScale : 4 * n ^ 4 ≤ D * n ^ 6 := by
    calc
      4 * n ^ 4 ≤ 12 * n ^ 4 := Nat.mul_le_mul_right _ (by omega)
      _ = 6 * (2 * n ^ 4) := by ring
      _ ≤ D * n ^ 6 := hSmallScaled
  have hRectangleScale : 4 * n ^ 7 ≤ n ^ 4 * (D * n ^ 6) := by
    calc
      4 * n ^ 7 ≤ (D * n ^ 3) * n ^ 7 :=
        Nat.mul_le_mul_right _ hRectangle
      _ = n ^ 4 * (D * n ^ 6) := by ring
  exact ⟨hDistancePositive, hLength, hSmallScaled, hRankScaled,
    hFour, hDistanceScale, hRectangleScale⟩

/-- Coefficient-bearing deterministic size bounds for
`m = M n^4`, `s = S n^7`, and `k = K n^5`. -/
theorem polynomialSchedule_coeff_sizeBounds
    (A D M S K n : Nat)
    (hD : D ≤ A) (hDPositive : 0 < D) (hMPositive : 0 < M) (hn : 0 < n)
    (hSmall : 12 * M ≤ D * n ^ 2)
    (hRank : 36 * K * S ≤ 5 * D ^ 2)
    (hRectangle : 4 * S ≤ M * D * n ^ 3) :
    0 < D * n ^ 6 ∧
    D * n ^ 6 ≤ A * n ^ 6 ∧
    6 * (2 * (M * n ^ 4)) ≤ D * n ^ 6 ∧
    36 * (K * n ^ 5) * (S * n ^ 7) ≤
      5 * (D * n ^ 6) * (D * n ^ 6) ∧
    4 ≤ D * n ^ 6 ∧
    4 * (M * n ^ 4) ≤ D * n ^ 6 ∧
    4 * (S * n ^ 7) ≤ (M * n ^ 4) * (D * n ^ 6) := by
  have hN4 : 0 < n ^ 4 := Nat.pow_pos hn
  have hN6 : 0 < n ^ 6 := Nat.pow_pos hn
  have hDistancePositive : 0 < D * n ^ 6 := Nat.mul_pos hDPositive hN6
  have hLength : D * n ^ 6 ≤ A * n ^ 6 := Nat.mul_le_mul_right _ hD
  have hSmallScaled : 6 * (2 * (M * n ^ 4)) ≤ D * n ^ 6 := by
    calc
      6 * (2 * (M * n ^ 4)) = (12 * M) * n ^ 4 := by ring
      _ ≤ (D * n ^ 2) * n ^ 4 := Nat.mul_le_mul_right _ hSmall
      _ = D * n ^ 6 := by ring
  have hRankScaled :
      36 * (K * n ^ 5) * (S * n ^ 7) ≤
        5 * (D * n ^ 6) * (D * n ^ 6) := by
    calc
      36 * (K * n ^ 5) * (S * n ^ 7) =
          (36 * K * S) * n ^ 12 := by ring
      _ ≤ (5 * D ^ 2) * n ^ 12 := Nat.mul_le_mul_right _ hRank
      _ = 5 * (D * n ^ 6) * (D * n ^ 6) := by ring
  have hFour : 4 ≤ D * n ^ 6 := by
    calc
      4 ≤ 12 * (M * n ^ 4) := by nlinarith [Nat.mul_pos hMPositive hN4]
      _ = 6 * (2 * (M * n ^ 4)) := by ring
      _ ≤ D * n ^ 6 := hSmallScaled
  have hDistanceScale : 4 * (M * n ^ 4) ≤ D * n ^ 6 := by
    calc
      4 * (M * n ^ 4) ≤ 12 * (M * n ^ 4) :=
        Nat.mul_le_mul_right _ (by omega)
      _ = 6 * (2 * (M * n ^ 4)) := by ring
      _ ≤ D * n ^ 6 := hSmallScaled
  have hRectangleScale :
      4 * (S * n ^ 7) ≤ (M * n ^ 4) * (D * n ^ 6) := by
    calc
      4 * (S * n ^ 7) = (4 * S) * n ^ 7 := by ring
      _ ≤ (M * D * n ^ 3) * n ^ 7 :=
        Nat.mul_le_mul_right _ hRectangle
      _ = (M * n ^ 4) * (D * n ^ 6) := by ring
  exact ⟨hDistancePositive, hLength, hSmallScaled, hRankScaled,
    hFour, hDistanceScale, hRectangleScale⟩

/-- Deterministic size bounds when the replicated local length is an
arbitrary quotient `N` lying between `x^6` and `64 x^6`.  The auxiliary
PK22 scales remain `m = M x^4`, `s = S x^7`, and `k = K x^5`. -/
theorem rootSchedule_coeff_sizeBounds
    (A D M S K N x : Nat)
    (hD : D ≤ A) (hDPositive : 0 < D) (hMPositive : 0 < M)
    (hx : 0 < x) (hLower : x ^ 6 ≤ N)
    (hSmall : 12 * M ≤ D * x ^ 2)
    (hRank : 36 * K * S ≤ 5 * D ^ 2)
    (hRectangle : 4 * S ≤ M * D * x ^ 3) :
    0 < D * N ∧
    D * N ≤ A * N ∧
    6 * (2 * (M * x ^ 4)) ≤ D * N ∧
    36 * (K * x ^ 5) * (S * x ^ 7) ≤ 5 * (D * N) * (D * N) ∧
    4 ≤ D * N ∧
    4 * (M * x ^ 4) ≤ D * N ∧
    4 * (S * x ^ 7) ≤ (M * x ^ 4) * (D * N) := by
  have hNPositive : 0 < N := (Nat.pow_pos hx).trans_le hLower
  have hDistancePositive : 0 < D * N := Nat.mul_pos hDPositive hNPositive
  have hLength : D * N ≤ A * N := Nat.mul_le_mul_right N hD
  have hSmallScaled : 6 * (2 * (M * x ^ 4)) ≤ D * N := by
    calc
      6 * (2 * (M * x ^ 4)) = (12 * M) * x ^ 4 := by ring
      _ ≤ (D * x ^ 2) * x ^ 4 := Nat.mul_le_mul_right _ hSmall
      _ = D * x ^ 6 := by ring
      _ ≤ D * N := Nat.mul_le_mul_left D hLower
  have hLowerSquare : x ^ 12 ≤ N ^ 2 := by
    calc
      x ^ 12 = (x ^ 6) ^ 2 := by ring
      _ ≤ N ^ 2 := Nat.pow_le_pow_left hLower 2
  have hRankScaled :
      36 * (K * x ^ 5) * (S * x ^ 7) ≤ 5 * (D * N) * (D * N) := by
    calc
      36 * (K * x ^ 5) * (S * x ^ 7) =
          (36 * K * S) * x ^ 12 := by ring
      _ ≤ (5 * D ^ 2) * x ^ 12 := Nat.mul_le_mul_right _ hRank
      _ ≤ (5 * D ^ 2) * N ^ 2 :=
        Nat.mul_le_mul_left (5 * D ^ 2) hLowerSquare
      _ = 5 * (D * N) * (D * N) := by ring
  have hMX4 : 0 < M * x ^ 4 :=
    Nat.mul_pos hMPositive (Nat.pow_pos hx)
  have hFour : 4 ≤ D * N := by
    calc
      4 ≤ 12 * (M * x ^ 4) := by omega
      _ = 6 * (2 * (M * x ^ 4)) := by ring
      _ ≤ D * N := hSmallScaled
  have hDistanceScale : 4 * (M * x ^ 4) ≤ D * N := by
    calc
      4 * (M * x ^ 4) ≤ 12 * (M * x ^ 4) :=
        Nat.mul_le_mul_right _ (by omega)
      _ = 6 * (2 * (M * x ^ 4)) := by ring
      _ ≤ D * N := hSmallScaled
  have hRectangleScale :
      4 * (S * x ^ 7) ≤ (M * x ^ 4) * (D * N) := by
    calc
      4 * (S * x ^ 7) = (4 * S) * x ^ 7 := by ring
      _ ≤ (M * D * x ^ 3) * x ^ 7 :=
        Nat.mul_le_mul_right _ hRectangle
      _ = (M * x ^ 4) * (D * x ^ 6) := by ring
      _ ≤ (M * x ^ 4) * (D * N) := by gcongr
  exact ⟨hDistancePositive, hLength, hSmallScaled, hRankScaled,
    hFour, hDistanceScale, hRectangleScale⟩

/-- The real-valued product-expansion budget for the polynomial schedule
follows from the integer coefficient bound `18 ≤ D n^2`. -/
theorem polynomialSchedule_realBudget
    (A D n : Nat) (hA : 0 < A) (hn : 0 < n)
    (hBudget : 18 ≤ D * n ^ 2) :
    4 * (n ^ 4 : ℝ) + 2 ≤
      ((D * n ^ 6 : Nat) : ℝ) /
          (3 * ((A * n ^ 6 : Nat) : ℝ)) *
        ((A * n ^ 6 : Nat) : ℝ) := by
  have hN4 : 0 < n ^ 4 := Nat.pow_pos hn
  have hInteger : 12 * n ^ 4 + 6 ≤ D * n ^ 6 := by
    calc
      12 * n ^ 4 + 6 ≤ 18 * n ^ 4 := by nlinarith
      _ ≤ (D * n ^ 2) * n ^ 4 := Nat.mul_le_mul_right _ hBudget
      _ = D * n ^ 6 := by ring
  have hReal : 12 * (n ^ 4 : ℝ) + 6 ≤ (D * n ^ 6 : Nat) := by
    exact_mod_cast hInteger
  have hWNonzero : ((A * n ^ 6 : Nat) : ℝ) ≠ 0 := by
    positivity
  have hCancel :
      ((D * n ^ 6 : Nat) : ℝ) /
          (3 * ((A * n ^ 6 : Nat) : ℝ)) *
        ((A * n ^ 6 : Nat) : ℝ) =
      ((D * n ^ 6 : Nat) : ℝ) / 3 := by
    field_simp
  rw [hCancel]
  linarith

/-- Coefficient-bearing real product-expansion budget. -/
theorem polynomialSchedule_coeff_realBudget
    (A D M n : Nat) (hA : 0 < A) (hn : 0 < n)
    (hBudget : 12 * M + 6 ≤ D * n ^ 2) :
    4 * ((M * n ^ 4 : Nat) : ℝ) + 2 ≤
      ((D * n ^ 6 : Nat) : ℝ) /
          (3 * ((A * n ^ 6 : Nat) : ℝ)) *
        ((A * n ^ 6 : Nat) : ℝ) := by
  have hN4 : 0 < n ^ 4 := Nat.pow_pos hn
  have hInteger : 12 * (M * n ^ 4) + 6 ≤ D * n ^ 6 := by
    calc
      12 * (M * n ^ 4) + 6 ≤ (12 * M + 6) * n ^ 4 := by
        nlinarith
      _ ≤ (D * n ^ 2) * n ^ 4 := Nat.mul_le_mul_right _ hBudget
      _ = D * n ^ 6 := by ring
  have hReal :
      12 * ((M * n ^ 4 : Nat) : ℝ) + 6 ≤ (D * n ^ 6 : Nat) := by
    exact_mod_cast hInteger
  have hWNonzero : ((A * n ^ 6 : Nat) : ℝ) ≠ 0 := by
    positivity
  have hCancel :
      ((D * n ^ 6 : Nat) : ℝ) /
          (3 * ((A * n ^ 6 : Nat) : ℝ)) *
        ((A * n ^ 6 : Nat) : ℝ) =
      ((D * n ^ 6 : Nat) : ℝ) / 3 := by
    field_simp
  rw [hCancel]
  linarith

/-- Real product-expansion budget for an arbitrary replicated block count
`N ≥ x^6`. -/
theorem rootSchedule_coeff_realBudget
    (A D M N x : Nat) (hA : 0 < A) (hx : 0 < x)
    (hLower : x ^ 6 ≤ N)
    (hBudget : 12 * M + 6 ≤ D * x ^ 2) :
    4 * ((M * x ^ 4 : Nat) : ℝ) + 2 ≤
      ((D * N : Nat) : ℝ) /
          (3 * ((A * N : Nat) : ℝ)) *
        ((A * N : Nat) : ℝ) := by
  have hX4 : 0 < x ^ 4 := Nat.pow_pos hx
  have hNPositive : 0 < N := (Nat.pow_pos hx).trans_le hLower
  have hInteger : 12 * (M * x ^ 4) + 6 ≤ D * N := by
    calc
      12 * (M * x ^ 4) + 6 ≤ (12 * M + 6) * x ^ 4 := by
        nlinarith
      _ ≤ (D * x ^ 2) * x ^ 4 := Nat.mul_le_mul_right _ hBudget
      _ = D * x ^ 6 := by ring
      _ ≤ D * N := Nat.mul_le_mul_left D hLower
  have hReal :
      12 * ((M * x ^ 4 : Nat) : ℝ) + 6 ≤ (D * N : Nat) := by
    exact_mod_cast hInteger
  have hWNonzero : ((A * N : Nat) : ℝ) ≠ 0 := by
    positivity
  have hCancel :
      ((D * N : Nat) : ℝ) /
          (3 * ((A * N : Nat) : ℝ)) *
        ((A * N : Nat) : ℝ) =
      ((D * N : Nat) : ℝ) / 3 := by
    field_simp
  rw [hCancel]
  linarith

/-- The semantic rate inequality is invariant under replication by an
arbitrary common positive-or-zero block count. -/
theorem replicatedSchedule_rateRatio
    (A B B' N : Nat) (rate : ℝ)
    (hCoefficient :
      2 * ((B : ℝ) + B') * A ≤
        (1 - rate) * ((A : ℝ) ^ 2 + 4 * B * B')) :
    2 * (((B * N : Nat) : ℝ) + (B' * N : Nat)) *
        ((A * N : Nat) : ℝ) ≤
      (1 - rate) *
        (((A * N : Nat) : ℝ) ^ 2 +
          4 * ((B * N : Nat) : ℝ) * (B' * N : Nat)) := by
  have hScale : 0 ≤ (((N : Nat) : ℝ) ^ 2) := sq_nonneg _
  have hScaled := mul_le_mul_of_nonneg_right hCoefficient hScale
  norm_num only [Nat.cast_mul] at ⊢ hScaled
  nlinarith

/-- The semantic rate inequality for linearly scaled local dimensions is
exactly its coefficient-level inequality; the common `n^12` factor is
nonnegative. -/
theorem polynomialSchedule_rateRatio
    (A B B' n : Nat) (rate : ℝ)
    (hCoefficient :
      2 * ((B : ℝ) + B') * A ≤
        (1 - rate) * ((A : ℝ) ^ 2 + 4 * B * B')) :
    2 * (((B * n ^ 6 : Nat) : ℝ) + (B' * n ^ 6 : Nat)) *
        ((A * n ^ 6 : Nat) : ℝ) ≤
      (1 - rate) *
        (((A * n ^ 6 : Nat) : ℝ) ^ 2 +
          4 * ((B * n ^ 6 : Nat) : ℝ) * (B' * n ^ 6 : Nat)) := by
  have hScale : 0 ≤ (((n ^ 6 : Nat) : ℝ) ^ 2) := sq_nonneg _
  have hScaled := mul_le_mul_of_nonneg_right hCoefficient hScale
  norm_num only [Nat.cast_mul, Nat.cast_pow] at ⊢ hScaled
  nlinarith

/-- A spectral scale `lambda ≤ C n^3` implies the three deterministic graph
thresholds for the coefficient-bearing polynomial schedule, subject only to
finite coefficient inequalities. -/
theorem polynomialSchedule_graphThresholds
    (A D M S C n : Nat) (lambda : ℝ) (hn : 0 < n)
    (hLambdaNonnegative : 0 ≤ lambda)
    (hLambda : lambda ≤ ((C * n ^ 3 : Nat) : ℝ))
    (hVertical : 2 * M + C ≤ D * n ^ 2)
    (hEdge : 4 * C ≤ M * n)
    (hFace : 16 * (2 * A + 6 * n + 1) * C ^ 2 ≤ S * n) :
    ((2 * (M * n ^ 4) : Nat) : ℝ) + lambda ≤ (D * n ^ 6 : Nat) ∧
    2 * (2 * lambda) ≤ ((M * n ^ 4 : Nat) : ℝ) ∧
    2 * (((Nat.log 2 (2 * (A * n ^ 6)) + 1 : Nat) : ℝ) *
      (8 * lambda ^ 2)) ≤ ((S * n ^ 7 : Nat) : ℝ) := by
  have hN3N4 : n ^ 3 ≤ n ^ 4 :=
    Nat.pow_le_pow_right hn (by norm_num)
  have hVerticalNat :
      2 * (M * n ^ 4) + C * n ^ 3 ≤ D * n ^ 6 := by
    calc
      2 * (M * n ^ 4) + C * n ^ 3 ≤
          2 * (M * n ^ 4) + C * n ^ 4 := by
        gcongr
      _ = (2 * M + C) * n ^ 4 := by ring
      _ ≤ (D * n ^ 2) * n ^ 4 := Nat.mul_le_mul_right _ hVertical
      _ = D * n ^ 6 := by ring
  have hVerticalReal :
      ((2 * (M * n ^ 4) : Nat) : ℝ) + ((C * n ^ 3 : Nat) : ℝ) ≤
        (D * n ^ 6 : Nat) := by
    exact_mod_cast hVerticalNat
  have hEdgeNat : 4 * (C * n ^ 3) ≤ M * n ^ 4 := by
    calc
      4 * (C * n ^ 3) = (4 * C) * n ^ 3 := by ring
      _ ≤ (M * n) * n ^ 3 := Nat.mul_le_mul_right _ hEdge
      _ = M * n ^ 4 := by ring
  have hEdgeReal :
      4 * ((C * n ^ 3 : Nat) : ℝ) ≤ (M * n ^ 4 : Nat) := by
    exact_mod_cast hEdgeNat
  have hLog : Nat.log 2 (2 * (A * n ^ 6)) + 1 ≤
      2 * A + 6 * n + 1 := by
    have hBase : Nat.log 2 (2 * (A * n ^ 6)) ≤ 2 * A + n * 6 := by
      simpa [mul_assoc] using
        (log_mul_self_pow_le_add 2 (2 * A) n 6 (by norm_num))
    omega
  have hLambdaSquare : lambda ^ 2 ≤
      (((C * n ^ 3 : Nat) : ℝ) ^ 2) := by
    exact (sq_le_sq₀ hLambdaNonnegative (by positivity)).2 hLambda
  have hFaceNat :
      16 * (2 * A + 6 * n + 1) * C ^ 2 * n ^ 6 ≤ S * n ^ 7 := by
    calc
      16 * (2 * A + 6 * n + 1) * C ^ 2 * n ^ 6 ≤
          (S * n) * n ^ 6 := Nat.mul_le_mul_right _ hFace
      _ = S * n ^ 7 := by ring
  have hFaceReal :
      16 * ((2 * A + 6 * n + 1 : Nat) : ℝ) *
          (((C * n ^ 3 : Nat) : ℝ) ^ 2) ≤
        ((S * n ^ 7 : Nat) : ℝ) := by
    have hFaceNat' :
        16 * (2 * A + 6 * n + 1) * (C * n ^ 3) ^ 2 ≤ S * n ^ 7 := by
      calc
        16 * (2 * A + 6 * n + 1) * (C * n ^ 3) ^ 2 =
            16 * (2 * A + 6 * n + 1) * C ^ 2 * n ^ 6 := by ring
        _ ≤ S * n ^ 7 := hFaceNat
    exact_mod_cast hFaceNat'
  constructor
  · linarith
  constructor
  · linarith
  · calc
      2 * (((Nat.log 2 (2 * (A * n ^ 6)) + 1 : Nat) : ℝ) *
          (8 * lambda ^ 2)) =
          16 * ((Nat.log 2 (2 * (A * n ^ 6)) + 1 : Nat) : ℝ) *
            lambda ^ 2 := by ring
      _ ≤ 16 * ((2 * A + 6 * n + 1 : Nat) : ℝ) *
          (((C * n ^ 3 : Nat) : ℝ) ^ 2) := by
        gcongr
      _ ≤ ((S * n ^ 7 : Nat) : ℝ) := hFaceReal

/-- Graph thresholds for a replicated local length `A N`, where
`x^6 ≤ N ≤ 64 x^6`.  The upper bound controls the logarithmic face term;
the lower bound supplies the distance scale. -/
theorem rootSchedule_graphThresholds
    (A D M S C N x : Nat) (lambda : ℝ) (hx : 0 < x)
    (hLower : x ^ 6 ≤ N) (hUpper : N ≤ 64 * x ^ 6)
    (hLambdaNonnegative : 0 ≤ lambda)
    (hLambda : lambda ≤ ((C * x ^ 3 : Nat) : ℝ))
    (hVertical : 2 * M + C ≤ D * x ^ 2)
    (hEdge : 4 * C ≤ M * x)
    (hFace : 16 * (128 * A + 6 * x + 1) * C ^ 2 ≤ S * x) :
    ((2 * (M * x ^ 4) : Nat) : ℝ) + lambda ≤ (D * N : Nat) ∧
    2 * (2 * lambda) ≤ ((M * x ^ 4 : Nat) : ℝ) ∧
    2 * (((Nat.log 2 (2 * (A * N)) + 1 : Nat) : ℝ) *
      (8 * lambda ^ 2)) ≤ ((S * x ^ 7 : Nat) : ℝ) := by
  have hX3X4 : x ^ 3 ≤ x ^ 4 :=
    Nat.pow_le_pow_right hx (by norm_num)
  have hVerticalNat :
      2 * (M * x ^ 4) + C * x ^ 3 ≤ D * N := by
    calc
      2 * (M * x ^ 4) + C * x ^ 3 ≤
          2 * (M * x ^ 4) + C * x ^ 4 := by
        gcongr
      _ = (2 * M + C) * x ^ 4 := by ring
      _ ≤ (D * x ^ 2) * x ^ 4 := Nat.mul_le_mul_right _ hVertical
      _ = D * x ^ 6 := by ring
      _ ≤ D * N := Nat.mul_le_mul_left D hLower
  have hVerticalReal :
      ((2 * (M * x ^ 4) : Nat) : ℝ) + ((C * x ^ 3 : Nat) : ℝ) ≤
        (D * N : Nat) := by
    exact_mod_cast hVerticalNat
  have hEdgeNat : 4 * (C * x ^ 3) ≤ M * x ^ 4 := by
    calc
      4 * (C * x ^ 3) = (4 * C) * x ^ 3 := by ring
      _ ≤ (M * x) * x ^ 3 := Nat.mul_le_mul_right _ hEdge
      _ = M * x ^ 4 := by ring
  have hEdgeReal :
      4 * ((C * x ^ 3 : Nat) : ℝ) ≤ (M * x ^ 4 : Nat) := by
    exact_mod_cast hEdgeNat
  have hLogArgument : 2 * (A * N) ≤ (128 * A) * x ^ 6 := by
    calc
      2 * (A * N) ≤ 2 * (A * (64 * x ^ 6)) := by gcongr
      _ = (128 * A) * x ^ 6 := by ring
  have hLog : Nat.log 2 (2 * (A * N)) + 1 ≤
      128 * A + 6 * x + 1 := by
    have hBase : Nat.log 2 ((128 * A) * x ^ 6) ≤
        128 * A + x * 6 :=
      log_mul_self_pow_le_add 2 (128 * A) x 6 (by norm_num)
    have hMono : Nat.log 2 (2 * (A * N)) ≤
        Nat.log 2 ((128 * A) * x ^ 6) :=
      Nat.log_mono_right hLogArgument
    omega
  have hLambdaSquare : lambda ^ 2 ≤
      (((C * x ^ 3 : Nat) : ℝ) ^ 2) := by
    exact (sq_le_sq₀ hLambdaNonnegative (by positivity)).2 hLambda
  have hFaceNat :
      16 * (128 * A + 6 * x + 1) * C ^ 2 * x ^ 6 ≤ S * x ^ 7 := by
    calc
      16 * (128 * A + 6 * x + 1) * C ^ 2 * x ^ 6 ≤
          (S * x) * x ^ 6 := Nat.mul_le_mul_right _ hFace
      _ = S * x ^ 7 := by ring
  have hFaceReal :
      16 * ((128 * A + 6 * x + 1 : Nat) : ℝ) *
          (((C * x ^ 3 : Nat) : ℝ) ^ 2) ≤
        ((S * x ^ 7 : Nat) : ℝ) := by
    have hFaceNat' :
        16 * (128 * A + 6 * x + 1) * (C * x ^ 3) ^ 2 ≤ S * x ^ 7 := by
      calc
        16 * (128 * A + 6 * x + 1) * (C * x ^ 3) ^ 2 =
            16 * (128 * A + 6 * x + 1) * C ^ 2 * x ^ 6 := by ring
        _ ≤ S * x ^ 7 := hFaceNat
    exact_mod_cast hFaceNat'
  constructor
  · linarith
  constructor
  · linarith
  · calc
      2 * (((Nat.log 2 (2 * (A * N)) + 1 : Nat) : ℝ) *
          (8 * lambda ^ 2)) =
          16 * ((Nat.log 2 (2 * (A * N)) + 1 : Nat) : ℝ) *
            lambda ^ 2 := by ring
      _ ≤ 16 * ((128 * A + 6 * x + 1 : Nat) : ℝ) *
          (((C * x ^ 3 : Nat) : ℝ) ^ 2) := by
        gcongr
      _ ≤ ((S * x ^ 7 : Nat) : ℝ) := hFaceReal

/-- The quadratic smoothing weight has only constant multiplicative loss:
`(A² + 1)^A ≤ 3 A^(2A)`. -/
theorem sq_add_one_pow_le_three_mul
    (A : Nat) (hA : 0 < A) :
    (A ^ 2 + 1) ^ A ≤ 3 * A ^ (2 * A) := by
  have hOne : 1 ≤ A := hA
  have hBase : A ^ 2 + 1 ≤ A * (A + 1) := by
    nlinarith
  have hRatioReal :
      (((A + 1) ^ A : Nat) : ℝ) < 3 * (((A ^ A : Nat) : ℝ)) := by
    have hAReal : (0 : ℝ) < A := by exact_mod_cast hA
    calc
      (((A + 1) ^ A : Nat) : ℝ) =
          (A : ℝ) ^ A * (1 + (A : ℝ)⁻¹) ^ A := by
        push_cast
        rw [← mul_pow]
        congr 1
        field_simp
      _ ≤ (A : ℝ) ^ A * Real.exp 1 := by
        gcongr
        exact Real.one_add_inv_pow_le_exp
      _ < (A : ℝ) ^ A * 3 := by
        exact mul_lt_mul_of_pos_left Real.exp_one_lt_three (pow_pos hAReal _)
      _ = 3 * (((A ^ A : Nat) : ℝ)) := by
        push_cast
        ring
  have hRatio : (A + 1) ^ A ≤ 3 * A ^ A := by
    exact_mod_cast hRatioReal.le
  calc
    (A ^ 2 + 1) ^ A ≤ (A * (A + 1)) ^ A :=
      Nat.pow_le_pow_left hBase A
    _ = A ^ A * (A + 1) ^ A := by rw [mul_pow]
    _ ≤ A ^ A * (3 * A ^ A) := Nat.mul_le_mul_left _ hRatio
    _ = 3 * A ^ (2 * A) := by
      rw [show 2 * A = A + A by omega, pow_add]
      ring


end QEC.Coding.TannerLiftedProduct
