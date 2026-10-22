import QEC.Coding.FiberBundle.PartitionedChecksProbability

/-!
# Explicit parameters for the HHO20 fiber-bundle construction

This module discharges the finite analytic side conditions left by the random
base, partition, and twist-spectrum arguments.  In particular, none of those
probabilistic estimates becomes an assumption of the exported construction
theorems.
-/

namespace QEC.Coding.FiberBundle.RandomPartition

/-- Real-valued presentation of the complete random-base failure envelope. -/
noncomputable def fullyGoodBaseFailureBoundReal
    (r Delta : Nat) : Real :=
  (14 * r : Real) * Real.exp (-(Delta : Real) / 40000) +
    ((1 + Real.exp (-(Delta : Real) / 2)) ^ (3 * r) - 1 +
      (2 : Real) ^ (3 * r) * ((4 : Real) / 7) ^ (4 * r)) +
    ((1 + Real.exp (-(3 : Real) * Delta / 28)) ^ (4 * r) - 1 +
      ((3 : Real) ^ ((4 * r) / 5) *
        ((4 : Real) / 3) ^ (4 * r)) *
        ((172 : Real) / 343) ^ (3 * r)) +
    ((1 + Real.exp (-(Delta : Real) / 1000)) ^ (3 * r) - 1)

/-- The ENNReal union bound contains no hidden infinite contribution. -/
theorem fullyGoodBaseFailureBound_toReal
    (r Delta : Nat) :
    (fullyGoodBaseFailureBound r Delta).toReal =
      fullyGoodBaseFailureBoundReal r Delta := by
  have hOneExp (x : Real) :
      (1 + ENNReal.ofReal (Real.exp x)).toReal =
        1 + Real.exp x := by
    rw [ENNReal.toReal_add (by norm_num) (by finiteness)]
    rw [ENNReal.toReal_ofReal (Real.exp_pos x).le]
    norm_num
  have hSub (x : Real) (n : Nat) :
      (((1 + ENNReal.ofReal (Real.exp x)) ^ n - 1 :
          ENNReal).toReal) =
        (1 + Real.exp x) ^ n - 1 := by
    have hBase :
        (1 : ENNReal) ≤
          1 + ENNReal.ofReal (Real.exp x) := by
      simp
    rw [ENNReal.toReal_sub_of_le
      (one_le_pow₀ hBase) (by finiteness)]
    rw [ENNReal.toReal_pow, hOneExp]
    norm_num
  have hDegreeNonneg :
      0 ≤ (14 * r : Real) *
        Real.exp (-(Delta : Real) / 40000) :=
    mul_nonneg (by positivity) (Real.exp_pos _).le
  unfold fullyGoodBaseFailureBound fullyGoodBaseFailureBoundReal
  repeat rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [hSub, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hDegreeNonneg,
    ENNReal.toReal_ofReal (show (0 : Real) ≤ 4 / 7 by norm_num),
    ENNReal.toReal_ofReal (show (0 : Real) ≤ 172 / 343 by norm_num),
    ENNReal.toReal_ofNat,
    ENNReal.toReal_div]

/-- The large-support rank tail is already below one percent once the base
scale reaches one hundred. -/
theorem rankLargeSupportTail_lt_one_hundred
    (r : Nat) (hr : 100 ≤ r) :
    (2 : Real) ^ (3 * r) *
        ((4 : Real) / 7) ^ (4 * r) <
      1 / 100 := by
  calc
    (2 : Real) ^ (3 * r) *
          ((4 : Real) / 7) ^ (4 * r) =
        ((2048 : Real) / 2401) ^ r := by
      rw [pow_mul, pow_mul, ← mul_pow]
      norm_num
    _ ≤ ((9 : Real) / 10) ^ r := by
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) r
    _ ≤ ((9 : Real) / 10) ^ 100 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hr
    _ < 1 / 100 := by norm_num

/-- When `r` is a multiple of five, the large-support distance tail groups
into powers of a single rational number strictly below `9/10`. -/
theorem distanceLargeSupportTail_lt_one_hundred
    (r : Nat) (hr : 500 ≤ r) (hFive : 5 ∣ r) :
    ((3 : Real) ^ ((4 * r) / 5) *
        ((4 : Real) / 3) ^ (4 * r)) *
        ((172 : Real) / 343) ^ (3 * r) <
      1 / 100 := by
  obtain ⟨q, rfl⟩ := hFive
  have hq : 100 ≤ q := by omega
  have hFour : (4 * (5 * q)) / 5 = 4 * q := by omega
  have hTwenty : 4 * (5 * q) = 20 * q := by omega
  have hFifteen : 3 * (5 * q) = 15 * q := by omega
  calc
    ((3 : Real) ^ ((4 * (5 * q)) / 5) *
          ((4 : Real) / 3) ^ (4 * (5 * q))) *
          ((172 : Real) / 343) ^ (3 * (5 * q)) =
        (((3 : Real) ^ 4 *
          ((4 : Real) / 3) ^ 20) *
          ((172 : Real) / 343) ^ 15) ^ q := by
      rw [hFour, hTwenty, hFifteen, pow_mul, pow_mul, pow_mul,
        ← mul_pow, ← mul_pow]
    _ ≤ ((9 : Real) / 10) ^ q := by
      exact pow_le_pow_left₀ (by positivity) (by norm_num) q
    _ ≤ ((9 : Real) / 10) ^ 100 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hq
    _ < 1 / 100 := by norm_num

/-- A finite power of `1 + x` is linear to within a factor two whenever its
total exponent load is at most one. -/
theorem one_add_pow_sub_one_le_two_mul
    (x : Real) (n : Nat) (hx : 0 ≤ x)
    (hSmall : (n : Real) * x ≤ 1) :
    (1 + x) ^ n - 1 ≤ 2 * ((n : Real) * x) := by
  have hPower :
      (1 + x) ^ n ≤ Real.exp ((n : Real) * x) := by
    calc
      (1 + x) ^ n ≤ (Real.exp x) ^ n := by
        exact pow_le_pow_left₀ (by positivity)
          (by simpa [add_comm] using Real.add_one_le_exp x) n
      _ = Real.exp ((n : Real) * x) := by
        rw [Real.exp_nat_mul]
  have hLoadNonneg : 0 ≤ (n : Real) * x := mul_nonneg (by positivity) hx
  have hAbs :=
    Real.abs_exp_sub_one_le
      (show |(n : Real) * x| ≤ 1 by
        simpa [abs_of_nonneg hLoadNonneg] using hSmall)
  calc
    (1 + x) ^ n - 1 ≤
        Real.exp ((n : Real) * x) - 1 := sub_le_sub_right hPower 1
    _ ≤ |Real.exp ((n : Real) * x) - 1| := le_abs_self _
    _ ≤ 2 * |(n : Real) * x| := hAbs
    _ = 2 * ((n : Real) * x) := by rw [abs_of_nonneg hLoadNonneg]

/-- Six explicit one-percent estimates are enough to place the complete
random-base failure envelope below one tenth.  These hypotheses are analytic
subgoals only; the parameter family below discharges them. -/
theorem fullyGoodBaseFailureBoundReal_lt_one_tenth
    (r Delta : Nat)
    (hr : 500 ≤ r) (hFive : 5 ∣ r)
    (hDegree :
      (14 * r : Real) * Real.exp (-(Delta : Real) / 40000) <
        1 / 100)
    (hRank :
      (3 * r : Real) * Real.exp (-(Delta : Real) / 2) <
        1 / 200)
    (hDistance :
      (4 * r : Real) *
          Real.exp (-(3 : Real) * Delta / 28) <
        1 / 200)
    (hExpansion :
      (3 * r : Real) * Real.exp (-(Delta : Real) / 1000) <
        1 / 200) :
    fullyGoodBaseFailureBoundReal r Delta < 1 / 10 := by
  have hRankLoadNonneg :
      0 ≤ (3 * r : Real) * Real.exp (-(Delta : Real) / 2) := by
    positivity
  have hDistanceLoadNonneg :
      0 ≤ (4 * r : Real) *
        Real.exp (-(3 : Real) * Delta / 28) := by
    positivity
  have hExpansionLoadNonneg :
      0 ≤ (3 * r : Real) * Real.exp (-(Delta : Real) / 1000) := by
    positivity
  have hRankGeometric :
      (1 + Real.exp (-(Delta : Real) / 2)) ^ (3 * r) - 1 <
        1 / 100 := by
    refine lt_of_le_of_lt
      (one_add_pow_sub_one_le_two_mul
        (Real.exp (-(Delta : Real) / 2)) (3 * r)
        (Real.exp_pos _).le ?_) ?_
    · norm_num at hRank ⊢
      nlinarith
    · norm_num at hRank ⊢
      nlinarith
  have hDistanceGeometric :
      (1 + Real.exp (-(3 : Real) * Delta / 28)) ^ (4 * r) - 1 <
        1 / 100 := by
    refine lt_of_le_of_lt
      (one_add_pow_sub_one_le_two_mul
        (Real.exp (-(3 : Real) * Delta / 28)) (4 * r)
        (Real.exp_pos _).le ?_) ?_
    · norm_num at hDistance ⊢
      nlinarith
    · norm_num at hDistance ⊢
      nlinarith
  have hExpansionGeometric :
      (1 + Real.exp (-(Delta : Real) / 1000)) ^ (3 * r) - 1 <
        1 / 100 := by
    refine lt_of_le_of_lt
      (one_add_pow_sub_one_le_two_mul
        (Real.exp (-(Delta : Real) / 1000)) (3 * r)
        (Real.exp_pos _).le ?_) ?_
    · norm_num at hExpansion ⊢
      nlinarith
    · norm_num at hExpansion ⊢
      nlinarith
  have hRankLarge :=
    rankLargeSupportTail_lt_one_hundred r (by omega)
  have hDistanceLarge :=
    distanceLargeSupportTail_lt_one_hundred r hr hFive
  dsimp [fullyGoodBaseFailureBoundReal]
  nlinarith

/-- ENNReal-free corollary for the bound consumed by the sample-selection
theorem. -/
theorem fullyGoodBaseFailureBound_toReal_lt_one_tenth
    (r Delta : Nat)
    (hr : 500 ≤ r) (hFive : 5 ∣ r)
    (hDegree :
      (14 * r : Real) * Real.exp (-(Delta : Real) / 40000) <
        1 / 100)
    (hRank :
      (3 * r : Real) * Real.exp (-(Delta : Real) / 2) <
        1 / 200)
    (hDistance :
      (4 * r : Real) *
          Real.exp (-(3 : Real) * Delta / 28) <
        1 / 200)
    (hExpansion :
      (3 * r : Real) * Real.exp (-(Delta : Real) / 1000) <
        1 / 200) :
    (fullyGoodBaseFailureBound r Delta).toReal < 1 / 10 := by
  rw [fullyGoodBaseFailureBound_toReal]
  exact fullyGoodBaseFailureBoundReal_lt_one_tenth
    r Delta hr hFive hDegree hRank hDistance hExpansion

/-- At every base scale used below, the heavy-check failure budget is already
below one quarter. -/
theorem exp_neg_r_div_ten_lt_one_fourth
    (r : Nat) (hr : 20 ≤ r) :
    Real.exp (-(r : Real) / 10) < (1 : Real) / 4 := by
  have hLogFour :
      Real.log 4 < (r : Real) / 10 := by
    rw [show (4 : Real) = 2 * 2 by norm_num, Real.log_mul
      (by norm_num : (2 : Real) ≠ 0) (by norm_num : (2 : Real) ≠ 0)]
    have hTwo := Real.log_two_lt_d9
    have hrReal : (20 : Real) ≤ r := by exact_mod_cast hr
    nlinarith
  calc
    Real.exp (-(r : Real) / 10) <
        Real.exp (-Real.log 4) := by
      apply Real.exp_lt_exp.mpr
      linarith
    _ = (1 : Real) / 4 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : Real) < 4)]
      rw [one_div]

/-- The paper-natural logarithmic light scale, the four random-base decay
loads, and `r ≥ 500` imply the exact numeric inequality required for joint
sample selection. -/
theorem hho20_joint_failure_sum_lt_one
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hr : 500 ≤ r) (hFive : 5 ∣ r)
    (hDegree :
      (14 * r : Real) * Real.exp (-(Delta : Real) / 40000) <
        1 / 100)
    (hRank :
      (3 * r : Real) * Real.exp (-(Delta : Real) / 2) <
        1 / 200)
    (hDistance :
      (4 * r : Real) *
          Real.exp (-(3 : Real) * Delta / 28) <
        1 / 200)
    (hExpansion :
      (3 * r : Real) * Real.exp (-(Delta : Real) / 1000) <
        1 / 200)
    (hLightLogScale :
      200 * (typeCount : Real) *
          Real.log (32 * r * typeCount : Nat) <
        Delta) :
    (fullyGoodBaseFailureBound r Delta).toReal +
        ((typeCount : Real) *
            ((1 +
              Real.exp
                (-(Delta : Real) / (200 * typeCount))) ^
                  (8 * r) - 1) +
          Real.exp (-(r : Real) / 10)) <
      1 := by
  have hBase :=
    fullyGoodBaseFailureBound_toReal_lt_one_tenth
      r Delta hr hFive hDegree hRank hDistance hExpansion
  have hrPos : 0 < r := by omega
  have hLight :=
    light_geometric_union_lt_half_of_exp_lt
      r Delta typeCount hrPos
      (exp_neg_delta_div_lt_inv_thirtyTwo_of_log_scale
        r Delta typeCount hrPos hLightLogScale)
  have hHeavy :=
    exp_neg_r_div_ten_lt_one_fourth r (by omega)
  linarith

/-! ## One explicit cofinal parameter hierarchy -/

/-- Circle length at hierarchy index `s`. -/
def hho20FiberLength (s : Nat) : Nat := 2 ^ s

/-- Number of twist types.  The large coefficient is the explicit spectral
constant from `TwistGraph.exists_twistSample_hasHHO20CayleySpectrum`. -/
def hho20TypeCount (s : Nat) : Nat := 40000000000 * s

/-- Sparse-base expected degree. -/
def hho20DegreeScale (s : Nat) : Nat :=
  10000000 * hho20TypeCount s * s

/-- Base aspect scale, rounded upward to a common multiple of five and the
twist-type count.  Unlike the former coarse product by the type count, this
rounding remains within a constant factor of the fiber-cell count. -/
def hho20BaseScale (s : Nat) : Nat :=
  (5 * hho20TypeCount s) *
    (hho20FiberLength s ^ 2 / (5 * hho20TypeCount s) + 1)

/-- From index `200`, the rounding modulus is already dominated by the
number of fiber cells. -/
theorem hho20_roundingModulus_le_fiberCells
    (s : Nat) (hs : 200 ≤ s) :
    5 * hho20TypeCount s ≤ hho20FiberLength s ^ 2 := by
  have hExp : 200000000000 * s ≤ 4 ^ s := by
    induction s, hs using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
        rw [pow_succ]
        calc
          200000000000 * (n + 1) ≤
              4 * (200000000000 * n) := by omega
          _ ≤ 4 * 4 ^ n := Nat.mul_le_mul_left 4 ih
          _ = 4 ^ n * 4 := by ring
  simp only [hho20TypeCount, hho20FiberLength]
  rw [show (2 ^ s) ^ 2 = 4 ^ s by rw [pow_two, ← mul_pow]; norm_num]
  convert hExp using 1 <;> ring

/-- The corrected base scale is strictly above the fiber-cell count. -/
theorem hho20_fiberCells_lt_baseScale
    (s : Nat) (hs : 20 ≤ s) :
    hho20FiberLength s ^ 2 < hho20BaseScale s := by
  unfold hho20BaseScale
  exact Nat.lt_mul_div_succ _ (by
    simp only [hho20TypeCount]
    positivity)

/-- The corrected base scale remains within a factor two of the fiber-cell
count throughout the public hierarchy. -/
theorem hho20_baseScale_le_two_fiberCells
    (s : Nat) (hs : 200 ≤ s) :
    hho20BaseScale s ≤ 2 * hho20FiberLength s ^ 2 := by
  let n := hho20FiberLength s ^ 2
  let b := 5 * hho20TypeCount s
  have hb : 0 < b := by
    dsimp [b, hho20TypeCount]
    positivity
  have hb_le_n : b ≤ n := by
    exact hho20_roundingModulus_le_fiberCells s hs
  have hfloor : b * (n / b) ≤ n := Nat.mul_div_le n b
  change b * (n / b + 1) ≤ 2 * n
  calc
    b * (n / b + 1) = b * (n / b) + b := by ring
    _ ≤ n + b := Nat.add_le_add_right hfloor b
    _ ≤ 2 * n := by omega

/-- The quadratic hierarchy degree is exponentially dominated from the
public threshold onward. -/
theorem hho20_degreeScale_le_two_fiberCells
    (s : Nat) (hs : 200 ≤ s) :
    hho20DegreeScale s ≤ 2 * hho20FiberLength s ^ 2 := by
  have hExp : 200000000000000000 * s ^ 2 ≤ 4 ^ s := by
    induction s, hs using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
        rw [pow_succ]
        calc
          200000000000000000 * (n + 1) ^ 2 ≤
              4 * (200000000000000000 * n ^ 2) := by
            have hsq : (n + 1) ^ 2 ≤ 4 * n ^ 2 := by nlinarith
            nlinarith
          _ ≤ 4 * 4 ^ n := Nat.mul_le_mul_left 4 ih
          _ = 4 ^ n * 4 := by ring
  simp only [hho20DegreeScale, hho20TypeCount, hho20FiberLength]
  rw [show (2 ^ s) ^ 2 = 4 ^ s by rw [pow_two, ← mul_pow]; norm_num]
  nlinarith

/-- `exp 100` dominates `2^100`; this is a convenient certified yardstick
for all fixed constants occurring in the parameter hierarchy. -/
theorem two_pow_hundred_lt_exp_hundred :
    (2 : Real) ^ 100 < Real.exp 100 := by
  have hTwo : (2 : Real) < Real.exp 1 := by
    have h :=
      Real.add_one_lt_exp (by norm_num : (1 : Real) ≠ 0)
    norm_num at h ⊢
    exact h
  calc
    (2 : Real) ^ 100 < (Real.exp 1) ^ 100 :=
      pow_lt_pow_left₀ hTwo (by norm_num) (by norm_num)
    _ = Real.exp 100 := by
      rw [← Real.exp_nat_mul]
      norm_num

/-- Every positive natural below `2^100` has logarithm below one hundred. -/
theorem log_nat_lt_hundred_of_lt_two_pow
    (n : Nat) (hn : 0 < n) (hBound : n < 2 ^ 100) :
    Real.log (n : Real) < 100 := by
  rw [Real.log_lt_iff_lt_exp (by exact_mod_cast hn)]
  have hBoundReal : (n : Real) < (2 : Real) ^ 100 := by
    exact_mod_cast hBound
  exact hBoundReal.trans two_pow_hundred_lt_exp_hundred

/-- Logarithm of the common `constant * s * 4^s` shape is at most linear in
`s`, with a deliberately loose constant that keeps later arithmetic robust. -/
theorem log_const_mul_s_mul_two_pow_sq_lt
    (coefficient s : Nat)
    (hCoefficient : 0 < coefficient)
    (hCoefficientSmall : coefficient < 2 ^ 100)
    (hs : 20 ≤ s) :
    Real.log
        (coefficient * s * (2 ^ s) ^ 2 : Nat) <
      8 * (s : Real) := by
  have hsPos : 0 < s := by omega
  have hLogCoefficient :
      Real.log (coefficient : Real) < 100 :=
    log_nat_lt_hundred_of_lt_two_pow
      coefficient hCoefficient hCoefficientSmall
  have hLogS :
      Real.log (s : Real) ≤ s := by
    have h :=
      Real.log_le_sub_one_of_pos
        (show (0 : Real) < s by exact_mod_cast hsPos)
    linarith
  have hLogTwo : Real.log 2 < 1 := by
    linarith [Real.log_two_lt_d9]
  have hCoefficientReal : (coefficient : Real) ≠ 0 := by positivity
  have hsReal : (s : Real) ≠ 0 := by positivity
  have hTwoReal : (2 : Real) ≠ 0 := by norm_num
  push_cast
  rw [Real.log_mul (mul_ne_zero hCoefficientReal hsReal)
      (pow_ne_zero 2 (pow_ne_zero s hTwoReal)),
    Real.log_mul hCoefficientReal hsReal,
    Real.log_pow, Real.log_pow]
  have hsRealLower : (20 : Real) ≤ s := by exact_mod_cast hs
  have hsRealPos : (0 : Real) < s := by exact_mod_cast hsPos
  have hLogTwoMul :
      (s : Real) * Real.log 2 < s :=
    by
      simpa using mul_lt_mul_of_pos_left hLogTwo hsRealPos
  have hLogTotal :
      Real.log (coefficient : Real) + Real.log (s : Real) +
          (2 : Real) * ((s : Real) * Real.log 2) <
        100 + (s : Real) + 2 * s := by
    nlinarith
  calc
    Real.log (coefficient : Real) + Real.log (s : Real) +
          (2 : Nat) * ((s : Nat) * Real.log 2) <
        100 + (s : Real) + 2 * s := hLogTotal
    _ ≤ 8 * (s : Real) := by nlinarith

/-- Variant with the two polynomial factors needed by the light-check union
bound. -/
theorem log_const_mul_s_sq_mul_two_pow_sq_lt
    (coefficient s : Nat)
    (hCoefficient : 0 < coefficient)
    (hCoefficientSmall : coefficient < 2 ^ 100)
    (hs : 20 ≤ s) :
    Real.log
        (coefficient * s ^ 2 * (2 ^ s) ^ 2 : Nat) <
      9 * (s : Real) := by
  have hsPos : 0 < s := by omega
  have hLogCoefficient :
      Real.log (coefficient : Real) < 100 :=
    log_nat_lt_hundred_of_lt_two_pow
      coefficient hCoefficient hCoefficientSmall
  have hLogS :
      Real.log (s : Real) ≤ s := by
    have h :=
      Real.log_le_sub_one_of_pos
        (show (0 : Real) < s by exact_mod_cast hsPos)
    linarith
  have hLogTwo : Real.log 2 < 1 := by
    linarith [Real.log_two_lt_d9]
  have hCoefficientReal : (coefficient : Real) ≠ 0 := by positivity
  have hsReal : (s : Real) ≠ 0 := by positivity
  have hTwoReal : (2 : Real) ≠ 0 := by norm_num
  push_cast
  rw [Real.log_mul (mul_ne_zero hCoefficientReal (pow_ne_zero 2 hsReal))
      (pow_ne_zero 2 (pow_ne_zero s hTwoReal)),
    Real.log_mul hCoefficientReal (pow_ne_zero 2 hsReal),
    Real.log_pow, Real.log_pow, Real.log_pow]
  have hsRealLower : (20 : Real) ≤ s := by exact_mod_cast hs
  have hsRealPos : (0 : Real) < s := by exact_mod_cast hsPos
  have hLogTwoMul :
      (s : Real) * Real.log 2 < s := by
    simpa using mul_lt_mul_of_pos_left hLogTwo hsRealPos
  have hLogTotal :
      Real.log (coefficient : Real) +
          (2 : Real) * Real.log (s : Real) +
          (2 : Real) * ((s : Real) * Real.log 2) <
        100 + 2 * (s : Real) + 2 * s := by
    nlinarith
  calc
    Real.log (coefficient : Real) +
          (2 : Nat) * Real.log (s : Real) +
          (2 : Nat) * ((s : Nat) * Real.log 2) <
        100 + 2 * (s : Real) + 2 * s := hLogTotal
    _ ≤ 9 * (s : Real) := by nlinarith

/-- Turning a logarithmic gap into the standard `x * exp (-y) < 1`
estimate. -/
theorem mul_exp_neg_lt_one_of_log_lt
    {x y : Real} (hx : 0 < x) (hLog : Real.log x < y) :
    x * Real.exp (-y) < 1 := by
  calc
    x * Real.exp (-y) =
        Real.exp (Real.log x) * Real.exp (-y) := by
      rw [Real.exp_log hx]
    _ = Real.exp (Real.log x - y) := by
      rw [← Real.exp_add]
      congr 1
    _ < Real.exp 0 := by
      apply Real.exp_lt_exp.mpr
      linarith
    _ = 1 := Real.exp_zero

/-- Uniform logarithmic bound for the degree-window prefactor. -/
theorem log_degree_prefactor_lt
    (s : Nat) (hs : 200 ≤ s) :
    Real.log (1400 * hho20BaseScale s : Nat) <
      8 * (s : Real) := by
  have hs20 : 20 ≤ s := by omega
  have hNat : 1400 * hho20BaseScale s ≤
      2800 * s * (2 ^ s) ^ 2 := by
    calc
      1400 * hho20BaseScale s ≤ 1400 * (2 * (2 ^ s) ^ 2) :=
        Nat.mul_le_mul_left 1400 (hho20_baseScale_le_two_fiberCells s hs)
      _ ≤ 2800 * s * (2 ^ s) ^ 2 := by
        have : 1 ≤ s := by omega
        nlinarith
  have hPos : (0 : Real) < 1400 * hho20BaseScale s := by
    simp only [hho20BaseScale, hho20TypeCount]
    positivity
  have hCast : (1400 * hho20BaseScale s : Real) ≤
      (2800 * s * (2 ^ s) ^ 2 : Nat) := by exact_mod_cast hNat
  push_cast
  exact (Real.log_le_log hPos hCast).trans_lt
    (log_const_mul_s_mul_two_pow_sq_lt
      2800 s (by norm_num) (by norm_num) hs20)

/-- Uniform logarithmic bound for the rank/expansion prefactor. -/
theorem log_six_hundred_base_prefactor_lt
    (s : Nat) (hs : 200 ≤ s) :
    Real.log (600 * hho20BaseScale s : Nat) <
      8 * (s : Real) := by
  have hs20 : 20 ≤ s := by omega
  have hNat : 600 * hho20BaseScale s ≤
      1200 * s * (2 ^ s) ^ 2 := by
    calc
      600 * hho20BaseScale s ≤ 600 * (2 * (2 ^ s) ^ 2) :=
        Nat.mul_le_mul_left 600 (hho20_baseScale_le_two_fiberCells s hs)
      _ ≤ 1200 * s * (2 ^ s) ^ 2 := by
        have : 1 ≤ s := by omega
        nlinarith
  have hPos : (0 : Real) < 600 * hho20BaseScale s := by
    simp only [hho20BaseScale, hho20TypeCount]
    positivity
  have hCast : (600 * hho20BaseScale s : Real) ≤
      (1200 * s * (2 ^ s) ^ 2 : Nat) := by exact_mod_cast hNat
  push_cast
  exact (Real.log_le_log hPos hCast).trans_lt
    (log_const_mul_s_mul_two_pow_sq_lt
      1200 s (by norm_num) (by norm_num) hs20)

/-- Uniform logarithmic bound for the distance prefactor. -/
theorem log_eight_hundred_base_prefactor_lt
    (s : Nat) (hs : 200 ≤ s) :
    Real.log (800 * hho20BaseScale s : Nat) <
      8 * (s : Real) := by
  have hs20 : 20 ≤ s := by omega
  have hNat : 800 * hho20BaseScale s ≤
      1600 * s * (2 ^ s) ^ 2 := by
    calc
      800 * hho20BaseScale s ≤ 800 * (2 * (2 ^ s) ^ 2) :=
        Nat.mul_le_mul_left 800 (hho20_baseScale_le_two_fiberCells s hs)
      _ ≤ 1600 * s * (2 ^ s) ^ 2 := by
        have : 1 ≤ s := by omega
        nlinarith
  have hPos : (0 : Real) < 800 * hho20BaseScale s := by
    simp only [hho20BaseScale, hho20TypeCount]
    positivity
  have hCast : (800 * hho20BaseScale s : Real) ≤
      (1600 * s * (2 ^ s) ^ 2 : Nat) := by exact_mod_cast hNat
  push_cast
  exact (Real.log_le_log hPos hCast).trans_lt
    (log_const_mul_s_mul_two_pow_sq_lt
      1600 s (by norm_num) (by norm_num) hs20)

/-- Uniform logarithmic bound for the complete light-check indexing set. -/
theorem log_light_prefactor_lt
    (s : Nat) (hs : 200 ≤ s) :
    Real.log
        (32 * hho20BaseScale s * hho20TypeCount s : Nat) <
      9 * (s : Real) := by
  have hs20 : 20 ≤ s := by omega
  have hNat : 32 * hho20BaseScale s * hho20TypeCount s ≤
      2560000000000 * s ^ 2 * (2 ^ s) ^ 2 := by
    calc
      32 * hho20BaseScale s * hho20TypeCount s ≤
          32 * (2 * (2 ^ s) ^ 2) * hho20TypeCount s := by
        gcongr
        exact hho20_baseScale_le_two_fiberCells s hs
      _ = 2560000000000 * s * (2 ^ s) ^ 2 := by
        simp only [hho20TypeCount]
        ring
      _ ≤ 2560000000000 * s ^ 2 * (2 ^ s) ^ 2 := by
        have hsSq : s ≤ s ^ 2 := by nlinarith
        gcongr
  have hPos : (0 : Real) <
      32 * hho20BaseScale s * hho20TypeCount s := by
    simp only [hho20BaseScale, hho20TypeCount]
    positivity
  have hCast : (32 * hho20BaseScale s * hho20TypeCount s : Real) ≤
      (2560000000000 * s ^ 2 * (2 ^ s) ^ 2 : Nat) := by
    exact_mod_cast hNat
  push_cast
  exact (Real.log_le_log hPos hCast).trans_lt
    (log_const_mul_s_sq_mul_two_pow_sq_lt
      2560000000000 s (by norm_num) (by norm_num) hs20)

/-- The degree-window contribution of the explicit hierarchy is below one
percent. -/
theorem hho20_degree_decay_lt
    (s : Nat) (hs : 200 ≤ s) :
    (14 * hho20BaseScale s : Real) *
        Real.exp (-(hho20DegreeScale s : Real) / 40000) <
      1 / 100 := by
  have hLog :
      Real.log (1400 * hho20BaseScale s : Nat) <
        (hho20DegreeScale s : Real) / 40000 := by
    calc
      Real.log (1400 * hho20BaseScale s : Nat) <
          8 * (s : Real) := log_degree_prefactor_lt s hs
      _ < (hho20DegreeScale s : Real) / 40000 := by
        simp only [hho20DegreeScale, hho20TypeCount]
        push_cast
        have hsPos : (0 : Real) < s := by
          exact_mod_cast (show 0 < s by omega)
        ring_nf
        have hsOne : (1 : Real) ≤ s := by
          exact_mod_cast (show 1 ≤ s by omega)
        have hsSq : (s : Real) ≤ s ^ 2 := by
          have := mul_nonneg hsPos.le (sub_nonneg.mpr hsOne)
          nlinarith
        nlinarith
  have hPositive :
      (0 : Real) < 1400 * hho20BaseScale s := by
    simp only [hho20BaseScale, hho20TypeCount, hho20FiberLength]
    positivity
  have hSmall :=
    mul_exp_neg_lt_one_of_log_lt hPositive (by
      push_cast at hLog
      exact hLog)
  norm_num at hSmall ⊢
  ring_nf at hSmall ⊢
  nlinarith [Real.exp_pos
    (-(hho20DegreeScale s : Real) / 40000)]

/-- The small-support rank contribution of the explicit hierarchy is below
one half percent. -/
theorem hho20_rank_decay_lt
    (s : Nat) (hs : 200 ≤ s) :
    (3 * hho20BaseScale s : Real) *
        Real.exp (-(hho20DegreeScale s : Real) / 2) <
      1 / 200 := by
  have hLog :
      Real.log (600 * hho20BaseScale s : Nat) <
        (hho20DegreeScale s : Real) / 2 := by
    calc
      Real.log (600 * hho20BaseScale s : Nat) <
          8 * (s : Real) :=
        log_six_hundred_base_prefactor_lt s hs
      _ < (hho20DegreeScale s : Real) / 2 := by
        simp only [hho20DegreeScale, hho20TypeCount]
        push_cast
        have hsPos : (0 : Real) < s := by
          exact_mod_cast (show 0 < s by omega)
        ring_nf
        have hsOne : (1 : Real) ≤ s := by
          exact_mod_cast (show 1 ≤ s by omega)
        have hsSq : (s : Real) ≤ s ^ 2 := by
          have := mul_nonneg hsPos.le (sub_nonneg.mpr hsOne)
          nlinarith
        nlinarith
  have hPositive :
      (0 : Real) < 600 * hho20BaseScale s := by
    simp only [hho20BaseScale, hho20TypeCount, hho20FiberLength]
    positivity
  have hSmall :=
    mul_exp_neg_lt_one_of_log_lt hPositive (by
      push_cast at hLog
      exact hLog)
  norm_num at hSmall ⊢
  ring_nf at hSmall ⊢
  nlinarith [Real.exp_pos
    (-(hho20DegreeScale s : Real) / 2)]

/-- The small-support distance contribution of the explicit hierarchy is
below one half percent. -/
theorem hho20_distance_decay_lt
    (s : Nat) (hs : 200 ≤ s) :
    (4 * hho20BaseScale s : Real) *
        Real.exp
          (-(3 : Real) * hho20DegreeScale s / 28) <
      1 / 200 := by
  have hLog :
      Real.log (800 * hho20BaseScale s : Nat) <
        (3 : Real) * hho20DegreeScale s / 28 := by
    calc
      Real.log (800 * hho20BaseScale s : Nat) <
          8 * (s : Real) :=
        log_eight_hundred_base_prefactor_lt s hs
      _ < (3 : Real) * hho20DegreeScale s / 28 := by
        simp only [hho20DegreeScale, hho20TypeCount]
        push_cast
        have hsPos : (0 : Real) < s := by
          exact_mod_cast (show 0 < s by omega)
        ring_nf
        have hsOne : (1 : Real) ≤ s := by
          exact_mod_cast (show 1 ≤ s by omega)
        have hsSq : (s : Real) ≤ s ^ 2 := by
          have := mul_nonneg hsPos.le (sub_nonneg.mpr hsOne)
          nlinarith
        nlinarith
  have hPositive :
      (0 : Real) < 800 * hho20BaseScale s := by
    simp only [hho20BaseScale, hho20TypeCount, hho20FiberLength]
    positivity
  have hSmall :=
    mul_exp_neg_lt_one_of_log_lt hPositive (by
      push_cast at hLog
      exact hLog)
  norm_num at hSmall ⊢
  ring_nf at hSmall ⊢
  nlinarith [Real.exp_pos
    (-(3 : Real) * hho20DegreeScale s / 28)]

/-- The strong-expansion contribution of the explicit hierarchy is below one
half percent. -/
theorem hho20_expansion_decay_lt
    (s : Nat) (hs : 200 ≤ s) :
    (3 * hho20BaseScale s : Real) *
        Real.exp (-(hho20DegreeScale s : Real) / 1000) <
      1 / 200 := by
  have hLog :
      Real.log (600 * hho20BaseScale s : Nat) <
        (hho20DegreeScale s : Real) / 1000 := by
    calc
      Real.log (600 * hho20BaseScale s : Nat) <
          8 * (s : Real) :=
        log_six_hundred_base_prefactor_lt s hs
      _ < (hho20DegreeScale s : Real) / 1000 := by
        simp only [hho20DegreeScale, hho20TypeCount]
        push_cast
        have hsPos : (0 : Real) < s := by
          exact_mod_cast (show 0 < s by omega)
        ring_nf
        have hsOne : (1 : Real) ≤ s := by
          exact_mod_cast (show 1 ≤ s by omega)
        have hsSq : (s : Real) ≤ s ^ 2 := by
          have := mul_nonneg hsPos.le (sub_nonneg.mpr hsOne)
          nlinarith
        nlinarith
  have hPositive :
      (0 : Real) < 600 * hho20BaseScale s := by
    simp only [hho20BaseScale, hho20TypeCount, hho20FiberLength]
    positivity
  have hSmall :=
    mul_exp_neg_lt_one_of_log_lt hPositive (by
      push_cast at hLog
      exact hLog)
  norm_num at hSmall ⊢
  ring_nf at hSmall ⊢
  nlinarith [Real.exp_pos
    (-(hho20DegreeScale s : Real) / 1000)]

/-- The explicit hierarchy satisfies the strengthened light-check logarithmic
scale. -/
theorem hho20_light_log_scale
    (s : Nat) (hs : 200 ≤ s) :
    200 * (hho20TypeCount s : Real) *
        Real.log
          (32 * hho20BaseScale s * hho20TypeCount s : Nat) <
      hho20DegreeScale s := by
  have hLog := log_light_prefactor_lt s hs
  have hsPos : (0 : Real) < s := by
    exact_mod_cast (show 0 < s by omega)
  have hTypePos : (0 : Real) < hho20TypeCount s := by
    simp only [hho20TypeCount]
    positivity
  have hScaled :
      200 * (hho20TypeCount s : Real) *
          Real.log
            (32 * hho20BaseScale s * hho20TypeCount s : Nat) <
        200 * (hho20TypeCount s : Real) * (9 * s) := by
    exact mul_lt_mul_of_pos_left hLog
      (mul_pos (by norm_num) hTypePos)
  refine hScaled.trans ?_
  simp only [hho20DegreeScale, hho20TypeCount]
  push_cast
  ring_nf
  nlinarith [sq_pos_of_pos hsPos]

/-- Elementary exponential domination used to keep the expected degree below
half the base size. -/
theorem million_mul_le_four_pow
    (s : Nat) (hs : 20 ≤ s) :
    1000000 * s ≤ 4 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      rw [pow_succ]
      calc
        1000000 * (n + 1) ≤ 4 * (1000000 * n) := by omega
        _ ≤ 4 * 4 ^ n := Nat.mul_le_mul_left 4 ih
        _ = 4 ^ n * 4 := by ring

/-- The hierarchy's base scale is positive and already exceeds all fixed
finite thresholds used by the probability argument. -/
theorem hho20_baseScale_ge_five_hundred
    (s : Nat) (hs : 200 ≤ s) :
    500 ≤ hho20BaseScale s := by
  have hPow : 2 ^ 20 ≤ 2 ^ s :=
    pow_le_pow_right₀ (by norm_num : (1 : Nat) ≤ 2) (by omega)
  have hlt := hho20_fiberCells_lt_baseScale s (by omega)
  simp only [hho20FiberLength] at hlt
  norm_num at hPow
  nlinarith

/-- The expected degree is at most half the base-variable count. -/
theorem hho20_degreeScale_le_two_baseScale
    (s : Nat) (hs : 200 ≤ s) :
    hho20DegreeScale s ≤ 2 * hho20BaseScale s := by
  exact (hho20_degreeScale_le_two_fiberCells s hs).trans
    (Nat.mul_le_mul_left 2
      (Nat.le_of_lt (hho20_fiberCells_lt_baseScale s (by omega))))

/-- The type count divides every check row count `3r`. -/
theorem hho20_typeCount_dvd_three_baseScale
    (s : Nat) :
    hho20TypeCount s ∣ 3 * hho20BaseScale s := by
  refine ⟨15 *
    (hho20FiberLength s ^ 2 / (5 * hho20TypeCount s) + 1), ?_⟩
  simp only [hho20BaseScale]
  ring

/-- The base scale is a multiple of five, as used to group the distance
tail. -/
theorem five_dvd_hho20BaseScale (s : Nat) :
    5 ∣ hho20BaseScale s := by
  refine ⟨hho20TypeCount s *
    (hho20FiberLength s ^ 2 / (5 * hho20TypeCount s) + 1), ?_⟩
  simp only [hho20BaseScale]
  ring

/-- The type count is nonzero throughout the cofinal hierarchy. -/
theorem hho20TypeCount_ne_zero
    (s : Nat) (hs : 20 ≤ s) :
    hho20TypeCount s ≠ 0 := by
  simp only [hho20TypeCount]
  positivity

/-- The hierarchy satisfies the heavy-check counting scale. -/
theorem hho20_log_degreeScale_lt
    (s : Nat) (hs : 20 ≤ s) :
    Real.log (hho20DegreeScale s : Real) <
      9 * (s : Real) := by
  have hLarge :=
    log_const_mul_s_sq_mul_two_pow_sq_lt
      400000000000000000 s (by norm_num) (by norm_num) hs
  have hsPos : 0 < s := by omega
  have hDegreePos : (0 : Real) < hho20DegreeScale s := by
    simp only [hho20DegreeScale, hho20TypeCount]
    positivity
  have hLe :
      (hho20DegreeScale s : Real) ≤
        (400000000000000000 * s ^ 2 * (2 ^ s) ^ 2 : Nat) := by
    exact_mod_cast (show
      hho20DegreeScale s ≤
        400000000000000000 * s ^ 2 * (2 ^ s) ^ 2 by
      simp only [hho20DegreeScale, hho20TypeCount]
      have hTwoPower : 1 ≤ 2 ^ s :=
        one_le_pow₀ (by norm_num : (1 : Nat) ≤ 2)
      have hOne : 1 ≤ (2 ^ s) ^ 2 := one_le_pow₀ hTwoPower
      nlinarith)
  exact (Real.log_le_log hDegreePos hLe).trans_lt hLarge

/-- The deterministic heavy-word enumeration budget is dominated by
`Delta`. -/
theorem hho20_heavy_scale
    (s : Nat) (hs : 20 ≤ s) :
    (100 : Real) * hho20TypeCount s *
        (1 + 2 * Real.log (hho20DegreeScale s)) ≤
      hho20DegreeScale s := by
  have hLog := hho20_log_degreeScale_lt s hs
  have hsPos : (0 : Real) < s := by
    exact_mod_cast (show 0 < s by omega)
  have hTypePos : (0 : Real) < hho20TypeCount s := by
    simp only [hho20TypeCount]
    positivity
  calc
    (100 : Real) * hho20TypeCount s *
          (1 + 2 * Real.log (hho20DegreeScale s)) ≤
        100 * hho20TypeCount s * (1 + 2 * (9 * s)) := by
      gcongr
    _ ≤ hho20DegreeScale s := by
      simp only [hho20DegreeScale, hho20TypeCount]
      push_cast
      ring_nf
      have hsOne : (1 : Real) ≤ s := by
        exact_mod_cast (show 1 ≤ s by omega)
      nlinarith [sq_pos_of_pos hsPos]

/-- The fiber is well past the explicit spectral threshold. -/
theorem hho20_fiberLength_ge
    (s : Nat) (hs : 20 ≤ s) :
    100001 ≤ hho20FiberLength s := by
  have hPow :
      2 ^ 20 ≤ 2 ^ s :=
    pow_le_pow_right₀ (by norm_num : (1 : Nat) ≤ 2) hs
  norm_num [hho20FiberLength] at hPow ⊢
  omega

/-- The twist type count meets the random-Cayley spectral budget. -/
theorem hho20_typeCount_spectrum
    (s : Nat) (hs : 20 ≤ s) :
    (40000000000 : Real) *
        Real.log (hho20FiberLength s : Real) ≤
      hho20TypeCount s := by
  have hsPos : (0 : Real) < s := by
    exact_mod_cast (show 0 < s by omega)
  have hLogTwo : Real.log 2 ≤ 1 := by
    linarith [Real.log_two_lt_d9]
  have hLogFiber :
      Real.log (hho20FiberLength s : Real) ≤ s := by
    simp only [hho20FiberLength]
    push_cast
    rw [Real.log_pow]
    simpa using mul_le_mul_of_nonneg_left hLogTwo hsPos.le
  simp only [hho20TypeCount]
  push_cast
  nlinarith

/-- Type enumeration is negligible compared with the base scale. -/
theorem hho20_typeCount_small
    (s : Nat) (hs : 200 ≤ s) :
    (100 : Real) * hho20TypeCount s ≤
      hho20BaseScale s := by
  have hDegree := hho20_degreeScale_le_two_fiberCells s hs
  have hLow : 200 * hho20TypeCount s ≤ hho20DegreeScale s := by
    simp only [hho20DegreeScale]
    have : 1 ≤ s := by omega
    nlinarith
  have hFiber : 100 * hho20TypeCount s ≤ hho20FiberLength s ^ 2 := by
    omega
  have hBase := Nat.le_of_lt (hho20_fiberCells_lt_baseScale s (by omega))
  exact_mod_cast hFiber.trans hBase

/-- All four random-base estimates and both partition estimates fit inside
the unit probability budget for the explicit hierarchy. -/
theorem hho20_hierarchy_joint_failure_sum_lt_one
    (s : Nat) (hs : 200 ≤ s) :
    letI : NeZero (hho20TypeCount s) :=
      ⟨hho20TypeCount_ne_zero s (by omega)⟩
    (fullyGoodBaseFailureBound
        (hho20BaseScale s) (hho20DegreeScale s)).toReal +
        ((hho20TypeCount s : Real) *
            ((1 +
              Real.exp
                (-(hho20DegreeScale s : Real) /
                  (200 * hho20TypeCount s))) ^
                    (8 * hho20BaseScale s) - 1) +
          Real.exp (-(hho20BaseScale s : Real) / 10)) <
      1 := by
  letI : NeZero (hho20TypeCount s) :=
    ⟨hho20TypeCount_ne_zero s (by omega)⟩
  exact hho20_joint_failure_sum_lt_one
    (hho20BaseScale s) (hho20DegreeScale s)
    (hho20TypeCount s)
    (hho20_baseScale_ge_five_hundred s hs)
    (five_dvd_hho20BaseScale s)
    (hho20_degree_decay_lt s hs)
    (hho20_rank_decay_lt s hs)
    (hho20_distance_decay_lt s hs)
    (hho20_expansion_decay_lt s hs)
    (hho20_light_log_scale s hs)

/-- Assumption-free finite HHO20 construction at every hierarchy index
`s ≥ 200`.  The witnesses simultaneously satisfy all random-base properties,
partitioned light/heavy checks, the Cayley spectrum event, and local
testability. -/
theorem exists_hho20_base_and_twist_at
    (s : Nat) (hs : 200 ≤ s) :
    letI : NeZero (hho20BaseScale s) :=
      ⟨by
        have := hho20_baseScale_ge_five_hundred s hs
        omega⟩
    letI : NeZero (hho20TypeCount s) :=
      ⟨hho20TypeCount_ne_zero s (by omega)⟩
    letI : NeZero (hho20FiberLength s) :=
      ⟨by
        have := hho20_fiberLength_ge s (by omega)
        omega⟩
    letI : NeZero (hho20FiberLength s - 1) :=
      ⟨by
        have := hho20_fiberLength_ge s (by omega)
        omega⟩
    ∃ (baseSample : RandomBase.Sample (hho20BaseScale s))
        (twistSample :
          RandomTwist.Sample (hho20BaseScale s)
            (hho20TypeCount s) (hho20FiberLength s)),
      RandomBase.IsFullyGood
          (Delta := hho20DegreeScale s) baseSample ∧
        TwistGraph.HasHHO20PartitionedChecks
          (hho20DegreeScale s) baseSample twistSample ∧
        TwistGraph.HasHHO20CayleySpectrum twistSample ∧
        TwistGraph.HasHHO20LocalTestability
          (hho20DegreeScale s) baseSample twistSample := by
  letI : NeZero (hho20BaseScale s) :=
    ⟨by
      have := hho20_baseScale_ge_five_hundred s hs
      omega⟩
  letI : NeZero (hho20TypeCount s) :=
    ⟨hho20TypeCount_ne_zero s (by omega)⟩
  letI : NeZero (hho20FiberLength s) :=
    ⟨by
      have := hho20_fiberLength_ge s (by omega)
      omega⟩
  letI : NeZero (hho20FiberLength s - 1) :=
    ⟨by
      have := hho20_fiberLength_ge s (by omega)
      omega⟩
  apply exists_fullyGood_hho20_base_and_twist
  · have := hho20_baseScale_ge_five_hundred s hs
    omega
  · exact hho20_degreeScale_le_two_baseScale s hs
  · simp only [hho20DegreeScale]
    calc
      40 ≤ 10000000 := by norm_num
      _ ≤ 10000000 * hho20TypeCount s :=
        Nat.le_mul_of_pos_right _ (by
          exact Nat.pos_of_ne_zero (hho20TypeCount_ne_zero s (by omega)))
      _ ≤ 10000000 * hho20TypeCount s * s :=
        Nat.le_mul_of_pos_right _ (by omega)
  · exact hho20_typeCount_dvd_three_baseScale s
  · simp only [hho20DegreeScale, hho20TypeCount]
    have hsPos : 0 < s := by omega
    positivity
  · exact Nat.one_le_iff_ne_zero.mpr (by
      simp only [hho20DegreeScale, hho20TypeCount]
      positivity)
  · exact hho20_typeCount_small s hs
  · exact hho20_heavy_scale s (by omega)
  · exact hho20_fiberLength_ge s (by omega)
  · exact hho20_typeCount_spectrum s (by omega)
  · exact hho20_hierarchy_joint_failure_sum_lt_one s hs

end QEC.Coding.FiberBundle.RandomPartition
