import QEC.Coding.FiberBundle.ExplicitFamily.DistanceBalancingLocality
import QEC.Coding.FiberBundle.ExplicitFamily.InitialLocality
import QEC.Coding.QLDPC.SourceValidity
/-!
# Explicit asymptotics of the final HHO20 family

The source corollary suppresses polylogarithmic factors.  Here the hierarchy
index `s` is an explicit logarithmic scale: its fiber length is `2^s`.  We
therefore certify the `3/5` exponent without real roots or informal asymptotic
notation by proving fifth-power inequalities against the cube of blocklength.
-/

namespace QEC.Coding.FiberBundle.HHO20DistanceBalancing

open QEC.Coding

universe u

/-- Coefficient in the exact identity `Delta(s) = A s^2`. -/
def degreeCoefficient : Nat := 10000000 * 40000000000

/-- Family-independent coefficient in the corrected blocklength envelope. -/
def blocklengthCoefficient : Nat :=
  2611456 * 16 * degreeCoefficient ^ 2

/-- One denominator large enough for both final CSS distance sectors. -/
def distanceCoefficient : Nat :=
  100000 * 101 * (4 * degreeCoefficient) ^ 2

/-- Explicit upper scale for the final number of qubits. -/
def blocklengthScaleAt (s : Nat) : Nat :=
  blocklengthCoefficient * s ^ 4 *
    RandomPartition.hho20FiberLength s ^ 10

/-- Explicit lower scale for the number of encoded qubits. -/
def dimensionScaleAt (s : Nat) : Nat :=
  RandomPartition.hho20FiberLength s ^ 6

/-- A single explicit lower scale shared by homological and cohomological
distance.  Its floor is harmless from hierarchy index `200` onward. -/
def distanceScaleAt (s : Nat) : Nat :=
  (RandomPartition.hho20FiberLength s ^ 2 / 2) *
    (RandomPartition.hho20FiberLength s ^ 4 /
      (distanceCoefficient * s ^ 4))

/-- Coefficient in `N^3 ≤ poly(s) K^5`. -/
def dimensionTradeoffCoefficient : Nat := blocklengthCoefficient ^ 3

/-- Coefficient in `N^3 ≤ poly(s) D^5`. -/
def distanceTradeoffCoefficient : Nat :=
  blocklengthCoefficient ^ 3 * (8 * distanceCoefficient) ^ 5

/-- Exact scales for the unreduced fiber-bundle member at hierarchy index
`s`.  They use the same rounded base scale as the later transformations. -/
def initialBlocklengthAt (s : Nat) : Nat :=
  7 * RandomPartition.hho20BaseScale s *
    RandomPartition.hho20FiberLength s ^ 2

def initialDimensionAt (s : Nat) : Nat :=
  RandomPartition.hho20BaseScale s

def initialXDistanceScaleAt (s : Nat) : Nat :=
  RandomPartition.hho20FiberLength s ^ 2 /
    (100000 * RandomPartition.hho20DegreeScale s)

def initialZDistanceScaleAt (s : Nat) : Nat :=
  RandomPartition.hho20FiberLength s ^ 3 /
    (5000 * RandomPartition.hho20DegreeScale s)

def initialLocalityScaleAt (s : Nat) : Nat :=
  101 * RandomPartition.hho20DegreeScale s + 2

/-- Polynomial coefficients for the unreduced `d_X` and `d_Z` claims. -/
def initialXTradeoffCoefficient : Nat :=
  56 * (100000 * degreeCoefficient) ^ 2

def initialZTradeoffCoefficient : Nat :=
  14 ^ 3 * 16 * (5000 * degreeCoefficient) ^ 4

theorem hho20FiberLength_two_mul (s : Nat) :
    RandomPartition.hho20FiberLength (2 * s) =
      RandomPartition.hho20FiberLength s ^ 2 := by
  unfold RandomPartition.hho20FiberLength
  rw [show 2 * s = s * 2 by omega, pow_mul]

/-- Exact degree formula for the explicit hierarchy. -/
theorem hho20DegreeScale_eq (s : Nat) :
    RandomPartition.hho20DegreeScale s = degreeCoefficient * s ^ 2 := by
  simp only [RandomPartition.hho20DegreeScale,
    RandomPartition.hho20TypeCount, degreeCoefficient]
  ring

/-- The corrected hierarchy blocklength is polynomial times `2^(10s)`. -/
theorem balancedBlocklengthUpperAt_le_scale
    (s : Nat) (hs : 200 ≤ s) :
    balancedBlocklengthUpperAt s ≤ blocklengthScaleAt s := by
  have hMain := RandomPartition.hho20_baseScale_le_two_fiberCells
    (2 * s) (by omega)
  have hBalance := RandomPartition.hho20_baseScale_le_two_fiberCells s hs
  calc
    balancedBlocklengthUpperAt s ≤
        2611456 *
          (2 * RandomPartition.hho20FiberLength (2 * s) ^ 2) *
          RandomPartition.hho20DegreeScale (2 * s) *
          (RandomPartition.hho20FiberLength (2 * s) *
            RandomPartition.hho20FiberLength (2 * s)) *
          (2 * RandomPartition.hho20FiberLength s ^ 2) *
          RandomPartition.hho20DegreeScale s := by
      unfold balancedBlocklengthUpperAt
      gcongr
    _ = blocklengthScaleAt s := by
      rw [hho20FiberLength_two_mul, hho20DegreeScale_eq,
        hho20DegreeScale_eq]
      simp only [blocklengthScaleAt, blocklengthCoefficient,
        degreeCoefficient]
      ring

/-- The product of the two construction dimensions contains `2^(6s)`. -/
theorem dimensionScale_le_baseScale_product
    (s : Nat) (hs : 200 ≤ s) :
    dimensionScaleAt s ≤
      RandomPartition.hho20BaseScale (2 * s) *
        RandomPartition.hho20BaseScale s := by
  have hMain := Nat.le_of_lt
    (RandomPartition.hho20_fiberCells_lt_baseScale (2 * s) (by omega))
  have hBalance := Nat.le_of_lt
    (RandomPartition.hho20_fiberCells_lt_baseScale s (by omega))
  simp only [dimensionScaleAt]
  rw [hho20FiberLength_two_mul] at hMain
  calc
    RandomPartition.hho20FiberLength s ^ 6 =
        (RandomPartition.hho20FiberLength s ^ 2) ^ 2 *
          RandomPartition.hho20FiberLength s ^ 2 := by ring
    _ ≤ RandomPartition.hho20BaseScale (2 * s) *
          RandomPartition.hho20BaseScale s :=
      Nat.mul_le_mul hMain hBalance

/-- The cohomological final distance contains the common corrected scale. -/
theorem distanceScaleAt_le_cohomology
    (s : Nat) (hs : 200 ≤ s) :
    distanceScaleAt s ≤ balancedCohomologyDistanceAt s := by
  let q := RandomPartition.hho20FiberLength s
  let Delta := RandomPartition.hho20DegreeScale (2 * s)
  let d := distanceCoefficient * s ^ 4
  let dc := 5000 * 101 * (4 * degreeCoefficient) ^ 2 * s ^ 4
  have hd : 0 < d := by
    dsimp [d, distanceCoefficient, degreeCoefficient]
    positivity
  have hdc : 0 < dc := by
    dsimp [dc, degreeCoefficient]
    positivity
  have hMulDiv : (q ^ 2 / 2) * (q ^ 4 / d) ≤ q ^ 6 / d := by
    apply (Nat.le_div_iff_mul_le hd).2
    calc
      (q ^ 2 / 2) * (q ^ 4 / d) * d =
          (q ^ 2 / 2) * ((q ^ 4 / d) * d) := by ring
      _ ≤ q ^ 2 * ((q ^ 4 / d) * d) :=
        Nat.mul_le_mul_right _ (Nat.div_le_self _ _)
      _ ≤ q ^ 2 * q ^ 4 :=
        Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
      _ = q ^ 6 := by ring
  have hDen : dc ≤ d := by
    dsimp [dc, d, distanceCoefficient]
    gcongr
    norm_num
  have hRaw : q ^ 6 / dc ≤ balancedCohomologyDistanceAt s := by
    have hMain := Nat.le_of_lt
      (RandomPartition.hho20_fiberCells_lt_baseScale (2 * s) (by omega))
    rw [hho20FiberLength_two_mul] at hMain
    unfold balancedCohomologyDistanceAt mainReducedHomologyDistance
    rw [Nat.div_div_eq_div_mul]
    have hNum : q ^ 6 ≤
        RandomPartition.hho20FiberLength (2 * s) *
          (4 * RandomPartition.hho20BaseScale (2 * s)) := by
      rw [hho20FiberLength_two_mul]
      nlinarith
    have hDcEq : dc = 5000 * Delta * (101 * Delta) := by
      dsimp [dc, Delta]
      rw [hho20DegreeScale_eq]
      ring
    rw [hDcEq]
    exact Nat.div_le_div_right hNum
  change (q ^ 2 / 2) * (q ^ 4 / d) ≤ _
  exact hMulDiv.trans ((Nat.div_le_div_left hDen hdc).trans hRaw)

/-- The homological final distance contains the same common scale. -/
theorem distanceScaleAt_le_homology
    (s : Nat) (hs : 200 ≤ s) :
    distanceScaleAt s ≤ balancedHomologyDistanceAt s := by
  let q := RandomPartition.hho20FiberLength s
  let Delta := RandomPartition.hho20DegreeScale (2 * s)
  let d1 := 100000 * Delta
  let d2 := 101 * Delta
  have hd1 : 0 < d1 := by
    dsimp [d1, Delta, RandomPartition.hho20DegreeScale,
      RandomPartition.hho20TypeCount]
    positivity
  have hBranchOne : q ^ 4 / d1 ≤ q ^ 4 / 2 := by
    apply Nat.div_le_div_left
    · have hDelta : 1 ≤ Delta := by
        have hDeltaPos : 0 < Delta := by
          dsimp [Delta, RandomPartition.hho20DegreeScale,
            RandomPartition.hho20TypeCount]
          positivity
        omega
      dsimp [d1]
      omega
    · norm_num
  have hMain := Nat.le_of_lt
    (RandomPartition.hho20_fiberCells_lt_baseScale (2 * s) (by omega))
  rw [hho20FiberLength_two_mul] at hMain
  have hBranchTwo : q ^ 4 / d1 ≤
      (6 * RandomPartition.hho20BaseScale (2 * s)) / d1 := by
    exact Nat.div_le_div_right (by nlinarith)
  have hInner : q ^ 4 / (d1 * d2) ≤
      (min (RandomPartition.hho20FiberLength (2 * s) ^ 2 / 2)
        ((6 * RandomPartition.hho20BaseScale (2 * s)) /
          (100000 * Delta))) / (101 * Delta) := by
    change q ^ 4 / (d1 * d2) ≤
      min ((RandomPartition.hho20FiberLength (2 * s)) ^ 2 / 2)
        ((6 * RandomPartition.hho20BaseScale (2 * s)) / d1) / d2
    rw [hho20FiberLength_two_mul]
    rw [← Nat.div_div_eq_div_mul]
    dsimp [q] at hBranchOne hBranchTwo
    exact Nat.div_le_div_right ((Nat.le_min).2
      ⟨by
          convert hBranchOne using 1 <;> ring,
        hBranchTwo⟩)
  have hDen : distanceCoefficient * s ^ 4 = d1 * d2 := by
    dsimp [distanceCoefficient, d1, d2, Delta]
    rw [hho20DegreeScale_eq]
    ring
  have hBalance := Nat.le_of_lt
    (RandomPartition.hho20_fiberCells_lt_baseScale s (by omega))
  have hFactor : q ^ 2 / 2 ≤
      (4 * RandomPartition.hho20BaseScale s) / 5 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 5)).2
    have hHalf := Nat.div_mul_le_self (q ^ 2) 2
    nlinarith
  change (q ^ 2 / 2) *
      (q ^ 4 / (distanceCoefficient * s ^ 4)) ≤ _
  unfold balancedHomologyDistanceAt mainReducedCohomologyDistance
  rw [hDen]
  simpa only [pow_two] using Nat.mul_le_mul hFactor hInner

theorem nat_le_two_pow (s : Nat) : s ≤ 2 ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
      rw [pow_succ]
      have hpow : 0 < 2 ^ s := by positivity
      omega

theorem distanceCoefficient_le_two_pow_two_hundred :
    distanceCoefficient ≤ 2 ^ 200 := by
  norm_num [distanceCoefficient, degreeCoefficient]

/-- Past the small finite prefix, the hierarchy exponential dominates the
square of its logarithmic index. -/
theorem sq_le_two_pow (s : Nat) (hs : 4 ≤ s) : s ^ 2 ≤ 2 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      rw [pow_succ]
      have hStep : (n + 1) ^ 2 ≤ 2 * n ^ 2 := by nlinarith
      calc
        (n + 1) ^ 2 ≤ 2 * n ^ 2 := hStep
        _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) := by simp only [pow_succ]; ring

/-- A quotient loses at most a factor two once its denominator fits in its
numerator. -/
theorem le_two_mul_mul_div
    (a d : Nat) (hd : 0 < d) (hda : d ≤ a) :
    a ≤ 2 * d * (a / d) := by
  have hq : 1 ≤ a / d := by
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.div_pos hda hd))
  have hmod : a % d ≤ d := (Nat.mod_lt a hd).le
  calc
    a = d * (a / d) + a % d := (Nat.div_add_mod a d).symm
    _ ≤ d * (a / d) + d := Nat.add_le_add_left hmod _
    _ ≤ d * (a / d) + d * (a / d) := by
      exact Nat.add_le_add_left
        (show d ≤ d * (a / d) by
          simpa only [mul_one] using Nat.mul_le_mul_left d hq) _
    _ = 2 * d * (a / d) := by ring

/-- From hierarchy index `200`, the common distance floor is positive and
still carries the full `2^(6s)/poly(s)` scale. -/
theorem fiberLength_pow_six_le_distanceScale
    (s : Nat) (hs : 200 ≤ s) :
    RandomPartition.hho20FiberLength s ^ 6 ≤
      8 * distanceCoefficient * s ^ 4 * distanceScaleAt s := by
  let q := RandomPartition.hho20FiberLength s
  let d := distanceCoefficient * s ^ 4
  have hCoeff : distanceCoefficient ≤ q := by
    calc
      distanceCoefficient ≤ 2 ^ 200 :=
        distanceCoefficient_le_two_pow_two_hundred
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
      _ = q := by rfl
  have hsSqQ : s ^ 2 ≤ q := by
    simpa only [q, RandomPartition.hho20FiberLength] using
      sq_le_two_pow s (by omega)
  have hdq : d ≤ q ^ 4 := by
    dsimp [d]
    calc
      distanceCoefficient * s ^ 4 =
          distanceCoefficient * (s ^ 2) ^ 2 := by ring
      _ ≤ q * q ^ 2 := Nat.mul_le_mul hCoeff
        (pow_le_pow_left' hsSqQ 2)
      _ ≤ q ^ 4 := by
        have hq : 1 ≤ q := by
          have hLarge := RandomPartition.hho20_fiberLength_ge s (by omega)
          dsimp [q]
          omega
        calc
          q * q ^ 2 = q ^ 3 * 1 := by ring
          _ ≤ q ^ 3 * q := Nat.mul_le_mul_left _ hq
          _ = q ^ 4 := by ring
  have hd : 0 < d := by
    have hsPos : 0 < s := by omega
    dsimp [d, distanceCoefficient, degreeCoefficient]
    positivity
  have hFloor := le_two_mul_mul_div (q ^ 4) d hd hdq
  have hqTwo : 2 ≤ q ^ 2 := by
    have hLarge := RandomPartition.hho20_fiberLength_ge s (by omega)
    dsimp [q]
    nlinarith
  have hHalf := le_two_mul_mul_div (q ^ 2) 2 (by norm_num) hqTwo
  change q ^ 6 ≤ 8 * distanceCoefficient * s ^ 4 *
    ((q ^ 2 / 2) * (q ^ 4 / d))
  calc
    q ^ 6 = q ^ 2 * q ^ 4 := by ring
    _ ≤ (2 * 2 * (q ^ 2 / 2)) *
          (2 * d * (q ^ 4 / d)) := Nat.mul_le_mul hHalf hFloor
    _ = 8 * distanceCoefficient * s ^ 4 *
        ((q ^ 2 / 2) * (q ^ 4 / d)) := by
      dsimp [d]
      ring

theorem initialDenominatorCoefficient_le_two_pow_two_hundred :
    100000 * degreeCoefficient ≤ 2 ^ 200 := by
  norm_num [degreeCoefficient]

theorem initialDenominatorAt_le_fiber_sq
    (s : Nat) (hs : 200 ≤ s) :
    100000 * RandomPartition.hho20DegreeScale s ≤
      RandomPartition.hho20FiberLength s ^ 2 := by
  let q := RandomPartition.hho20FiberLength s
  have hCoeff : 100000 * degreeCoefficient ≤ q := by
    calc
      100000 * degreeCoefficient ≤ 2 ^ 200 :=
        initialDenominatorCoefficient_le_two_pow_two_hundred
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
      _ = q := by rfl
  have hsSqQ : s ^ 2 ≤ q := by
    simpa only [q, RandomPartition.hho20FiberLength] using
      sq_le_two_pow s (by omega)
  rw [hho20DegreeScale_eq]
  change 100000 * (degreeCoefficient * s ^ 2) ≤ q ^ 2
  calc
    100000 * (degreeCoefficient * s ^ 2) =
        (100000 * degreeCoefficient) * s ^ 2 := by ring
    _ ≤ q * q := Nat.mul_le_mul hCoeff hsSqQ
    _ = q ^ 2 := by ring

/-- The explicit unreduced X-distance scale lies below the source's two
cohomological alternatives. -/
theorem initialXDistanceScaleAt_le_source
    (s : Nat) (hs : 200 ≤ s) :
    initialXDistanceScaleAt s ≤
      min (RandomPartition.hho20FiberLength s ^ 2 / 2)
        ((6 * RandomPartition.hho20BaseScale s) /
          (100000 * RandomPartition.hho20DegreeScale s)) := by
  let q := RandomPartition.hho20FiberLength s
  let d := 100000 * RandomPartition.hho20DegreeScale s
  have hd : 2 ≤ d := by
    have hdPos : 0 < d := by
      dsimp [d, RandomPartition.hho20DegreeScale,
        RandomPartition.hho20TypeCount]
      positivity
    omega
  have hBase := Nat.le_of_lt
    (RandomPartition.hho20_fiberCells_lt_baseScale s (by omega))
  change q ^ 2 / d ≤ min (q ^ 2 / 2)
    ((6 * RandomPartition.hho20BaseScale s) / d)
  apply (Nat.le_min).2
  constructor
  · exact Nat.div_le_div_left hd (by norm_num)
  · apply Nat.div_le_div_right
    calc
      q ^ 2 ≤ RandomPartition.hho20BaseScale s := hBase
      _ ≤ 6 * RandomPartition.hho20BaseScale s := by omega

/-- The explicit unreduced Z-distance scale lies below the source homology
bound. -/
theorem initialZDistanceScaleAt_le_source
    (s : Nat) (hs : 200 ≤ s) :
    initialZDistanceScaleAt s ≤
      (RandomPartition.hho20FiberLength s *
        (4 * RandomPartition.hho20BaseScale s)) /
          (5000 * RandomPartition.hho20DegreeScale s) := by
  have hBase := Nat.le_of_lt
    (RandomPartition.hho20_fiberCells_lt_baseScale s (by omega))
  unfold initialZDistanceScaleAt
  apply Nat.div_le_div_right
  calc
    RandomPartition.hho20FiberLength s ^ 3 =
        RandomPartition.hho20FiberLength s *
          RandomPartition.hho20FiberLength s ^ 2 := by ring
    _ ≤ RandomPartition.hho20FiberLength s *
          RandomPartition.hho20BaseScale s :=
      Nat.mul_le_mul_left _ hBase
    _ ≤ RandomPartition.hho20FiberLength s *
          (4 * RandomPartition.hho20BaseScale s) := by
      apply Nat.mul_le_mul_left
      omega

/-- Exact finite form of the unreduced `K = Theta(sqrt N)` claim. -/
theorem initial_dimension_square_bounds (s : Nat) (hs : 200 ≤ s) :
    initialBlocklengthAt s ≤ 7 * initialDimensionAt s ^ 2 ∧
    7 * initialDimensionAt s ^ 2 ≤ 2 * initialBlocklengthAt s := by
  have hLower := Nat.le_of_lt
    (RandomPartition.hho20_fiberCells_lt_baseScale s (by omega))
  have hUpper := RandomPartition.hho20_baseScale_le_two_fiberCells s hs
  unfold initialBlocklengthAt initialDimensionAt
  constructor <;> nlinarith

/-- Power-law form of `d_X = Omega(sqrt N / poly(s))` for the unreduced
family. -/
theorem initial_x_distance_tradeoff
    (s N D : Nat) (hs : 200 ≤ s)
    (hN : N ≤ initialBlocklengthAt s)
    (hD : initialXDistanceScaleAt s ≤ D) :
    N ≤ initialXTradeoffCoefficient * s ^ 4 * D ^ 2 := by
  let q := RandomPartition.hho20FiberLength s
  let d := 100000 * RandomPartition.hho20DegreeScale s
  have hd : 0 < d := by
    dsimp [d, RandomPartition.hho20DegreeScale,
      RandomPartition.hho20TypeCount]
    positivity
  have hdq := initialDenominatorAt_le_fiber_sq s hs
  have hFloor := le_two_mul_mul_div (q ^ 2) d hd (by
    simpa only [d, q] using hdq)
  have hqD : q ^ 2 ≤ 2 * d * D := by
    exact hFloor.trans (Nat.mul_le_mul_left (2 * d) hD)
  have hBase := RandomPartition.hho20_baseScale_le_two_fiberCells s hs
  calc
    N ≤ initialBlocklengthAt s := hN
    _ ≤ 14 * q ^ 4 := by
      unfold initialBlocklengthAt
      dsimp [q] at hBase ⊢
      nlinarith
    _ ≤ 14 * (2 * d * D) ^ 2 := by
      have hPow := pow_le_pow_left' hqD 2
      convert Nat.mul_le_mul_left 14 hPow using 1 <;> ring
    _ = initialXTradeoffCoefficient * s ^ 4 * D ^ 2 := by
      dsimp [d, initialXTradeoffCoefficient]
      rw [hho20DegreeScale_eq]
      ring

/-- Power-law form of `d_Z = Omega(N^(3/4) / poly(s))` for the unreduced
family. -/
theorem initial_z_distance_tradeoff
    (s N D : Nat) (hs : 200 ≤ s)
    (hN : N ≤ initialBlocklengthAt s)
    (hD : initialZDistanceScaleAt s ≤ D) :
    N ^ 3 ≤ initialZTradeoffCoefficient * s ^ 8 * D ^ 4 := by
  let q := RandomPartition.hho20FiberLength s
  let d := 5000 * RandomPartition.hho20DegreeScale s
  have hd : 0 < d := by
    dsimp [d, RandomPartition.hho20DegreeScale,
      RandomPartition.hho20TypeCount]
    positivity
  have hdq : d ≤ q ^ 3 := by
    have hLarge := initialDenominatorAt_le_fiber_sq s hs
    dsimp [d, q]
    calc
      5000 * RandomPartition.hho20DegreeScale s ≤
          100000 * RandomPartition.hho20DegreeScale s := by
        apply Nat.mul_le_mul_right
        norm_num
      _ ≤ RandomPartition.hho20FiberLength s ^ 2 := hLarge
      _ ≤ RandomPartition.hho20FiberLength s ^ 3 := by
        have hq : 1 ≤ RandomPartition.hho20FiberLength s := by
          have := RandomPartition.hho20_fiberLength_ge s (by omega)
          omega
        calc
          RandomPartition.hho20FiberLength s ^ 2 =
              RandomPartition.hho20FiberLength s ^ 2 * 1 := by ring
          _ ≤ RandomPartition.hho20FiberLength s ^ 2 *
              RandomPartition.hho20FiberLength s :=
            Nat.mul_le_mul_left _ hq
          _ = RandomPartition.hho20FiberLength s ^ 3 := by ring
  have hFloor := le_two_mul_mul_div (q ^ 3) d hd hdq
  have hqD : q ^ 3 ≤ 2 * d * D := by
    exact hFloor.trans (Nat.mul_le_mul_left (2 * d) hD)
  have hBase := RandomPartition.hho20_baseScale_le_two_fiberCells s hs
  calc
    N ^ 3 ≤ initialBlocklengthAt s ^ 3 := pow_le_pow_left' hN 3
    _ ≤ (14 * q ^ 4) ^ 3 := by
      gcongr
      unfold initialBlocklengthAt
      dsimp [q] at hBase ⊢
      nlinarith
    _ = 14 ^ 3 * (q ^ 3) ^ 4 := by ring
    _ ≤ 14 ^ 3 * (2 * d * D) ^ 4 :=
      Nat.mul_le_mul_left (14 ^ 3) (pow_le_pow_left' hqD 4)
    _ = initialZTradeoffCoefficient * s ^ 8 * D ^ 4 := by
      dsimp [d, initialZTradeoffCoefficient]
      rw [hho20DegreeScale_eq]
      ring

/-- Logical homology dimension cannot exceed the number of middle cells. -/
theorem finrank_middleHomology_le_card
    {zero one two : Type u} [Fintype zero] [Fintype one] [Fintype two]
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) zero) (Word (ZMod 2) one) (Word (ZMod 2) two)) :
    Module.finrank (ZMod 2) X.middleHomology ≤ Fintype.card one := by
  calc
    Module.finrank (ZMod 2) X.middleHomology ≤
        Module.finrank (ZMod 2) X.middleCycleCode.carrier :=
      Submodule.finrank_quotient_le X.middleBoundaryInCycles
    _ = Dimension X.middleCycleCode := rfl
    _ ≤ Length (ZMod 2) one := X.middleCycleCode.dimension_le_length
    _ = Fintype.card one := rfl

/-- Exact fifth-power form of `K = Ω(N^(3/5)/polylog N)`. -/
theorem dimension_three_fifths
    (s N K : Nat) (hs : 1 ≤ s)
    (hN : N ≤ blocklengthScaleAt s)
    (hK : dimensionScaleAt s ≤ K) :
    N ^ 3 ≤ dimensionTradeoffCoefficient * s ^ 12 * K ^ 5 := by
  let q := RandomPartition.hho20FiberLength s
  have hqK : q ^ 6 ≤ K := by
    apply (show q ^ 6 ≤ dimensionScaleAt s by rfl).trans
    exact hK
  calc
    N ^ 3 ≤ blocklengthScaleAt s ^ 3 := pow_le_pow_left' hN 3
    _ = dimensionTradeoffCoefficient * s ^ 12 * (q ^ 6) ^ 5 := by
      simp only [blocklengthScaleAt, dimensionTradeoffCoefficient, q]
      ring
    _ ≤ dimensionTradeoffCoefficient * s ^ 12 * K ^ 5 := by
      gcongr

/-- Exact fifth-power form of `D = Ω(N^(3/5)/polylog N)`. -/
theorem distance_three_fifths
    (s N D : Nat) (hs : 200 ≤ s)
    (hN : N ≤ blocklengthScaleAt s)
    (hD : distanceScaleAt s ≤ D) :
    N ^ 3 ≤ distanceTradeoffCoefficient * s ^ 32 * D ^ 5 := by
  let q := RandomPartition.hho20FiberLength s
  have hqD : q ^ 6 ≤ 8 * distanceCoefficient * s ^ 4 * D := by
    exact (fiberLength_pow_six_le_distanceScale s hs).trans
      (Nat.mul_le_mul_left (8 * distanceCoefficient * s ^ 4) hD)
  calc
    N ^ 3 ≤ blocklengthScaleAt s ^ 3 := pow_le_pow_left' hN 3
    _ = blocklengthCoefficient ^ 3 * s ^ 12 * (q ^ 6) ^ 5 := by
      simp only [blocklengthScaleAt, q]
      ring
    _ ≤ blocklengthCoefficient ^ 3 * s ^ 12 *
        (8 * distanceCoefficient * s ^ 4 * D) ^ 5 := by
      gcongr
    _ = distanceTradeoffCoefficient * s ^ 32 * D ^ 5 := by
      simp only [distanceTradeoffCoefficient]
      ring

/-- Complete finite certificate for the unreduced HHO20 fiber-bundle member.
The square and fourth-power inequalities are exact integer forms of the
source's `K = Theta(sqrt N)`, `d_X = Omega(sqrt N / polylog N)`, and
`d_Z = Omega(N^(3/4) / polylog N)` claims. -/
def InitialFamilyCertificate
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (s : Nat)
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) : Prop :=
  let D₀ := RandomTwist.fiberBundleData baseSample twistSample
  let X₀ := chainComplex D₀
  let N₀ := Fintype.card
    (QubitIndex (Fin (3 * r)) (Fin (4 * r))
      (ZMod (ell * ell)) (ZMod (ell * ell)))
  let K₀ := Module.finrank (ZMod 2) X₀.middleHomology
  (binaryCSSCode D₀).stabilizer.IsSourceValidBinary ∧
    CohomologyDistanceAtLeast D₀ (initialXDistanceScaleAt s) ∧
    HomologyDistanceAtLeast D₀ (initialZDistanceScaleAt s) ∧
    BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence X₀).localityProfile
      (initialLocalityScaleAt s) ∧
    N₀ = initialBlocklengthAt s ∧
    K₀ = initialDimensionAt s ∧
    N₀ ≤ 7 * K₀ ^ 2 ∧
    7 * K₀ ^ 2 ≤ 2 * N₀ ∧
    N₀ ≤ initialXTradeoffCoefficient * s ^ 4 *
      initialXDistanceScaleAt s ^ 2 ∧
    N₀ ^ 3 ≤ initialZTradeoffCoefficient * s ^ 8 *
      initialZDistanceScaleAt s ^ 4

theorem initialFamilyCertificate_of_good
    (s : Nat) (hs : 200 ≤ s)
    (baseSample : RandomBase.Sample (RandomPartition.hho20BaseScale s))
    (twistSample : RandomTwist.Sample
      (RandomPartition.hho20BaseScale s)
      (RandomPartition.hho20TypeCount s)
      (RandomPartition.hho20FiberLength s))
    [NeZero (RandomPartition.hho20TypeCount s)]
    [NeZero (RandomPartition.hho20FiberLength s)]
    [NeZero (RandomPartition.hho20FiberLength s - 1)]
    (hGood : RandomBase.IsFullyGood
      (Delta := RandomPartition.hho20DegreeScale s) baseSample)
    (hLTC : TwistGraph.HasHHO20LocalTestability
      (RandomPartition.hho20DegreeScale s) baseSample twistSample) :
    InitialFamilyCertificate s baseSample twistSample := by
  rcases hGood with ⟨⟨hDegree, hRank, hDistance⟩, hExpansion⟩
  let D₀ := RandomTwist.fiberBundleData baseSample twistSample
  let X₀ := chainComplex D₀
  let N₀ := Fintype.card
    (QubitIndex
      (Fin (3 * RandomPartition.hho20BaseScale s))
      (Fin (4 * RandomPartition.hho20BaseScale s))
      (ZMod (RandomPartition.hho20FiberLength s *
        RandomPartition.hho20FiberLength s))
      (ZMod (RandomPartition.hho20FiberLength s *
        RandomPartition.hho20FiberLength s)))
  let K₀ := Module.finrank (ZMod 2) X₀.middleHomology
  have hDelta : 1 ≤ RandomPartition.hho20DegreeScale s := by
    exact Nat.one_le_iff_ne_zero.mpr (by
      simp only [RandomPartition.hho20DegreeScale,
        RandomPartition.hho20TypeCount]
      positivity)
  have hXSource := cohomologyDistanceAtLeast_explicit
    baseSample twistSample hRank hDelta hDegree hExpansion
  have hXSource' : CohomologyDistanceAtLeast D₀
      (min (RandomPartition.hho20FiberLength s ^ 2 / 2)
        ((6 * RandomPartition.hho20BaseScale s) /
          (100000 * RandomPartition.hho20DegreeScale s))) := by
    intro z hz hnontrivial
    simpa only [ZMod.card, pow_two] using hXSource z hz hnontrivial
  have hZSource := homologyDistanceAtLeast_explicit
    baseSample twistSample hRank hDistance hLTC hDelta
  have hX : CohomologyDistanceAtLeast D₀
      (initialXDistanceScaleAt s) := by
    intro z hz hnontrivial
    exact (initialXDistanceScaleAt_le_source s hs).trans
      (hXSource' z hz hnontrivial)
  have hZ : HomologyDistanceAtLeast D₀
      (initialZDistanceScaleAt s) := by
    intro z hz hnontrivial
    exact (initialZDistanceScaleAt_le_source s hs).trans
      (hZSource z hz hnontrivial)
  have hLocality : BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence X₀).localityProfile
      (initialLocalityScaleAt s) := by
    exact RandomBase.initialFiberBundle_boundedLocality
      baseSample twistSample hDegree
  have hN : N₀ = initialBlocklengthAt s := by
    dsimp only [N₀, initialBlocklengthAt]
    rw [card_hho20_qubitIndex]
    ring
  have hK : K₀ = initialDimensionAt s := by
    dsimp only [K₀, X₀, D₀, initialDimensionAt]
    exact finrank_middleHomology_eq_r baseSample twistSample hRank
  have hSquare := initial_dimension_square_bounds s hs
  have hSquareOne : N₀ ≤ 7 * K₀ ^ 2 := by
    rw [hN, hK]
    exact hSquare.1
  have hSquareTwo : 7 * K₀ ^ 2 ≤ 2 * N₀ := by
    rw [hN, hK]
    exact hSquare.2
  have hXTradeoff := initial_x_distance_tradeoff s N₀
    (initialXDistanceScaleAt s) hs (by simpa [hN]) (le_refl _)
  have hZTradeoff := initial_z_distance_tradeoff s N₀
    (initialZDistanceScaleAt s) hs (by simpa [hN]) (le_refl _)
  unfold InitialFamilyCertificate
  dsimp only
  exact ⟨binaryCSSCode_stabilizer_isSourceValidBinary D₀,
    hX, hZ, hLocality, hN, hK,
    hSquareOne, hSquareTwo,
    hXTradeoff, hZTradeoff⟩

/-- Named qubit coordinates of the final construction. -/
def FinalCZeroIndex
    {rMain typeCount ell rBalance : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample rMain)
    (twistSample : RandomTwist.Sample rMain typeCount ell)
    (balanceSample : RandomBase.Sample rBalance) : Type :=
  DistanceBalancing.C0Index
    (LocalityMainCTwo baseSample twistSample)
    (LocalityMainQubit baseSample twistSample)
    (BalanceBit balanceSample) (BalanceCheck balanceSample)

def FinalQubitIndex
    {rMain typeCount ell rBalance : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample rMain)
    (twistSample : RandomTwist.Sample rMain typeCount ell)
    (balanceSample : RandomBase.Sample rBalance) : Type :=
  DistanceBalancing.QubitIndex
    (LocalityMainQubit baseSample twistSample)
    (LocalityMainCZero baseSample twistSample)
    (BalanceBit balanceSample) (BalanceCheck balanceSample)

def FinalCTwoIndex
    {rMain typeCount ell rBalance : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample rMain)
    (twistSample : RandomTwist.Sample rMain typeCount ell)
    (balanceSample : RandomBase.Sample rBalance) : Type :=
  DistanceBalancing.C2Index
    (LocalityMainCZero baseSample twistSample)
    (BalanceBit balanceSample)

noncomputable instance instFintypeFinalCZeroIndex
    {rMain typeCount ell rBalance : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample rMain)
    (twistSample : RandomTwist.Sample rMain typeCount ell)
    (balanceSample : RandomBase.Sample rBalance) :
    Fintype (FinalCZeroIndex baseSample twistSample balanceSample) := by
  unfold FinalCZeroIndex
  infer_instance

noncomputable instance instFintypeFinalQubitIndex
    {rMain typeCount ell rBalance : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample rMain)
    (twistSample : RandomTwist.Sample rMain typeCount ell)
    (balanceSample : RandomBase.Sample rBalance) :
    Fintype (FinalQubitIndex baseSample twistSample balanceSample) := by
  unfold FinalQubitIndex
  infer_instance

noncomputable instance instDecidableEqFinalQubitIndex
    {rMain typeCount ell rBalance : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample rMain)
    (twistSample : RandomTwist.Sample rMain typeCount ell)
    (balanceSample : RandomBase.Sample rBalance) :
    DecidableEq (FinalQubitIndex baseSample twistSample balanceSample) :=
  Classical.decEq _

noncomputable instance instFintypeFinalCTwoIndex
    {rMain typeCount ell rBalance : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample rMain)
    (twistSample : RandomTwist.Sample rMain typeCount ell)
    (balanceSample : RandomBase.Sample rBalance) :
    Fintype (FinalCTwoIndex baseSample twistSample balanceSample) := by
  unfold FinalCTwoIndex
  infer_instance

/-- The final complex with all three coordinate types kept behind stable
construction names. -/
noncomputable def finalComplex
    {rMain typeCount ell rBalance : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample rMain)
    (twistSample : RandomTwist.Sample rMain typeCount ell)
    (balanceSample : RandomBase.Sample rBalance) :
    ChainComplexData (ZMod 2)
      (Word (ZMod 2) (FinalCZeroIndex
        baseSample twistSample balanceSample))
      (Word (ZMod 2) (FinalQubitIndex
        baseSample twistSample balanceSample))
      (Word (ZMod 2) (FinalCTwoIndex
        baseSample twistSample balanceSample)) :=
  balancedLocalityComplex baseSample twistSample balanceSample

/-- Exact, assumption-free HHO20 fiber-bundle and qLDPC family theorem.

For every hierarchy index `s ≥ 200`, the construction itself selects the
random Tanner base, rotation twists, and balancing code.  The unreduced
member carries `InitialFamilyCertificate`, including exact integer forms of
the source's square-root dimension, asymmetric X/Z distances, and
polylogarithmic locality.  The same base and twist witnesses then pass through
weight reduction and distance balancing.  The resulting binary CSS chain
complex is source-valid, has uniform locality `8`, and both CSS distance
sectors exceed `distanceScaleAt s`.  The final two inequalities are the
integer fifth-power form of `K,D = Ω(N^(3/5)/polylog N)`; `2^(6s) ≤ N`
records that `s` is a logarithmic family scale rather than an unrelated
external parameter. -/
theorem exists_hho20_binary_css_qldpc_family_at :
    ∀ (s : Nat), ∀ (hs : 200 ≤ s),
    letI : NeZero (RandomPartition.hho20TypeCount (2 * s)) :=
      ⟨RandomPartition.hho20TypeCount_ne_zero (2 * s) (by omega)⟩
    letI : NeZero (RandomPartition.hho20FiberLength (2 * s)) :=
      ⟨by
        have := RandomPartition.hho20_fiberLength_ge (2 * s) (by omega)
        omega⟩
    letI : NeZero (RandomPartition.hho20FiberLength (2 * s) - 1) :=
      ⟨by
        have := RandomPartition.hho20_fiberLength_ge (2 * s) (by omega)
        omega⟩
    ∃ (baseSample : RandomBase.Sample
          (RandomPartition.hho20BaseScale (2 * s)))
        (twistSample : RandomTwist.Sample
          (RandomPartition.hho20BaseScale (2 * s))
          (RandomPartition.hho20TypeCount (2 * s))
          (RandomPartition.hho20FiberLength (2 * s)))
        (balanceSample : RandomBase.Sample
          (RandomPartition.hho20BaseScale s)),
      let X := finalComplex
        baseSample twistSample balanceSample
      let N := Fintype.card
        (FinalQubitIndex baseSample twistSample balanceSample)
      let K := Module.finrank (ZMod 2) X.middleHomology
      InitialFamilyCertificate (2 * s) baseSample twistSample ∧
        (X.binaryCSSCode).stabilizer.IsSourceValidBinary ∧
        MiddleHomologyDistanceAtLeast X (distanceScaleAt s) ∧
        MiddleCohomologyDistanceAtLeast X (distanceScaleAt s) ∧
        BoundedLocality
          (QEC.QLDPC.chainComplexBoundaryIncidence X).localityProfile 8 ∧
        dimensionScaleAt s ≤ K ∧
        N ≤ blocklengthScaleAt s ∧
        RandomPartition.hho20FiberLength s ^ 6 ≤ N ∧
        N ^ 3 ≤ dimensionTradeoffCoefficient * s ^ 12 * K ^ 5 ∧
        N ^ 3 ≤ distanceTradeoffCoefficient * s ^ 32 *
          distanceScaleAt s ^ 5 := by
  intro s hs
  letI : NeZero (RandomPartition.hho20TypeCount (2 * s)) :=
    ⟨RandomPartition.hho20TypeCount_ne_zero (2 * s) (by omega)⟩
  letI : NeZero (RandomPartition.hho20FiberLength (2 * s)) :=
    ⟨by
      have := RandomPartition.hho20_fiberLength_ge (2 * s) (by omega)
      omega⟩
  letI : NeZero (RandomPartition.hho20FiberLength (2 * s) - 1) :=
    ⟨by
      have := RandomPartition.hho20_fiberLength_ge (2 * s) (by omega)
      omega⟩
  obtain ⟨baseSample, twistSample, balanceSample, hAll⟩ :=
    exists_distanceBalancedCode_at s hs
  have hDistances := hAll.1
  have hBlocklength := hAll.2.1
  have hDimension := hAll.2.2.1
  have hMainGood := hAll.2.2.2.1
  have hMainLTC := hAll.2.2.2.2.1
  have hInitial : InitialFamilyCertificate (2 * s)
      baseSample twistSample := by
    exact initialFamilyCertificate_of_good (2 * s) (by omega)
      baseSample twistSample hMainGood hMainLTC
  let X := finalComplex baseSample twistSample balanceSample
  let N := Fintype.card
    (FinalQubitIndex baseSample twistSample balanceSample)
  let K := Module.finrank (ZMod 2) X.middleHomology
  have hComplex : X = DistanceBalancing.chainComplex
      (balancedData baseSample twistSample balanceSample) := by
    change balancedLocalityComplex baseSample twistSample balanceSample = _
    exact balancedLocalityComplex_eq baseSample twistSample balanceSample
  have hHomology : MiddleHomologyDistanceAtLeast X
      (balancedHomologyDistanceAt s) := by
    rw [hComplex]
    exact hDistances.1
  have hCohomology : MiddleCohomologyDistanceAtLeast X
      (balancedCohomologyDistanceAt s) := by
    rw [hComplex]
    exact hDistances.2
  have hHomologyScale : MiddleHomologyDistanceAtLeast X
      (distanceScaleAt s) := by
    intro z hz hnontrivial
    exact (distanceScaleAt_le_homology s hs).trans
      (hHomology z hz hnontrivial)
  have hCohomologyScale : MiddleCohomologyDistanceAtLeast X
      (distanceScaleAt s) := by
    intro z hz hnontrivial
    exact (distanceScaleAt_le_cohomology s hs).trans
      (hCohomology z hz hnontrivial)
  have hLocality : BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence X).localityProfile 8 := by
    exact balancedLocalityComplex_bounded_eight
      baseSample twistSample balanceSample
  have hK : dimensionScaleAt s ≤ K := by
    dsimp only [K]
    rw [hComplex]
    exact (dimensionScale_le_baseScale_product s hs).trans hDimension
  have hN : N ≤ blocklengthScaleAt s := by
    change Fintype.card
        (DistanceBalancing.QubitIndex
          (MainQubit baseSample twistSample)
          (MainCZero baseSample twistSample)
          (BalanceBit balanceSample) (BalanceCheck balanceSample)) ≤
      blocklengthScaleAt s
    exact hBlocklength.trans (balancedBlocklengthUpperAt_le_scale s hs)
  have hKN : K ≤ N := by
    exact finrank_middleHomology_le_card X
  have hExponential : RandomPartition.hho20FiberLength s ^ 6 ≤ N := by
    apply (show RandomPartition.hho20FiberLength s ^ 6 ≤
        dimensionScaleAt s by rfl).trans
    exact hK.trans hKN
  have hKTradeoff := dimension_three_fifths s N K (by omega) hN hK
  have hDTradeoff := distance_three_fifths s N (distanceScaleAt s)
    hs hN (le_refl _)
  refine ⟨baseSample, twistSample, balanceSample, ?_⟩
  dsimp only
  exact ⟨hInitial, X.binaryCSSCode_stabilizer_isSourceValidBinary,
    hHomologyScale, hCohomologyScale, hLocality, hK, hN,
    hExponential, hKTradeoff, hDTradeoff⟩

end QEC.Coding.FiberBundle.HHO20DistanceBalancing
