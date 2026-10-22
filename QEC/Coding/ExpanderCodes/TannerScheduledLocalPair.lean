import QEC.Coding.ExpanderCodes.TannerScheduleBounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Finite simultaneous PK22 local-code pairs

The weighted low-weight and sparse-rectangle budgets construct one pair of
finite-field local matrices satisfying rank, distance, and product expansion
in both orientations. The resulting pair is a finite witness, not a graph or
asymptotic family.
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

/-- Weight used to prove the finite local-code block inequalities. -/
def quadraticWeightBase (q A : Nat) : Nat := q * A ^ 2

/-- A logarithmic number of rows suffices for the finite weighted block
estimate at relative distance `D/A`. -/
def logarithmicLocalRows (q A D : Nat) : Nat :=
  D + 2 * D * (Nat.log q A + 1) + 5

/-- The quadratic weight turns the one-block low-weight event into a pure
logarithmic row budget. -/
theorem weightedBlockFactor_lt_of_logarithmicRows
    (q A D r : Nat) (hq : 2 ≤ q) (hA : 0 < A) (hD : D ≤ A)
    (hRows : logarithmicLocalRows q A D ≤ r) :
    6 * (q + quadraticWeightBase q A) ^ A <
      q ^ r * (quadraticWeightBase q A) ^ (A - D) := by
  let e := 2 * D * (Nat.log q A + 1)
  have hqPositive : 0 < q := by omega
  have hAlog : A ≤ q ^ (Nat.log q A + 1) := by
    simpa [Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (by omega : 1 < q) A).le
  have hAPower : A ^ (2 * D) ≤ q ^ e := by
    calc
      A ^ (2 * D) ≤ (q ^ (Nat.log q A + 1)) ^ (2 * D) :=
        Nat.pow_le_pow_left hAlog _
      _ = q ^ e := by simp [e, ← pow_mul, Nat.mul_comm]
  have hEighteen : 18 < q ^ 5 := by
    calc
      18 < 2 ^ 5 := by norm_num
      _ ≤ q ^ 5 := Nat.pow_le_pow_left hq 5
  have hCore : 18 * A ^ (2 * D) < q ^ (e + 5) := by
    calc
      18 * A ^ (2 * D) ≤ 18 * q ^ e :=
        Nat.mul_le_mul_left 18 hAPower
      _ < q ^ 5 * q ^ e :=
        (Nat.mul_lt_mul_right (Nat.pow_pos hqPositive)).2 hEighteen
      _ = q ^ (e + 5) := by rw [← pow_add, Nat.add_comm]
  have hExponent : D + e + 5 ≤ r := by
    simpa [logarithmicLocalRows, e, Nat.add_assoc] using hRows
  have hSplit : 2 * D + 2 * (A - D) = 2 * A := by omega
  have hSmooth :
      (A ^ 2 + 1) ^ A ≤ 3 * A ^ (2 * A) :=
    sq_add_one_pow_le_three_mul A hA
  have hLeft :
      6 * (q + quadraticWeightBase q A) ^ A ≤
        18 * q ^ A * A ^ (2 * A) := by
    unfold quadraticWeightBase
    calc
      6 * (q + q * A ^ 2) ^ A =
          6 * (q * (A ^ 2 + 1)) ^ A := by ring
      _ = 6 * q ^ A * (A ^ 2 + 1) ^ A := by rw [mul_pow]; ring
      _ ≤ 6 * q ^ A * (3 * A ^ (2 * A)) := by gcongr
      _ = 18 * q ^ A * A ^ (2 * A) := by ring
  have hCoreScaled :
      18 * q ^ A * A ^ (2 * A) <
        q ^ (A + e + 5) * A ^ (2 * (A - D)) := by
    have hPowSplit :
        A ^ (2 * A) = A ^ (2 * D) * A ^ (2 * (A - D)) := by
      rw [← pow_add, hSplit]
    calc
      18 * q ^ A * A ^ (2 * A) =
          q ^ A * (18 * A ^ (2 * D)) * A ^ (2 * (A - D)) := by
        rw [hPowSplit]
        ac_rfl
      _ < q ^ A * q ^ (e + 5) * A ^ (2 * (A - D)) := by
        exact Nat.mul_lt_mul_of_pos_right
          ((Nat.mul_lt_mul_left (Nat.pow_pos hqPositive)).2 hCore)
          (Nat.pow_pos hA)
      _ = q ^ (A + e + 5) * A ^ (2 * (A - D)) := by
        rw [show A + e + 5 = A + (e + 5) by omega]
        simp only [pow_add]
  calc
    6 * (q + quadraticWeightBase q A) ^ A <
        q ^ (A + e + 5) * A ^ (2 * (A - D)) :=
      hLeft.trans_lt hCoreScaled
    _ ≤ q ^ (A + (r - D)) * A ^ (2 * (A - D)) := by
      have hED : e + 5 ≤ r - D := Nat.le_sub_of_add_le (by omega)
      exact Nat.mul_le_mul_right _
        (Nat.pow_le_pow_right hqPositive (by omega))
    _ = q ^ r * (quadraticWeightBase q A) ^ (A - D) := by
      have hDr : D ≤ r := le_trans (Nat.le_add_right D (e + 5)) hExponent
      have hExponentSplit : A + (r - D) = r + (A - D) := by omega
      unfold quadraticWeightBase
      rw [hExponentSplit, pow_add, mul_pow, ← pow_mul]
      ring

/-- Choosing the same logarithmic row count in both orientations gives all
four one-block weighted inequalities once twice that row count fits in the
local length. -/
theorem logarithmicRows_blockWitnesses
    (q A D : Nat) (hq : 2 ≤ q) (hA : 0 < A) (hD : D ≤ A)
    (hRowsFit : 2 * logarithmicLocalRows q A D ≤ A) :
    let B := logarithmicLocalRows q A D
    let L := quadraticWeightBase q A
    (6 * (q + L) ^ A < q ^ B * L ^ (A - D)) ∧
    (6 * (q + L) ^ A < q ^ (A - B) * L ^ (A - D)) ∧
    (6 * (q + L) ^ A < q ^ B * L ^ (A - D)) ∧
    (6 * (q + L) ^ A < q ^ (A - B) * L ^ (A - D)) := by
  dsimp only
  have hForward := weightedBlockFactor_lt_of_logarithmicRows
    q A D (logarithmicLocalRows q A D) hq hA hD le_rfl
  have hReverseRows :
      logarithmicLocalRows q A D ≤ A - logarithmicLocalRows q A D := by
    omega
  have hReverse := weightedBlockFactor_lt_of_logarithmicRows
    q A D (A - logarithmicLocalRows q A D)
    hq hA hD hReverseRows
  exact ⟨hForward, hReverse, hForward, hReverse⟩

/-- The exact low-weight sum is bounded by `coarseLowWeightFactor`. -/
theorem lowWeightFactor_le_coarse
    (w d q : Nat) (hq : 0 < q) :
    (∑ t : Fin d, Nat.choose w t.1 * q ^ t.1) ≤
      coarseLowWeightFactor w d q := by
  simpa [coarseLowWeightFactor] using
    (ProductExpansion.choose_power_sum_le w 0 d q hq)

/-- A weighted binomial bound for the same low-weight sum.  Unlike
`lowWeightFactor_le_coarse`, this estimate remains exponential-linear when
`d` is a fixed fraction of `w`: multiplying the truncated sum by
`L^(w-d)` embeds every summand into the full expansion of `(q + L)^w`. -/
theorem pow_mul_lowWeightFactor_le_add_pow
    (w d q L : Nat) (hd : d ≤ w) (hL : 0 < L) :
    L ^ (w - d) * (∑ t : Fin d, Nat.choose w t.1 * q ^ t.1) ≤
      (q + L) ^ w := by
  classical
  rw [Fin.sum_univ_eq_sum_range
    (fun x ↦ Nat.choose w x * q ^ x) d, Finset.mul_sum]
  calc
    ∑ x ∈ Finset.range d,
        L ^ (w - d) * (Nat.choose w x * q ^ x) ≤
        ∑ x ∈ Finset.range d,
          q ^ x * L ^ (w - x) * Nat.choose w x := by
      apply Finset.sum_le_sum
      intro x hx
      have hxd : x < d := Finset.mem_range.mp hx
      have hPower : L ^ (w - d) ≤ L ^ (w - x) :=
        Nat.pow_le_pow_right hL
          (Nat.sub_le_sub_left (Nat.le_of_lt hxd) w)
      calc
        L ^ (w - d) * (Nat.choose w x * q ^ x) =
            q ^ x * L ^ (w - d) * Nat.choose w x := by ac_rfl
        _ ≤ q ^ x * L ^ (w - x) * Nat.choose w x :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hPower)
    _ ≤ ∑ x ∈ Finset.range (w + 1),
          q ^ x * L ^ (w - x) * Nat.choose w x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_mono (by omega)
      · intro x _ _
        positivity
    _ = (q + L) ^ w := by
      simpa using (add_pow q L w).symm

/-- A scaled power budget implies the corresponding exact truncated-binomial
budget.  This is the cancellation form used by the four kernel/image bad
events in the random local-pair argument. -/
theorem lowWeightFactor_lt_of_scaled_add_pow
    (w d q L C target : Nat) (hd : d ≤ w) (hL : 0 < L)
    (hBudget : C * (q + L) ^ w < target * L ^ (w - d)) :
    C * (∑ t : Fin d, Nat.choose w t.1 * q ^ t.1) < target := by
  have hBound := pow_mul_lowWeightFactor_le_add_pow w d q L hd hL
  have hScaled :
      (C * (∑ t : Fin d, Nat.choose w t.1 * q ^ t.1)) * L ^ (w - d) ≤
        C * (q + L) ^ w := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      Nat.mul_le_mul_left C hBound
  exact Nat.lt_of_mul_lt_mul_right (hScaled.trans_lt hBudget)

/-- A strict weighted-binomial budget on one parameter block replicates on
every positive multiple of that block.  Including the constant `6` in the
one-block hypothesis absorbs the six bad events without an asymptotic
constant argument. -/
theorem replicate_scaled_add_pow_budget
    (A D B q L n : Nat) (hn : 0 < n)
    (hBlock : 6 * (q + L) ^ A < q ^ B * L ^ (A - D)) :
    6 * (q + L) ^ (A * n) <
      q ^ (B * n) * L ^ (A * n - D * n) := by
  have hPow := Nat.pow_lt_pow_left hBlock (Nat.ne_of_gt hn)
  have hSix : 6 ≤ 6 ^ n := by
    simpa using Nat.pow_le_pow_right (by norm_num : 0 < 6) hn
  calc
    6 * (q + L) ^ (A * n) ≤
        6 ^ n * (q + L) ^ (A * n) :=
      Nat.mul_le_mul_right _ hSix
    _ = (6 * (q + L) ^ A) ^ n := by
      rw [mul_pow, pow_mul]
    _ < (q ^ B * L ^ (A - D)) ^ n := hPow
    _ = q ^ (B * n) * L ^ (A * n - D * n) := by
      rw [mul_pow, ← pow_mul, ← pow_mul,
        ← Nat.mul_sub_right_distrib]

/-- Two one-block weighted budgets for each local dimension produce all four
exact low-weight bad-event inequalities on every positive block multiple.
The complementary exponents `A - B` and `A - B'` are precisely the image
budgets after multiplying by the respective rank powers. -/
theorem exactLowWeightFactors_of_blocks
    (A D B B' q L n : Nat)
    (hD : D ≤ A) (hB : B ≤ A) (hB' : B' ≤ A)
    (hq : 0 < q) (hL : 0 < L) (hn : 0 < n)
    (hFirstKernelBlock :
      6 * (q + L) ^ A < q ^ B * L ^ (A - D))
    (hFirstImageBlock :
      6 * (q + L) ^ A < q ^ (A - B) * L ^ (A - D))
    (hSecondKernelBlock :
      6 * (q + L) ^ A < q ^ B' * L ^ (A - D))
    (hSecondImageBlock :
      6 * (q + L) ^ A < q ^ (A - B') * L ^ (A - D)) :
    (6 * (∑ t : Fin (D * n),
      Nat.choose (A * n) t.1 * q ^ t.1) < q ^ (B * n)) ∧
    (6 * (q ^ (B * n) * (∑ t : Fin (D * n),
      Nat.choose (A * n) t.1 * q ^ t.1)) < q ^ (A * n)) ∧
    (6 * (∑ t : Fin (D * n),
      Nat.choose (A * n) t.1 * q ^ t.1) < q ^ (B' * n)) ∧
    (6 * (q ^ (B' * n) * (∑ t : Fin (D * n),
      Nat.choose (A * n) t.1 * q ^ t.1)) < q ^ (A * n)) := by
  have hDn : D * n ≤ A * n := Nat.mul_le_mul_right n hD
  have hFirstKernelBudget := replicate_scaled_add_pow_budget
    A D B q L n hn hFirstKernelBlock
  have hSecondKernelBudget := replicate_scaled_add_pow_budget
    A D B' q L n hn hSecondKernelBlock
  have hFirstImageComplement := replicate_scaled_add_pow_budget
    A D (A - B) q L n hn hFirstImageBlock
  have hSecondImageComplement := replicate_scaled_add_pow_budget
    A D (A - B') q L n hn hSecondImageBlock
  have hFirstExponent : B * n + (A - B) * n = A * n := by
    rw [← Nat.add_mul, Nat.add_sub_of_le hB]
  have hSecondExponent : B' * n + (A - B') * n = A * n := by
    rw [← Nat.add_mul, Nat.add_sub_of_le hB']
  have hFirstImageBudget :
      (6 * q ^ (B * n)) * (q + L) ^ (A * n) <
        q ^ (A * n) * L ^ (A * n - D * n) := by
    calc
      (6 * q ^ (B * n)) * (q + L) ^ (A * n) =
          q ^ (B * n) * (6 * (q + L) ^ (A * n)) := by ac_rfl
      _ < q ^ (B * n) *
          (q ^ ((A - B) * n) * L ^ (A * n - D * n)) :=
        (Nat.mul_lt_mul_left (Nat.pow_pos hq)).2 hFirstImageComplement
      _ = q ^ (A * n) * L ^ (A * n - D * n) := by
        rw [← mul_assoc, ← pow_add, hFirstExponent]
  have hSecondImageBudget :
      (6 * q ^ (B' * n)) * (q + L) ^ (A * n) <
        q ^ (A * n) * L ^ (A * n - D * n) := by
    calc
      (6 * q ^ (B' * n)) * (q + L) ^ (A * n) =
          q ^ (B' * n) * (6 * (q + L) ^ (A * n)) := by ac_rfl
      _ < q ^ (B' * n) *
          (q ^ ((A - B') * n) * L ^ (A * n - D * n)) :=
        (Nat.mul_lt_mul_left (Nat.pow_pos hq)).2 hSecondImageComplement
      _ = q ^ (A * n) * L ^ (A * n - D * n) := by
        rw [← mul_assoc, ← pow_add, hSecondExponent]
  constructor
  · exact lowWeightFactor_lt_of_scaled_add_pow
      (A * n) (D * n) q L 6 (q ^ (B * n)) hDn hL
      hFirstKernelBudget
  constructor
  · simpa [mul_assoc] using lowWeightFactor_lt_of_scaled_add_pow
      (A * n) (D * n) q L (6 * q ^ (B * n)) (q ^ (A * n))
      hDn hL hFirstImageBudget
  constructor
  · exact lowWeightFactor_lt_of_scaled_add_pow
      (A * n) (D * n) q L 6 (q ^ (B' * n)) hDn hL
      hSecondKernelBudget
  · simpa [mul_assoc] using lowWeightFactor_lt_of_scaled_add_pow
      (A * n) (D * n) q L (6 * q ^ (B' * n)) (q ^ (A * n))
      hDn hL hSecondImageBudget

/-- The exact sparse-rectangle factor used by the bidirectional union bound
is bounded by `coarseRectangleFactor`. -/
theorem rectangleFactor_le_coarse
    (w m s q : Nat) :
    (Nat.choose w (w - 2 * m)) ^ 2 *
        (s * (((w - 2 * m) * (w - 2 * m) + 1) ^ s) *
          q ^ (2 * (2 * m) * w + s)) ≤
      coarseRectangleFactor w m s q := by
  have hChoose : Nat.choose w (w - 2 * m) ≤ 2 ^ w :=
    Nat.choose_le_two_pow w (w - 2 * m)
  have hChooseSq : (Nat.choose w (w - 2 * m)) ^ 2 ≤ 4 ^ w := by
    calc
      (Nat.choose w (w - 2 * m)) ^ 2 ≤ (2 ^ w) ^ 2 :=
        Nat.pow_le_pow_left hChoose 2
      _ = 4 ^ w := by
        rw [← pow_mul, Nat.mul_comm w 2, pow_mul]
        norm_num
  have hSide :
      (w - 2 * m) * (w - 2 * m) + 1 ≤ w * w + 1 := by
    gcongr <;> omega
  unfold coarseRectangleFactor
  have hExponent : 2 * (2 * m) * w + s = 4 * m * w + s := by ring
  have hMiddle :
      s * (((w - 2 * m) * (w - 2 * m) + 1) ^ s) *
          q ^ (2 * (2 * m) * w + s) ≤
        s * ((w * w + 1) ^ s) * q ^ (4 * m * w + s) := by
    rw [hExponent]
    exact Nat.mul_le_mul_right _
      (Nat.mul_le_mul_left s (Nat.pow_le_pow_left hSide s))
  exact Nat.mul_le_mul hChooseSq hMiddle

/-- The coarse rectangle factor is at most one explicit power of the field
size.  Logarithms retain the sublinear `s log w` contribution instead of
replacing it by the unusable `s w` bound. -/
theorem coarseRectangleFactor_le_power
    (w m s q : Nat) (hq : 2 ≤ q) :
    coarseRectangleFactor w m s q ≤
      q ^ coarseRectangleExponent w m s q := by
  have hqOne : 1 < q := by omega
  have hFour : 4 ≤ q ^ 2 := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  have hFourPow : 4 ^ w ≤ q ^ (2 * w) := by
    calc
      4 ^ w ≤ (q ^ 2) ^ w := Nat.pow_le_pow_left hFour w
      _ = q ^ (2 * w) := by rw [← pow_mul]
  have hS : s ≤ q ^ (Nat.log q s + 1) := by
    simpa [Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self hqOne s).le
  have hSide : w * w + 1 ≤
      q ^ (Nat.log q (w * w + 1) + 1) := by
    simpa [Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self hqOne (w * w + 1)).le
  have hSidePow : (w * w + 1) ^ s ≤
      q ^ ((Nat.log q (w * w + 1) + 1) * s) := by
    calc
      (w * w + 1) ^ s ≤
          (q ^ (Nat.log q (w * w + 1) + 1)) ^ s :=
        Nat.pow_le_pow_left hSide s
      _ = q ^ ((Nat.log q (w * w + 1) + 1) * s) := by
        rw [← pow_mul]
  unfold coarseRectangleFactor coarseRectangleExponent
  calc
    4 ^ w * (s * (w * w + 1) ^ s * q ^ (4 * m * w + s)) ≤
        q ^ (2 * w) *
          (q ^ (Nat.log q s + 1) *
            q ^ ((Nat.log q (w * w + 1) + 1) * s) *
              q ^ (4 * m * w + s)) := by
      exact Nat.mul_le_mul hFourPow
        (Nat.mul_le_mul (Nat.mul_le_mul hS hSidePow) le_rfl)
    _ = q ^ (2 * w + (Nat.log q s + 1) +
        (Nat.log q (w * w + 1) + 1) * s + (4 * m * w + s)) := by
      repeat' rw [← pow_add]
      simp only [Nat.add_assoc]

/-- An exponent comparison implies the exact sparse-rectangle bad-event
budget, including its factor `6`. -/
theorem rectangleFactor_lt_of_exponent
    (w m s q target : Nat) (hq : 2 ≤ q)
    (hExponent : coarseRectangleExponent w m s q + 3 < target) :
    6 * ((Nat.choose w (w - 2 * m)) ^ 2 *
      (s * (((w - 2 * m) * (w - 2 * m) + 1) ^ s) *
        q ^ (2 * (2 * m) * w + s))) < q ^ target := by
  have hqOne : 1 < q := by omega
  have hSix : 6 ≤ q ^ 3 := by
    calc
      6 ≤ 2 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have hExact := rectangleFactor_le_coarse w m s q
  have hCoarse := coarseRectangleFactor_le_power w m s q hq
  calc
    6 * ((Nat.choose w (w - 2 * m)) ^ 2 *
        (s * (((w - 2 * m) * (w - 2 * m) + 1) ^ s) *
          q ^ (2 * (2 * m) * w + s))) ≤
        6 * coarseRectangleFactor w m s q :=
      Nat.mul_le_mul_left 6 hExact
    _ ≤ q ^ 3 * q ^ coarseRectangleExponent w m s q :=
      Nat.mul_le_mul hSix hCoarse
    _ = q ^ (coarseRectangleExponent w m s q + 3) := by
      rw [← pow_add, Nat.add_comm]
    _ < q ^ target := Nat.pow_lt_pow_right hqOne hExponent

/-- Finite block witnesses for the low-weight terms and two integer exponent
comparisons for the rectangle terms imply all six exact pair inequalities.
This is the arithmetic endpoint needed by the random local-pair theorem. -/
theorem exactPairFactors_of_blocks
    (A D B B' m s k q L n : Nat)
    (hD : D ≤ A) (hB : B ≤ A) (hB' : B' ≤ A)
    (hq : 2 ≤ q) (hL : 0 < L) (hn : 0 < n)
    (hFirstKernelBlock :
      6 * (q + L) ^ A < q ^ B * L ^ (A - D))
    (hFirstImageBlock :
      6 * (q + L) ^ A < q ^ (A - B) * L ^ (A - D))
    (hSecondKernelBlock :
      6 * (q + L) ^ A < q ^ B' * L ^ (A - D))
    (hSecondImageBlock :
      6 * (q + L) ^ A < q ^ (A - B') * L ^ (A - D))
    (hForwardRectangle :
      coarseRectangleExponent (A * n) m s q + 3 < k * (B * n))
    (hReverseRectangle :
      coarseRectangleExponent (A * n) m s q + 3 < k * (B' * n)) :
    (6 * (∑ t : Fin (D * n),
      Nat.choose (A * n) t.1 * q ^ t.1) < q ^ (B * n)) ∧
    (6 * (q ^ (B * n) * (∑ t : Fin (D * n),
      Nat.choose (A * n) t.1 * q ^ t.1)) < q ^ (A * n)) ∧
    (6 * (∑ t : Fin (D * n),
      Nat.choose (A * n) t.1 * q ^ t.1) < q ^ (B' * n)) ∧
    (6 * (q ^ (B' * n) * (∑ t : Fin (D * n),
      Nat.choose (A * n) t.1 * q ^ t.1)) < q ^ (A * n)) ∧
    (6 * ((Nat.choose (A * n) (A * n - 2 * m)) ^ 2 *
      (s * (((A * n - 2 * m) * (A * n - 2 * m) + 1) ^ s) *
        q ^ (2 * (2 * m) * (A * n) + s))) < q ^ (k * (B * n))) ∧
    (6 * ((Nat.choose (A * n) (A * n - 2 * m)) ^ 2 *
      (s * (((A * n - 2 * m) * (A * n - 2 * m) + 1) ^ s) *
        q ^ (2 * (2 * m) * (A * n) + s))) < q ^ (k * (B' * n))) := by
  obtain ⟨hFirstKernel, hFirstImage, hSecondKernel, hSecondImage⟩ :=
    exactLowWeightFactors_of_blocks A D B B' q L n
      hD hB hB' (by omega) hL hn hFirstKernelBlock hFirstImageBlock
      hSecondKernelBlock hSecondImageBlock
  exact ⟨hFirstKernel, hFirstImage, hSecondKernel, hSecondImage,
    rectangleFactor_lt_of_exponent
      (A * n) m s q (k * (B * n)) hq hForwardRectangle,
    rectangleFactor_lt_of_exponent
      (A * n) m s q (k * (B' * n)) hq hReverseRectangle⟩

/-- The concrete polynomial schedule
`w = A n^6`, `d = D n^6`, `m = n^4`, `s = n^7`, `k = n^5`
discharges all six exact pair inequalities from four finite block witnesses
and two linear lower bounds on `n`. -/
theorem exactPairFactors_of_polynomialSchedule
    (A D B B' q L n : Nat)
    (hD : D ≤ A) (hB : B ≤ A) (hB' : B' ≤ A)
    (hq : 2 ≤ q) (hA : 0 < A) (hL : 0 < L) (hn : 0 < n)
    (hFirstKernelBlock :
      6 * (q + L) ^ A < q ^ B * L ^ (A - D))
    (hFirstImageBlock :
      6 * (q + L) ^ A < q ^ (A - B) * L ^ (A - D))
    (hSecondKernelBlock :
      6 * (q + L) ^ A < q ^ B' * L ^ (A - D))
    (hSecondImageBlock :
      6 * (q + L) ^ A < q ^ (A - B') * L ^ (A - D))
    (hForwardThreshold : 8 * A + 26 < B * n)
    (hReverseThreshold : 8 * A + 26 < B' * n) :
    (6 * (∑ t : Fin (D * n ^ 6),
      Nat.choose (A * n ^ 6) t.1 * q ^ t.1) < q ^ (B * n ^ 6)) ∧
    (6 * (q ^ (B * n ^ 6) * (∑ t : Fin (D * n ^ 6),
      Nat.choose (A * n ^ 6) t.1 * q ^ t.1)) < q ^ (A * n ^ 6)) ∧
    (6 * (∑ t : Fin (D * n ^ 6),
      Nat.choose (A * n ^ 6) t.1 * q ^ t.1) < q ^ (B' * n ^ 6)) ∧
    (6 * (q ^ (B' * n ^ 6) * (∑ t : Fin (D * n ^ 6),
      Nat.choose (A * n ^ 6) t.1 * q ^ t.1)) < q ^ (A * n ^ 6)) ∧
    (6 * ((Nat.choose (A * n ^ 6) (A * n ^ 6 - 2 * n ^ 4)) ^ 2 *
      (n ^ 7 * (((A * n ^ 6 - 2 * n ^ 4) *
        (A * n ^ 6 - 2 * n ^ 4) + 1) ^ (n ^ 7)) *
        q ^ (2 * (2 * n ^ 4) * (A * n ^ 6) + n ^ 7))) <
          q ^ (n ^ 5 * (B * n ^ 6))) ∧
    (6 * ((Nat.choose (A * n ^ 6) (A * n ^ 6 - 2 * n ^ 4)) ^ 2 *
      (n ^ 7 * (((A * n ^ 6 - 2 * n ^ 4) *
        (A * n ^ 6 - 2 * n ^ 4) + 1) ^ (n ^ 7)) *
        q ^ (2 * (2 * n ^ 4) * (A * n ^ 6) + n ^ 7))) <
          q ^ (n ^ 5 * (B' * n ^ 6))) := by
  apply exactPairFactors_of_blocks
    A D B B' (n ^ 4) (n ^ 7) (n ^ 5) q L (n ^ 6)
    hD hB hB' hq hL (Nat.pow_pos hn)
    hFirstKernelBlock hFirstImageBlock
    hSecondKernelBlock hSecondImageBlock
  · exact coarseRectangleExponent_polynomial_lt_rank
      A B n q hq hA hn hForwardThreshold
  · exact coarseRectangleExponent_polynomial_lt_rank
      A B' n q hq hA hn hReverseThreshold

/-- Exact six-event budget for an arbitrary replicated block count
`N` controlled by the sixth-root scale `x`. -/
theorem exactPairFactors_of_rootSchedule
    (A D M S K B B' q L N x : Nat)
    (hD : D ≤ A) (hB : B ≤ A) (hB' : B' ≤ A)
    (hq : 2 ≤ q) (hA : 0 < A) (hL : 0 < L) (hx : 0 < x)
    (hLower : x ^ 6 ≤ N) (hUpper : N ≤ 64 * x ^ 6)
    (hFirstKernelBlock :
      6 * (q + L) ^ A < q ^ B * L ^ (A - D))
    (hFirstImageBlock :
      6 * (q + L) ^ A < q ^ (A - B) * L ^ (A - D))
    (hSecondKernelBlock :
      6 * (q + L) ^ A < q ^ B' * L ^ (A - D))
    (hSecondImageBlock :
      6 * (q + L) ^ A < q ^ (A - B') * L ^ (A - D))
    (hForwardThreshold :
      2 * (64 * A) + 2 * (64 * A) * S + 4 * M * (64 * A) +
          16 * S + 11 < K * B * x)
    (hReverseThreshold :
      2 * (64 * A) + 2 * (64 * A) * S + 4 * M * (64 * A) +
          16 * S + 11 < K * B' * x) :
    (6 * (∑ t : Fin (D * N),
      Nat.choose (A * N) t.1 * q ^ t.1) < q ^ (B * N)) ∧
    (6 * (q ^ (B * N) * (∑ t : Fin (D * N),
      Nat.choose (A * N) t.1 * q ^ t.1)) < q ^ (A * N)) ∧
    (6 * (∑ t : Fin (D * N),
      Nat.choose (A * N) t.1 * q ^ t.1) < q ^ (B' * N)) ∧
    (6 * (q ^ (B' * N) * (∑ t : Fin (D * N),
      Nat.choose (A * N) t.1 * q ^ t.1)) < q ^ (A * N)) ∧
    (6 * ((Nat.choose (A * N) (A * N - 2 * (M * x ^ 4))) ^ 2 *
      (S * x ^ 7 * (((A * N - 2 * (M * x ^ 4)) *
        (A * N - 2 * (M * x ^ 4)) + 1) ^ (S * x ^ 7)) *
        q ^ (2 * (2 * (M * x ^ 4)) * (A * N) + S * x ^ 7))) <
          q ^ ((K * x ^ 5) * (B * N))) ∧
    (6 * ((Nat.choose (A * N) (A * N - 2 * (M * x ^ 4))) ^ 2 *
      (S * x ^ 7 * (((A * N - 2 * (M * x ^ 4)) *
        (A * N - 2 * (M * x ^ 4)) + 1) ^ (S * x ^ 7)) *
        q ^ (2 * (2 * (M * x ^ 4)) * (A * N) + S * x ^ 7))) <
          q ^ ((K * x ^ 5) * (B' * N))) := by
  apply exactPairFactors_of_blocks
    A D B B' (M * x ^ 4) (S * x ^ 7) (K * x ^ 5) q L N
    hD hB hB' hq hL ((Nat.pow_pos hx).trans_le hLower)
    hFirstKernelBlock hFirstImageBlock
    hSecondKernelBlock hSecondImageBlock
  · exact coarseRectangleExponent_rootSchedule_coeff_lt_rank
      A M S K B N x q hq hA hx hLower hUpper hForwardThreshold
  · exact coarseRectangleExponent_rootSchedule_coeff_lt_rank
      A M S K B' N x q hq hA hx hLower hUpper hReverseThreshold

omit [DecidableEq R] [DecidableEq R'] in
set_option maxHeartbeats 1200000 in
/-- The coefficient-bearing polynomial schedule constructs one simultaneous
random local-code pair, independently of the eventual labelled graph family.
All probabilistic estimates are discharged by finite block witnesses and
integer coefficient inequalities. -/
theorem exists_polynomialScheduled_localPair
    (A D M S K B B' L n : Nat)
    (hWCard : Fintype.card W = A * n ^ 6)
    (hRCard : Fintype.card R = B * n ^ 6)
    (hR'Card : Fintype.card R' = B' * n ^ 6)
    (hD : D ≤ A) (hB : B ≤ A) (hB' : B' ≤ A)
    (hA : 0 < A) (hDPositive : 0 < D) (hL : 0 < L) (hn : 0 < n)
    (hSmall : 12 * M ≤ D * n ^ 2)
    (hRankTarget : 36 * K * S ≤ 5 * D ^ 2)
    (hFirstKernelBlock :
      6 * (Nat.card F + L) ^ A <
        (Nat.card F) ^ B * L ^ (A - D))
    (hFirstImageBlock :
      6 * (Nat.card F + L) ^ A <
        (Nat.card F) ^ (A - B) * L ^ (A - D))
    (hSecondKernelBlock :
      6 * (Nat.card F + L) ^ A <
        (Nat.card F) ^ B' * L ^ (A - D))
    (hSecondImageBlock :
      6 * (Nat.card F + L) ^ A <
        (Nat.card F) ^ (A - B') * L ^ (A - D))
    (hForwardThreshold :
      2 * A + 2 * A * S + 4 * M * A + 16 * S + 11 < K * B * n)
    (hReverseThreshold :
      2 * A + 2 * A * S + 4 * M * A + 16 * S + 11 < K * B' * n) :
    ∃ (h : Matrix R W F) (h' : Matrix R' W F),
      h.rank = Fintype.card R ∧
      h'.rank = Fintype.card R' ∧
      (∀ c : Word F W, c ∈ (ProductExpansion.parityCheckCode h).carrier →
        c ≠ 0 → D * n ^ 6 ≤ HammingWeight c) ∧
      (∀ c : Word F W,
        c ∈ (ProductExpansion.parityCheckCode
          (ProductExpansion.generatorImageParityCheck h)).carrier →
        c ≠ 0 → D * n ^ 6 ≤ HammingWeight c) ∧
      (∀ c : Word F W, c ∈ (ProductExpansion.parityCheckCode h').carrier →
        c ≠ 0 → D * n ^ 6 ≤ HammingWeight c) ∧
      (∀ c : Word F W,
        c ∈ (ProductExpansion.parityCheckCode
          (ProductExpansion.generatorImageParityCheck h')).carrier →
        c ≠ 0 → D * n ^ 6 ≤ HammingWeight c) ∧
      ProductExpansion.ProductExpanding h
        (ProductExpansion.generatorImageParityCheck h')
        (S * n ^ 7) (2 * (M * n ^ 4))
        (((D * n ^ 6 : Nat) : ℝ) / (3 * (Fintype.card W : ℝ))) ∧
      ProductExpansion.ProductExpanding h'
        (ProductExpansion.generatorImageParityCheck h)
        (S * n ^ 7) (2 * (M * n ^ 4))
        (((D * n ^ 6 : Nat) : ℝ) / (3 * (Fintype.card W : ℝ))) := by
  have hq : 2 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hPair := exactPairFactors_of_blocks
    A D B B' (M * n ^ 4) (S * n ^ 7) (K * n ^ 5)
    (Nat.card F) L (n ^ 6) hD hB hB' hq hL (Nat.pow_pos hn)
    hFirstKernelBlock hFirstImageBlock hSecondKernelBlock hSecondImageBlock
    (coarseRectangleExponent_polynomial_coeff_lt_rank
      A M S K B n (Nat.card F) hq hA hn hForwardThreshold)
    (coarseRectangleExponent_polynomial_coeff_lt_rank
      A M S K B' n (Nat.card F) hq hA hn hReverseThreshold)
  obtain ⟨hFirstKernel, hFirstImage, hSecondKernel, hSecondImage,
      hForwardRectangle, hReverseRectangle⟩ := hPair
  have hPositive : 0 < D * n ^ 6 :=
    Nat.mul_pos hDPositive (Nat.pow_pos hn)
  have hLength : D * n ^ 6 ≤ Fintype.card W := by
    rw [hWCard]
    exact Nat.mul_le_mul_right _ hD
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
      _ ≤ (5 * D ^ 2) * n ^ 12 :=
        Nat.mul_le_mul_right _ hRankTarget
      _ = 5 * (D * n ^ 6) * (D * n ^ 6) := by ring
  apply ProductExpansion.exists_bidirectional_productExpanding_pair
    (F := F) (W := W) (R := R) (R' := R')
    (D * n ^ 6) (S * n ^ 7) (2 * (M * n ^ 4)) (K * n ^ 5)
    hPositive hLength hSmallScaled hRankScaled
  · simpa [hWCard, hRCard] using hFirstKernel
  · simpa [hWCard, hRCard] using hFirstImage
  · simpa [hWCard, hR'Card] using hSecondKernel
  · simpa [hWCard, hR'Card] using hSecondImage
  · simpa [hWCard, hRCard, mul_assoc] using hForwardRectangle
  · simpa [hWCard, hR'Card, mul_assoc] using hReverseRectangle

omit [DecidableEq R] [DecidableEq R'] in
set_option maxHeartbeats 1200000 in
/-- Construct the simultaneous random local-code pair at every compatible
replication count `N`, using `x = floor(N^(1/6))` only for the auxiliary
sublinear scales. -/
theorem exists_rootScheduled_localPair
    (A D M S K B B' L N x : Nat)
    (hWCard : Fintype.card W = A * N)
    (hRCard : Fintype.card R = B * N)
    (hR'Card : Fintype.card R' = B' * N)
    (hD : D ≤ A) (hB : B ≤ A) (hB' : B' ≤ A)
    (hA : 0 < A) (hDPositive : 0 < D) (hL : 0 < L) (hx : 0 < x)
    (hLower : x ^ 6 ≤ N) (hUpper : N ≤ 64 * x ^ 6)
    (hSmall : 12 * M ≤ D * x ^ 2)
    (hRankTarget : 36 * K * S ≤ 5 * D ^ 2)
    (hFirstKernelBlock :
      6 * (Nat.card F + L) ^ A <
        (Nat.card F) ^ B * L ^ (A - D))
    (hFirstImageBlock :
      6 * (Nat.card F + L) ^ A <
        (Nat.card F) ^ (A - B) * L ^ (A - D))
    (hSecondKernelBlock :
      6 * (Nat.card F + L) ^ A <
        (Nat.card F) ^ B' * L ^ (A - D))
    (hSecondImageBlock :
      6 * (Nat.card F + L) ^ A <
        (Nat.card F) ^ (A - B') * L ^ (A - D))
    (hForwardThreshold :
      2 * (64 * A) + 2 * (64 * A) * S + 4 * M * (64 * A) +
          16 * S + 11 < K * B * x)
    (hReverseThreshold :
      2 * (64 * A) + 2 * (64 * A) * S + 4 * M * (64 * A) +
          16 * S + 11 < K * B' * x) :
    ∃ (h : Matrix R W F) (h' : Matrix R' W F),
      h.rank = Fintype.card R ∧
      h'.rank = Fintype.card R' ∧
      (∀ c : Word F W, c ∈ (ProductExpansion.parityCheckCode h).carrier →
        c ≠ 0 → D * N ≤ HammingWeight c) ∧
      (∀ c : Word F W,
        c ∈ (ProductExpansion.parityCheckCode
          (ProductExpansion.generatorImageParityCheck h)).carrier →
        c ≠ 0 → D * N ≤ HammingWeight c) ∧
      (∀ c : Word F W, c ∈ (ProductExpansion.parityCheckCode h').carrier →
        c ≠ 0 → D * N ≤ HammingWeight c) ∧
      (∀ c : Word F W,
        c ∈ (ProductExpansion.parityCheckCode
          (ProductExpansion.generatorImageParityCheck h')).carrier →
        c ≠ 0 → D * N ≤ HammingWeight c) ∧
      ProductExpansion.ProductExpanding h
        (ProductExpansion.generatorImageParityCheck h')
        (S * x ^ 7) (2 * (M * x ^ 4))
        (((D * N : Nat) : ℝ) / (3 * (Fintype.card W : ℝ))) ∧
      ProductExpansion.ProductExpanding h'
        (ProductExpansion.generatorImageParityCheck h)
        (S * x ^ 7) (2 * (M * x ^ 4))
        (((D * N : Nat) : ℝ) / (3 * (Fintype.card W : ℝ))) := by
  have hq : 2 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hPair := exactPairFactors_of_rootSchedule
    A D M S K B B' (Nat.card F) L N x
    hD hB hB' hq hA hL hx hLower hUpper
    hFirstKernelBlock hFirstImageBlock hSecondKernelBlock hSecondImageBlock
    hForwardThreshold hReverseThreshold
  obtain ⟨hFirstKernel, hFirstImage, hSecondKernel, hSecondImage,
      hForwardRectangle, hReverseRectangle⟩ := hPair
  have hNPositive : 0 < N := (Nat.pow_pos hx).trans_le hLower
  have hPositive : 0 < D * N := Nat.mul_pos hDPositive hNPositive
  have hLength : D * N ≤ Fintype.card W := by
    rw [hWCard]
    exact Nat.mul_le_mul_right _ hD
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
      _ ≤ (5 * D ^ 2) * x ^ 12 :=
        Nat.mul_le_mul_right _ hRankTarget
      _ ≤ (5 * D ^ 2) * N ^ 2 :=
        Nat.mul_le_mul_left (5 * D ^ 2) hLowerSquare
      _ = 5 * (D * N) * (D * N) := by ring
  apply ProductExpansion.exists_bidirectional_productExpanding_pair
    (F := F) (W := W) (R := R) (R' := R')
    (D * N) (S * x ^ 7) (2 * (M * x ^ 4)) (K * x ^ 5)
    hPositive hLength hSmallScaled hRankScaled
  · simpa [hWCard, hRCard] using hFirstKernel
  · simpa [hWCard, hRCard] using hFirstImage
  · simpa [hWCard, hR'Card] using hSecondKernel
  · simpa [hWCard, hR'Card] using hSecondImage
  · simpa [hWCard, hRCard, mul_assoc] using hForwardRectangle
  · simpa [hWCard, hR'Card, mul_assoc] using hReverseRectangle


end QEC.Coding.TannerLiftedProduct
