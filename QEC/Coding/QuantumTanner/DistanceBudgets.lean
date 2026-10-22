import QEC.Coding.QuantumTanner.LocalDescent
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Integer and asymptotic budgets for Quantum Tanner distance

The degree is fixed after choosing the source exponents. These inequalities
justify the rounding and lower-order losses in [LZ22, proof of thm:main].
They do not assert existence of a Ramanujan square-complex family.
-/

noncomputable section

namespace QEC.Coding.QuantumTanner

open Filter

/-- The exceptional-view threshold, with the source's exact ceiling. -/
def distanceNormalCutoff (epsilon : ℝ) (Delta : Nat) : Nat :=
  Nat.ceil ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon))

/-- A uniform line-error bound obtained from the robust normal-view cover. -/
def distanceLineError (delta epsilon : ℝ) (Delta : Nat) : Nat :=
  (distanceNormalCutoff epsilon Delta - 1) / Nat.ceil (delta * Delta)

private theorem eventual_power_margin
    (a b c : ℝ) (hab : a < b) (hc : 0 < c) :
    ∃ t : Nat, ∀ n : Nat, t ≤ n → 2 ≤ n ∧ (n : ℝ) ^ a < c * (n : ℝ) ^ b := by
  have hSmall := (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).eventually (gt_mem_nhds hc)
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

private theorem eventual_floor_power_lower
    (a b c : ℝ) (hab : a < b) (hb : 0 < b) (hc : 0 < c) :
    ∃ t : Nat, ∀ n : Nat, t ≤ n →
      2 ≤ n ∧ c * (n : ℝ) ^ a ≤ (Nat.floor ((n : ℝ) ^ b) : ℝ) := by
  obtain ⟨tA, hA⟩ := eventual_power_margin a b (1 / (2 * c)) hab (by positivity)
  obtain ⟨tB, hB⟩ := eventual_power_margin 0 b (1 / 2) hb (by norm_num)
  refine ⟨max tA tB, ?_⟩
  intro n hn
  obtain ⟨hTwo, hSmall⟩ := hA n ((Nat.le_max_left _ _).trans hn)
  obtain ⟨_, hLarge⟩ := hB n ((Nat.le_max_right _ _).trans hn)
  have hFloor := Nat.lt_floor_add_one ((n : ℝ) ^ b)
  have hScaled := mul_lt_mul_of_pos_left hSmall (show 0 < 2 * c by positivity)
  have hCancel : (2 * c) * (1 / (2 * c)) = 1 := by field_simp
  have hScaled' : 2 * c * (n : ℝ) ^ a < (n : ℝ) ^ b := by
    calc
      2 * c * (n : ℝ) ^ a < (2 * c) * ((1 / (2 * c)) * (n : ℝ) ^ b) := hScaled
      _ = (n : ℝ) ^ b := by rw [← mul_assoc, hCancel, one_mul]
  norm_num only [Real.rpow_zero] at hLarge
  exact ⟨hTwo, by linarith⟩

/-- The integer cover budget is bounded by the source's real sublinear error.
This controls the actual ceiling and natural-number division. -/
theorem distanceLineError_le_real_bound
    (delta epsilon : ℝ) (Delta : Nat) (hDelta : 0 < Delta) (hDeltaDistance : 0 < delta) :
    (distanceLineError delta epsilon Delta : ℝ) ≤
      (Delta : ℝ) ^ ((1 : ℝ) / 2 - epsilon) / delta := by
  have hD : (0 : ℝ) < Delta := by exact_mod_cast hDelta
  let n := distanceNormalCutoff epsilon Delta
  let d := Nat.ceil (delta * Delta)
  let e := distanceLineError delta epsilon Delta
  have hPower : 0 < (Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon) := Real.rpow_pos_of_pos hD _
  have hn : 0 < n := Nat.ceil_pos.mpr hPower
  have hCeil := Nat.ceil_lt_add_one hPower.le
  have hCastSub : ((n - 1 : Nat) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hnBound : ((n - 1 : Nat) : ℝ) ≤ (Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon) := by
    dsimp [n, distanceNormalCutoff] at hCastSub ⊢
    linarith
  have hDistance : delta * Delta ≤ (d : ℝ) := Nat.le_ceil _
  have hDiv : e * d ≤ n - 1 := Nat.div_mul_le_self _ _
  have hDiv' : (e : ℝ) * d ≤ ((n - 1 : Nat) : ℝ) := by exact_mod_cast hDiv
  have hScaled := mul_le_mul_of_nonneg_left hDistance (Nat.cast_nonneg e)
  have hPowerProduct : (Delta : ℝ) * (Delta : ℝ) ^ ((1 : ℝ) / 2 - epsilon) =
      (Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon) := by
    calc
      (Delta : ℝ) * (Delta : ℝ) ^ ((1 : ℝ) / 2 - epsilon) =
          (Delta : ℝ) ^ (1 : ℝ) * (Delta : ℝ) ^ ((1 : ℝ) / 2 - epsilon) := by
        rw [Real.rpow_one]
      _ = (Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon) := by
        rw [← Real.rpow_add hD]
        congr 1
        ring
  apply (le_div_iff₀ hDeltaDistance).mpr
  apply le_of_mul_le_mul_left (a := (Delta : ℝ)) ?_ hD
  dsimp only [e] at *
  nlinarith

/-- The source exponent inequalities give all the real smallness margins
needed for exceptional sets, punctures, robustness and the final strict
weight decrease, including a genuine lower bound on the integer puncture budget. -/
theorem exists_eventual_distance_real_margins
    (delta epsilon gamma : ℝ) (hDeltaDistance : 0 < delta)
    (hEpsilon : 0 < epsilon) (hEpsilonHalf : epsilon < 1 / 2)
    (hGammaLower : 1 / 2 + epsilon < gamma) (hGammaUpper : gamma < 1) :
    ∃ t : Nat, ∀ Delta : Nat, t ≤ Delta →
      2 ≤ Delta ∧
      64 / (Delta : ℝ) ^ (1 - 2 * epsilon) ≤ 1 / 2 ∧
      (Delta : ℝ) ^ ((1 : ℝ) / 2 - epsilon) / delta <
        min (delta / 4) (delta ^ 3 / 12288) * Delta ∧
      (Nat.floor ((Delta : ℝ) ^ gamma) : ℝ) <
        min (min (delta / 4) (delta ^ 3 / 8192)) 1 * Delta ∧
      (Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2) <
        delta ^ 2 / 8 * (Delta : ℝ) ^ (2 : ℝ) ∧
      40960 / delta ^ 2 * (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon) ≤
        (Nat.floor ((Delta : ℝ) ^ gamma) : ℝ) := by
  obtain ⟨tE, hE⟩ := eventual_power_margin 0 (1 - 2 * epsilon) (1 / 128)
    (by linarith) (by norm_num)
  obtain ⟨tL, hL⟩ := eventual_power_margin ((1 : ℝ) / 2 - epsilon) 1
    (delta * min (delta / 4) (delta ^ 3 / 12288)) (by linarith) (by positivity)
  obtain ⟨tP, hP⟩ := eventual_power_margin gamma 1
    (min (min (delta / 4) (delta ^ 3 / 8192)) 1) hGammaUpper (by positivity)
  obtain ⟨tW, hW⟩ := eventual_power_margin ((3 : ℝ) / 2 - epsilon / 2) 2
    (delta ^ 2 / 8) (by linarith) (by positivity)
  obtain ⟨tB, hB⟩ := eventual_floor_power_lower ((1 : ℝ) / 2 + epsilon) gamma
    (40960 / delta ^ 2) hGammaLower (by linarith) (by positivity)
  refine ⟨max tE (max tL (max tP (max tW tB))), ?_⟩
  intro Delta hDegree
  obtain ⟨hTwo, hExceptional⟩ := hE Delta ((Nat.le_max_left _ _).trans hDegree)
  have hRest := (Nat.le_max_right _ _).trans hDegree
  obtain ⟨_, hLine⟩ := hL Delta ((Nat.le_max_left _ _).trans hRest)
  have hRest' := (Nat.le_max_right _ _).trans hRest
  obtain ⟨_, hPuncture⟩ := hP Delta ((Nat.le_max_left _ _).trans hRest')
  have hRest'' := (Nat.le_max_right _ _).trans hRest'
  obtain ⟨_, hWeight⟩ := hW Delta ((Nat.le_max_left _ _).trans hRest'')
  obtain ⟨_, hLower⟩ := hB Delta ((Nat.le_max_right _ _).trans hRest'')
  have hD : (0 : ℝ) < Delta := by exact_mod_cast (by omega : 0 < Delta)
  have hPower : 0 < (Delta : ℝ) ^ (1 - 2 * epsilon) := Real.rpow_pos_of_pos hD _
  have hFraction : 64 / (Delta : ℝ) ^ (1 - 2 * epsilon) ≤ 1 / 2 := by
    apply (div_le_iff₀ hPower).mpr
    norm_num only [Real.rpow_zero] at hExceptional
    linarith
  have hLine' : (Delta : ℝ) ^ ((1 : ℝ) / 2 - epsilon) / delta <
      min (delta / 4) (delta ^ 3 / 12288) * Delta := by
    apply (div_lt_iff₀ hDeltaDistance).mpr
    simpa only [Real.rpow_one, mul_assoc, mul_left_comm, mul_comm] using hLine
  have hFloor := Nat.floor_le (Real.rpow_nonneg hD.le gamma)
  exact ⟨hTwo, hFraction, hLine', hFloor.trans_lt (by simpa only [Real.rpow_one] using hPuncture),
    hWeight, hLower⟩

/-- Integer versions of the source's robustness and final descent margins.
The actual floor punctures and ceiling-based line error are used throughout. -/
theorem exists_eventual_distance_integer_margins
    (delta epsilon gamma : ℝ) (hDeltaDistance : 0 < delta)
    (hEpsilon : 0 < epsilon) (hEpsilonHalf : epsilon < 1 / 2)
    (hGammaLower : 1 / 2 + epsilon < gamma) (hGammaUpper : gamma < 1) :
    ∃ t : Nat, ∀ Delta : Nat, t ≤ Delta →
      let d := Nat.ceil (delta * Delta)
      let e := distanceLineError delta epsilon Delta
      let p := Nat.floor ((Delta : ℝ) ^ gamma)
      let w := Nat.floor ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2))
      2 ≤ Delta ∧ 0 < distanceNormalCutoff epsilon Delta ∧
      distanceNormalCutoff epsilon Delta - 1 ≤ w ∧
      p ≤ Delta ∧ p < d ∧ e < d ∧
      2 * w ≤ (d - p) * (d - p) ∧ 2 * Delta * e ≤ w ∧
      ((6 * Delta * e + 4 * Delta * p : Nat) : ℝ) <
        (d - e : Nat) * (delta ^ 2 * Delta / 256) ∧
      64 / (Delta : ℝ) ^ (1 - 2 * epsilon) ≤ 1 / 2 ∧
      40960 / delta ^ 2 * (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon) ≤ (p : ℝ) := by
  obtain ⟨tR, hR⟩ := exists_eventual_distance_real_margins delta epsilon gamma
    hDeltaDistance hEpsilon hEpsilonHalf hGammaLower hGammaUpper
  obtain ⟨tW, hW⟩ := eventual_floor_power_lower ((3 : ℝ) / 2 - epsilon)
    ((3 : ℝ) / 2 - epsilon / 2) (2 / delta) (by linarith) (by linarith) (by positivity)
  refine ⟨max tR tW, ?_⟩
  intro Delta hDegree
  dsimp only
  obtain ⟨hTwo, hFraction, hLine, hPuncture, hWeight, hLower⟩ :=
    hR Delta ((Nat.le_max_left _ _).trans hDegree)
  obtain ⟨_, hErrorWeight⟩ := hW Delta ((Nat.le_max_right _ _).trans hDegree)
  let d := Nat.ceil (delta * Delta)
  let e := distanceLineError delta epsilon Delta
  let p := Nat.floor ((Delta : ℝ) ^ gamma)
  let w := Nat.floor ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2))
  have hD : (0 : ℝ) < Delta := by exact_mod_cast (by omega : 0 < Delta)
  have hOne : (1 : ℝ) ≤ Delta := by exact_mod_cast (by omega : 1 ≤ Delta)
  have hDistance : delta * Delta ≤ (d : ℝ) := Nat.le_ceil _
  have hError := distanceLineError_le_real_bound delta epsilon Delta (by omega) hDeltaDistance
  have hErrorSmall : (e : ℝ) < min (delta / 4) (delta ^ 3 / 12288) * Delta := hError.trans_lt hLine
  have hErrorDistance : (e : ℝ) < delta / 4 * Delta :=
    hErrorSmall.trans_le (mul_le_mul_of_nonneg_right (min_le_left _ _) hD.le)
  have hErrorCost : (e : ℝ) < delta ^ 3 / 12288 * Delta :=
    hErrorSmall.trans_le (mul_le_mul_of_nonneg_right (min_le_right _ _) hD.le)
  have hPunctureDistance : (p : ℝ) < delta / 4 * Delta := by
    exact hPuncture.trans_le (mul_le_mul_of_nonneg_right
      ((min_le_left _ _).trans (min_le_left _ _)) hD.le)
  have hPunctureCost : (p : ℝ) < delta ^ 3 / 8192 * Delta := by
    exact hPuncture.trans_le (mul_le_mul_of_nonneg_right
      ((min_le_left _ _).trans (min_le_right _ _)) hD.le)
  have hpDegree : p ≤ Delta := by
    have hReal : (p : ℝ) < Delta :=
      hPuncture.trans_le (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (min_le_right (min (delta / 4) (delta ^ 3 / 8192)) 1) hD.le)
    exact_mod_cast hReal.le
  have hpD : p < d := by exact_mod_cast (by nlinarith : (p : ℝ) < d)
  have heD : e < d := by exact_mod_cast (by nlinarith : (e : ℝ) < d)
  have hCastDP : ((d - p : Nat) : ℝ) = (d : ℝ) - p := by rw [Nat.cast_sub hpD.le]
  have hCastDE : ((d - e : Nat) : ℝ) = (d : ℝ) - e := by rw [Nat.cast_sub heD.le]
  have hDP : 3 * delta * Delta / 4 ≤ ((d - p : Nat) : ℝ) := by rw [hCastDP]; nlinarith
  have hDE : 3 * delta * Delta / 4 ≤ ((d - e : Nat) : ℝ) := by rw [hCastDE]; nlinarith
  have hFloorWeight : (w : ℝ) ≤ (Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2) :=
    Nat.floor_le (Real.rpow_nonneg hD.le _)
  have hPunctureBudget : 2 * w ≤ (d - p) * (d - p) := by
    have hDPSquare : (3 * delta * Delta / 4) ^ 2 ≤ (((d - p : Nat) : ℝ)) ^ 2 :=
      (sq_le_sq₀ (by positivity) (Nat.cast_nonneg _)).mpr hDP
    have hWeight' : (2 : ℝ) * w ≤ (((d - p : Nat) : ℝ)) * ((d - p : Nat) : ℝ) := by
      norm_num only [Real.rpow_two] at hWeight
      nlinarith
    exact_mod_cast hWeight'
  have hPowerProduct : (Delta : ℝ) * (Delta : ℝ) ^ ((1 : ℝ) / 2 - epsilon) =
      (Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon) := by
    calc
      (Delta : ℝ) * (Delta : ℝ) ^ ((1 : ℝ) / 2 - epsilon) =
          (Delta : ℝ) ^ (1 : ℝ) * (Delta : ℝ) ^ ((1 : ℝ) / 2 - epsilon) := by rw [Real.rpow_one]
      _ = (Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon) := by
        rw [← Real.rpow_add hD]
        congr 1
        ring
  have hErrorBudget : 2 * Delta * e ≤ w := by
    have hScaled := mul_le_mul_of_nonneg_left hError (show 0 ≤ 2 * (Delta : ℝ) by positivity)
    have hBound : (2 : ℝ) * Delta * e ≤
        (2 / delta) * (Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon) := by
      calc
        (2 : ℝ) * Delta * e ≤ 2 * Delta * ((Delta : ℝ) ^ ((1 : ℝ) / 2 - epsilon) / delta) := hScaled
        _ = (2 / delta) * ((Delta : ℝ) * (Delta : ℝ) ^ ((1 : ℝ) / 2 - epsilon)) := by ring
        _ = _ := by rw [hPowerProduct]
    exact_mod_cast hBound.trans hErrorWeight
  have hMargin : ((6 * Delta * e + 4 * Delta * p : Nat) : ℝ) <
      (d - e : Nat) * (delta ^ 2 * Delta / 256) := by
    have hLineScaled := mul_lt_mul_of_pos_left hErrorCost (show 0 < 6 * (Delta : ℝ) by positivity)
    have hPunctureScaled := mul_lt_mul_of_pos_left hPunctureCost (show 0 < 4 * (Delta : ℝ) by positivity)
    have hHeavyScaled := mul_le_mul_of_nonneg_right hDE
      (show 0 ≤ delta ^ 2 * Delta / 256 by positivity)
    have hPositive : 0 < delta ^ 3 * (Delta : ℝ) ^ 2 := by positivity
    push_cast
    nlinarith only [hLineScaled, hPunctureScaled, hHeavyScaled, hPositive]
  have hNormalPos : 0 < distanceNormalCutoff epsilon Delta :=
    Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hD _)
  have hNormalWeight : distanceNormalCutoff epsilon Delta - 1 ≤ w := by
    have hCeil := Nat.ceil_lt_add_one (Real.rpow_nonneg hD.le ((3 : ℝ) / 2 - epsilon))
    have hCast : ((distanceNormalCutoff epsilon Delta - 1 : Nat) : ℝ) =
        (distanceNormalCutoff epsilon Delta : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ distanceNormalCutoff epsilon Delta)]
      norm_num
    apply Nat.le_floor
    have hPower := Real.rpow_le_rpow_of_exponent_le hOne
      (show (3 : ℝ) / 2 - epsilon ≤ 3 / 2 - epsilon / 2 by linarith)
    dsimp [distanceNormalCutoff] at hCast ⊢
    linarith only [hCeil, hCast, hPower]
  exact ⟨hTwo, hNormalPos, hNormalWeight, hpDegree, hpD, heD,
    hPunctureBudget, hErrorBudget, hMargin, hFraction, hLower⟩

/-- The union-graph density loss is also sublinear. This statement does not
restrict `delta` to be at most one. -/
theorem exists_eventual_distance_density_margin
    (delta epsilon : ℝ) (hDeltaDistance : 0 < delta) (hEpsilon : 0 < epsilon) :
    ∃ t : Nat, ∀ Delta : Nat, t ≤ Delta →
      2 ≤ Delta ∧
      (distanceLineError delta epsilon Delta : ℝ) +
        (Delta : ℝ) ^ ((1 : ℝ) / 2 - epsilon) / 2 ≤ delta * Delta / 2 := by
  obtain ⟨t, ht⟩ := eventual_power_margin ((1 : ℝ) / 2 - epsilon) 1
    (min (delta ^ 2 / 4) (delta / 2)) (by linarith) (by positivity)
  refine ⟨t, ?_⟩
  intro Delta hDegree
  obtain ⟨hTwo, hPower⟩ := ht Delta hDegree
  rw [Real.rpow_one] at hPower
  have hD : (0 : ℝ) < Delta := by exact_mod_cast (by omega : 0 < Delta)
  have hError := distanceLineError_le_real_bound delta epsilon Delta (by omega) hDeltaDistance
  have hLeft := hPower.trans_le (mul_le_mul_of_nonneg_right (min_le_left _ _) hD.le)
  have hRight := hPower.trans_le (mul_le_mul_of_nonneg_right (min_le_right _ _) hD.le)
  have hErrorSmall : (distanceLineError delta epsilon Delta : ℝ) < delta * Delta / 4 := by
    apply hError.trans_lt
    apply (div_lt_iff₀ hDeltaDistance).mpr
    nlinarith only [hLeft]
  exact ⟨hTwo, by linarith only [hErrorSmall, hRight]⟩

/-- Exact scalar mixing budgets used in the source distance argument.
`s` is the actual active-vertex count, and `n` the actual group cardinality.
No graph or spectral conclusion is encoded in these arithmetic hypotheses. -/
theorem distance_mixing_scalar_budgets
    (delta epsilon : ℝ) (Delta s n p : Nat)
    (hDelta : 2 ≤ Delta) (hDeltaDistance : 0 < delta)
    (hSmall : (s : ℝ) ≤ n / (4 * (Delta : ℝ) ^ (1 / 2 + epsilon)))
    (hError : distanceLineError delta epsilon Delta < Nat.ceil (delta * Delta))
    (hDensity : (distanceLineError delta epsilon Delta : ℝ) +
      (Delta : ℝ) ^ ((1 : ℝ) / 2 - epsilon) / 2 ≤ delta * Delta / 2)
    (hFractionHalf : 64 / (Delta : ℝ) ^ (1 - 2 * epsilon) ≤ 1 / 2)
    (hPuncture : 40960 / delta ^ 2 * (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon) ≤ (p : ℝ)) :
    let normal := (Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon)
    let fraction := 64 / (Delta : ℝ) ^ (1 - 2 * epsilon)
    let gap := delta * Delta / 2
    let ratio := 64 / (delta ^ 2 * Delta)
    let threshold := delta ^ 2 * Delta / 256
    let uniform := 32 / (Delta : ℝ) * (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon)
    2 * ((Delta * Delta : Nat) : ℝ) * s ≤ normal * n ∧
    4 * (4 * (Delta : ℝ)) ^ 2 ≤ fraction * normal ^ 2 ∧
    ((Delta + Delta : Nat) : ℝ) * s + gap * n ≤
      ((Nat.ceil (delta * Delta) - distanceLineError delta epsilon Delta : Nat) : ℝ) * n ∧
    (4 * Real.sqrt (Delta : ℝ)) ^ 2 ≤ ratio * gap ^ 2 ∧
    2 * threshold * ratio ≤ 1 - fraction ∧
    ((Delta + Delta : Nat) : ℝ) * (fraction * s) ≤ uniform * n ∧
    (uniform + 4 * Real.sqrt (Delta : ℝ) *
      Real.sqrt (fraction * (2 * ((Delta + Delta : Nat) : ℝ)))) *
      ((Delta + Delta : Nat) : ℝ) ≤ (p : ℝ) * threshold := by
  dsimp only
  have hD : (0 : ℝ) < Delta := by exact_mod_cast (by omega : 0 < Delta)
  have hTwo : (2 : ℝ) ≤ Delta := by exact_mod_cast hDelta
  have hP : 0 < (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon) := Real.rpow_pos_of_pos hD _
  have hF : 0 < (Delta : ℝ) ^ (1 - 2 * epsilon) := Real.rpow_pos_of_pos hD _
  have hT : 0 < (Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon) := Real.rpow_pos_of_pos hD _
  have hProduct : (Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon) *
      (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon) = (Delta : ℝ) ^ 2 := by
    rw [← Real.rpow_add hD]
    norm_num [show (3 : ℝ) / 2 - epsilon + (1 / 2 + epsilon) = 2 by ring]
  have hNormalSquare : ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon)) ^ 2 =
      (Delta : ℝ) ^ 2 * (Delta : ℝ) ^ (1 - 2 * epsilon) := by
    rw [← Real.rpow_mul_natCast hD.le, ← Real.rpow_natCast _ 2, ← Real.rpow_add hD]
    congr 1
    ring
  have hDensityProduct : (Delta : ℝ) ^ ((1 : ℝ) / 2 - epsilon) *
      (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon) = (Delta : ℝ) := by
    rw [← Real.rpow_add hD, show (1 : ℝ) / 2 - epsilon + (1 / 2 + epsilon) = 1 by ring,
      Real.rpow_one]
  have hMeanProduct : (Delta : ℝ) ^ (1 - 2 * epsilon) *
      ((Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon)) ^ 2 = (Delta : ℝ) ^ 2 := by
    rw [← Real.rpow_mul_natCast hD.le, ← Real.rpow_add hD]
    norm_num [show (1 - 2 * epsilon) + ((1 : ℝ) / 2 + epsilon) * 2 = 2 by ring]
  have hRootProduct : (Delta : ℝ) ^ (1 - 2 * epsilon) *
      ((Delta : ℝ) ^ epsilon) ^ 2 = (Delta : ℝ) := by
    rw [← Real.rpow_mul_natCast hD.le, ← Real.rpow_add hD]
    norm_num [show (1 - 2 * epsilon) + epsilon * 2 = 1 by ring]
  have hRoot : Real.sqrt (64 / (Delta : ℝ) ^ (1 - 2 * epsilon) * (4 * Delta)) =
      16 * (Delta : ℝ) ^ epsilon := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
    field_simp [hF.ne']
    nlinarith only [hRootProduct]
  have hMixedRoot : Real.sqrt (Delta : ℝ) * (Delta : ℝ) ^ epsilon =
      (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hD]
  have hSmall' := (le_div_iff₀ (show 0 < 4 * (Delta : ℝ) ^ (1 / 2 + epsilon) by positivity)).mp hSmall
  have hSquareSmall : 2 * ((Delta * Delta : Nat) : ℝ) * s ≤
      (Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon) * n := by
    have hScaled := mul_le_mul_of_nonneg_left hSmall' hT.le
    push_cast
    nlinarith only [hScaled, hProduct, (show (0 : ℝ) ≤ s from Nat.cast_nonneg s)]
  have hFraction : 4 * (4 * (Delta : ℝ)) ^ 2 ≤
      64 / (Delta : ℝ) ^ (1 - 2 * epsilon) *
        ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon)) ^ 2 := by
    rw [hNormalSquare]
    field_simp
    ring_nf
    norm_num
  have hUnionDensity : ((Delta + Delta : Nat) : ℝ) * s + delta * Delta / 2 * n ≤
      ((Nat.ceil (delta * Delta) - distanceLineError delta epsilon Delta : Nat) : ℝ) * n := by
    have hScaled := mul_le_mul_of_nonneg_left hSmall' (show 0 ≤ (Delta : ℝ) by positivity)
    have hSparse : 2 * (Delta : ℝ) * s ≤
        (Delta : ℝ) ^ ((1 : ℝ) / 2 - epsilon) / 2 * n := by
      apply le_of_mul_le_mul_left (a := (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon)) ?_ hP
      nlinarith only [hScaled, hDensityProduct]
    have hCeil := Nat.le_ceil (delta * (Delta : ℝ))
    have hMargin := mul_le_mul_of_nonneg_right hDensity (Nat.cast_nonneg n)
    have hCeilScaled := mul_le_mul_of_nonneg_right hCeil (Nat.cast_nonneg n)
    rw [Nat.cast_sub hError.le, Nat.cast_add]
    nlinarith only [hSparse, hMargin, hCeilScaled]
  have hRatio : (4 * Real.sqrt (Delta : ℝ)) ^ 2 ≤
      64 / (delta ^ 2 * Delta) * (delta * Delta / 2) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hD.le]
    field_simp
    nlinarith
  have hAverage : 2 * (delta ^ 2 * Delta / 256) * (64 / (delta ^ 2 * Delta)) ≤
      1 - 64 / (Delta : ℝ) ^ (1 - 2 * epsilon) := by
    have hCancel : 2 * (delta ^ 2 * Delta / 256) * (64 / (delta ^ 2 * Delta)) = (1 : ℝ) / 2 := by
      field_simp
      ring
    rw [hCancel]
    linarith only [hFractionHalf]
  have hMean : ((Delta + Delta : Nat) : ℝ) * (64 / (Delta : ℝ) ^ (1 - 2 * epsilon) * s) ≤
      (32 / (Delta : ℝ) * (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon)) * n := by
    have hScaled := mul_le_mul_of_nonneg_left hSmall' (show 0 ≤ 32 / (Delta : ℝ) *
      (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon) by positivity)
    rw [Nat.cast_add]
    apply le_of_mul_le_mul_left (a := (Delta : ℝ) ^ (1 - 2 * epsilon)) ?_ hF
    have hIdentity : (Delta : ℝ) ^ (1 - 2 * epsilon) *
        ((32 / (Delta : ℝ) * (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon)) *
          ((s : ℝ) * (4 * (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon)))) = 128 * Delta * s := by
      calc
        _ = (128 * s / (Delta : ℝ)) * ((Delta : ℝ) ^ (1 - 2 * epsilon) *
            ((Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon)) ^ 2) := by ring
        _ = 128 * Delta * s := by
          rw [hMeanProduct]
          field_simp <;> ring
    have hMul := mul_le_mul_of_nonneg_left hScaled hF.le
    rw [hIdentity] at hMul
    convert hMul using 1 <;> field_simp [hF.ne'] <;> ring
  have hSelection : (32 / (Delta : ℝ) * (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon) +
      4 * Real.sqrt (Delta : ℝ) * Real.sqrt (64 / (Delta : ℝ) ^ (1 - 2 * epsilon) *
        (2 * ((Delta + Delta : Nat) : ℝ)))) * ((Delta + Delta : Nat) : ℝ) ≤
      (p : ℝ) * (delta ^ 2 * Delta / 256) := by
    have hReciprocal : 32 / (Delta : ℝ) ≤ 16 := (div_le_iff₀ hD).mpr (by linarith)
    have hLower := mul_le_mul_of_nonneg_right hPuncture
      (show 0 ≤ delta ^ 2 * (Delta : ℝ) / 256 by positivity)
    have hCancel : (40960 / delta ^ 2 * (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon)) *
        (delta ^ 2 * Delta / 256) = 160 * Delta * (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon) := by
      field_simp
      ring
    rw [hCancel] at hLower
    have hRecScaled := mul_le_mul_of_nonneg_right hReciprocal hP.le
    have hRecScaled' := mul_le_mul_of_nonneg_right hRecScaled (show 0 ≤ 2 * (Delta : ℝ) by positivity)
    simp only [Nat.cast_add]
    rw [show 2 * ((Delta : ℝ) + Delta) = 4 * Delta by ring, hRoot]
    have hMixed : 4 * Real.sqrt (Delta : ℝ) * (16 * (Delta : ℝ) ^ epsilon) =
        64 * (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon) := by
      nlinarith only [hMixedRoot]
    rw [hMixed]
    nlinarith only [hRecScaled', hLower]
  exact ⟨hSquareSmall, hFraction, hUnionDensity, hRatio, hAverage, hMean, hSelection⟩

end QEC.Coding.QuantumTanner
