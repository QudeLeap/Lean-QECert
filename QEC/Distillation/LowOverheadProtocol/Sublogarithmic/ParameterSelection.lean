import QEC.Distillation.LowOverheadProtocol.Sublogarithmic.Entropy
import QEC.Distillation.LowOverheadProtocol.Sublogarithmic.ParameterSequence
import QEC.Distillation.LowOverheadProtocol.Sublogarithmic.BinomialTailAsymptotics

/-!
# HH18 sublogarithmic parameter selection

This module constructs the exact rationally cleared natural parameter sequence
and its analytic finite-count Gamma selector.  It contains no code-construction
object or terminal theorem.
-/

namespace QEC.Distillation.HH18.HH18SublogarithmicEntropy

open Coding.PuncturedReedMuller
open Coding.ReedMuller
open Filter Topology

/-! ## Exact rational clearing and the natural HH18 sequence -/

/-- The doubled cleared `r` coordinate. -/
def parameterR (D j : Nat) : Nat := 2 * D * j

/-- The integral `w = 3rp` coordinate for `p = A/D`. -/
def parameterW (A j : Nat) : Nat := 6 * A * j

/-- The actual HH18 row parameter. -/
def parameterM (D j : Nat) : Nat := 6 * D * j + 1

/-- The exact finite length count. -/
def parameterLength (A D j : Nat) : Nat :=
  binomialTail (parameterM D j) (parameterW A j)

/-- The exact finite logical-dimension exponent count. -/
def parameterDimension (A D j : Nat) : Nat :=
  binomialUpTo (parameterM D j) (parameterW A j)

/-- The exact finite distance count. -/
def parameterDistance (A D j : Nat) : Nat :=
  binomialTail (parameterR D j + 1) (parameterW A j)

/-- The finite source-facing logarithmic ratio. -/
noncomputable def parameterGamma (A D j : Nat) : ℝ :=
  Real.log ((parameterLength A D j : ℝ) / parameterDimension A D j) /
    Real.log (parameterDistance A D j : ℝ)

/-- A rational strictly inside the source window has a positive natural
numerator and denominator, the cleared upper bound, and its exact quotient
representation. -/
theorem rat_num_den_in_window {q : ℚ}
    (hqL : (1 / 6 : ℚ) < q) (hqU : q < (1 / 3 : ℚ)) :
    let A : Nat := q.num.natAbs
    let D : Nat := q.den
    0 < A ∧ 0 < D ∧ 3 * A < D ∧ q = (A : ℚ) / D := by
  dsimp
  have hq0 : 0 < q := lt_trans (by norm_num) hqL
  have hnum : 0 < q.num := Rat.num_pos.mpr hq0
  have hA : 0 < q.num.natAbs := Int.natAbs_pos.mpr hnum.ne'
  have hnum_eq : (q.num.natAbs : ℤ) = q.num :=
    Int.natAbs_of_nonneg hnum.le
  have hnum_rat : (q.num : ℚ) = q.num.natAbs := by
    rw [Nat.cast_natAbs, abs_of_pos]
    exact_mod_cast hnum
  have hq_repr : q = (q.num.natAbs : ℚ) / q.den := by
    calc
      q = (q.num : ℚ) / q.den := q.num_div_den.symm
      _ = (q.num.natAbs : ℚ) / q.den := by rw [hnum_rat]
  have hden_rat : (0 : ℚ) < q.den := by
    exact_mod_cast q.den_pos
  refine ⟨hA, q.den_pos, ?_, hq_repr⟩
  rw [hq_repr] at hqU
  have hnum_lt : (q.num.natAbs : ℚ) < (1 / 3 : ℚ) * q.den :=
    (div_lt_iff₀ hden_rat).mp hqU
  have hthree_lt : (3 : ℚ) * q.num.natAbs < q.den := by
    nlinarith
  exact_mod_cast hthree_lt

/-- The doubled cleared sequence has `m = 3r+1`, the exact rational slope,
and the actual natural-number admissibility condition. -/
theorem parameter_sequence_admissible
    (A D j : Nat) (hA : 0 < A) (hD : 0 < D)
    (hwindow : 3 * A < D) (hj : 0 < j) :
    parameterM D j = 3 * parameterR D j + 1 ∧
      (parameterW A j : ℚ) =
        3 * (parameterR D j : ℚ) * ((A : ℚ) / D) ∧
      Admissible (parameterW A j) (parameterR D j) (parameterM D j) := by
  constructor
  · unfold parameterM parameterR
    ring
  constructor
  · unfold parameterW parameterR
    have hD0 : (D : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hD
    push_cast
    field_simp [hD0]
    ring
  · unfold parameterW parameterR parameterM Admissible
    have hstrict : 12 * A * j < 4 * D * j := by
      have hscaled : (3 * A) * j < D * j :=
        Nat.mul_lt_mul_of_pos_right hwindow hj
      calc
        12 * A * j = 4 * ((3 * A) * j) := by ring
        _ < 4 * (D * j) := Nat.mul_lt_mul_of_pos_left hscaled (by omega)
        _ = 4 * D * j := by ring
    constructor
    · omega
    constructor
    · convert hstrict using 1 <;> ring
    · calc
        2 * (2 * D * j) = 4 * D * j := by ring
        _ ≤ 6 * D * j := Nat.mul_le_mul_right j (by omega)
        _ < 6 * D * j + 1 := Nat.lt_succ_self _

/-! ## Finite binomial sandwiches used by the three count limits -/

private theorem choose_mono_right_le_half {n a b : Nat}
    (hab : a ≤ b) (hb : b ≤ n / 2) :
    Nat.choose n a ≤ Nat.choose n b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hle ih =>
      have hb : b ≤ n / 2 := by omega
      have hlt : b < n / 2 := by omega
      exact (ih hb).trans (Nat.choose_le_succ_of_lt_half_left hlt)

private theorem binomialTail_eq_binomialUpTo_complement {n w : Nat}
    (hw : w < n) :
    binomialTail n w = binomialUpTo n (n - w - 1) := by
  classical
  unfold binomialTail binomialUpTo
  calc
    (∑ i ∈ Finset.Icc (w + 1) n, Nat.choose n i) =
        ∑ i ∈ Finset.Ico (w + 1) (n + 1), Nat.choose n i := by
      rw [Finset.Ico_add_one_right_eq_Icc]
    _ = ∑ i ∈ Finset.Ico (w + 1) (n + 1), Nat.choose n (n - i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      exact (Nat.choose_symm (Nat.lt_succ_iff.mp (Finset.mem_Ico.mp hi).2)).symm
    _ = ∑ i ∈ Finset.Ico 0 (n - w), Nat.choose n i := by
      simpa [Nat.succ_sub_succ_eq_sub] using
        (Finset.sum_Ico_reflect (fun i : Nat => Nat.choose n i) (w + 1)
          (m := n + 1) (n := n) (by omega))
    _ = ∑ i ∈ Finset.Ico 0 (n - w - 1 + 1), Nat.choose n i := by
      have hpos : 0 < n - w := Nat.sub_pos_of_lt hw
      have hwidth : n - w - 1 + 1 = n - w :=
        Nat.sub_add_cancel (Nat.succ_le_iff.mpr hpos)
      rw [hwidth]
    _ = ∑ i ∈ Finset.Icc 0 (n - w - 1), Nat.choose n i := by
      rw [Finset.Ico_add_one_right_eq_Icc]

private theorem binomialUpTo_choose_sandwich {n w : Nat}
    (hw : w ≤ n / 2) :
    Nat.choose n w ≤ binomialUpTo n w ∧
      binomialUpTo n w ≤ (w + 1) * Nat.choose n w := by
  unfold binomialUpTo
  constructor
  · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp)
  · calc
      ∑ i ∈ Finset.Icc 0 w, Nat.choose n i ≤
          ∑ i ∈ Finset.Icc 0 w, Nat.choose n w := by
        apply Finset.sum_le_sum
        intro i hi
        exact choose_mono_right_le_half (Finset.mem_Icc.mp hi).2 hw
      _ = (w + 1) * Nat.choose n w := by simp

private theorem binomialTail_high_choose_sandwich {n w : Nat}
    (hw : w < n) (hhalf : n - w - 1 ≤ n / 2) :
    Nat.choose n (n - w - 1) ≤ binomialTail n w ∧
      binomialTail n w ≤ (n - w) * Nat.choose n (n - w - 1) := by
  rw [binomialTail_eq_binomialUpTo_complement hw]
  have hpos : 0 < n - w := Nat.sub_pos_of_lt hw
  have hwidth : n - w - 1 + 1 = n - w :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hpos)
  simpa [hwidth] using binomialUpTo_choose_sandwich hhalf

private theorem choose_shifted_ray_le_two_choose_ray (s a : Nat)
    (ha : 0 < a) (hhalf : 2 * a ≤ s) (j : Nat) (hj : 0 < j) :
    Nat.choose (s * j + 1) (a * j) ≤ 2 * Nat.choose (s * j) (a * j) := by
  have hak : 0 < a * j := Nat.mul_pos ha hj
  have hhalf_index : a * j - 1 < (s * j) / 2 := by
    have hscaled : 2 * (a * j) ≤ s * j := by
      calc
        2 * (a * j) = (2 * a) * j := by ring
        _ ≤ s * j := Nat.mul_le_mul_right j hhalf
    omega
  have hprev := Nat.choose_le_succ_of_lt_half_left hhalf_index
  have hprev' :
      Nat.choose (s * j) (a * j - 1) ≤ Nat.choose (s * j) (a * j) := by
    simpa [Nat.sub_add_cancel (Nat.succ_le_iff.mpr hak)] using hprev
  rw [Nat.choose_succ_left (s * j) (a * j) hak]
  omega

private theorem binomialUpTo_shifted_choose_sandwich
    (s a : Nat) (hhalf : 2 * a < s) (j : Nat) :
    Nat.choose (s * j + 1) (a * j) ≤ binomialUpTo (s * j + 1) (a * j) ∧
      binomialUpTo (s * j + 1) (a * j) ≤
        (a * j + 1) * Nat.choose (s * j + 1) (a * j) := by
  apply binomialUpTo_choose_sandwich
  by_cases hj : j = 0
  · subst hj
    omega
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj
    have hscaled : 2 * (a * j) < s * j := by
      calc
        2 * (a * j) = (2 * a) * j := by ring
        _ < s * j := Nat.mul_lt_mul_of_pos_right hhalf hjpos
    omega

private theorem binomialTail_high_shifted_choose_sandwich
    (b w : Nat) (hdominant : 2 * b < b + w) (j : Nat) :
    Nat.choose ((b + w) * j + 1) (b * j) ≤
        binomialTail ((b + w) * j + 1) (w * j) ∧
      binomialTail ((b + w) * j + 1) (w * j) ≤
        (b * j + 1) * Nat.choose ((b + w) * j + 1) (b * j) := by
  have htail : w * j < (b + w) * j + 1 := by
    apply Nat.lt_succ_of_le
    rw [Nat.add_mul]
    omega
  have hcomp : (b + w) * j + 1 - w * j - 1 = b * j := by
    rw [Nat.add_mul]
    omega
  have hwidth : (b + w) * j + 1 - w * j = b * j + 1 := by
    rw [Nat.add_mul]
    omega
  have hhalf : (b + w) * j + 1 - w * j - 1 ≤ ((b + w) * j + 1) / 2 := by
    rw [hcomp]
    by_cases hj : j = 0
    · subst hj
      omega
    · have hjpos : 0 < j := Nat.pos_of_ne_zero hj
      have hscaled : 2 * (b * j) < (b + w) * j := by
        calc
          2 * (b * j) = (2 * b) * j := by ring
          _ < (b + w) * j := Nat.mul_lt_mul_of_pos_right hdominant hjpos
      omega
  simpa [hcomp, hwidth] using
    binomialTail_high_choose_sandwich htail hhalf

/-! ## Proportional logarithmic limits from the factorial-ray base -/

private theorem tendsto_log_choose_mul_div (a b : Nat)
    (ha : 0 < a) (hb : 0 < b) :
    Tendsto
      (fun j : Nat => Real.log (Nat.choose ((a + b) * j) (a * j) : ℝ) / j)
      atTop
      (𝓝 ((a + b) * Real.log (a + b) - a * Real.log a - b * Real.log b)) := by
  have hab : 0 < a + b := Nat.add_pos_left ha _
  have hN := HH18BinomialTailAsymptotics.tendsto_log_factorial_mul_div_sub
    (a + b) hab
  have hA := HH18BinomialTailAsymptotics.tendsto_log_factorial_mul_div_sub a ha
  have hB := HH18BinomialTailAsymptotics.tendsto_log_factorial_mul_div_sub b hb
  have hrays : Tendsto
      (fun j : Nat =>
        (Real.log (((a + b) * j).factorial : ℝ) / j - (a + b) * Real.log j) -
          (Real.log ((a * j).factorial : ℝ) / j - a * Real.log j) -
          (Real.log ((b * j).factorial : ℝ) / j - b * Real.log j))
      atTop
      (𝓝 ((a + b) * Real.log (a + b) - a * Real.log a - b * Real.log b)) := by
    convert (hN.sub hA).sub hB using 1
    · ext j
      push_cast
      ring
    · congr 1
      push_cast
      ring
  refine hrays.congr' (eventually_atTop.2 ⟨1, fun j hj => ?_⟩)
  have hk : a * j ≤ (a + b) * j :=
    Nat.mul_le_mul_right j (Nat.le_add_right a b)
  have hsub : (a + b) * j - a * j = b * j := by
    rw [Nat.add_mul, Nat.add_sub_cancel_left]
  have hchoose_pos : (0 : ℝ) < Nat.choose ((a + b) * j) (a * j) := by
    exact_mod_cast Nat.choose_pos hk
  have hfactA_pos : (0 : ℝ) < (a * j).factorial := by positivity
  have hfactB_pos : (0 : ℝ) < (b * j).factorial := by positivity
  have hfactorial :
      (Nat.choose ((a + b) * j) (a * j) : ℝ) * (a * j).factorial *
          (b * j).factorial = ((a + b) * j).factorial := by
    have hfactorial_nat := Nat.choose_mul_factorial_mul_factorial hk
    rw [hsub] at hfactorial_nat
    exact_mod_cast hfactorial_nat
  have hlog_choose :
      Real.log (Nat.choose ((a + b) * j) (a * j) : ℝ) =
        Real.log (((a + b) * j).factorial : ℝ) -
          Real.log ((a * j).factorial : ℝ) -
          Real.log ((b * j).factorial : ℝ) := by
    rw [← hfactorial,
      Real.log_mul (mul_ne_zero hchoose_pos.ne' hfactA_pos.ne')
        hfactB_pos.ne',
      Real.log_mul hchoose_pos.ne' hfactA_pos.ne']
    ring
  have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hj
  change _ = Real.log (Nat.choose ((a + b) * j) (a * j) : ℝ) / (j : ℝ)
  rw [hlog_choose]
  field_simp [hjR]
  ring

private theorem tendsto_log_choose_shifted_ray_div (s a : Nat)
    (ha : 0 < a) (hhalf : 2 * a ≤ s) (L : ℝ)
    (hbase : Tendsto
      (fun j : Nat => Real.log (Nat.choose (s * j) (a * j) : ℝ) / j)
      atTop (𝓝 L)) :
    Tendsto
      (fun j : Nat => Real.log (Nat.choose (s * j + 1) (a * j) : ℝ) / j)
      atTop (𝓝 L) := by
  let base : Nat → ℝ := fun j => Nat.choose (s * j) (a * j)
  let shifted : Nat → ℝ := fun j => Nat.choose (s * j + 1) (a * j)
  have hlog_two_div : Tendsto (fun j : Nat => Real.log 2 / j) atTop (𝓝 0) := by
    exact tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)
  have hdelta : Tendsto
      (fun j : Nat => (Real.log (shifted j) - Real.log (base j)) / j)
      atTop (𝓝 0) := by
    apply squeeze_zero'
    · apply Filter.Eventually.of_forall
      intro j
      have has : a ≤ s := by omega
      have hbase_pos : 0 < base j := by
        dsimp [base]
        exact_mod_cast Nat.choose_pos (Nat.mul_le_mul_right j has)
      have hmono : base j ≤ shifted j := by
        dsimp [base, shifted]
        exact_mod_cast (by
          simpa [Nat.succ_eq_add_one] using Nat.choose_le_succ (s * j) (a * j))
      exact div_nonneg (sub_nonneg.mpr (Real.log_le_log hbase_pos hmono))
        (by positivity)
    · filter_upwards [eventually_ge_atTop (1 : Nat)] with j hj
      have has : a ≤ s := by omega
      have hbase_pos : 0 < base j := by
        dsimp [base]
        exact_mod_cast Nat.choose_pos (Nat.mul_le_mul_right j has)
      have hshift_pos : 0 < shifted j := by
        dsimp [shifted]
        exact_mod_cast Nat.choose_pos
          (Nat.le_trans (Nat.mul_le_mul_right j has) (Nat.le_succ _))
      have hfactor : shifted j ≤ 2 * base j := by
        dsimp [base, shifted]
        exact_mod_cast choose_shifted_ray_le_two_choose_ray s a ha hhalf j
          (Nat.zero_lt_of_lt hj)
      have hlog_factor : Real.log (shifted j) ≤ Real.log (2 * base j) := by
        exact Real.log_le_log hshift_pos hfactor
      have hlog_upper : Real.log (shifted j) - Real.log (base j) ≤ Real.log 2 := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hbase_pos.ne'] at hlog_factor
        linarith
      exact div_le_div_of_nonneg_right hlog_upper (by positivity)
    · exact hlog_two_div
  have hsum : Tendsto
      (fun j : Nat =>
        Real.log (base j) / j + (Real.log (shifted j) - Real.log (base j)) / j)
      atTop (𝓝 L) := by
    simpa using hbase.add hdelta
  refine hsum.congr' (eventually_atTop.2 ⟨1, fun j hj => ?_⟩)
  have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hj
  dsimp [base, shifted] at *
  field_simp
  ring

private theorem tendsto_log_affine_ray_div_zero (a : Nat) :
    Tendsto (fun j : Nat => Real.log (a * j + 1 : ℝ) / j) atTop (𝓝 0) := by
  have hlog_div : Tendsto (fun j : Nat => Real.log (j : ℝ) / j) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
        tendsto_natCast_atTop_atTop
  have hconst_div : Tendsto
      (fun j : Nat => Real.log (a + 1 : ℝ) / j) atTop (𝓝 0) := by
    exact tendsto_const_div_atTop_nhds_zero_nat (Real.log (a + 1 : ℝ))
  have hupper : Tendsto
      (fun j : Nat => Real.log ((a + 1) * j : ℝ) / j) atTop (𝓝 0) := by
    have hsum : Tendsto
        (fun j : Nat => Real.log (a + 1 : ℝ) / j + Real.log (j : ℝ) / j)
        atTop (𝓝 0) := by
      simpa using hconst_div.add hlog_div
    refine hsum.congr'
      (eventually_atTop.2 ⟨1, fun j hj => ?_⟩)
    have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hj
    change _ = Real.log ((a + 1 : ℝ) * (j : ℝ)) / (j : ℝ)
    rw [Real.log_mul (by positivity) (by positivity)]
    field_simp
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop (1 : Nat)] with j hj
    apply div_nonneg
    · apply Real.log_nonneg
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le (a * j))
    · positivity
  · filter_upwards [eventually_ge_atTop (1 : Nat)] with j hj
    have hnat : a * j + 1 ≤ (a + 1) * j := by
      calc
        a * j + 1 ≤ a * j + j := Nat.add_le_add_left hj _
        _ = (a + 1) * j := by ring
    have hlog : Real.log (a * j + 1 : ℝ) ≤ Real.log ((a + 1) * j : ℝ) := by
      apply Real.log_le_log
      · positivity
      · exact_mod_cast hnat
    exact div_le_div_of_nonneg_right hlog (by positivity)
  · exact hupper

private theorem tendsto_log_dominant_sandwich_div
    (m : Nat) (term total : Nat → Nat) (L : ℝ)
    (hterm : Tendsto
      (fun j : Nat => Real.log (term j : ℝ) / j) atTop (𝓝 L))
    (hterm_pos : ∀ j, 0 < term j)
    (hsand : ∀ j, term j ≤ total j ∧ total j ≤ (m * j + 1) * term j) :
    Tendsto (fun j : Nat => Real.log (total j : ℝ) / j) atTop (𝓝 L) := by
  have hlog_lower : ∀ j, Real.log (term j : ℝ) ≤ Real.log (total j : ℝ) := by
    intro j
    have hterm_posR : (0 : ℝ) < term j := by exact_mod_cast hterm_pos j
    have hterm_le_total : (term j : ℝ) ≤ total j := by exact_mod_cast (hsand j).1
    exact Real.log_le_log hterm_posR hterm_le_total
  have hlog_upper : ∀ j,
      Real.log (total j : ℝ) ≤
        Real.log (term j : ℝ) + Real.log (m * j + 1 : ℝ) := by
    intro j
    have hterm_posR : (0 : ℝ) < term j := by exact_mod_cast hterm_pos j
    have hterm_le_total : (term j : ℝ) ≤ total j := by exact_mod_cast (hsand j).1
    have htotal_posR : (0 : ℝ) < total j := lt_of_lt_of_le hterm_posR hterm_le_total
    have htotal_le : (total j : ℝ) ≤ (m * j + 1 : ℝ) * term j := by
      exact_mod_cast (hsand j).2
    have hfactor_pos : (0 : ℝ) < m * j + 1 := by positivity
    calc
      Real.log (total j : ℝ) ≤ Real.log ((m * j + 1 : ℝ) * term j) :=
        Real.log_le_log htotal_posR htotal_le
      _ = Real.log (term j : ℝ) + Real.log (m * j + 1 : ℝ) := by
        rw [Real.log_mul hfactor_pos.ne' hterm_posR.ne']
        ring
  have hdelta : Tendsto
      (fun j : Nat =>
        (Real.log (total j : ℝ) - Real.log (term j : ℝ)) / j)
      atTop (𝓝 0) := by
    apply squeeze_zero'
    · filter_upwards [eventually_ge_atTop (1 : Nat)] with j hj
      exact div_nonneg (sub_nonneg.mpr (hlog_lower j)) (by positivity)
    · filter_upwards [eventually_ge_atTop (1 : Nat)] with j hj
      have hbound :
          Real.log (total j : ℝ) - Real.log (term j : ℝ) ≤
            Real.log (m * j + 1 : ℝ) := by
        linarith [hlog_upper j]
      exact div_le_div_of_nonneg_right hbound (by positivity)
    · exact tendsto_log_affine_ray_div_zero m
  have hsum : Tendsto
      (fun j : Nat =>
        Real.log (term j : ℝ) / j +
          (Real.log (total j : ℝ) - Real.log (term j : ℝ)) / j)
      atTop (𝓝 L) := by
    simpa using hterm.add hdelta
  refine hsum.congr' (eventually_atTop.2 ⟨1, fun j hj => ?_⟩)
  have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hj
  field_simp
  ring

private theorem tendsto_log_binomialUpTo_shifted_ray_div (s a : Nat)
    (ha : 0 < a) (hhalf : 2 * a < s) (L : ℝ)
    (hchoose : Tendsto
      (fun j : Nat => Real.log (Nat.choose (s * j + 1) (a * j) : ℝ) / j)
      atTop (𝓝 L)) :
    Tendsto
      (fun j : Nat => Real.log (binomialUpTo (s * j + 1) (a * j) : ℝ) / j)
      atTop (𝓝 L) := by
  refine tendsto_log_dominant_sandwich_div a
    (fun j => Nat.choose (s * j + 1) (a * j))
    (fun j => binomialUpTo (s * j + 1) (a * j)) L hchoose ?_ ?_
  · intro j
    have has : a ≤ s := by omega
    exact Nat.choose_pos (Nat.le_trans (Nat.mul_le_mul_right j has) (Nat.le_succ _))
  · intro j
    exact binomialUpTo_shifted_choose_sandwich s a hhalf j

private theorem tendsto_log_binomialTail_high_shifted_ray_div (b w : Nat)
    (hb : 0 < b) (hw : 0 < w) (hdominant : 2 * b < b + w) :
    Tendsto
      (fun j : Nat => Real.log (binomialTail ((b + w) * j + 1) (w * j) : ℝ) / j)
      atTop
      (𝓝 ((b + w) * Real.log (b + w) - b * Real.log b - w * Real.log w)) := by
  have hchoose_base := tendsto_log_choose_mul_div b w hb hw
  have hshift : Tendsto
      (fun j : Nat => Real.log (Nat.choose ((b + w) * j + 1) (b * j) : ℝ) / j)
      atTop
      (𝓝 ((b + w) * Real.log (b + w) - b * Real.log b - w * Real.log w)) := by
    apply tendsto_log_choose_shifted_ray_div (b + w) b hb hdominant.le
    simpa using hchoose_base
  refine tendsto_log_dominant_sandwich_div b
    (fun j => Nat.choose ((b + w) * j + 1) (b * j))
    (fun j => binomialTail ((b + w) * j + 1) (w * j))
    ((b + w) * Real.log (b + w) - b * Real.log b - w * Real.log w)
    hshift ?_ ?_
  · intro j
    have hrow : b * j ≤ (b + w) * j := by
      rw [Nat.add_mul]
      omega
    exact Nat.choose_pos (Nat.le_trans hrow (Nat.le_succ _))
  · intro j
    exact binomialTail_high_shifted_choose_sandwich b w hdominant j

/-! ## The three exact count log limits -/

noncomputable def parameterLengthLimit (D : Nat) : ℝ :=
  6 * D * Real.log 2

noncomputable def entropyRay (s a : Nat) : ℝ :=
  s * Real.log s - a * Real.log a - (s - a) * Real.log (s - a)

noncomputable def parameterDimensionLimit (A D : Nat) : ℝ :=
  entropyRay (6 * D) (6 * A)

noncomputable def parameterDistanceLimit (A D : Nat) : ℝ :=
  entropyRay (2 * D) (6 * A)

private theorem central_choose_le_parameterLength (A D j : Nat)
    (hwindow : 3 * A < D) (hj : 0 < j) :
    Nat.choose (6 * D * j + 1) (3 * D * j) ≤ parameterLength A D j := by
  unfold parameterLength parameterM parameterW
  unfold binomialTail
  apply Finset.single_le_sum (fun _ _ => Nat.zero_le _)
  simp only [Finset.mem_Icc]
  have hcenter : 6 * A * j + 1 ≤ 3 * D * j := by
    have hscaled : 3 * A * j < D * j :=
      Nat.mul_lt_mul_of_pos_right hwindow hj
    have htwice : 2 * (3 * A * j) < 2 * (D * j) :=
      Nat.mul_lt_mul_of_pos_left hscaled (by omega)
    calc
      6 * A * j + 1 = 2 * (3 * A * j) + 1 := by ring
      _ ≤ 2 * (D * j) := Nat.succ_le_iff.mpr htwice
      _ ≤ 3 * (D * j) := Nat.mul_le_mul_right (D * j) (by omega)
      _ = 3 * D * j := by ring
  constructor
  · exact hcenter
  · calc
      3 * D * j = 3 * (D * j) := by ring
      _ ≤ 6 * (D * j) := Nat.mul_le_mul_right (D * j) (by omega)
      _ = 6 * D * j := by ring
      _ ≤ 6 * D * j + 1 := Nat.le_succ _

private theorem tendsto_log_two_pow_shifted_ray_div (D : Nat) :
    Tendsto
      (fun j : Nat => Real.log ((2 ^ (6 * D * j + 1) : Nat) : ℝ) / j)
      atTop (𝓝 (parameterLengthLimit D)) := by
  have hzero : Tendsto (fun j : Nat => Real.log 2 / j) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)
  have hmain : Tendsto
      (fun j : Nat => 6 * (D : ℝ) * Real.log 2 + Real.log 2 / j)
      atTop (𝓝 (parameterLengthLimit D)) := by
    simpa [parameterLengthLimit] using
      (tendsto_const_nhds (x := 6 * (D : ℝ) * Real.log 2)).add hzero
  refine hmain.congr' (eventually_atTop.2 ⟨1, fun j hj => ?_⟩)
  have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hj
  push_cast
  rw [Real.log_pow]
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  field_simp

theorem tendsto_log_parameterLength_div (A D : Nat)
    (hD : 0 < D) (hwindow : 3 * A < D) :
    Tendsto
      (fun j : Nat => Real.log (parameterLength A D j : ℝ) / j)
      atTop (𝓝 (parameterLengthLimit D)) := by
  have hcentral_base : Tendsto
      (fun j : Nat =>
        Real.log (Nat.choose ((3 * D + 3 * D) * j) (3 * D * j) : ℝ) / j)
      atTop
      (𝓝 ((((3 * D : Nat) : ℝ) + ((3 * D : Nat) : ℝ)) *
          Real.log (((3 * D : Nat) : ℝ) + ((3 * D : Nat) : ℝ)) -
        ((3 * D : Nat) : ℝ) * Real.log ((3 * D : Nat) : ℝ) -
        ((3 * D : Nat) : ℝ) * Real.log ((3 * D : Nat) : ℝ))) :=
    tendsto_log_choose_mul_div (3 * D) (3 * D) (by omega) (by omega)
  have hcentral_base' : Tendsto
      (fun j : Nat => Real.log (Nat.choose (6 * D * j) (3 * D * j) : ℝ) / j)
      atTop
      (𝓝 (6 * D * Real.log (6 * D) -
        ((3 * D : Nat) : ℝ) * Real.log ((3 * D : Nat) : ℝ) -
        ((3 * D : Nat) : ℝ) * Real.log ((3 * D : Nat) : ℝ))) := by
    have hsum : 3 * D + 3 * D = 6 * D := by omega
    have hsumR : ((3 * D : Nat) : ℝ) + ((3 * D : Nat) : ℝ) = 6 * (D : ℝ) := by
      exact_mod_cast hsum
    rw [hsum] at hcentral_base
    simpa only [hsumR] using hcentral_base
  have hcentral : Tendsto
      (fun j : Nat => Real.log (Nat.choose (6 * D * j + 1) (3 * D * j) : ℝ) / j)
      atTop (𝓝 (parameterLengthLimit D)) := by
    have hshift := tendsto_log_choose_shifted_ray_div (6 * D) (3 * D)
      (by omega) (by omega)
      (6 * D * Real.log (6 * D) -
        ((3 * D : Nat) : ℝ) * Real.log ((3 * D : Nat) : ℝ) -
        ((3 * D : Nat) : ℝ) * Real.log ((3 * D : Nat) : ℝ)) hcentral_base'
    have hlog : Real.log (6 * (D : ℝ)) = Real.log 2 + Real.log (3 * D) := by
      rw [show 6 * (D : ℝ) = 2 * (3 * D) by ring,
        Real.log_mul (by norm_num) (by positivity)]
    have hlimit :
        6 * (D : ℝ) * Real.log (6 * D) -
          ((3 * D : Nat) : ℝ) * Real.log ((3 * D : Nat) : ℝ) -
          ((3 * D : Nat) : ℝ) * Real.log ((3 * D : Nat) : ℝ) =
            parameterLengthLimit D := by
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      unfold parameterLengthLimit
      rw [hlog]
      ring
    rw [← hlimit]
    exact hshift
  have hupper := tendsto_log_two_pow_shifted_ray_div D
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hcentral hupper ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : Nat)] with j hj_one
    have hj : 0 < j := Nat.zero_lt_of_lt hj_one
    have hterm_pos : (0 : ℝ) < Nat.choose (6 * D * j + 1) (3 * D * j) := by
      have hindex : 3 * D * j ≤ 6 * D * j + 1 := by
        have hscale : 3 * (D * j) ≤ 6 * (D * j) :=
          Nat.mul_le_mul_right (D * j) (by omega)
        calc
          3 * D * j = 3 * (D * j) := by ring
          _ ≤ 6 * (D * j) := hscale
          _ = 6 * D * j := by ring
          _ ≤ 6 * D * j + 1 := Nat.le_succ _
      exact_mod_cast Nat.choose_pos hindex
    have hterm_le :
        (Nat.choose (6 * D * j + 1) (3 * D * j) : ℝ) ≤ parameterLength A D j := by
      exact_mod_cast central_choose_le_parameterLength A D j hwindow hj
    exact div_le_div_of_nonneg_right (Real.log_le_log hterm_pos hterm_le)
      (by positivity)
  · filter_upwards [eventually_ge_atTop (1 : Nat)] with j hj_one
    have hj : 0 < j := Nat.zero_lt_of_lt hj_one
    have htail_le : parameterLength A D j ≤ 2 ^ (6 * D * j + 1) := by
      exact
        HH18BinomialTailAsymptotics.binomialTail_le_two_pow
          (6 * D * j + 1) (6 * A * j)
    have htail_pos : (0 : ℝ) < parameterLength A D j := by
      have hindex : 3 * D * j ≤ 6 * D * j + 1 := by
        have hscale : 3 * (D * j) ≤ 6 * (D * j) :=
          Nat.mul_le_mul_right (D * j) (by omega)
        calc
          3 * D * j = 3 * (D * j) := by ring
          _ ≤ 6 * (D * j) := hscale
          _ = 6 * D * j := by ring
          _ ≤ 6 * D * j + 1 := Nat.le_succ _
      have hterm_pos : 0 < Nat.choose (6 * D * j + 1) (3 * D * j) :=
        Nat.choose_pos hindex
      have htail_posNat : 0 < parameterLength A D j := lt_of_lt_of_le hterm_pos
        (central_choose_le_parameterLength A D j hwindow hj)
      exact_mod_cast htail_posNat
    have htail_leR : (parameterLength A D j : ℝ) ≤
        ((2 ^ (6 * D * j + 1) : Nat) : ℝ) := by
      exact_mod_cast htail_le
    exact div_le_div_of_nonneg_right (Real.log_le_log htail_pos htail_leR)
      (by positivity)

theorem tendsto_log_parameterDimension_div (A D : Nat)
    (hA : 0 < A) (hD : 0 < D) (hwindow : 3 * A < D) :
    Tendsto
      (fun j : Nat => Real.log (parameterDimension A D j : ℝ) / j)
      atTop (𝓝 (parameterDimensionLimit A D)) := by
  have hcomp : 0 < D - A := by omega
  have hhalf : 2 * (6 * A) < 6 * D := by omega
  have hbase := tendsto_log_choose_mul_div (6 * A) (6 * (D - A))
    (by omega) (by omega)
  have hsum : 6 * A + 6 * (D - A) = 6 * D := by omega
  have hsumR : ((6 * A : Nat) : ℝ) + ((6 * (D - A) : Nat) : ℝ) =
      6 * (D : ℝ) := by
    exact_mod_cast hsum
  rw [hsum, hsumR] at hbase
  have hshift := tendsto_log_choose_shifted_ray_div (6 * D) (6 * A)
    (by omega) (by omega)
    (6 * (D : ℝ) * Real.log (6 * D) -
      ((6 * A : Nat) : ℝ) * Real.log ((6 * A : Nat) : ℝ) -
      ((6 * (D - A) : Nat) : ℝ) * Real.log ((6 * (D - A) : Nat) : ℝ)) hbase
  have hprefix := tendsto_log_binomialUpTo_shifted_ray_div (6 * D) (6 * A)
    (by omega) hhalf
    (6 * (D : ℝ) * Real.log (6 * D) -
      ((6 * A : Nat) : ℝ) * Real.log ((6 * A : Nat) : ℝ) -
      ((6 * (D - A) : Nat) : ℝ) * Real.log ((6 * (D - A) : Nat) : ℝ)) hshift
  have hlimit :
      6 * (D : ℝ) * Real.log (6 * D) -
        ((6 * A : Nat) : ℝ) * Real.log ((6 * A : Nat) : ℝ) -
        ((6 * (D - A) : Nat) : ℝ) * Real.log ((6 * (D - A) : Nat) : ℝ) =
          parameterDimensionLimit A D := by
    unfold parameterDimensionLimit entropyRay
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    rw [Nat.cast_sub (by omega)]
    ring
  change Tendsto
    (fun j : Nat => Real.log (binomialUpTo (6 * D * j + 1) (6 * A * j) : ℝ) / j)
    atTop (𝓝 (parameterDimensionLimit A D))
  rw [← hlimit]
  exact hprefix

theorem tendsto_log_parameterDistance_div (A D : Nat)
    (hA : 0 < A) (hD : 0 < D) (hwindowL : D < 6 * A)
    (hwindowU : 3 * A < D) :
    Tendsto
      (fun j : Nat => Real.log (parameterDistance A D j : ℝ) / j)
      atTop (𝓝 (parameterDistanceLimit A D)) := by
  let b : Nat := 2 * D - 6 * A
  let w : Nat := 6 * A
  have hb : 0 < b := by
    dsimp [b]
    omega
  have hw : 0 < w := by
    dsimp [w]
    omega
  have hsum : b + w = 2 * D := by
    dsimp [b, w]
    omega
  have hsumR : (b : ℝ) + (w : ℝ) = ((2 * D : Nat) : ℝ) := by
    exact_mod_cast hsum
  have hdominant : 2 * b < b + w := by
    dsimp [b, w]
    omega
  have htail := tendsto_log_binomialTail_high_shifted_ray_div b w hb hw
    hdominant
  rw [hsumR, hsum] at htail
  dsimp [w] at htail
  have hlimit :
      ((2 * D : Nat) : ℝ) * Real.log ((2 * D : Nat) : ℝ) -
        (b : ℝ) * Real.log (b : ℝ) -
        ((6 * A : Nat) : ℝ) * Real.log ((6 * A : Nat) : ℝ) =
          parameterDistanceLimit A D := by
    have hsub : ((2 * D - 6 * A : Nat) : ℝ) =
        2 * (D : ℝ) - 6 * (A : ℝ) := by
      rw [Nat.cast_sub (by omega)]
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    dsimp [b]
    unfold parameterDistanceLimit entropyRay
    rw [hsub]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    ring
  change Tendsto
    (fun j : Nat => Real.log (binomialTail (2 * D * j + 1) (6 * A * j) : ℝ) / j)
    atTop (𝓝 (parameterDistanceLimit A D))
  rw [← hlimit]
  exact htail

/-! ## Entropy normalization and the exact Gamma bridge -/

private theorem entropyRay_eq_mul_binEntropy (s a : Nat)
    (ha : 0 < a) (has : a < s) :
    entropyRay s a = (s : ℝ) * Real.binEntropy ((a : ℝ) / s) := by
  have hs : 0 < s := lt_trans ha has
  have hsub : 0 < s - a := Nat.sub_pos_of_lt has
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hs
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ha
  have hsubR : ((s - a : Nat) : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hsub
  have hcastSub : ((s - a : Nat) : ℝ) = (s : ℝ) - a := by
    rw [Nat.cast_sub has.le]
  have hone_sub : 1 - (a : ℝ) / s = ((s - a : Nat) : ℝ) / s := by
    rw [hcastSub]
    field_simp [hsR]
  have hinv_a : ((a : ℝ) / s)⁻¹ = (s : ℝ) / a := by
    field_simp [hsR, haR]
  have hinv_sub : (((s - a : Nat) : ℝ) / s)⁻¹ = (s : ℝ) / (s - a) := by
    rw [hcastSub]
    field_simp [hsR, hsubR]
  have hlog_sub : Real.log ((s : ℝ) / ((s : ℝ) - a)) =
      Real.log (s : ℝ) - Real.log ((s - a : Nat) : ℝ) := by
    rw [← hcastSub]
    exact Real.log_div hsR hsubR
  unfold entropyRay Real.binEntropy
  rw [hinv_a, hone_sub, hinv_sub,
    Real.log_div hsR haR, hlog_sub]
  rw [hcastSub]
  field_simp [hsR]
  ring

private theorem parameterDimensionLimit_entropy (A D : Nat)
    (hA : 0 < A) (hwindow : 3 * A < D) :
    parameterDimensionLimit A D =
      (6 * D : ℝ) * Real.binEntropy ((A : ℝ) / D) := by
  have hscaled : 6 * A < 6 * D := by omega
  have hentropy := entropyRay_eq_mul_binEntropy (6 * D) (6 * A)
    (by omega) hscaled
  have hD : (D : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (show 0 < D by omega)
  have hscale : ((6 * A : ℝ) / (6 * D : ℝ)) = (A : ℝ) / D := by
    field_simp [hD]
  simpa [parameterDimensionLimit, hscale] using hentropy

private theorem parameterDistanceLimit_entropy (A D : Nat)
    (hA : 0 < A) (hwindow : 3 * A < D) :
    parameterDistanceLimit A D =
      (2 * D : ℝ) * Real.binEntropy (3 * (A : ℝ) / D) := by
  have hscaled : 6 * A < 2 * D := by omega
  have hentropy := entropyRay_eq_mul_binEntropy (2 * D) (6 * A)
    (by omega) hscaled
  have hD : (D : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (show 0 < D by omega)
  have hscale : ((6 * A : ℝ) / (2 * D : ℝ)) = 3 * (A : ℝ) / D := by
    push_cast
    field_simp [hD]
    norm_num
  simpa [parameterDistanceLimit, hscale] using hentropy

/-- The quotient of the three independently derived count exponents is the
same source Gamma formula as in the canonical entropy module. -/
theorem parameter_count_ratio_eq_hh18Gamma (A D : Nat)
    (hA : 0 < A) (hD : 0 < D) (hwindow : 3 * A < D) :
    (parameterLengthLimit D - parameterDimensionLimit A D) /
        parameterDistanceLimit A D =
      hh18Gamma ((A : ℝ) / D) := by
  have hp0 : 0 < (A : ℝ) / D := by positivity
  have hp1 : (A : ℝ) / D < 1 := by
    apply (div_lt_one₀ (by positivity : (0 : ℝ) < D)).mpr
    exact_mod_cast (show A < D by omega)
  have hp30 : 0 < 3 * (A : ℝ) / D := by positivity
  have hp31 : 3 * (A : ℝ) / D < 1 := by
    apply (div_lt_one₀ (by positivity : (0 : ℝ) < D)).mpr
    exact_mod_cast hwindow
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have hentropy3 : Real.binEntropy (3 * (A : ℝ) / D) ≠ 0 :=
    (Real.binEntropy_pos hp30 hp31).ne'
  rw [parameterDimensionLimit_entropy A D hA hwindow,
    parameterDistanceLimit_entropy A D hA hwindow]
  unfold parameterLengthLimit hh18Gamma hh18BinaryEntropy
  field_simp [hlog2, hentropy3]
  ring

/-! ## From the count limits to the finite log ratio -/

private theorem parameter_counts_pos (A D j : Nat)
    (hA : 0 < A) (hD : 0 < D) (hwindow : 3 * A < D) (hj : 0 < j) :
    0 < parameterLength A D j ∧
      0 < parameterDimension A D j ∧
      0 < parameterDistance A D j := by
  have hlength_index : parameterW A j < parameterM D j := by
    unfold parameterW parameterM
    have hscaled : 3 * A * j < D * j :=
      Nat.mul_lt_mul_of_pos_right hwindow hj
    have htwice : 2 * (3 * A * j) < 2 * (D * j) :=
      Nat.mul_lt_mul_of_pos_left hscaled (by omega)
    calc
      6 * A * j = 2 * (3 * A * j) := by ring
      _ < 2 * (D * j) := htwice
      _ ≤ 6 * (D * j) := Nat.mul_le_mul_right (D * j) (by omega)
      _ = 6 * D * j := by ring
      _ < 6 * D * j + 1 := Nat.lt_succ_self _
  have hdistance_index : parameterW A j < parameterR D j + 1 := by
    unfold parameterW parameterR
    have hscaled : 3 * A * j < D * j :=
      Nat.mul_lt_mul_of_pos_right hwindow hj
    have htwice : 2 * (3 * A * j) < 2 * (D * j) :=
      Nat.mul_lt_mul_of_pos_left hscaled (by omega)
    calc
      6 * A * j = 2 * (3 * A * j) := by ring
      _ < 2 * (D * j) := htwice
      _ = 2 * D * j := by ring
      _ < 2 * D * j + 1 := Nat.lt_succ_self _
  constructor
  · unfold parameterLength
    exact lt_of_lt_of_le
      (Nat.choose_pos (Nat.succ_le_iff.mpr hlength_index))
      (HH18BinomialTailAsymptotics.choose_succ_le_tail _ _
        (Nat.succ_le_iff.mpr hlength_index))
  constructor
  · unfold parameterDimension binomialUpTo
    calc
      0 < 1 := by omega
      _ = Nat.choose (parameterM D j) 0 := by simp
      _ ≤ ∑ i ∈ Finset.Icc 0 (parameterW A j), Nat.choose (parameterM D j) i :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp)
  · unfold parameterDistance
    exact lt_of_lt_of_le
      (Nat.choose_pos (Nat.succ_le_iff.mpr hdistance_index))
      (HH18BinomialTailAsymptotics.choose_succ_le_tail _ _
        (Nat.succ_le_iff.mpr hdistance_index))

private theorem tendsto_parameterGamma_of_log_limits
    {A D : Nat} {LN LK LD : ℝ}
    (hN : Tendsto
      (fun j : Nat => Real.log (parameterLength A D j : ℝ) / j) atTop (𝓝 LN))
    (hK : Tendsto
      (fun j : Nat => Real.log (parameterDimension A D j : ℝ) / j) atTop (𝓝 LK))
    (hD : Tendsto
      (fun j : Nat => Real.log (parameterDistance A D j : ℝ) / j) atTop (𝓝 LD))
    (hLD : LD ≠ 0)
    (hpositive : ∀ᶠ j in atTop,
      0 < parameterLength A D j ∧
        0 < parameterDimension A D j ∧ 0 < parameterDistance A D j) :
    Tendsto (parameterGamma A D) atTop (𝓝 ((LN - LK) / LD)) := by
  have hnumerator : Tendsto
      (fun j : Nat =>
        Real.log (parameterLength A D j : ℝ) / j -
          Real.log (parameterDimension A D j : ℝ) / j)
      atTop (𝓝 (LN - LK)) := hN.sub hK
  have hquotient := hnumerator.div hD hLD
  refine hquotient.congr' ?_
  filter_upwards [hpositive, eventually_ge_atTop (1 : Nat)]
    with j hjpos hj_one
  have hj : 0 < j := Nat.zero_lt_of_lt hj_one
  have hjNat : j ≠ 0 := Nat.ne_of_gt hj
  have hjR : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hjNat
  have hN0 : (parameterLength A D j : ℝ) ≠ 0 := by exact_mod_cast hjpos.1.ne'
  have hK0 : (parameterDimension A D j : ℝ) ≠ 0 := by exact_mod_cast hjpos.2.1.ne'
  unfold parameterGamma
  rw [Real.log_div hN0 hK0]
  rw [Pi.div_apply]
  by_cases hz : Real.log (parameterDistance A D j : ℝ) = 0
  · simp [hz]
  · field_simp [hjR, hz]

theorem tendsto_parameterGamma (A D : Nat)
    (hA : 0 < A) (hD : 0 < D) (hwindowL : D < 6 * A)
    (hwindowU : 3 * A < D) :
    Tendsto (parameterGamma A D) atTop
      (𝓝 (hh18Gamma ((A : ℝ) / D))) := by
  have hN := tendsto_log_parameterLength_div A D hD hwindowU
  have hK := tendsto_log_parameterDimension_div A D hA hD hwindowU
  have hDistance := tendsto_log_parameterDistance_div A D hA hD
    hwindowL hwindowU
  have hp30 : 0 < 3 * (A : ℝ) / D := by positivity
  have hp31 : 3 * (A : ℝ) / D < 1 := by
    apply (div_lt_one₀ (by positivity : (0 : ℝ) < D)).mpr
    exact_mod_cast hwindowU
  have hLD : parameterDistanceLimit A D ≠ 0 := by
    rw [parameterDistanceLimit_entropy A D hA hwindowU]
    exact mul_ne_zero (by positivity)
      (Real.binEntropy_pos hp30 hp31).ne'
  have hpositive : ∀ᶠ j in atTop,
      0 < parameterLength A D j ∧
        0 < parameterDimension A D j ∧ 0 < parameterDistance A D j := by
    filter_upwards [eventually_ge_atTop (1 : Nat)] with j hj_one
    exact parameter_counts_pos A D j hA hD hwindowU (Nat.zero_lt_of_lt hj_one)
  have hratio := tendsto_parameterGamma_of_log_limits
    hN hK hDistance hLD hpositive
  rw [parameter_count_ratio_eq_hh18Gamma A D hA hD hwindowU] at hratio
  exact hratio

/-! ## Every-positive-eta selector -/

/-- For every positive tolerance, select a rational slope and a concrete
natural HH18 sequence whose finite count ratio is close to the real source
infimum and is strictly below `1339 / 1500`, hence below one.  The p0 witness
appears only through the already-derived strict upper bound on the infimum. -/
theorem exists_finite_subunit_gamma_selector (eta : ℝ) (heta : 0 < eta) :
    ∃ q : ℚ, ∃ A D j : Nat,
      (1 / 6 : ℚ) < q ∧ q < (1 / 3 : ℚ) ∧
        0 < A ∧ 0 < D ∧ 3 * A < D ∧ 0 < j ∧ q = (A : ℚ) / D ∧
        let r := parameterR D j
        let w := parameterW A j
        let m := parameterM D j
        let n := parameterLength A D j
        let k := parameterDimension A D j
        let d := parameterDistance A D j
        Admissible w r m ∧
          (w : ℚ) = 3 * (r : ℚ) * q ∧
          parameterGamma A D j = Real.log ((n : ℝ) / k) / Real.log d ∧
          |parameterGamma A D j - hh18GammaInf| < eta ∧
          parameterGamma A D j < (1339 / 1500 : ℝ) ∧
          parameterGamma A D j < 1 := by
  let epsilon : ℝ := min (eta / 3) (161 / 1500)
  have hepsilon_pos : 0 < epsilon := by
    dsimp [epsilon]
    exact lt_min (by linarith) (by norm_num)
  have hepsilon_eta : epsilon ≤ eta / 3 := by
    dsimp [epsilon]
    exact min_le_left _ _
  have hepsilon_fixed : epsilon ≤ 161 / 1500 := by
    dsimp [epsilon]
    exact min_le_right _ _
  rcases exists_rat_mem_parameterInterval_hh18Gamma_lt epsilon hepsilon_pos with
    ⟨q, hqI, hqGamma⟩
  have hqIReal : (1 / 6 : ℝ) < (q : ℝ) ∧ (q : ℝ) < (1 / 3 : ℝ) := by
    exact hqI
  have hqL : (1 / 6 : ℚ) < q := by
    apply (Rat.cast_lt (K := ℝ)).mp
    norm_num [Rat.cast_div]
    exact hqIReal.1
  have hqU : q < (1 / 3 : ℚ) := by
    apply (Rat.cast_lt (K := ℝ)).mp
    norm_num [Rat.cast_div]
    exact hqIReal.2
  rcases rat_num_den_in_window hqL hqU with ⟨hA, hD, hwindow, hq⟩
  have hwindowL : q.den < 6 * q.num.natAbs := by
    have hqR : (1 / 6 : ℚ) < (q.num.natAbs : ℚ) / q.den := by
      rw [← hq]
      exact hqL
    have hdenR : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
    have hcleared : (q.den : ℚ) < 6 * q.num.natAbs := by
      have := (lt_div_iff₀ hdenR).mp hqR
      nlinarith
    exact_mod_cast hcleared
  have hqR : (q : ℝ) = (q.num.natAbs : ℝ) / q.den := by
    have hqcast := congrArg (fun x : ℚ => (x : ℝ)) hq
    simpa only [Rat.cast_div, Rat.cast_natCast] using hqcast
  have hgammaLimit := tendsto_parameterGamma q.num.natAbs q.den
    hA hD hwindowL hwindow
  have hgammaLimitQ : Tendsto (parameterGamma q.num.natAbs q.den) atTop
      (𝓝 (hh18Gamma (q : ℝ))) := by
    simpa only [hqR] using hgammaLimit
  have hnearBall : ∀ᶠ j in atTop,
      parameterGamma q.num.natAbs q.den j ∈
        Metric.ball (hh18Gamma (q : ℝ)) epsilon :=
    hgammaLimitQ.eventually (Metric.ball_mem_nhds _ hepsilon_pos)
  have hnear : ∀ᶠ j in atTop,
      |parameterGamma q.num.natAbs q.den j - hh18Gamma (q : ℝ)| < epsilon := by
    filter_upwards [hnearBall] with j hj
    simpa [Metric.mem_ball, Real.dist_eq] using hj
  rcases eventually_atTop.1 hnear with ⟨J, hJ⟩
  let j : Nat := max 1 J
  have hj : 0 < j := by
    dsimp [j]
    omega
  have hjlarge : J ≤ j := by
    dsimp [j]
    exact Nat.le_max_right _ _
  have hnear_j :
      |parameterGamma q.num.natAbs q.den j - hh18Gamma (q : ℝ)| < epsilon :=
    hJ j hjlarge
  have hqInf : hh18GammaInf ≤ hh18Gamma (q : ℝ) := by
    change sInf hh18GammaSet ≤ hh18Gamma (q : ℝ)
    apply csInf_le hh18GammaSet_bddBelow
    exact ⟨(q : ℝ), hqI, rfl⟩
  have hInfStrict : hh18GammaInf < (339 / 500 : ℝ) :=
    hh18GammaInf_lt_339_div_500
  have hqInfClose : |hh18Gamma (q : ℝ) - hh18GammaInf| < epsilon := by
    rw [abs_of_nonneg (sub_nonneg.mpr hqInf)]
    linarith
  have habs : |parameterGamma q.num.natAbs q.den j - hh18GammaInf| < eta := by
    calc
      |parameterGamma q.num.natAbs q.den j - hh18GammaInf| =
          |(parameterGamma q.num.natAbs q.den j - hh18Gamma (q : ℝ)) +
            (hh18Gamma (q : ℝ) - hh18GammaInf)| := by ring
      _ ≤ |parameterGamma q.num.natAbs q.den j - hh18Gamma (q : ℝ)| +
            |hh18Gamma (q : ℝ) - hh18GammaInf| := abs_add_le _ _
      _ < epsilon + epsilon := add_lt_add hnear_j hqInfClose
      _ < eta := by nlinarith
  have hgammaUpper : parameterGamma q.num.natAbs q.den j <
      hh18Gamma (q : ℝ) + epsilon := by
    have h := abs_lt.mp hnear_j
    linarith
  have hsubunit : parameterGamma q.num.natAbs q.den j <
      (1339 / 1500 : ℝ) := by
    linarith
  have hsubunit_one : parameterGamma q.num.natAbs q.den j < 1 := by
    calc
      parameterGamma q.num.natAbs q.den j < (1339 / 1500 : ℝ) := hsubunit
      _ < 1 := by norm_num
  rcases parameter_sequence_admissible q.num.natAbs q.den j hA hD hwindow hj
    with ⟨hm, hslope, hadmissible⟩
  have hslopeQ :
      (parameterW q.num.natAbs j : ℚ) =
        3 * (parameterR q.den j : ℚ) * q := by
    calc
      (parameterW q.num.natAbs j : ℚ) =
          3 * (parameterR q.den j : ℚ) *
            ((q.num.natAbs : ℚ) / q.den) := hslope
      _ = 3 * (parameterR q.den j : ℚ) * q := by rw [← hq]
  refine ⟨q, q.num.natAbs, q.den, j, hqL, hqU, hA, hD, hwindow, hj, hq, ?_⟩
  change
    Admissible (parameterW q.num.natAbs j) (parameterR q.den j)
        (parameterM q.den j) ∧
      (parameterW q.num.natAbs j : ℚ) =
        3 * (parameterR q.den j : ℚ) * q ∧
      parameterGamma q.num.natAbs q.den j =
        Real.log
          ((parameterLength q.num.natAbs q.den j : ℝ) /
            (parameterDimension q.num.natAbs q.den j : ℝ)) /
          Real.log (parameterDistance q.num.natAbs q.den j : ℝ) ∧
      |parameterGamma q.num.natAbs q.den j - hh18GammaInf| < eta ∧
      parameterGamma q.num.natAbs q.den j < (1339 / 1500 : ℝ) ∧
      parameterGamma q.num.natAbs q.den j < 1
  exact ⟨hadmissible, hslopeQ, rfl, habs, hsubunit, hsubunit_one⟩

end QEC.Distillation.HH18.HH18SublogarithmicEntropy
