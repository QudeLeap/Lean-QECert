import QEC.Distillation.LowOverheadProtocol.Sublogarithmic.ParameterSelection
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# HH18 sublogarithmic target schedule

This module derives the exact double-power target schedule from the selected
binomial distance and converts the selected count ratio into a target-log
real-power bound.  It constructs no protocol family, count attachment, or
terminal theorem.
-/

namespace QEC.Distillation.HH18.HH18SublogarithmicEntropy

open Coding.PuncturedReedMuller
open Coding.ReedMuller
open Filter Topology

/-! ## Double-power target error and exact logarithmic inversion -/

/-- The explicit target used for an integer concatenation depth. -/
def doublePowerTarget (q : ℝ) (d z : Nat) : ℝ := q ^ (d ^ z)

/-- The exponent determined by one selected code block. -/
noncomputable def concatenationExponent (n k d : Nat) : ℝ :=
  Real.log ((n : ℝ) / k) / Real.log d

/-- If 0 < q < 1 and 1 < d, every finite target is strictly between zero
and one. This supplies the logarithm domain facts required by the cost bound.
-/
private theorem doublePowerTarget_pos_lt_one {q : ℝ} {d z : Nat}
    (hq0 : 0 < q) (hq1 : q < 1) (hd : 1 < d) :
    0 < doublePowerTarget q d z ∧ doublePowerTarget q d z < 1 := by
  unfold doublePowerTarget
  have hd0 : 0 < d := by omega
  have hdz : 0 < d ^ z := pow_pos hd0 _
  constructor
  · exact pow_pos hq0 _
  · exact pow_lt_one₀ hq0.le hq1 (ne_of_gt hdz)

/-- The double-power target tends to zero. The proof composes growth of the
natural exponent d^z with geometric decay of q^t; it is not a protocol
convergence assertion. -/
private theorem tendsto_doublePowerTarget_zero {q : ℝ} {d : Nat}
    (hq0 : 0 < q) (hq1 : q < 1) (hd : 1 < d) :
    Tendsto (fun z : Nat => doublePowerTarget q d z) atTop (𝓝 0) := by
  unfold doublePowerTarget
  have hpow : Tendsto (fun t : Nat => q ^ t) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1
  have hgrowth : Tendsto (fun z : Nat => d ^ z) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hd
  exact hpow.comp hgrowth

/-- The logarithm of the reciprocal target is exactly one geometric depth
factor times the fixed positive logarithm log (1/q). -/
private theorem log_inv_doublePowerTarget {q : ℝ} {d z : Nat}
    (_hq0 : 0 < q) :
    Real.log (1 / doublePowerTarget q d z) =
      (d : ℝ) ^ z * Real.log (1 / q) := by
  unfold doublePowerTarget
  rw [one_div, Real.log_inv, Real.log_pow, one_div, Real.log_inv]
  push_cast
  ring

/-- Dividing the target logarithm by log d exposes the precise geometric
depth factor.  This is the direct target-log/depth relation used before the
real-power conversion. -/
private theorem log_inv_doublePowerTarget_div_log_d {q : ℝ} {d z : Nat}
    (hq0 : 0 < q) (hd : 1 < d) :
    Real.log (1 / doublePowerTarget q d z) / Real.log d =
      (d : ℝ) ^ z * (Real.log (1 / q) / Real.log d) := by
  have hdReal : 1 < (d : ℝ) := by exact_mod_cast hd
  have hlogd : 0 < Real.log d := Real.log_pos hdReal
  rw [log_inv_doublePowerTarget hq0]
  field_simp [ne_of_gt hlogd]

/-- The first exact inversion: the geometric depth base is recovered from the
logarithm of the reciprocal target. -/
private theorem doublePowerTarget_log_inversion {q : ℝ} {d z : Nat}
    (hq0 : 0 < q) (hq1 : q < 1) :
    (d : ℝ) ^ z =
      Real.log (1 / doublePowerTarget q d z) / Real.log (1 / q) := by
  have hone_div : 1 < (1 / q) := by
    apply (lt_div_iff₀ hq0).2
    nlinarith
  have hlogq : 0 < Real.log (1 / q) := Real.log_pos hone_div
  rw [log_inv_doublePowerTarget hq0]
  field_simp [ne_of_gt hlogq]

/-- The second exact inversion recovers the real-valued depth from the target.
It records the precise two-log relation rather than using an asymptotic
inverse. -/
private theorem depth_from_doublePowerTarget {q : ℝ} {d z : Nat}
    (hq0 : 0 < q) (hq1 : q < 1) (hd : 1 < d) :
    (z : ℝ) =
      Real.log
        (Real.log (1 / doublePowerTarget q d z) / Real.log (1 / q)) /
          Real.log d := by
  have hdReal : 1 < (d : ℝ) := by exact_mod_cast hd
  have hlogd : 0 < Real.log d := Real.log_pos hdReal
  rw [← doublePowerTarget_log_inversion hq0 hq1]
  rw [Real.log_pow]
  field_simp [ne_of_gt hlogd]

/-! ## Target-log real-power conversion -/

/-- A positive selected code ratio is the real-power of the depth base raised
to the code exponent. This is the arithmetic core behind the overhead
conversion. -/
private theorem ratio_pow_eq_rpow_depth_base {n k d z : Nat}
    (hn : 0 < n) (hk : 0 < k) (hd : 1 < d) :
    ((n : ℝ) / k) ^ z =
      Real.rpow ((d : ℝ) ^ z) (concatenationExponent n k d) := by
  have hratio : 0 < (n : ℝ) / k := by
    exact div_pos (Nat.cast_pos.mpr hn) (Nat.cast_pos.mpr hk)
  have hdReal : 1 < (d : ℝ) := by exact_mod_cast hd
  have hdPos : 0 < (d : ℝ) := lt_trans zero_lt_one hdReal
  have hbase : 0 < (d : ℝ) ^ z := pow_pos hdPos _
  have hlogd : 0 < Real.log d := Real.log_pos hdReal
  calc
    ((n : ℝ) / k) ^ z = Real.rpow ((n : ℝ) / k) (z : ℝ) :=
      (Real.rpow_natCast _ _).symm
    _ = Real.exp (Real.log ((n : ℝ) / k) * (z : ℝ)) :=
      Real.rpow_def_of_pos hratio _
    _ = Real.exp
        (Real.log ((d : ℝ) ^ z) * concatenationExponent n k d) := by
      congr 1
      rw [Real.log_pow]
      unfold concatenationExponent
      field_simp [ne_of_gt hlogd]
    _ = Real.rpow ((d : ℝ) ^ z) (concatenationExponent n k d) :=
      (Real.rpow_def_of_pos hbase _).symm

/-- The direct count ratio has an exact expression in terms of the target
logarithm. The fixed denominator is what later becomes part of the overhead
coefficient. -/
private theorem ratio_pow_eq_target_log_rpow_quotient {q : ℝ} {n k d z : Nat}
    (hq0 : 0 < q) (hq1 : q < 1) (hn : 0 < n) (hk : 0 < k) (hd : 1 < d) :
    ((n : ℝ) / k) ^ z =
      Real.rpow (Real.log (1 / doublePowerTarget q d z))
          (concatenationExponent n k d) /
        Real.rpow (Real.log (1 / q)) (concatenationExponent n k d) := by
  have hdReal : 1 < (d : ℝ) := by exact_mod_cast hd
  have hone_div : 1 < (1 / q) := by
    apply (lt_div_iff₀ hq0).2
    nlinarith
  have hlogq : 0 < Real.log (1 / q) := Real.log_pos hone_div
  have hrpowq : 0 < Real.rpow (Real.log (1 / q))
      (concatenationExponent n k d) :=
    Real.rpow_pos_of_pos hlogq _
  have hmul :
      Real.rpow ((d : ℝ) ^ z * Real.log (1 / q))
          (concatenationExponent n k d) =
        Real.rpow ((d : ℝ) ^ z) (concatenationExponent n k d) *
          Real.rpow (Real.log (1 / q)) (concatenationExponent n k d) := by
    simpa only [Real.rpow_eq_pow] using
      (Real.mul_rpow (by positivity : 0 ≤ (d : ℝ) ^ z) hlogq.le
        (z := concatenationExponent n k d))
  rw [ratio_pow_eq_rpow_depth_base hn hk hd]
  rw [log_inv_doublePowerTarget hq0]
  calc
    Real.rpow ((d : ℝ) ^ z) (concatenationExponent n k d) =
        (Real.rpow ((d : ℝ) ^ z) (concatenationExponent n k d) *
          Real.rpow (Real.log (1 / q)) (concatenationExponent n k d)) /
          Real.rpow (Real.log (1 / q)) (concatenationExponent n k d) := by
      field_simp [ne_of_gt hrpowq]
    _ = Real.rpow ((d : ℝ) ^ z * Real.log (1 / q))
          (concatenationExponent n k d) /
        Real.rpow (Real.log (1 / q)) (concatenationExponent n k d) := by
      exact congrArg
        (fun x : ℝ => x / Real.rpow (Real.log (1 / q)) (concatenationExponent n k d))
        hmul.symm

/-- The coefficient arising from a uniform positive lower bound sigma on
success probability. Its only nonconstant factor is fixed once the code and
input rate are selected. -/
private noncomputable def rawSuccessAdjustmentCoefficient
    (q sigma : ℝ) (n k d : Nat) : ℝ :=
  (1 / sigma) /
    Real.rpow (Real.log (1 / q)) (concatenationExponent n k d)

/-- The coefficient is strictly positive on the stated numeric domain. -/
private theorem rawSuccessAdjustmentCoefficient_pos {q sigma : ℝ} {n k d : Nat}
    (hq0 : 0 < q) (hq1 : q < 1) (hsigma : 0 < sigma) :
    0 < rawSuccessAdjustmentCoefficient q sigma n k d := by
  have hone_div : 1 < (1 / q) := by
    apply (lt_div_iff₀ hq0).2
    nlinarith
  have hlogq : 0 < Real.log (1 / q) := Real.log_pos hone_div
  unfold rawSuccessAdjustmentCoefficient
  exact div_pos (one_div_pos.mpr hsigma)
    (Real.rpow_pos_of_pos hlogq _)

/-- A real direct count ratio divided by any actual success probability bounded
below by sigma is controlled by the target logarithm. All count and success
quantities remain explicit arguments. -/
private theorem ratio_pow_div_success_le_target_rpow
    {q sigma success : ℝ} {n k d z : Nat}
    (hq0 : 0 < q) (hq1 : q < 1) (hsigma : 0 < sigma)
    (hsuccess : sigma ≤ success) (hn : 0 < n) (hk : 0 < k) (hd : 1 < d) :
    ((n : ℝ) / k) ^ z / success ≤
      rawSuccessAdjustmentCoefficient q sigma n k d *
        Real.rpow (Real.log (1 / doublePowerTarget q d z))
          (concatenationExponent n k d) := by
  have hratioNonneg : 0 ≤ ((n : ℝ) / k) ^ z := by positivity
  have hone_div : 1 < (1 / q) := by
    apply (lt_div_iff₀ hq0).2
    nlinarith
  have hlogq : 0 < Real.log (1 / q) := Real.log_pos hone_div
  have hrpowq : 0 < Real.rpow (Real.log (1 / q))
      (concatenationExponent n k d) :=
    Real.rpow_pos_of_pos hlogq _
  calc
    ((n : ℝ) / k) ^ z / success ≤ ((n : ℝ) / k) ^ z / sigma :=
      div_le_div_of_nonneg_left hratioNonneg hsigma hsuccess
    _ = rawSuccessAdjustmentCoefficient q sigma n k d *
        Real.rpow (Real.log (1 / doublePowerTarget q d z))
          (concatenationExponent n k d) := by
      rw [ratio_pow_eq_target_log_rpow_quotient hq0 hq1 hn hk hd]
      unfold rawSuccessAdjustmentCoefficient
      field_simp [ne_of_gt hrpowq, ne_of_gt hsigma]
/-! ## Actual selected-count nontriviality -/

/-- The selected finite length is positive, derived from its binomial tail. -/
theorem selected_parameter_length_pos (A D j : Nat)
    (_hD : 0 < D) (hwindow : 3 * A < D) (hj : 0 < j) :
    0 < parameterLength A D j := by
  have hindex : parameterW A j < parameterM D j := by
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
  unfold parameterLength
  exact lt_of_lt_of_le
    (Nat.choose_pos (Nat.succ_le_iff.mpr hindex))
    (HH18BinomialTailAsymptotics.choose_succ_le_tail _ _
      (Nat.succ_le_iff.mpr hindex))

/-- The selected finite dimension count is positive by its concrete prefix. -/
theorem selected_parameter_dimension_pos (A D j : Nat) :
    0 < parameterDimension A D j := by
  unfold parameterDimension binomialUpTo
  calc
    0 < 1 := by omega
    _ = Nat.choose (parameterM D j) 0 := by simp
    _ ≤ ∑ i ∈ Finset.Icc 0 (parameterW A j), Nat.choose (parameterM D j) i :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp)

/-- The selected binomial-tail distance is genuinely larger than one. -/
theorem selected_parameter_distance_one_lt (A D j : Nat)
    (hD : 0 < D) (hwindow : 3 * A < D) (hj : 0 < j) :
    1 < parameterDistance A D j := by
  have hscaled : 3 * A * j < D * j :=
    Nat.mul_lt_mul_of_pos_right hwindow hj
  have hindex : parameterW A j + 1 ≤ parameterR D j := by
    unfold parameterW parameterR
    have htwice : 2 * (3 * A * j) < 2 * (D * j) :=
      Nat.mul_lt_mul_of_pos_left hscaled (by omega)
    calc
      6 * A * j + 1 = 2 * (3 * A * j) + 1 := by ring
      _ ≤ 2 * (D * j) := Nat.succ_le_iff.mpr htwice
      _ = 2 * D * j := by ring
  have hrow : 1 < parameterR D j + 1 := by
    have hDj : 0 < D * j := Nat.mul_pos hD hj
    unfold parameterR
    have htwoDj : 0 < 2 * (D * j) := Nat.mul_pos (by omega) hDj
    calc
      1 ≤ 2 * (D * j) := htwoDj
      _ < 2 * (D * j) + 1 := Nat.lt_succ_self _
      _ = 2 * D * j + 1 := by ring
  calc
    1 < parameterR D j + 1 := hrow
    _ = Nat.choose (parameterR D j + 1) (parameterR D j) := by
      exact (Nat.choose_succ_self_right _).symm
    _ ≤ parameterDistance A D j := by
      unfold parameterDistance binomialTail
      apply Finset.single_le_sum (fun i _ => Nat.zero_le _)
      exact Finset.mem_Icc.mpr ⟨hindex, Nat.le_succ _⟩

/-- Positivity and distance nontriviality are derived from the exact selected
counts, not supplied by a schedule conclusion. -/
theorem selected_parameter_counts_nontrivial (A D j : Nat)
    (hD : 0 < D) (hwindow : 3 * A < D) (hj : 0 < j) :
    0 < parameterLength A D j ∧ 0 < parameterDimension A D j ∧
      1 < parameterDistance A D j :=
  ⟨selected_parameter_length_pos A D j hD hwindow hj,
    selected_parameter_dimension_pos A D j,
    selected_parameter_distance_one_lt A D j hD hwindow hj⟩

/-! ## Selected exact double-power target -/

/-- The target at depth z, using the exact selected binomial-tail distance. -/
def selectedDoublePowerTarget (q : ℝ) (A D j z : Nat) : ℝ :=
  doublePowerTarget q (parameterDistance A D j) z

theorem selectedDoublePowerTarget_pos_lt_one {q : ℝ} {A D j z : Nat}
    (hq0 : 0 < q) (hq1 : q < 1) (hD : 0 < D)
    (hwindow : 3 * A < D) (hj : 0 < j) :
    0 < selectedDoublePowerTarget q A D j z ∧
      selectedDoublePowerTarget q A D j z < 1 := by
  simpa [selectedDoublePowerTarget] using
    doublePowerTarget_pos_lt_one hq0 hq1
      (selected_parameter_distance_one_lt A D j hD hwindow hj)

/-- The genuine double-power target tends to zero for the selected distance. -/
theorem tendsto_selectedDoublePowerTarget_zero {q : ℝ} {A D j : Nat}
    (hq0 : 0 < q) (hq1 : q < 1) (hD : 0 < D)
    (hwindow : 3 * A < D) (hj : 0 < j) :
    Tendsto (fun z : Nat => selectedDoublePowerTarget q A D j z)
      atTop (𝓝 0) := by
  simpa [selectedDoublePowerTarget] using
    tendsto_doublePowerTarget_zero hq0 hq1
      (selected_parameter_distance_one_lt A D j hD hwindow hj)

theorem log_inv_selectedDoublePowerTarget {q : ℝ} {A D j z : Nat}
    (hq0 : 0 < q) :
    Real.log (1 / selectedDoublePowerTarget q A D j z) =
      (parameterDistance A D j : ℝ) ^ z * Real.log (1 / q) := by
  simpa [selectedDoublePowerTarget] using
    log_inv_doublePowerTarget (q := q) (d := parameterDistance A D j)
      (z := z) hq0

theorem depth_from_selectedDoublePowerTarget {q : ℝ} {A D j z : Nat}
    (hq0 : 0 < q) (hq1 : q < 1) (hD : 0 < D)
    (hwindow : 3 * A < D) (hj : 0 < j) :
    (z : ℝ) =
      Real.log
        (Real.log (1 / selectedDoublePowerTarget q A D j z) /
          Real.log (1 / q)) / Real.log (parameterDistance A D j) := by
  simpa [selectedDoublePowerTarget] using
    depth_from_doublePowerTarget (q := q) (d := parameterDistance A D j)
      (z := z) hq0 hq1
      (selected_parameter_distance_one_lt A D j hD hwindow hj)

/-! ## Selected target-log real-power conversion -/

theorem selected_ratio_pow_eq_rpow_depth_base (A D j z : Nat)
    (hD : 0 < D) (hwindow : 3 * A < D) (hj : 0 < j) :
    ((parameterLength A D j : ℝ) / parameterDimension A D j) ^ z =
      Real.rpow ((parameterDistance A D j : ℝ) ^ z)
        (concatenationExponent (parameterLength A D j)
          (parameterDimension A D j) (parameterDistance A D j)) := by
  rcases selected_parameter_counts_nontrivial A D j hD hwindow hj with
    ⟨hn, hk, hd⟩
  exact ratio_pow_eq_rpow_depth_base hn hk hd

theorem selected_ratio_pow_eq_target_log_rpow_quotient
    {q : ℝ} {A D j z : Nat} (hq0 : 0 < q) (hq1 : q < 1)
    (hD : 0 < D) (hwindow : 3 * A < D) (hj : 0 < j) :
    ((parameterLength A D j : ℝ) / parameterDimension A D j) ^ z =
      Real.rpow (Real.log (1 / selectedDoublePowerTarget q A D j z))
          (concatenationExponent (parameterLength A D j)
            (parameterDimension A D j) (parameterDistance A D j)) /
        Real.rpow (Real.log (1 / q))
          (concatenationExponent (parameterLength A D j)
            (parameterDimension A D j) (parameterDistance A D j)) := by
  rcases selected_parameter_counts_nontrivial A D j hD hwindow hj with
    ⟨hn, hk, hd⟩
  simpa [selectedDoublePowerTarget] using
    ratio_pow_eq_target_log_rpow_quotient (q := q)
      (n := parameterLength A D j) (k := parameterDimension A D j)
      (d := parameterDistance A D j) (z := z) hq0 hq1 hn hk hd

/-! ## Later successful-output adjustment boundary -/

/-- The later successful-output adapter must supply its actual lower success
bound.  This theorem does not identify, attach, or package any counts. -/
noncomputable def selectedSuccessAdjustmentCoefficient (q sigma : ℝ)
    (A D j : Nat) : ℝ :=
  rawSuccessAdjustmentCoefficient q sigma (parameterLength A D j)
    (parameterDimension A D j) (parameterDistance A D j)

theorem selectedSuccessAdjustmentCoefficient_pos {q sigma : ℝ} {A D j : Nat}
    (hq0 : 0 < q) (hq1 : q < 1) (hsigma : 0 < sigma) :
    0 < selectedSuccessAdjustmentCoefficient q sigma A D j := by
  unfold selectedSuccessAdjustmentCoefficient
  exact rawSuccessAdjustmentCoefficient_pos hq0 hq1 hsigma

/-- A later adapter can apply this only after supplying an actual success lower
bound for its own construction; no count or error attachment occurs here. -/
theorem selected_ratio_pow_div_success_le_target_rpow
    {q sigma success : ℝ} {A D j z : Nat}
    (hq0 : 0 < q) (hq1 : q < 1) (hsigma : 0 < sigma)
    (hsuccess : sigma ≤ success) (hD : 0 < D)
    (hwindow : 3 * A < D) (hj : 0 < j) :
    ((parameterLength A D j : ℝ) / parameterDimension A D j) ^ z / success ≤
      selectedSuccessAdjustmentCoefficient q sigma A D j *
        Real.rpow (Real.log (1 / selectedDoublePowerTarget q A D j z))
          (concatenationExponent (parameterLength A D j)
            (parameterDimension A D j) (parameterDistance A D j)) := by
  rcases selected_parameter_counts_nontrivial A D j hD hwindow hj with
    ⟨hn, hk, hd⟩
  simpa [selectedDoublePowerTarget, selectedSuccessAdjustmentCoefficient] using
    ratio_pow_div_success_le_target_rpow (q := q) (sigma := sigma)
      (success := success) (n := parameterLength A D j)
      (k := parameterDimension A D j) (d := parameterDistance A D j) (z := z)
      hq0 hq1 hsigma hsuccess hn hk hd

end QEC.Distillation.HH18.HH18SublogarithmicEntropy
