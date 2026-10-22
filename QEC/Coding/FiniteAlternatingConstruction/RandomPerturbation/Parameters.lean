import QEC.Coding.ProbabilisticConstruction.SphericalCap.Area
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Explicit existence of perturbation parameters

These are conservative internal constants for [BDL26, Section 3]. They do not
certify the paper's printed numerical example. Density is selected before the
local dependency count, and the scale is selected last.
-/

namespace QEC.Coding.BDL26RandomPerturbation

open QEC.Coding.ProbabilisticConstruction.SphericalCap

/-- The side estimate uses angle one third, not the weaker width angle one sixth. -/
theorem side_chord_sine : (1 : ℝ) / 6 ≤ 2 * Real.sin (1 / 6) := by
  have h := Real.sin_gt_sub_cube (x := (1 : ℝ) / 6) (by norm_num)
  linarith

noncomputable def widthFactor : ℝ := 1 - Real.cos (1 / 6)

theorem widthFactor_pos : 0 < widthFactor := by
  have hpi := Real.two_le_pi
  have hc := (cos_mem_open_unit (θ := (1 : ℝ) / 6) (by norm_num) (by linarith)).2
  exact sub_pos.mpr hc

/-- Choose an integer cap scale with positive source width; no numeric witness is assumed. -/
theorem exists_cap_integer : ∃ m : ℕ, 2 ≤ m ∧ 1 < 6 * (m : ℝ) * widthFactor := by
  obtain ⟨m, hm⟩ := exists_nat_gt (max 2 (1 / (6 * widthFactor)))
  have hm2 : (2 : ℝ) < m := lt_of_le_of_lt (le_max_left _ _) hm
  have hmdiv : 1 / (6 * widthFactor) < (m : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hm
  have hp : 0 < 6 * widthFactor := mul_pos (by norm_num) widthFactor_pos
  have hmprod := (div_lt_iff₀ hp).mp hmdiv
  refine ⟨m, ?_, ?_⟩
  · exact_mod_cast hm2.le
  · nlinarith

/-- Every sufficiently large chosen integer satisfies the cap and width conditions. -/
theorem cap_integer_bounds {m : ℕ} (hm : 2 ≤ m)
    (hw : 1 < 6 * (m : ℝ) * widthFactor) :
    1 < (m : ℝ) ∧ 1 < 2 * (m : ℝ) ∧ 2 * (m : ℝ) < 6 * m ∧
      0 < 6 * (m : ℝ) * widthFactor - 1 ∧
      0 < 1 / (12 * (m : ℝ)) ∧ 1 / (12 * (m : ℝ)) < Real.pi := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : 0 < 12 * (m : ℝ) := by positivity
  have hθ : (1 : ℝ) / (12 * m) ≤ 1 := (div_le_iff₀ hp).mpr (by linarith)
  have hpi := Real.two_le_pi
  refine ⟨by linarith, by linarith, by linarith, by linarith, by positivity, ?_⟩
  linarith

/-- A density can be selected above both the target and the deterministic handoff. -/
theorem exists_input_density (tPrime handoff : ℝ) :
    ∃ t : ℝ, 0 < t ∧ tPrime < t ∧ handoff < t := by
  refine ⟨max 0 (max tPrime handoff) + 1, ?_, ?_, ?_⟩
  · have := le_max_left (0 : ℝ) (max tPrime handoff); linarith
  · have := (le_max_left tPrime handoff).trans (le_max_right 0 (max tPrime handoff))
    linarith
  · have := (le_max_right tPrime handoff).trans (le_max_right 0 (max tPrime handoff))
    linarith

/-- With four-triangle events the decay threshold is linear, so a concrete maximum suffices. -/
noncomputable def perturbationScale (alpha probabilityConstant : ℝ) (D : ℕ) : ℝ :=
  max 1 (max (13 / (2 * alpha + 1)) (4 * probabilityConstant * (D + 1)))

theorem perturbationScale_bounds {alpha probabilityConstant : ℝ} (ha : 0 ≤ alpha) (D : ℕ) :
    1 ≤ perturbationScale alpha probabilityConstant D ∧
      13 ≤ (2 * alpha + 1) * perturbationScale alpha probabilityConstant D ∧
      4 * probabilityConstant * (D + 1) ≤ perturbationScale alpha probabilityConstant D := by
  have hp : 0 < 2 * alpha + 1 := by linarith
  have hfirst := le_max_left (1 : ℝ)
    (max (13 / (2 * alpha + 1)) (4 * probabilityConstant * (D + 1)))
  have hsecond := (le_max_left (13 / (2 * alpha + 1))
    (4 * probabilityConstant * (D + 1))).trans (le_max_right (1 : ℝ) _)
  have hthird := (le_max_right (13 / (2 * alpha + 1))
    (4 * probabilityConstant * (D + 1))).trans (le_max_right (1 : ℝ) _)
  refine ⟨hfirst, ?_, hthird⟩
  have hs := (div_le_iff₀ hp).mp hsecond
  simpa [perturbationScale, mul_comm] using hs

/-- Integral scale choice makes the later finite lattice cubes explicit. -/
theorem exists_integer_scale {alpha probabilityConstant : ℝ} (ha : 0 ≤ alpha) (D : ℕ) :
    ∃ lambda : ℕ, 1 ≤ lambda ∧ 13 ≤ (2*alpha+1)*(lambda : ℝ) ∧
      4*probabilityConstant*(D+1) ≤ (lambda : ℝ) := by
  obtain ⟨lambda,hl⟩ := exists_nat_gt (perturbationScale alpha probabilityConstant D)
  have hb := perturbationScale_bounds (probabilityConstant := probabilityConstant) ha D
  refine ⟨lambda, ?_, ?_, hb.2.2.trans hl.le⟩
  · exact_mod_cast hb.1.trans hl.le
  · exact hb.2.1.trans (mul_le_mul_of_nonneg_left hl.le (by linarith))

end QEC.Coding.BDL26RandomPerturbation
