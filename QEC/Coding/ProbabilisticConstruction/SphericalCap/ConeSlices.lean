import QEC.Coding.ProbabilisticConstruction.SphericalCap.AxialCoordinates
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Axial slices of a spherical cone

For a positive height cutoff `c`, a unit-ball cone has disk slices. Their
squared radii are quadratic on either side of the crossover height `c`.
This supplies an elementary Fubini route to spherical cap area.
-/

namespace QEC.Coding.ProbabilisticConstruction.SphericalCap

open MeasureTheory Metric Set
open scoped ENNReal

/-- Squared transverse slope of the cone for a positive cosine cutoff. -/
noncomputable def coneSlopeSq (c : ℝ) : ℝ := (1 - c ^ 2) / c ^ 2

theorem coneSlopeSq_nonneg {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    0 ≤ coneSlopeSq c := by
  unfold coneSlopeSq
  apply div_nonneg
  · nlinarith
  · positivity

/-- The cone inequality is a disk inequality at each fixed axial height. -/
theorem cone_slice_iff {c z q : ℝ} (hc : 0 < c) (hq : 0 ≤ q) :
    c * Real.sqrt (z ^ 2 + q ^ 2) ≤ z ↔
      0 ≤ z ∧ q ^ 2 ≤ coneSlopeSq c * z ^ 2 := by
  have hs : 0 ≤ z ^ 2 + q ^ 2 := by positivity
  have hr : 0 ≤ Real.sqrt (z ^ 2 + q ^ 2) := Real.sqrt_nonneg _
  have he := Real.sq_sqrt hs
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  constructor
  · intro h
    have hz : 0 ≤ z := le_trans (mul_nonneg hc.le hr) h
    refine ⟨hz, ?_⟩
    have hsq : c ^ 2 * (z ^ 2 + q ^ 2) ≤ z ^ 2 := by
      have hsq := (sq_le_sq₀ (mul_nonneg hc.le hr) hz).mpr h
      simpa only [mul_pow, he] using hsq
    rw [coneSlopeSq, div_mul_eq_mul_div, le_div_iff₀ hc2]
    nlinarith
  · rintro ⟨hz, hq2⟩
    rw [coneSlopeSq, div_mul_eq_mul_div, le_div_iff₀ hc2] at hq2
    apply (sq_le_sq₀ (mul_nonneg hc.le hr) hz).mp
    rw [mul_pow, he]
    nlinarith

/-- The cone is the active radial constraint below the cutoff height. -/
theorem coneSlopeSq_mul_le_ball {c z : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hz0 : 0 ≤ z) (hzc : z ≤ c) :
    coneSlopeSq c * z ^ 2 ≤ 1 - z ^ 2 := by
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc0
  rw [coneSlopeSq, div_mul_eq_mul_div, div_le_iff₀ hc2]
  nlinarith

/-- The ball is the active radial constraint above the cutoff height. -/
theorem ball_le_coneSlopeSq_mul {c z : ℝ} (hc0 : 0 < c) (hcz : c ≤ z) :
    1 - z ^ 2 ≤ coneSlopeSq c * z ^ 2 := by
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc0
  rw [coneSlopeSq, div_mul_eq_mul_div, le_div_iff₀ hc2]
  nlinarith

/-- Exact two-dimensional slice area, including the radius-zero degeneracy. -/
theorem volume_disk_sqrt {a : ℝ} (ha : 0 ≤ a) :
    volume (closedBall (0 : EuclideanSpace ℝ (Fin 2)) (Real.sqrt a)) =
      ENNReal.ofReal (Real.pi * a) := by
  rw [EuclideanSpace.volume_closedBall_fin_two, ← ENNReal.ofReal_pow,
    Real.sq_sqrt ha, ← ENNReal.ofReal_mul ha]
  · congr 1
    ring
  · positivity

/-- The closed solid cone in the unit ball, aligned with coordinate zero. -/
def axialCone (c : ℝ) : Set Ambient :=
  {x | ‖x‖ ≤ 1 ∧ c * ‖x‖ ≤ x 0}

theorem measurableSet_axialCone (c : ℝ) : MeasurableSet (axialCone c) := by
  change MeasurableSet ({x : Ambient | ‖x‖ ≤ 1} ∩ {x | c * ‖x‖ ≤ x 0})
  exact (isClosed_le continuous_norm continuous_const).measurableSet.inter
    (isClosed_le (continuous_const.mul continuous_norm) (by fun_prop)).measurableSet

/-- The two constraints on the transverse disk are simultaneously exact. -/
theorem axialCone_section {c z : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    {y : Transverse | axialEquiv.symm (z, y) ∈ axialCone c} =
      closedBall 0 (Real.sqrt (min (coneSlopeSq c * z ^ 2) (1 - z ^ 2))) := by
  ext y
  have hnorm := norm_sq_axial (axialEquiv.symm (z, y))
  simp only [MeasurableEquiv.apply_symm_apply] at hnorm
  have hfst : (axialEquiv.symm (z, y)) 0 = z := by
    change (axialEquiv (axialEquiv.symm (z, y))).1 = z
    rw [MeasurableEquiv.apply_symm_apply]
  have hroot : ‖axialEquiv.symm (z, y)‖ = Real.sqrt (z ^ 2 + ‖y‖ ^ 2) := by
    rw [← hnorm, Real.sqrt_sq (norm_nonneg _)]
  have hmin : 0 ≤ min (coneSlopeSq c * z ^ 2) (1 - z ^ 2) := by
    apply le_min
    · exact mul_nonneg (coneSlopeSq_nonneg hc0 hc1) (sq_nonneg _)
    · nlinarith
  simp only [mem_setOf_eq, axialCone, hfst, hroot, mem_closedBall, dist_zero_right,
    Real.le_sqrt (norm_nonneg _) hmin, le_min_iff]
  rw [cone_slice_iff hc0 (norm_nonneg y)]
  have hsq : 0 ≤ z ^ 2 + ‖y‖ ^ 2 := by positivity
  have he := Real.sq_sqrt hsq
  have hr := Real.sqrt_nonneg (z ^ 2 + ‖y‖ ^ 2)
  constructor
  · rintro ⟨hb, _, hc⟩
    exact ⟨hc, by nlinarith⟩
  · rintro ⟨hc, hb⟩
    exact ⟨by nlinarith, hz0, hc⟩

theorem axialCone_section_empty {c z : ℝ} (hc0 : 0 < c)
    (hz : z < 0 ∨ 1 < z) :
    {y : Transverse | axialEquiv.symm (z, y) ∈ axialCone c} = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro y h
  have hnorm := norm_sq_axial (axialEquiv.symm (z, y))
  simp only [MeasurableEquiv.apply_symm_apply] at hnorm
  have hfst : (axialEquiv.symm (z, y)) 0 = z := by
    change (axialEquiv (axialEquiv.symm (z, y))).1 = z
    rw [MeasurableEquiv.apply_symm_apply]
  change ‖axialEquiv.symm (z, y)‖ ≤ 1 ∧
    c * ‖axialEquiv.symm (z, y)‖ ≤ (axialEquiv.symm (z, y)) 0 at h
  rw [hfst] at h
  rcases hz with hz | hz
  · exact (not_le_of_gt hz) ((mul_nonneg hc0.le (norm_nonneg _)).trans h.2)
  · nlinarith [norm_nonneg (axialEquiv.symm (z, y)), sq_nonneg ‖y‖]

/-- Integrating the two polynomial slices gives the solid-cone volume. -/
theorem cone_slice_integral {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    (∫ z in (0 : ℝ)..c, Real.pi * (coneSlopeSq c * z ^ 2)) +
      (∫ z in c..1, Real.pi * (1 - z ^ 2)) =
        (2 * Real.pi / 3) * (1 - c) := by
  have h0 : c ≠ 0 := ne_of_gt hc0
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub intervalIntegrable_const (intervalIntegral.intervalIntegrable_pow 2)]
  simp only [intervalIntegral.integral_const, integral_pow, sub_zero,
    zero_pow (by decide : 3 ≠ 0), one_pow, smul_eq_mul]
  unfold coneSlopeSq
  field_simp
  <;> ring

end QEC.Coding.ProbabilisticConstruction.SphericalCap
