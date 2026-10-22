import QEC.Coding.ProbabilisticConstruction.SphericalCap.Measure

namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise

def solidCapCone (u : Sphere) (c : ℝ) : Set Space :=
  {x | ‖x‖ ≤ 1 ∧ c * ‖x‖ ≤ inner ℝ (u : Space) x}

theorem solidCapCone_measurable (u : Sphere) (c : ℝ) :
    MeasurableSet (solidCapCone u c) := by
  change MeasurableSet ({x : Space | ‖x‖ ≤ 1} ∩
    {x | c * ‖x‖ ≤ inner ℝ (u : Space) x})
  exact (isClosed_le continuous_norm continuous_const).measurableSet.inter
    (isClosed_le (continuous_const.mul continuous_norm) (by fun_prop)).measurableSet

theorem openCone_subset_solid (u : Sphere) (c : ℝ) :
    Ioo (0 : ℝ) 1 • ((↑) '' cap u c) ⊆ solidCapCone u c := by
  rintro x ⟨r,hr,y,⟨s,hs,rfl⟩,rfl⟩
  have hn : ‖r • (s : Space)‖ = r := displacement_norm r hr.1.le s
  change ‖r • (s : Space)‖ ≤ 1 ∧
    c * ‖r • (s : Space)‖ ≤ inner ℝ (u : Space) (r • (s : Space))
  rw [hn, real_inner_smul_right]
  exact ⟨hr.2.le, by simpa [mul_comm] using mul_le_mul_of_nonneg_left hs hr.1.le⟩

theorem mem_openCone_of_mem_solid (u : Sphere) (c : ℝ) {x : Space}
    (hx : x ∈ solidCapCone u c) (h0 : x ≠ 0) (h1 : ‖x‖ ≠ 1) :
    x ∈ Ioo (0 : ℝ) 1 • ((↑) '' cap u c) := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr h0
  let s : Sphere := ⟨‖x‖⁻¹ • x, by
    simp only [mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']⟩
  refine ⟨‖x‖, ⟨hn, lt_of_le_of_ne hx.1 h1⟩, (s : Space), ?_, ?_⟩
  · refine ⟨s, ?_, rfl⟩
    change c ≤ inner ℝ (u : Space) (‖x‖⁻¹ • x)
    rw [real_inner_smul_right]
    have h := (div_le_div_iff_of_pos_right hn).mpr hx.2
    simpa [div_eq_mul_inv, mul_comm, mul_assoc, hn.ne'] using h
  · change ‖x‖ • (‖x‖⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]

theorem area_cap_eq_three_volume_solid (u : Sphere) (c : ℝ) :
    area (cap u c) = 3 * (volume : Measure Space) (solidCapCone u c) := by
  rw [area, Measure.toSphere_apply' _ (measurableSet_cap u c)]
  have hd : Module.finrank ℝ Space = 3 := by simp [Space]
  rw [hd]
  congr 1
  apply measure_eq_measure_of_null_diff (openCone_subset_solid u c)
  have hsub : solidCapCone u c \ (Ioo (0 : ℝ) 1 • ((↑) '' cap u c)) ⊆
      sphere (0 : Space) 1 ∪ {0} := by
    intro x hx
    by_cases h0 : x = 0
    · exact Or.inr h0
    · left
      have h1 : ‖x‖ = 1 := by
        by_contra h1
        exact hx.2 (mem_openCone_of_mem_solid u c hx.1 h0 h1)
      simpa only [mem_sphere, dist_zero_right] using h1
  apply measure_mono_null hsub
  exact measure_union_null (Measure.addHaar_sphere volume 0 1) (measure_singleton 0)

end QEC.Coding.ProbabilisticConstruction.SphericalCap
