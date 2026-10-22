import QEC.Coding.ProbabilisticConstruction.SphericalCap.ConeBridge
import QEC.Coding.ProbabilisticConstruction.SphericalCap.ConeVolume
import QEC.Coding.ProbabilisticConstruction.SphericalCap.LevelSets

namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise

theorem solidCapCone_reflection (u v : Sphere) (c : ℝ) :
    solidCapCone u c = axisReflection (u : Space) (v : Space) ⁻¹' solidCapCone v c := by
  ext x
  have hu : axisReflection (u : Space) (v : Space) (u : Space) = (v : Space) :=
    axisReflection_apply _ _ (by simp)
  have hi := (axisReflection (u : Space) (v : Space)).inner_map_map (u : Space) x
  rw [hu] at hi
  simp only [solidCapCone, mem_setOf_eq, mem_preimage,
    LinearIsometryEquiv.norm_map, hi]

theorem area_cap_axis_invariant (u v : Sphere) (c : ℝ) :
    area (cap u c) = area (cap v c) := by
  rw [area_cap_eq_three_volume_solid, area_cap_eq_three_volume_solid,
    solidCapCone_reflection u v c]
  congr 1
  exact (axisReflection_measurePreserving (u : Space) (v : Space)).measure_preimage
    (solidCapCone_measurable v c).nullMeasurableSet

noncomputable def north : Sphere :=
  ⟨EuclideanSpace.basisFun (Fin 3) ℝ 0, by
    simpa only [mem_sphere, dist_zero_right] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).norm_eq_one 0⟩

theorem solidCapCone_north (c : ℝ) : solidCapCone north c = axialCone c := by
  ext x
  simp only [solidCapCone, axialCone, north, EuclideanSpace.basisFun_inner]

theorem area_cap_of_pos (u : Sphere) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    area (cap u c) = ENNReal.ofReal (2 * Real.pi * (1-c)) := by
  rw [area_cap_axis_invariant u north c, area_cap_eq_three_volume_solid,
    solidCapCone_north, volume_axialCone hc0 hc1]
  have he : (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) := by norm_num
  rw [he, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)]
  congr 1
  ring

theorem ambient_latitude_zero (u : Sphere) (c : ℝ) :
    (volume : Measure Space) {x | c * ‖x‖ = inner ℝ (u : Space) x} = 0 := by
  have he : {x : Space | c * ‖x‖ = inner ℝ (u : Space) x} =
      axisReflection (u : Space) (north : Space) ⁻¹' {x : Space | c * ‖x‖ = x 0} := by
    ext x
    have hu : axisReflection (u : Space) (north : Space) (u : Space) = (north : Space) :=
      axisReflection_apply _ _ (by simp)
    have hi := (axisReflection (u : Space) (north : Space)).inner_map_map (u : Space) x
    rw [hu] at hi
    have hcoord : inner ℝ (north : Space) (axisReflection (u : Space) (north : Space) x) =
        (axisReflection (u : Space) (north : Space) x) 0 := by
      simp only [north,EuclideanSpace.basisFun_inner]
    rw [hcoord] at hi
    simp only [mem_setOf_eq,mem_preimage,LinearIsometryEquiv.norm_map,hi]
  rw [he, (axisReflection_measurePreserving (u : Space) (north : Space)).measure_preimage]
  · exact axial_level_zero c
  · exact (isClosed_eq (continuous_const.mul continuous_norm)
      (by fun_prop)).measurableSet.nullMeasurableSet

theorem area_latitude_zero (u : Sphere) (c : ℝ) :
    area {s : Sphere | inner ℝ (u : Space) (s : Space) = c} = 0 := by
  have hmeas : MeasurableSet {s : Sphere | inner ℝ (u : Space) (s : Space) = c} :=
    (isClosed_eq (by fun_prop) continuous_const).measurableSet
  rw [area,Measure.toSphere_apply' _ hmeas]
  have hsub : Ioo (0:ℝ) 1 • ((↑) '' {s : Sphere | inner ℝ (u : Space) (s : Space) = c}) ⊆
      {x : Space | c * ‖x‖ = inner ℝ (u : Space) x} := by
    rintro x ⟨r,hr,y,⟨s,hs,rfl⟩,rfl⟩
    change c * ‖r • (s : Space)‖ = inner ℝ (u : Space) (r • (s : Space))
    rw [displacement_norm r hr.1.le,real_inner_smul_right,hs,mul_comm]
  rw [measure_mono_null hsub (ambient_latitude_zero u c),mul_zero]

theorem area_univ : area univ = ENNReal.ofReal (4 * Real.pi) := by
  have hd : Module.finrank ℝ Space = 3 := by simp [Space]
  rw [area,Measure.toSphere_apply_univ,hd,EuclideanSpace.volume_ball_fin_three]
  simp only [ENNReal.ofReal_one,one_pow,one_mul]
  norm_num only
  have he : (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) := by norm_num
  rw [he, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)]
  congr 1
  ring

/-- Antipodal axis; this preserves surface area by the proved reflection formula. -/
def opposite (u : Sphere) : Sphere := ⟨-(u : Space), by simpa using u.property⟩

theorem cap_opposite_union (u : Sphere) (c : ℝ) :
    cap u c ∪ cap (opposite u) (-c) = univ := by
  ext s
  simp only [cap,opposite,mem_union,mem_setOf_eq,inner_neg_left,mem_univ,iff_true]
  rcases le_total c (inner ℝ (u : Space) (s : Space)) with h | h
  · exact Or.inl h
  · exact Or.inr (neg_le_neg h)

theorem cap_opposite_inter (u : Sphere) (c : ℝ) :
    cap u c ∩ cap (opposite u) (-c) =
      {s : Sphere | inner ℝ (u : Space) (s : Space) = c} := by
  ext s
  simp only [cap,opposite,mem_inter_iff,mem_setOf_eq,inner_neg_left]
  constructor
  · rintro ⟨h1,h2⟩
    linarith
  · intro h
    constructor <;> linarith

theorem area_cap_add_opposite (u : Sphere) (c : ℝ) :
    area (cap u c) + area (cap (opposite u) (-c)) = ENNReal.ofReal (4 * Real.pi) := by
  have h := measure_union_add_inter (μ := area) (cap u c)
    (measurableSet_cap (opposite u) (-c))
  rw [cap_opposite_union,cap_opposite_inter,area_latitude_zero,add_zero,area_univ] at h
  exact h.symm

/-- Exact surface area of a closed spherical cap, for the entire cutoff interval. -/
theorem area_cap (u : Sphere) {c : ℝ} (hc0 : -1 < c) (hc1 : c < 1) :
    area (cap u c) = ENNReal.ofReal (2 * Real.pi * (1-c)) := by
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · have hother := area_cap_of_pos (opposite u) (c := -c) (by linarith) (by linarith)
    have hs := area_cap_add_opposite u c
    rw [hother] at hs
    apply (ENNReal.toReal_eq_toReal_iff' (area_cap_ne_top u c) ENNReal.ofReal_ne_top).mp
    have hr := congrArg ENNReal.toReal hs
    rw [ENNReal.toReal_add (area_cap_ne_top u c) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 4 * Real.pi),
      ENNReal.toReal_ofReal (mul_nonneg (by positivity : 0 ≤ 2 * Real.pi) (by linarith : 0 ≤ 1 - -c))] at hr
    rw [ENNReal.toReal_ofReal (mul_nonneg (by positivity : 0 ≤ 2 * Real.pi) (by linarith : 0 ≤ 1-c))]
    linarith
  · have hs := area_cap_add_opposite u 0
    rw [neg_zero,area_cap_axis_invariant (opposite u) u 0] at hs
    apply (ENNReal.toReal_eq_toReal_iff' (area_cap_ne_top u 0) ENNReal.ofReal_ne_top).mp
    have hr := congrArg ENNReal.toReal hs
    rw [ENNReal.toReal_add (area_cap_ne_top u 0) (area_cap_ne_top u 0),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 4 * Real.pi)] at hr
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.pi * (1-(0:ℝ)))]
    linarith
  · exact area_cap_of_pos u hc hc1

theorem cos_mem_open_unit {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    -1 < Real.cos θ ∧ Real.cos θ < 1 := by
  constructor
  · simpa using Real.cos_lt_cos_of_nonneg_of_le_pi hθ0.le le_rfl hθπ
  · simpa using Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hθπ.le hθ0

theorem area_cap_angle (u : Sphere) {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    area (cap u (Real.cos θ)) = ENNReal.ofReal (2*Real.pi*(1-Real.cos θ)) :=
  area_cap u (cos_mem_open_unit hθ0 hθπ).1 (cos_mem_open_unit hθ0 hθπ).2

theorem capLaw_angle_isProbabilityMeasure (u : Sphere) {θ : ℝ}
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi) : IsProbabilityMeasure (capLaw u (Real.cos θ)) :=
  capLaw_isProbabilityMeasure u (cos_mem_open_unit hθ0 hθπ).2

end QEC.Coding.ProbabilisticConstruction.SphericalCap
