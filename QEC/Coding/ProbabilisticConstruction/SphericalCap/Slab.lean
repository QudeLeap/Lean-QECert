import QEC.Coding.ProbabilisticConstruction.SphericalCap.Zones

namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped ENNReal

-- Off-tree continuation; concrete slab theorem derives its own area hypothesis.
theorem capLaw_le_of_area_le (u : Sphere) {c A : ℝ} (hc0 : -1 < c) (hc1 : c < 1)
    {E : Set Sphere} (hE : MeasurableSet E) (hA : area E ≤ ENNReal.ofReal A) :
    capLaw u c E ≤ ENNReal.ofReal (A / (2 * Real.pi * (1-c))) := by
  have hd : 0 < 2 * Real.pi * (1-c) := mul_pos (by positivity) (sub_pos.mpr hc1)
  calc
    capLaw u c E = (area (cap u c))⁻¹ * area (E ∩ cap u c) := by
      rw [capLaw,Measure.smul_apply,Measure.restrict_apply hE,smul_eq_mul]
    _ ≤ (area (cap u c))⁻¹ * ENNReal.ofReal A := by
      exact mul_le_mul' le_rfl ((measure_mono inter_subset_left).trans hA)
    _ = ENNReal.ofReal (A / (2 * Real.pi * (1-c))) := by
      rw [area_cap u hc0 hc1,ENNReal.ofReal_div_of_pos hd,div_eq_mul_inv,mul_comm]

theorem area_zone_le (n : Sphere) {a b : ℝ} (hab : a ≤ b) :
    area (zone n a b) ≤ ENNReal.ofReal (2 * Real.pi * (b-a)) := by
  rw [area_zone n hab]
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact max_le (sub_nonneg.mpr hab)
    (sub_le_sub (min_le_right _ _) (le_max_right _ _))

def slab (n : Sphere) (d h : ℝ) : Set Space :=
  {p | |inner ℝ (n : Space) p - d| ≤ h}

theorem measurableSet_slab (n : Sphere) (d h : ℝ) : MeasurableSet (slab n d h) :=
  (isClosed_le (by fun_prop) continuous_const).measurableSet

theorem displacement_slab_preimage {R : ℝ} (hR : 0 < R) (n : Sphere) (d h : ℝ) :
    (fun s : Sphere => R • (s : Space)) ⁻¹' slab n d h =
      zone n ((d-h)/R) ((d+h)/R) := by
  ext s
  simp only [slab,zone,mem_preimage,mem_setOf_eq,real_inner_smul_right,abs_le]
  constructor
  · rintro ⟨h1,h2⟩
    exact ⟨(div_le_iff₀ hR).mpr (by nlinarith), (le_div_iff₀ hR).mpr (by nlinarith)⟩
  · rintro ⟨h1,h2⟩
    have h1 := (div_le_iff₀ hR).mp h1
    have h2 := (le_div_iff₀ hR).mp h2
    constructor <;> nlinarith

theorem capDisplacementLaw_slab_le {R c h : ℝ} (hR : 0 < R)
    (u n : Sphere) (hc0 : -1 < c) (hc1 : c < 1) (d : ℝ) (hh : 0 ≤ h) :
    capDisplacementLaw R u c (slab n d h) ≤ ENNReal.ofReal (2*h/(R*(1-c))) := by
  rw [capDisplacementLaw,Measure.map_apply (by fun_prop) (measurableSet_slab n d h),
    displacement_slab_preimage hR]
  have hab : (d-h)/R ≤ (d+h)/R := (div_le_div_iff_of_pos_right hR).mpr (by linarith)
  have he : 2 * Real.pi * ((d+h)/R - (d-h)/R) = 4 * Real.pi * h / R := by ring
  have hb := area_zone_le n hab
  rw [he] at hb
  have hbound := capLaw_le_of_area_le u hc0 hc1 (measurableSet_zone n _ _) hb
  have hfactor : (4 * Real.pi * h / R) / (2 * Real.pi * (1-c)) =
      2*h/(R*(1-c)) := by field_simp [Real.pi_ne_zero, hR.ne', (sub_pos.mpr hc1).ne']; ring
  rwa [hfactor] at hbound

end QEC.Coding.ProbabilisticConstruction.SphericalCap
