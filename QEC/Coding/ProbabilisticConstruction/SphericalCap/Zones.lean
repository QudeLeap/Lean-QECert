import QEC.Coding.ProbabilisticConstruction.SphericalCap.Area

namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped ENNReal

theorem height_mem_Icc (u s : Sphere) : inner ℝ (u : Space) (s : Space) ∈ Icc (-1:ℝ) 1 := by
  have h := abs_real_inner_le_norm (u : Space) (s : Space)
  simpa only [norm_coe,mul_one,abs_le,mem_Icc] using h

noncomputable def capHeight (c : ℝ) : ℝ := max 0 (1-max (-1) c)

theorem area_cap_all (u : Sphere) (c : ℝ) :
    area (cap u c) = ENNReal.ofReal (2 * Real.pi * capHeight c) := by
  by_cases hlow : c ≤ -1
  · have he : cap u c = univ := by
      ext s
      simp only [cap,mem_setOf_eq,mem_univ,iff_true]
      exact hlow.trans (height_mem_Icc u s).1
    rw [he,area_univ]
    congr 1
    simp [capHeight,max_eq_left hlow] <;> ring
  · by_cases hhigh : 1 ≤ c
    · have hs : cap u c ⊆ {s : Sphere | inner ℝ (u : Space) (s : Space) = 1} := by
        intro s h
        exact le_antisymm (height_mem_Icc u s).2 (hhigh.trans h)
      rw [measure_mono_null hs (area_latitude_zero u 1)]
      have hh : capHeight c = 0 := by
        simp only [capHeight,max_eq_right (by linarith : (-1:ℝ) ≤ c),
          max_eq_left (by linarith : 1-c ≤ 0)]
      simp [hh]
    · have hc0 : -1 < c := lt_of_not_ge hlow
      have hc1 : c < 1 := lt_of_not_ge hhigh
      rw [area_cap u hc0 hc1]
      simp only [capHeight,max_eq_right hc0.le,max_eq_right (by linarith : 0 ≤ 1-c)]

def zone (u : Sphere) (a b : ℝ) : Set Sphere :=
  {s | a ≤ inner ℝ (u : Space) (s : Space) ∧ inner ℝ (u : Space) (s : Space) ≤ b}

theorem measurableSet_zone (u : Sphere) (a b : ℝ) : MeasurableSet (zone u a b) := by
  change MeasurableSet ({s : Sphere | a ≤ inner ℝ (u : Space) (s : Space)} ∩
    {s : Sphere | inner ℝ (u : Space) (s : Space) ≤ b})
  exact (measurableSet_cap u a).inter
    (isClosed_le (by fun_prop) continuous_const).measurableSet

theorem zone_ae_cap_difference (u : Sphere) (a b : ℝ) :
    zone u a b =ᵐ[area] (cap u a \ cap u b : Set Sphere) := by
  have hnot : ∀ᵐ (s : Sphere) ∂area, inner ℝ (u : Space) (s : Space) ≠ b := by
    apply ae_iff.mpr
    simpa only [not_not] using area_latitude_zero u b
  filter_upwards [hnot] with s hs
  apply propext
  change (a ≤ inner ℝ (u : Space) (s : Space) ∧ inner ℝ (u : Space) (s : Space) ≤ b) ↔
    (a ≤ inner ℝ (u : Space) (s : Space) ∧ ¬ b ≤ inner ℝ (u : Space) (s : Space))
  rw [not_le]
  exact and_congr_right (fun _ => le_iff_lt_or_eq.trans (or_iff_left hs))

theorem capHeight_difference {a b : ℝ} (hab : a ≤ b) :
    capHeight a - capHeight b = max 0 (min 1 b - max (-1) a) := by
  simp only [capHeight,max_def,min_def]
  split_ifs <;> linarith

theorem area_zone (u : Sphere) {a b : ℝ} (hab : a ≤ b) :
    area (zone u a b) = ENNReal.ofReal (2 * Real.pi * max 0 (min 1 b - max (-1) a)) := by
  have hsub : cap u b ⊆ cap u a := fun s hs => hab.trans hs
  have hnonneg : 0 ≤ 2 * Real.pi * capHeight b :=
    mul_nonneg (by positivity) (show 0 ≤ capHeight b from le_max_left _ _)
  rw [measure_congr (zone_ae_cap_difference u a b),
    measure_diff hsub (measurableSet_cap u b).nullMeasurableSet (area_cap_ne_top u b),
    area_cap_all,area_cap_all,
    ← ENNReal.ofReal_sub _ hnonneg]
  congr 1
  rw [← mul_sub,capHeight_difference hab]

end QEC.Coding.ProbabilisticConstruction.SphericalCap
