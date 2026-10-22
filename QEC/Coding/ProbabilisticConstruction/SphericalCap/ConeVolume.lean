import QEC.Coding.ProbabilisticConstruction.SphericalCap.ConeSlices
import Mathlib.MeasureTheory.Integral.Prod

namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal

theorem cone_section_area {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (z : ℝ) :
    volume {y : Transverse | axialEquiv.symm (z,y) ∈ axialCone c} =
      (Icc 0 c).indicator (fun z => ENNReal.ofReal (Real.pi * (coneSlopeSq c * z^2))) z +
      (Ioc c 1).indicator (fun z => ENNReal.ofReal (Real.pi * (1-z^2))) z := by
  by_cases hz : z ∈ Icc 0 c
  · have hnot : z ∉ Ioc c 1 := by intro h; exact (not_lt_of_ge hz.2) h.1
    rw [indicator_of_mem hz, indicator_of_notMem hnot, add_zero,
      axialCone_section hc0 hc1.le hz.1 (hz.2.trans hc1.le),
      min_eq_left (coneSlopeSq_mul_le_ball hc0 hc1.le hz.1 hz.2), volume_disk_sqrt]
    exact mul_nonneg (coneSlopeSq_nonneg hc0 hc1.le) (sq_nonneg z)
  · by_cases hz2 : z ∈ Ioc c 1
    · rw [indicator_of_notMem hz, indicator_of_mem hz2, zero_add,
        axialCone_section hc0 hc1.le (hc0.le.trans hz2.1.le) hz2.2,
        min_eq_right (ball_le_coneSlopeSq_mul hc0 hz2.1.le), volume_disk_sqrt]
      nlinarith [hc0.le.trans hz2.1.le, hz2.2]
    · rw [indicator_of_notMem hz, indicator_of_notMem hz2, zero_add,
        axialCone_section_empty hc0, measure_empty]
      simp only [mem_Icc, mem_Ioc, not_and_or, not_le, not_lt] at hz hz2
      rcases hz with hz | hz
      · exact Or.inl hz
      · rcases hz2 with hz2 | hz2
        · exact False.elim ((not_le_of_gt hz) hz2)
        · exact Or.inr hz2

theorem volume_axialCone {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    (volume : Measure Ambient) (axialCone c) =
      ENNReal.ofReal ((2 * Real.pi / 3) * (1-c)) := by
  let f : ℝ → ℝ := fun z => Real.pi * (coneSlopeSq c * z^2)
  let g : ℝ → ℝ := fun z => Real.pi * (1-z^2)
  have hfcont : Continuous f := by fun_prop
  have hgcont : Continuous g := by fun_prop
  have hfi : IntervalIntegrable f volume 0 c := hfcont.intervalIntegrable _ _
  have hgi : IntervalIntegrable g volume c 1 := hgcont.intervalIntegrable _ _
  have hfn : ∀ z ∈ Icc 0 c, 0 ≤ f z := by
    intro z hz
    exact mul_nonneg Real.pi_pos.le
      (mul_nonneg (coneSlopeSq_nonneg hc0 hc1.le) (sq_nonneg _))
  have hgn : ∀ z ∈ Icc c 1, 0 ≤ g z := by
    intro z hz
    apply mul_nonneg Real.pi_pos.le
    have hz0 := hc0.trans_le hz.1
    nlinarith [hz.2]
  have hfint : (∫⁻ z in Icc (0:ℝ) c, ENNReal.ofReal (f z)) =
      ENNReal.ofReal (∫ z in (0:ℝ)..c, f z) := by
    rw [← restrict_Ioc_eq_restrict_Icc,
      ← ofReal_integral_eq_lintegral_ofReal hfi.1,
      ← intervalIntegral.integral_of_le hc0.le]
    exact (ae_restrict_mem measurableSet_Ioc).mono (fun z hz => hfn z ⟨hz.1.le,hz.2⟩)
  have hgint : (∫⁻ z in Ioc c 1, ENNReal.ofReal (g z)) =
      ENNReal.ofReal (∫ z in c..1, g z) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hgi.1,
      ← intervalIntegral.integral_of_le hc1.le]
    exact (ae_restrict_mem measurableSet_Ioc).mono (fun z hz => hgn z ⟨hz.1.le,hz.2⟩)
  have hfnonneg : 0 ≤ ∫ z in (0:ℝ)..c, f z :=
    intervalIntegral.integral_nonneg hc0.le hfn
  have hgnonneg : 0 ≤ ∫ z in c..1, g z :=
    intervalIntegral.integral_nonneg hc1.le hgn
  have hm : MeasurePreserving axialEquiv.symm (volume.prod volume) volume :=
    axialEquiv_measurePreserving.symm
  rw [← hm.measure_preimage_equiv (axialCone c),
    Measure.prod_apply ((measurableSet_axialCone c).preimage axialEquiv.symm.measurable)]
  simp_rw [show ∀ z, volume (Prod.mk z ⁻¹' (axialEquiv.symm ⁻¹' axialCone c)) =
    (Icc 0 c).indicator (fun z => ENNReal.ofReal (f z)) z +
      (Ioc c 1).indicator (fun z => ENNReal.ofReal (g z)) z from
    fun z => cone_section_area hc0 hc1 z]
  rw [lintegral_add_left ((by fun_prop : Measurable fun z => ENNReal.ofReal (f z)).indicator
      measurableSet_Icc), lintegral_indicator measurableSet_Icc,
    lintegral_indicator measurableSet_Ioc, hfint, hgint,
    ← ENNReal.ofReal_add hfnonneg hgnonneg]
  congr 1
  exact cone_slice_integral hc0 hc1

end QEC.Coding.ProbabilisticConstruction.SphericalCap
