import QEC.Coding.ProbabilisticConstruction.SphericalCap.ConeSlices
import Mathlib.MeasureTheory.Integral.Prod

namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal

theorem axial_level_zero_of_ne_zero {c : ℝ} (hc : c ≠ 0) :
    (volume : Measure Ambient) {x | c * ‖x‖ = x 0} = 0 := by
  let L : Set Ambient := {x | c * ‖x‖ = x 0}
  have hLm : MeasurableSet L :=
    (isClosed_eq (continuous_const.mul continuous_norm) (by fun_prop)).measurableSet
  have hm : MeasurePreserving axialEquiv.symm (volume.prod volume) volume :=
    axialEquiv_measurePreserving.symm
  rw [← hm.measure_preimage_equiv L,
    Measure.prod_apply (hLm.preimage axialEquiv.symm.measurable)]
  have hsection : ∀ z : ℝ, volume (Prod.mk z ⁻¹' (axialEquiv.symm ⁻¹' L)) = 0 := by
    intro z
    apply measure_mono_null (t := sphere (0 : Transverse)
      (Real.sqrt (coneSlopeSq c * z^2)))
    · intro y hy
      have hn := norm_sq_axial (axialEquiv.symm (z,y))
      simp only [MeasurableEquiv.apply_symm_apply] at hn
      have hfst : (axialEquiv.symm (z,y)) 0 = z := by
        change (axialEquiv (axialEquiv.symm (z,y))).1 = z
        rw [MeasurableEquiv.apply_symm_apply]
      change c * ‖axialEquiv.symm (z,y)‖ = (axialEquiv.symm (z,y)) 0 at hy
      rw [hfst] at hy
      have hs := congrArg (fun x : ℝ => x^2) hy
      rw [mul_pow,hn] at hs
      have hq : ‖y‖^2 = coneSlopeSq c * z^2 := by
        unfold coneSlopeSq
        field_simp
        nlinarith
      change dist y 0 = Real.sqrt (coneSlopeSq c * z^2)
      rw [dist_zero_right, ← hq, Real.sqrt_sq (norm_nonneg _)]
    · exact Measure.addHaar_sphere volume 0 _
  simp_rw [hsection, lintegral_zero]

theorem axial_level_zero (c : ℝ) :
    (volume : Measure Ambient) {x | c * ‖x‖ = x 0} = 0 := by
  by_cases hc : c = 0
  · subst c
    let L : Set Ambient := {x | (0:ℝ) * ‖x‖ = x 0}
    have hLm : MeasurableSet L :=
      (isClosed_eq (continuous_const.mul continuous_norm) (by fun_prop)).measurableSet
    have hm : MeasurePreserving axialEquiv.symm (volume.prod volume) volume :=
      axialEquiv_measurePreserving.symm
    rw [← hm.measure_preimage_equiv L,
      Measure.prod_apply (hLm.preimage axialEquiv.symm.measurable)]
    calc
      _ = ∫⁻ z : ℝ, (0 : ℝ≥0∞) := by
        apply lintegral_congr_ae
        filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0] with z hz
        have he : Prod.mk z ⁻¹' (axialEquiv.symm ⁻¹' L) = ∅ := by
          ext y
          have hfst : (axialEquiv.symm (z,y)) 0 = z := by
            change (axialEquiv (axialEquiv.symm (z,y))).1 = z
            rw [MeasurableEquiv.apply_symm_apply]
          simp [L,hfst,hz,eq_comm]
        rw [he,measure_empty]
      _ = 0 := lintegral_zero
  · exact axial_level_zero_of_ne_zero hc

end QEC.Coding.ProbabilisticConstruction.SphericalCap
