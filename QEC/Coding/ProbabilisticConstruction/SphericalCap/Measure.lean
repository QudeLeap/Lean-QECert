import QEC.Coding.ProbabilisticConstruction.SphericalCap.ConeSlices
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Continuous uniform spherical caps

The reference measure is the surface measure induced by ambient Lebesgue
measure through `Measure.toSphere`. The cap law is its normalized restriction.
-/

namespace QEC.Coding.ProbabilisticConstruction.SphericalCap

open MeasureTheory Metric Set
open scoped ENNReal Pointwise

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Sphere := Metric.sphere (0 : Space) 1

noncomputable def area : Measure Sphere :=
  (volume : Measure Space).toSphere

instance : IsFiniteMeasure area := by unfold area; infer_instance
instance : area.IsOpenPosMeasure := by unfold area; infer_instance

@[simp] theorem norm_coe (s : Sphere) : ‖(s : Space)‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using s.property

/-- A point on the sphere spans a proper subspace of the ambient space. -/
theorem span_singleton_ne_top (s : Sphere) :
    (ℝ ∙ (s : Space)) ≠ ⊤ := by
  have hs : (s : Space) ≠ 0 := by
    intro h
    have := norm_coe s
    simp [h] at this
  intro h
  have hd := finrank_span_singleton (K := ℝ) hs
  rw [h] at hd
  norm_num [Space] at hd

/-- Surface area has no point masses: a singleton cone lies in a line. -/
instance : MeasureTheory.NullSingletonClass area where
  measure_singleton s := by
    rw [area, Measure.toSphere_apply' _ (measurableSet_singleton s)]
    have hsub : Ioo (0 : ℝ) 1 • ((↑) '' ({s} : Set Sphere)) ⊆
        (ℝ ∙ (s : Space) : Set Space) := by
      rintro x ⟨r, hr, y, ⟨t, ht, rfl⟩, rfl⟩
      have ht : t = s := ht
      subst t
      exact Submodule.smul_mem _ r (Submodule.mem_span_singleton_self _)
    have hz : (volume : Measure Space)
        (Ioo (0 : ℝ) 1 • ((↑) '' ({s} : Set Sphere))) = 0 := by
      apply le_antisymm _ bot_le
      exact (measure_mono hsub).trans_eq
        (Measure.addHaar_submodule volume _ (span_singleton_ne_top s))
    rw [hz, mul_zero]

/-- Closed spherical cap with an inner-product cutoff. -/
def cap (u : Sphere) (c : ℝ) : Set Sphere :=
  {s | c ≤ inner ℝ (u : Space) (s : Space)}

theorem isClosed_cap (u : Sphere) (c : ℝ) : IsClosed (cap u c) := by
  exact isClosed_le continuous_const (by fun_prop)

theorem measurableSet_cap (u : Sphere) (c : ℝ) : MeasurableSet (cap u c) :=
  (isClosed_cap u c).measurableSet

/-- Positivity follows already from a nonempty relatively open subcap. -/
theorem area_cap_ne_zero (u : Sphere) {c : ℝ} (hc : c < 1) :
    area (cap u c) ≠ 0 := by
  have ho : IsOpen {s : Sphere | c < inner ℝ (u : Space) (s : Space)} :=
    isOpen_lt continuous_const (by fun_prop)
  have hn : ({s : Sphere | c < inner ℝ (u : Space) (s : Space)} : Set Sphere).Nonempty := by
    refine ⟨u, ?_⟩
    simpa only [mem_setOf_eq, real_inner_self_eq_norm_sq, norm_coe, one_pow] using hc
  have hsub : {s : Sphere | c < inner ℝ (u : Space) (s : Space)} ⊆ cap u c := by
    intro s hs
    change c ≤ inner ℝ (u : Space) (s : Space)
    exact hs.le
  exact ne_of_gt ((ho.measure_pos area hn).trans_le (measure_mono hsub))

theorem area_cap_ne_top (u : Sphere) (c : ℝ) : area (cap u c) ≠ ∞ :=
  measure_ne_top _ _

/-- The normalized restriction of actual surface area. -/
noncomputable def capLaw (u : Sphere) (c : ℝ) : Measure Sphere :=
  (area (cap u c))⁻¹ • area.restrict (cap u c)

theorem capLaw_isProbabilityMeasure (u : Sphere) {c : ℝ} (hc : c < 1) :
    IsProbabilityMeasure (capLaw u c) := by
  constructor
  simp only [capLaw, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (area_cap_ne_zero u hc) (area_cap_ne_top u c)

theorem capLaw_cap (u : Sphere) {c : ℝ} (hc : c < 1) : capLaw u c (cap u c) = 1 := by
  simp only [capLaw, Measure.smul_apply,
    Measure.restrict_apply (measurableSet_cap u c), inter_self, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (area_cap_ne_zero u hc) (area_cap_ne_top u c)

/-- Radius scaling is a pushforward, and does not change the sampling law. -/
noncomputable def capDisplacementLaw (R : ℝ) (u : Sphere) (c : ℝ) : Measure Space :=
  (capLaw u c).map (fun s : Sphere => R • (s : Space))

theorem capDisplacementLaw_isProbabilityMeasure (R : ℝ) (u : Sphere) {c : ℝ}
    (hc : c < 1) : IsProbabilityMeasure (capDisplacementLaw R u c) := by
  letI := capLaw_isProbabilityMeasure u hc
  exact Measure.isProbabilityMeasure_map (by fun_prop)

theorem displacement_norm (R : ℝ) (hR : 0 ≤ R) (s : Sphere) :
    ‖R • (s : Space)‖ = R := by
  simp [norm_smul, abs_of_nonneg hR]

instance (u : Sphere) (c : ℝ) : MeasureTheory.NullSingletonClass (capLaw u c) where
  measure_singleton s := by
    simp only [capLaw, Measure.smul_apply, measure_singleton, smul_zero]

theorem displacement_injective {R : ℝ} (hR : R ≠ 0) :
    Function.Injective (fun s : Sphere => R • (s : Space)) := by
  intro s t h
  apply Subtype.ext
  exact (smul_right_injective Space hR) h

theorem capDisplacementLaw_nullSingleton {R : ℝ} (hR : R ≠ 0) (u : Sphere) (c : ℝ) :
    MeasureTheory.NullSingletonClass (capDisplacementLaw R u c) := by
  constructor
  intro p
  rw [capDisplacementLaw, Measure.map_apply (by fun_prop) (measurableSet_singleton p)]
  have hs : ((fun s : Sphere => R • (s : Space)) ⁻¹' ({p} : Set Space)).Subsingleton := by
    intro s hs t ht
    apply displacement_injective hR
    exact hs.trans ht.symm
  exact hs.measure_zero _

theorem capDisplacementLaw_radius {R : ℝ} (hR : 0 ≤ R) (u : Sphere) {c : ℝ}
    (hc : c < 1) : capDisplacementLaw R u c (sphere (0 : Space) R) = 1 := by
  letI := capLaw_isProbabilityMeasure u hc
  rw [capDisplacementLaw, Measure.map_apply (by fun_prop) isClosed_sphere.measurableSet]
  have he : (fun s : Sphere => R • (s : Space)) ⁻¹' sphere (0 : Space) R = univ := by
    ext s
    simp only [mem_preimage, mem_sphere, dist_zero_right, displacement_norm R hR,
      mem_univ, iff_true]
  rw [he, measure_univ]

/-- Actual radius-scaled closed cap in ambient space. -/
def displacementCap (R : ℝ) (u : Sphere) (c : ℝ) : Set Space :=
  {p | ‖p‖ = R ∧ R*c ≤ inner ℝ (u : Space) p}

theorem measurableSet_displacementCap (R : ℝ) (u : Sphere) (c : ℝ) :
    MeasurableSet (displacementCap R u c) := by
  change MeasurableSet ({p : Space | ‖p‖ = R} ∩ {p : Space | R*c ≤ inner ℝ (u : Space) p})
  exact ((isClosed_eq continuous_norm continuous_const).inter
    (isClosed_le continuous_const (by fun_prop))).measurableSet

theorem displacementCap_preimage {R : ℝ} (hR : 0 < R) (u : Sphere) (c : ℝ) :
    (fun s : Sphere => R • (s : Space)) ⁻¹' displacementCap R u c = cap u c := by
  ext s
  simp only [displacementCap,cap,mem_preimage,mem_setOf_eq,
    displacement_norm R hR.le, true_and,real_inner_smul_right]
  exact mul_le_mul_iff_right₀ hR

theorem capDisplacementLaw_capSupport {R c : ℝ} (hR : 0 < R) (u : Sphere) (hc : c < 1) :
    capDisplacementLaw R u c (displacementCap R u c) = 1 := by
  rw [capDisplacementLaw,Measure.map_apply (by fun_prop) (measurableSet_displacementCap R u c),
    displacementCap_preimage hR,capLaw_cap u hc]

end QEC.Coding.ProbabilisticConstruction.SphericalCap
