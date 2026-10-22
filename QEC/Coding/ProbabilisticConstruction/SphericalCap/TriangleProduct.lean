import QEC.Coding.ProbabilisticConstruction.SphericalCap.TriangleGeometry
import QEC.Coding.ProbabilisticConstruction.SphericalCap.Slab
import Mathlib.Probability.Independence.Basic

namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators

theorem pi_event_le_of_sections (μ : Fin 3 → Measure Space)
    [∀ i, IsProbabilityMeasure (μ i)] (i : Fin 3)
    {E : Set (Fin 3 → Space)} (hE : MeasurableSet E) (C : ℝ≥0∞)
    (hsections : ∀ q : Fin 2 → Space, μ i {p | i.insertNth (α := fun _ : Fin 3 => Space) p q ∈ E} ≤ C) :
    Measure.pi μ E ≤ C := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => Space) i
  have hp := (measurePreserving_piFinSuccAbove μ i).symm e
  rw [← hp.measure_preimage hE.nullMeasurableSet, Measure.prod_apply_symm (e.symm.measurable hE)]
  calc
    _ ≤ ∫⁻ _ : Fin 2 → Space, C ∂Measure.pi (fun j => μ (i.succAbove j)) := by
      apply lintegral_mono
      intro q
      exact hsections q
    _ = C := by simp

theorem largeWeightHit_section_subset_slab (r : Fin 3 → Space) (z : Space)
    (ρ : ℝ) (i : Fin 3) (q : Fin 2 → Space) :
    ∃ n : Sphere, {p : Space | i.insertNth (α := fun _ : Fin 3 => Space) p q ∈ largeWeightHit r z ρ i} ⊆
      slab n (inner ℝ (n : Space) (z-r i)) (3*ρ) := by
  obtain ⟨n,hn⟩ := exists_unit_normal_except (fun j => r j+i.insertNth (α := fun _ : Fin 3 => Space) (0:Space) q j) z i
  refine ⟨n, ?_⟩
  intro p hp
  obtain ⟨w,hw,hball⟩ := hp
  have hnormal : ∀ j, j ≠ i →
      inner ℝ (n : Space) (r j+i.insertNth (α := fun _ : Fin 3 => Space) p q j-z) = 0 := by
    intro j hj
    obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hj
    simpa only [Fin.insertNth_apply_succAbove] using hn (i.succAbove k) (Fin.succAbove_ne i k)
  have hb := large_weight_slab w hw hball n hnormal
  simp only [Fin.insertNth_apply_same] at hb
  change |inner ℝ (n : Space) p - inner ℝ (n : Space) (z-r i)| ≤ 3*ρ
  convert hb using 1 <;> simp only [inner_sub_right,inner_add_right] <;> ring

theorem capProduct_largeWeightHit_le {R ρ : ℝ} (hR : 0 < R) (hρ : 0 ≤ ρ)
    (u : Fin 3 → Sphere) (c : Fin 3 → ℝ) (hc0 : ∀ i, -1 < c i) (hc1 : ∀ i, c i < 1)
    (r : Fin 3 → Space) (z : Space) (i : Fin 3) :
    Measure.pi (fun j => capDisplacementLaw R (u j) (c j)) (largeWeightHit r z ρ i) ≤
      ENNReal.ofReal (6*ρ/(R*(1-c i))) := by
  letI (j : Fin 3) : IsProbabilityMeasure (capDisplacementLaw R (u j) (c j)) :=
    capDisplacementLaw_isProbabilityMeasure R (u j) (hc1 j)
  apply pi_event_le_of_sections _ i (isClosed_largeWeightHit r z ρ i).measurableSet
  intro q
  obtain ⟨n,hn⟩ := largeWeightHit_section_subset_slab r z ρ i q
  have hb := capDisplacementLaw_slab_le hR (u i) n (hc0 i) (hc1 i)
    (inner ℝ (n : Space) (z-r i)) (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hρ)
  have he : 2*(3*ρ)/(R*(1-c i)) = 6*ρ/(R*(1-c i)) := by ring
  rw [he] at hb
  exact (measure_mono hn).trans hb

theorem capProduct_triangleHit_le {R ρ : ℝ} (hR : 0 < R) (hρ : 0 ≤ ρ)
    (u : Fin 3 → Sphere) (c : Fin 3 → ℝ) (hc0 : ∀ i, -1 < c i) (hc1 : ∀ i, c i < 1)
    (r : Fin 3 → Space) (z : Space) :
    Measure.pi (fun j => capDisplacementLaw R (u j) (c j)) (triangleHit r z ρ) ≤
      ENNReal.ofReal ((6*ρ/R) * ∑ i, 1/(1-c i)) := by
  rw [triangleHit_eq_union]
  calc
    _ ≤ ∑ i, Measure.pi (fun j => capDisplacementLaw R (u j) (c j))
        (largeWeightHit r z ρ i) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ i, ENNReal.ofReal (6*ρ/(R*(1-c i))) :=
      Finset.sum_le_sum fun i _ => capProduct_largeWeightHit_le hR hρ u c hc0 hc1 r z i
    _ = ENNReal.ofReal (∑ i, 6*ρ/(R*(1-c i))) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro i _
      exact div_nonneg (mul_nonneg (by norm_num) hρ) (mul_nonneg hR.le (sub_pos.mpr (hc1 i)).le)
    _ = _ := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      field_simp [hR.ne', (sub_pos.mpr (hc1 i)).ne']
      <;> ring

theorem selected_product_measurePreserving {ι : Type*} [Fintype ι]
    (μ : ι → Measure Space) [∀ i, IsProbabilityMeasure (μ i)]
    (j : Fin 3 → ι) (hj : Function.Injective j) :
    MeasurePreserving (fun p : ι → Space => fun k => p (j k))
      (Measure.pi μ) (Measure.pi fun k => μ (j k)) := by
  have hind : iIndepFun (fun i (p : ι → Space) => p i) (Measure.pi μ) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  refine ⟨by fun_prop, ?_⟩
  have he := iIndepFun.map_fun_eq_pi_map (fun k => (measurable_pi_apply (j k)).aemeasurable) (hind.precomp hj)
  simpa only [(measurePreserving_eval μ _).map_eq] using he

theorem selected_capProduct_triangleHit_le {ι : Type*} [Fintype ι]
    {R ρ : ℝ} (hR : 0 < R) (hρ : 0 ≤ ρ)
    (u : ι → Sphere) (c : ι → ℝ) (hc0 : ∀ i, -1 < c i) (hc1 : ∀ i, c i < 1)
    (j : Fin 3 → ι) (hj : Function.Injective j) (r : Fin 3 → Space) (z : Space) :
    Measure.pi (fun k => capDisplacementLaw R (u k) (c k))
      {p | (fun k => p (j k)) ∈ triangleHit r z ρ} ≤
      ENNReal.ofReal ((6*ρ/R) * ∑ k, 1/(1-c (j k))) := by
  letI (k : ι) : IsProbabilityMeasure (capDisplacementLaw R (u k) (c k)) :=
    capDisplacementLaw_isProbabilityMeasure R (u k) (hc1 k)
  have hp := selected_product_measurePreserving
    (fun k => capDisplacementLaw R (u k) (c k)) j hj
  change Measure.pi (fun k => capDisplacementLaw R (u k) (c k))
    ((fun p : ι → Space => fun k => p (j k)) ⁻¹' triangleHit r z ρ) ≤ _
  rw [hp.measure_preimage (measurableSet_triangleHit r z ρ).nullMeasurableSet]
  exact capProduct_triangleHit_le hR hρ (fun k => u (j k)) (fun k => c (j k))
    (fun k => hc0 (j k)) (fun k => hc1 (j k)) r z

theorem capProduct_triangleHit_le_same_cutoff {R ρ c : ℝ} (hR : 0 < R) (hρ : 0 ≤ ρ)
    (u : Fin 3 → Sphere) (hc0 : -1 < c) (hc1 : c < 1)
    (r : Fin 3 → Space) (z : Space) :
    Measure.pi (fun j => capDisplacementLaw R (u j) c) (triangleHit r z ρ) ≤
      ENNReal.ofReal (18*ρ/(R*(1-c))) := by
  have hb := capProduct_triangleHit_le hR hρ u (fun _ => c) (fun _ => hc0) (fun _ => hc1) r z
  have he : (6*ρ/R) * ∑ _ : Fin 3, 1/(1-c) = 18*ρ/(R*(1-c)) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hR.ne', (sub_pos.mpr hc1).ne']
    <;> ring
  rwa [he] at hb

end QEC.Coding.ProbabilisticConstruction.SphericalCap
