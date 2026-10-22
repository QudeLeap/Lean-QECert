import QEC.Coding.ProbabilisticConstruction.SphericalCap.Measure
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.Maps.Proper.Basic

namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped BigOperators

theorem exists_unit_normal_pair (b c : Space) :
    ∃ n : Space, ‖n‖ = 1 ∧ inner ℝ n b = 0 ∧ inner ℝ n c = 0 := by
  classical
  let K := Submodule.span ℝ ({b,c} : Set Space)
  have hdim : Module.finrank ℝ K ≤ 2 := by
    have h := finrank_span_le_card (R := ℝ) ({b,c} : Set Space)
    apply h.trans
    rw [Set.toFinset_insert, Set.toFinset_singleton]
    exact (Finset.card_insert_le _ _).trans (by simp)
  have hadd := K.finrank_add_finrank_orthogonal
  have hpos : 0 < Module.finrank ℝ Kᗮ := by
    have he : Module.finrank ℝ Space = 3 := by simp [Space]
    rw [he] at hadd
    omega
  obtain ⟨v,hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hv0 : (v : Space) ≠ 0 := by simpa using hv
  have hn : ‖(v : Space)‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
  refine ⟨‖(v : Space)‖⁻¹ • (v : Space), ?_, ?_, ?_⟩
  · simp [norm_smul, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), hn]
  · rw [real_inner_smul_left]
    have hi : inner ℝ (v : Space) b = 0 :=
      (K.mem_orthogonal' _).mp v.property b (Submodule.subset_span (by simp))
    rw [hi,mul_zero]
  · rw [real_inner_smul_left]
    have hi : inner ℝ (v : Space) c = 0 :=
      (K.mem_orthogonal' _).mp v.property c (Submodule.subset_span (by simp))
    rw [hi,mul_zero]

noncomputable def barycenterMap (a : Fin 3 → Space) : (Fin 3 → ℝ) →ₗ[ℝ] Space :=
  ∑ i, (LinearMap.proj i).smulRight (a i)

@[simp] theorem barycenterMap_apply (a : Fin 3 → Space) (w : Fin 3 → ℝ) :
    barycenterMap a w = ∑ i, w i • a i := by simp [barycenterMap]

theorem convexHull_range_eq_barycenters (a : Fin 3 → Space) :
    convexHull ℝ (range a) = barycenterMap a '' stdSimplex ℝ (Fin 3) := by
  classical
  rw [← convexHull_basis_eq_stdSimplex, LinearMap.image_convexHull, ← Set.range_comp]
  congr 2
  funext i
  simp [Function.comp_def, barycenterMap]

theorem exists_unit_normal_except (a : Fin 3 → Space) (z : Space) (i : Fin 3) :
    ∃ n : Sphere, ∀ j, j ≠ i → inner ℝ (n : Space) (a j-z) = 0 := by
  obtain ⟨n,hn,h0,h1⟩ := exists_unit_normal_pair (a (i.succAbove 0)-z) (a (i.succAbove 1)-z)
  refine ⟨⟨n, by simpa only [Metric.mem_sphere, dist_zero_right] using hn⟩, ?_⟩
  intro j hj
  obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hj
  fin_cases k
  · exact h0
  · exact h1

def triangleHit (r : Fin 3 → Space) (z : Space) (ρ : ℝ) : Set (Fin 3 → Space) :=
  {p | ∃ y ∈ convexHull ℝ (range fun j => r j+p j), dist y z ≤ ρ}

theorem triangleHit_iff_weights (r : Fin 3 → Space) (z : Space) (ρ : ℝ)
    (p : Fin 3 → Space) : p ∈ triangleHit r z ρ ↔
    ∃ w : stdSimplex ℝ (Fin 3), dist (∑ j, (w : Fin 3 → ℝ) j • (r j+p j)) z ≤ ρ := by
  simp only [triangleHit, mem_setOf_eq, convexHull_range_eq_barycenters, mem_image]
  constructor
  · rintro ⟨y,⟨w,hw,rfl⟩,h⟩
    exact ⟨⟨w,hw⟩,h⟩
  · rintro ⟨w,h⟩
    exact ⟨barycenterMap _ w, ⟨w,w.property,rfl⟩,h⟩

-- A qualifying point has at least one weight >= 1/3, including boundary weights.
theorem exists_large_weight {w : Fin 3 → ℝ} (hw : w ∈ stdSimplex ℝ (Fin 3)) :
    ∃ i, (1:ℝ)/3 ≤ w i := by
  by_contra! h
  have hs := hw.2
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
  change w 0 + (w 1 + w 2) = 1 at hs
  linarith [h 0, h 1, h 2]

def largeWeightHit (r : Fin 3 → Space) (z : Space) (ρ : ℝ) (i : Fin 3) :
    Set (Fin 3 → Space) :=
  {p | ∃ w : stdSimplex ℝ (Fin 3), (1:ℝ)/3 ≤ (w : Fin 3 → ℝ) i ∧
    dist (∑ j, (w : Fin 3 → ℝ) j • (r j + p j)) z ≤ ρ}

theorem isClosed_largeWeightHit (r : Fin 3 → Space) (z : Space) (ρ : ℝ) (i : Fin 3) :
    IsClosed (largeWeightHit r z ρ i) := by
  let E : Set ((Fin 3 → Space) × stdSimplex ℝ (Fin 3)) :=
    {pw | (1:ℝ)/3 ≤ (pw.2 : Fin 3 → ℝ) i ∧
      dist (∑ j, (pw.2 : Fin 3 → ℝ) j • (r j+pw.1 j)) z ≤ ρ}
  have hwcont (j : Fin 3) : Continuous
      (fun pw : (Fin 3 → Space) × stdSimplex ℝ (Fin 3) => (pw.2 : Fin 3 → ℝ) j) :=
    (continuous_apply j).comp (continuous_subtype_val.comp continuous_snd)
  have hpcont (j : Fin 3) : Continuous
      (fun pw : (Fin 3 → Space) × stdSimplex ℝ (Fin 3) => r j+pw.1 j) :=
    continuous_const.add ((continuous_apply j).comp continuous_fst)
  have hsum : Continuous (fun pw : (Fin 3 → Space) × stdSimplex ℝ (Fin 3) =>
      ∑ j, (pw.2 : Fin 3 → ℝ) j • (r j+pw.1 j)) :=
    continuous_finset_sum _ (fun j _ => (hwcont j).smul (hpcont j))
  have hc : IsClosed E := by
    change IsClosed
      ({pw : (Fin 3 → Space) × stdSimplex ℝ (Fin 3) | (1:ℝ)/3 ≤ (pw.2 : Fin 3 → ℝ) i} ∩
       {pw : (Fin 3 → Space) × stdSimplex ℝ (Fin 3) |
         dist (∑ j, (pw.2 : Fin 3 → ℝ) j • (r j+pw.1 j)) z ≤ ρ})
    exact (isClosed_le continuous_const (hwcont i)).inter
      (isClosed_le (hsum.dist continuous_const) continuous_const)
  have he : largeWeightHit r z ρ i = Prod.fst '' E := by
    ext p
    simp only [largeWeightHit,E,mem_setOf_eq,mem_image,Prod.exists]
    aesop
  rw [he]
  exact isClosedMap_fst_of_compactSpace _ hc

theorem triangleHit_eq_union (r : Fin 3 → Space) (z : Space) (ρ : ℝ) :
    triangleHit r z ρ = ⋃ i, largeWeightHit r z ρ i := by
  ext p
  rw [triangleHit_iff_weights]
  simp only [mem_iUnion,largeWeightHit,mem_setOf_eq]
  constructor
  · rintro ⟨w,hw⟩
    obtain ⟨i,hi⟩ := exists_large_weight w.property
    exact ⟨i,w,hi,hw⟩
  · rintro ⟨i,w,_,hw⟩
    exact ⟨w,hw⟩

theorem measurableSet_triangleHit (r : Fin 3 → Space) (z : Space) (ρ : ℝ) :
    MeasurableSet (triangleHit r z ρ) := by
  rw [triangleHit_eq_union]
  exact MeasurableSet.iUnion fun i => (isClosed_largeWeightHit r z ρ i).measurableSet

theorem barycenter_sub (a : Fin 3 → Space) (z : Space)
    (w : stdSimplex ℝ (Fin 3)) :
    (∑ j, (w : Fin 3 → ℝ) j • a j)-z =
      ∑ j, (w : Fin 3 → ℝ) j • (a j-z) := by
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
  erw [w.property.2]
  rw [one_smul]

theorem large_weight_slab {a : Fin 3 → Space} {z : Space} {ρ : ℝ} {i : Fin 3}
    (w : stdSimplex ℝ (Fin 3)) (hw : (1:ℝ)/3 ≤ (w : Fin 3 → ℝ) i)
    (hball : dist (∑ j, (w : Fin 3 → ℝ) j • a j) z ≤ ρ)
    (n : Sphere) (hn : ∀ j, j ≠ i → inner ℝ (n : Space) (a j-z) = 0) :
    |inner ℝ (n : Space) (a i-z)| ≤ 3*ρ := by
  have he : inner ℝ (n : Space) ((∑ j, (w : Fin 3 → ℝ) j • a j)-z) =
      (w : Fin 3 → ℝ) i * inner ℝ (n : Space) (a i-z) := by
    rw [barycenter_sub a z w, inner_sum]
    simp_rw [real_inner_smul_right]
    exact Finset.sum_eq_single i (fun j _ hji => by rw [hn j hji,mul_zero])
      (by simp)
  have hb := abs_real_inner_le_norm (n : Space)
    ((∑ j, (w : Fin 3 → ℝ) j • a j)-z)
  rw [he,norm_coe,one_mul,abs_mul] at hb
  erw [abs_of_nonneg (w.property.1 i)] at hb
  have hh : ‖(∑ j, (w : Fin 3 → ℝ) j • a j)-z‖ ≤ ρ := hball
  have hsmall : (1:ℝ)/3 * |inner ℝ (n : Space) (a i-z)| ≤ ρ :=
    (mul_le_mul_of_nonneg_right hw (abs_nonneg _)).trans (hb.trans hh)
  linarith

end QEC.Coding.ProbabilisticConstruction.SphericalCap
