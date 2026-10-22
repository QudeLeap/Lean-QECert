import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.GramProjection
import Mathlib.Analysis.Convex.Topology

/-! # Nearest triangle point and barycentric stationarity

These lemmas apply to arbitrary triples, including repeated vertices.
-/

namespace QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open Set
open scoped BigOperators InnerProductSpace

theorem inner_nonpos_distance_le (z y x : Space)
    (h : inner ℝ (z-y) (x-y) ≤ 0) : dist z y ≤ dist z x := by
  have he : z-x = (z-y)-(x-y) := by abel
  have hs : ‖z-y‖^2 ≤ ‖z-x‖^2 := by
    rw [he]
    have hn := norm_sub_sq_real (z-y) (x-y)
    nlinarith [sq_nonneg ‖x-y‖]
  rw [dist_eq_norm,dist_eq_norm]
  nlinarith [norm_nonneg (z-y),norm_nonneg (z-x)]

theorem triangle_nearest_weights (a : Fin 3 → Space) (z : Space) :
    ∃ w : stdSimplex ℝ (Fin 3),
      (∀ x ∈ convexHull ℝ (range a),
        dist z (barycenterMap a w) ≤ dist z x) ∧
      ∀ i, inner ℝ (z-barycenterMap a w) (a i-barycenterMap a w) ≤ 0 := by
  have hc := convex_convexHull ℝ (range a)
  have hn : (convexHull ℝ (range a)).Nonempty :=
    ⟨a 0,subset_convexHull ℝ _ (mem_range_self 0)⟩
  obtain ⟨y,hy,hmin⟩ := exists_norm_eq_iInf_of_complete_convex hn
    ((Set.finite_range a).isCompact_convexHull ℝ).isComplete hc z
  have hi := (norm_eq_iInf_iff_real_inner_le_zero hc hy).mp hmin
  obtain ⟨w,hw,rfl⟩ := (convexHull_range_eq_barycenters a ▸ hy)
  refine ⟨⟨w,hw⟩,?_,?_⟩
  · intro x hx
    exact inner_nonpos_distance_le _ _ _ (hi x hx)
  · intro i
    exact hi _ (subset_convexHull ℝ _ (mem_range_self i))

theorem barycenter_affine_coordinates (a : Fin 3 → Space)
    (w : stdSimplex ℝ (Fin 3)) :
    barycenterMap a w = a 0+w.val 1 • (a 1-a 0)+w.val 2 • (a 2-a 0) := by
  have hs := w.property.2
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hs
  change w.val 0+(w.val 1+w.val 2) = 1 at hs
  rw [barycenterMap_apply]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  have h0 : w.val 0 = 1-w.val 1-w.val 2 := by linarith
  change w.val 0 • a 0+(w.val 1 • a 1+w.val 2 • a 2) = _
  rw [h0]
  module

theorem positive_weights_stationary (a : Fin 3 → Space) (z : Space)
    (w : stdSimplex ℝ (Fin 3)) (hw : ∀ i, 0 < w.val i)
    (hi : ∀ i, inner ℝ (z-barycenterMap a w) (a i-barycenterMap a w) ≤ 0) :
    ∀ i, inner ℝ (z-barycenterMap a w) (a i-barycenterMap a w) = 0 := by
  let y := barycenterMap a w
  have hsum : ∑ i, w.val i • (a i-y) = 0 := by
    simp only [smul_sub,Finset.sum_sub_distrib,← Finset.sum_smul,w.property.2,one_smul]
    change barycenterMap a w-y = 0
    exact sub_self _
  have hs : ∑ i, w.val i*inner ℝ (z-y) (a i-y) = 0 := by
    have h := congrArg (inner ℝ (z-y)) hsum
    simpa only [inner_sum,real_inner_smul_right,inner_zero_right] using h
  have hn : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      w.val i*inner ℝ (z-y) (a i-y) ≤ 0 := by
    intro i _
    exact mul_nonpos_of_nonneg_of_nonpos (hw i).le (hi i)
  have he := (Finset.sum_eq_zero_iff_of_nonpos hn).mp hs
  intro i
  exact (mul_eq_zero.mp (he i (Finset.mem_univ i))).resolve_left (ne_of_gt (hw i))

theorem boundary_weights_on_edge (a : Fin 3 → Space) (w : stdSimplex ℝ (Fin 3))
    (hw : ∃ i, w.val i = 0) :
    ∃ i j : Fin 3, i < j ∧ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      barycenterMap a w = a i+t • (a j-a i) := by
  have hs := w.property.2
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hs
  change w.val 0+(w.val 1+w.val 2) = 1 at hs
  have h0 := w.property.1 0
  have h1 := w.property.1 1
  have h2 := w.property.1 2
  obtain ⟨i,hi⟩ := hw
  fin_cases i
  · change w.val 0 = 0 at hi
    refine ⟨1,2,by decide,w.val 2,h2,by linarith,?_⟩
    rw [barycenterMap_apply]
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    have he : w.val 1 = 1-w.val 2 := by linarith
    change w.val 0 • a 0+(w.val 1 • a 1+w.val 2 • a 2) = _
    rw [hi,he]
    module
  · change w.val 1 = 0 at hi
    refine ⟨0,2,by decide,w.val 2,h2,by linarith,?_⟩
    rw [barycenter_affine_coordinates,hi]
    module
  · change w.val 2 = 0 at hi
    refine ⟨0,1,by decide,w.val 1,h1,by linarith,?_⟩
    rw [barycenter_affine_coordinates,hi]
    module

theorem stationary_weights_plane (a : Fin 3 → Space) (z : Space)
    (w : stdSimplex ℝ (Fin 3))
    (hi : ∀ i, inner ℝ (z-barycenterMap a w) (a i-barycenterMap a w) = 0)
    (hdet : gramDet (a 1-a 0) (a 2-a 0) ≠ 0) :
    w.val 1 = planeU (a 1-a 0) (a 2-a 0) (z-a 0) ∧
      w.val 2 = planeV (a 1-a 0) (a 2-a 0) (z-a 0) := by
  have h1 : inner ℝ (z-barycenterMap a w) (a 1-a 0) = 0 := by
    have he : a 1-a 0 = (a 1-barycenterMap a w)-(a 0-barycenterMap a w) := by abel
    rw [he,inner_sub_right,hi 1,hi 0,sub_self]
  have h2 : inner ℝ (z-barycenterMap a w) (a 2-a 0) = 0 := by
    have he : a 2-a 0 = (a 2-barycenterMap a w)-(a 0-barycenterMap a w) := by abel
    rw [he,inner_sub_right,hi 2,hi 0,sub_self]
  have he : z-barycenterMap a w =
      (z-a 0)-(w.val 1 • (a 1-a 0)+w.val 2 • (a 2-a 0)) := by
    rw [barycenter_affine_coordinates]
    abel
  rw [he] at h1 h2
  rw [inner_sub_left,inner_add_left,real_inner_smul_left,real_inner_smul_left,
    real_inner_self_eq_norm_sq,real_inner_comm (a 1-a 0) (a 2-a 0)] at h1
  rw [inner_sub_left,inner_add_left,real_inner_smul_left,real_inner_smul_left,
    real_inner_self_eq_norm_sq] at h2
  apply plane_coefficients_unique _ _ _ hdet <;> linarith

end QEC.Coding.BDL26RandomPerturbation
