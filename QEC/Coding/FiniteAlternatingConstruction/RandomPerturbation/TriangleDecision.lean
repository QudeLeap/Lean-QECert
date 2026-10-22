import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.SingularTriangle

/-! # Exact seven-face closed triangle / closed ball decision predicate -/

namespace QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open Set
open scoped BigOperators InnerProductSpace

noncomputable def planePoint (a : Fin 3 → Space) (z : Space) : Space :=
  a 0+planeU (a 1-a 0) (a 2-a 0) (z-a 0) • (a 1-a 0)+
    planeV (a 1-a 0) (a 2-a 0) (z-a 0) • (a 2-a 0)

def planeFeasible (a : Fin 3 → Space) (z : Space) : Prop :=
  gramDet (a 1-a 0) (a 2-a 0) ≠ 0 ∧
    0 ≤ planeU (a 1-a 0) (a 2-a 0) (z-a 0) ∧
    0 ≤ planeV (a 1-a 0) (a 2-a 0) (z-a 0) ∧
    planeU (a 1-a 0) (a 2-a 0) (z-a 0)+
      planeV (a 1-a 0) (a 2-a 0) (z-a 0) ≤ 1

theorem segmentPoint_mem_triangle (a : Fin 3 → Space) (z : Space) (i j : Fin 3) :
    segmentPoint (a i) (a j) z ∈ convexHull ℝ (range a) := by
  apply (convex_convexHull ℝ (range a)).add_smul_mem
    (subset_convexHull ℝ _ (mem_range_self i))
    (by simpa using subset_convexHull ℝ (range a) (mem_range_self j))
  exact clampUnit_bounds _

theorem planePoint_mem_triangle (a : Fin 3 → Space) (z : Space)
    (h : planeFeasible a z) : planePoint a z ∈ convexHull ℝ (range a) := by
  let u := planeU (a 1-a 0) (a 2-a 0) (z-a 0)
  let v := planeV (a 1-a 0) (a 2-a 0) (z-a 0)
  let w : Fin 3 → ℝ := ![1-u-v,u,v]
  have hw : w ∈ stdSimplex ℝ (Fin 3) := by
    constructor
    · intro i
      fin_cases i
      · change 0 ≤ 1-u-v
        have ht : u+v ≤ 1 := h.2.2.2
        linarith
      · change 0 ≤ u
        exact h.2.1
      · change 0 ≤ v
        exact h.2.2.1
    · simp [w,Fin.sum_univ_succ]
  have he : barycenterMap a w = planePoint a z := by
    have hcoords := barycenter_affine_coordinates a ⟨w,hw⟩
    change barycenterMap a w = a 0+u • (a 1-a 0)+v • (a 2-a 0) at hcoords
    exact hcoords
  rw [← he,convexHull_range_eq_barycenters]
  exact ⟨w,hw,rfl⟩

/-- Three vertices, three unordered edges, and a feasible nonsingular affine face. -/
def triangleBallTest (a : Fin 3 → Space) (z : Space) (ρ : ℝ) : Prop :=
  (∃ i, dist z (a i) ≤ ρ) ∨
    (∃ i j : Fin 3, i < j ∧ dist z (segmentPoint (a i) (a j) z) ≤ ρ) ∨
    (planeFeasible a z ∧ dist z (planePoint a z) ≤ ρ)

theorem triangleBallTest_iff (a : Fin 3 → Space) (z : Space) (ρ : ℝ) :
    triangleBallTest a z ρ ↔ ∃ y ∈ convexHull ℝ (range a), dist y z ≤ ρ := by
  constructor
  · rintro (⟨i,hi⟩ | ⟨i,j,_,hij⟩ | ⟨h,hp⟩)
    · exact ⟨a i,subset_convexHull ℝ _ (mem_range_self i),by simpa [dist_comm] using hi⟩
    · exact ⟨segmentPoint (a i) (a j) z,segmentPoint_mem_triangle a z i j,
        by simpa [dist_comm] using hij⟩
    · exact ⟨planePoint a z,planePoint_mem_triangle a z h,by simpa [dist_comm] using hp⟩
  · rintro ⟨x,hx,hxz⟩
    obtain ⟨w,hmin,hi⟩ := triangle_nearest_weights a z
    have hwρ : dist z (barycenterMap a w) ≤ ρ :=
      (hmin x hx).trans (by simpa [dist_comm] using hxz)
    have hedge : (∃ i j : Fin 3, i < j ∧ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
        barycenterMap a w = a i+t • (a j-a i)) → triangleBallTest a z ρ := by
      rintro ⟨i,j,hij,t,ht0,ht1,he⟩
      right; left
      refine ⟨i,j,hij,?_⟩
      exact (segmentPoint_nearest (a i) (a j) z ht0 ht1).trans (he ▸ hwρ)
    by_cases hzero : ∃ i, w.val i = 0
    · exact hedge (boundary_weights_on_edge a w hzero)
    · by_cases hdet : gramDet (a 1-a 0) (a 2-a 0) = 0
      · exact hedge (singular_weights_on_edge a w hdet)
      · have hpos : ∀ i, 0 < w.val i := fun i =>
          lt_of_le_of_ne (w.property.1 i) (Ne.symm (fun h => hzero ⟨i,h⟩))
        have hstation := positive_weights_stationary a z w hpos hi
        obtain ⟨hu,hv⟩ := stationary_weights_plane a z w hstation hdet
        right; right
        refine ⟨⟨hdet,?_,?_,?_⟩,?_⟩
        · rw [← hu]; exact w.property.1 1
        · rw [← hv]; exact w.property.1 2
        · rw [← hu,← hv]
          have hs := w.property.2
          simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hs
          change w.val 0+(w.val 1+w.val 2) = 1 at hs
          linarith [w.property.1 0]
        · have he : barycenterMap a w = planePoint a z := by
            rw [barycenter_affine_coordinates,hu,hv]
            rfl
          simpa only [he] using hwρ

end QEC.Coding.BDL26RandomPerturbation
