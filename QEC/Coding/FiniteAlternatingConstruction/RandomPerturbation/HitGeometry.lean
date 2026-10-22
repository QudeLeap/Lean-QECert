import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.LocalLemmaApplication

/-! # Actual hit geometry for the deterministic event net -/

namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap

/-- Convexity keeps the entire perturbed triangle near its scaled old X anchor. -/
theorem perturbed_triangle_near_anchor (P : TannerSquarePresentation)
    (J p : Vertex P → Space) (t R lambda : ℝ)
    (hJ : IsBoundedDensityLocalMap P J t) (hl : 0 ≤ lambda)
    (hp : ∀ v, ‖p v‖ ≤ R) (a : Triangle P) :
    oldTriangleImage P (perturbedMap P J lambda p) a ⊆
      Metric.closedBall (lambda • oldAnchor P J a) (R+lambda) := by
  rw [oldTriangleImage_eq]
  apply convexHull_min _ (convex_closedBall _ _)
  rintro y ⟨i,rfl⟩
  have hs := scaled_half_triangle_sides P J t hJ hl a i 0
  have hs' : ‖lambda • ((1/2 : ℝ) • J (triangleVertex P a i))-
      lambda • oldAnchor P J a‖ ≤ lambda := by
    simpa only [oldAnchor,triangleVertex,Matrix.cons_val_zero] using hs
  change ‖(lambda • ((1/2 : ℝ) • J (triangleVertex P a i))+
    p (triangleVertex P a i))-lambda • oldAnchor P J a‖ ≤ R+lambda
  have he : (lambda • ((1/2 : ℝ) • J (triangleVertex P a i))+
      p (triangleVertex P a i))-lambda • oldAnchor P J a =
      (lambda • ((1/2 : ℝ) • J (triangleVertex P a i))-
        lambda • oldAnchor P J a)+p (triangleVertex P a i) := by abel
  rw [he]
  exact (norm_add_le _ _).trans (by linarith [hp (triangleVertex P a i)])

theorem hit_center_near_anchor (P : TannerSquarePresentation)
    (J p : Vertex P → Space) (t R lambda : ℝ)
    (hJ : IsBoundedDensityLocalMap P J t) (hl : 0 ≤ lambda)
    (hp : ∀ v, ‖p v‖ ≤ R) (a : Triangle P) (z : Space)
    (hit : (oldTriangleImage P (perturbedMap P J lambda p) a ∩
      Metric.closedBall z 1).Nonempty) :
    dist z (lambda • oldAnchor P J a) ≤ R+lambda+1 := by
  obtain ⟨y,hy,hz⟩ := hit
  have hy' := perturbed_triangle_near_anchor P J p t R lambda hJ hl hp a hy
  have hzy : dist z y ≤ 1 := by simpa only [Metric.mem_closedBall,dist_comm] using hz
  have hya : dist y (lambda • oldAnchor P J a) ≤ R+lambda := hy'
  exact (dist_triangle _ y _).trans (by linarith)

/-- A common unit ball forces the unscaled anchors into the fixed local pool.
The extra two units absorb both unit-ball radii at every integral lambda >= 1. -/
theorem common_hits_anchor_distance (P : TannerSquarePresentation)
    (J p : Vertex P → Space) (t alpha lambda : ℝ)
    (hJ : IsBoundedDensityLocalMap P J t) (hl : 1 ≤ lambda)
    (hp : ∀ v, ‖p v‖ ≤ alpha*lambda) (a b : Triangle P) (z : Space)
    (ha : (oldTriangleImage P (perturbedMap P J lambda p) a ∩ Metric.closedBall z 1).Nonempty)
    (hb : (oldTriangleImage P (perturbedMap P J lambda p) b ∩ Metric.closedBall z 1).Nonempty) :
    dist (oldAnchor P J a) (oldAnchor P J b) ≤ 2*alpha+4 := by
  have hl0 : 0 ≤ lambda := by linarith
  have hza := hit_center_near_anchor P J p t (alpha*lambda) lambda hJ hl0 hp a z ha
  have hzb := hit_center_near_anchor P J p t (alpha*lambda) lambda hJ hl0 hp b z hb
  have hd := dist_triangle (lambda • oldAnchor P J a) z (lambda • oldAnchor P J b)
  rw [dist_comm (lambda • oldAnchor P J a) z] at hd
  rw [dist_eq_norm,← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg hl0,
    ← dist_eq_norm] at hd
  have hlpos : 0 < lambda := by linarith
  apply (mul_le_mul_iff_right₀ hlpos).mp
  nlinarith

end QEC.Coding.BDL26RandomPerturbation
