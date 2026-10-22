import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.GridCover
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.Incidence

/-! # Labeled density under finite covers and half scaling -/

namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap

/-- Covering counts preserve labels, including coincident or collapsed images. -/
theorem familyHits_card_le_cover {ι κ E : Type*} [Fintype ι] [Fintype κ]
    (images : ι → Set E) (region : Set E) (cover : κ → Set E)
    (hcover : ∀ p ∈ region, ∃ k, p ∈ cover k) :
    (familyHits images region).card ≤ ∑ k, (familyHits images (cover k)).card := by
  classical
  have hsub : familyHits images region ⊆
      Finset.univ.biUnion (fun k => familyHits images (cover k)) := by
    intro i hi
    obtain ⟨p,hpi,hpr⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨k,hpk⟩ := hcover p hpr
    exact Finset.mem_biUnion.mpr ⟨k,Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,p,hpi,hpk⟩⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)

theorem familyHits_integer_ball_le {ι : Type*} [Fintype ι]
    (images : ι → Set Space) (t : ℝ)
    (hdensity : ∀ c, ((familyHits images (Metric.closedBall c 1)).card : ℝ) ≤ t)
    (K : ℕ) (center : Space) :
    ((familyHits images (Metric.closedBall center K)).card : ℝ) ≤ (2*K+1 : ℕ)^3*t := by
  have h := familyHits_card_le_cover images (Metric.closedBall center K)
    (fun g : Grid K => Metric.closedBall (center+gridPoint K g) 1)
    (exists_grid_cover K center)
  have hr : ((familyHits images (Metric.closedBall center K)).card : ℝ) ≤
      ∑ g : Grid K, ((familyHits images (Metric.closedBall (center+gridPoint K g) 1)).card : ℝ) := by
    exact_mod_cast h
  calc
    _ ≤ ∑ g : Grid K, ((familyHits images (Metric.closedBall (center+gridPoint K g) 1)).card : ℝ) := hr
    _ ≤ ∑ _g : Grid K, t := Finset.sum_le_sum (fun g _ => hdensity _)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,grid_card,nsmul_eq_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]

theorem oldTriangleImage_smul (P : TannerSquarePresentation) (J : Vertex P → Space)
    (a : ℝ) (t : Triangle P) :
    oldTriangleImage P (fun v => a • J v) t =
      (fun p => a • p) '' oldTriangleImage P J t := by
  rw [oldTriangleImage_eq,oldTriangleImage_eq]
  have h := (LinearMap.lsmul ℝ Space a).image_convexHull
    (Set.range fun i => J (triangleVertex P t i))
  change (fun p : Space => a • p) '' convexHull ℝ (Set.range fun i => J (triangleVertex P t i)) =
    convexHull ℝ ((fun p : Space => a • p) '' Set.range fun i => J (triangleVertex P t i)) at h
  rw [← Set.range_comp'] at h
  exact h.symm

theorem oldTriangleImage_subset_face (P : TannerSquarePresentation) (J : Vertex P → Space)
    (t : Triangle P) : oldTriangleImage P J t ⊆ tannerFaceImage P J t.1 := by
  rcases t with ⟨f,s⟩
  fin_cases s
  · exact Set.subset_union_left
  · have h : oldTriangleImage P J (f,1) =
        convexHull ℝ {J (.x (P.faceX f)),J (.z (P.faceZ f)),J (.q (P.faceQ f 1))} := by
      unfold oldTriangleImage
      congr 1
      ext p
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
      tauto
    change oldTriangleImage P J (f,1) ⊆ tannerFaceImage P J f
    rw [h]
    exact Set.subset_union_right

/-- Half scaling transfers a triangle hit to the original radius-two square hit. -/
theorem half_triangle_hit (P : TannerSquarePresentation) (J : Vertex P → Space)
    (center : Space) (t : Triangle P)
    (ht : t ∈ familyHits (oldTriangleImage P (fun v => (1/2 : ℝ) • J v))
      (Metric.closedBall center 1)) :
    t.1 ∈ familyHits (tannerFaceImage P J) (Metric.closedBall ((2 : ℝ) • center) 2) := by
  classical
  obtain ⟨p,hp,hball⟩ := (Finset.mem_filter.mp ht).2
  rw [oldTriangleImage_smul] at hp
  obtain ⟨w,hw,rfl⟩ := hp
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,w,oldTriangleImage_subset_face P J t hw,?_⟩
  have hn : ‖(1/2 : ℝ) • w-center‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall,dist_eq_norm] using hball
  have he : w-(2 : ℝ) • center = (2 : ℝ) • ((1/2 : ℝ) • w-center) := by module
  change ‖w-(2 : ℝ) • center‖ ≤ 2
  rw [he,norm_smul]
  norm_num
  linarith

/-- Both auxiliary labels are retained: the half-scaled density is at most 250t. -/
theorem half_triangle_density (P : TannerSquarePresentation) (J : Vertex P → Space)
    (t : ℝ) (hJ : IsBoundedDensityLocalMap P J t) (center : Space) :
    ((familyHits (oldTriangleImage P (fun v => (1/2 : ℝ) • J v))
      (Metric.closedBall center 1)).card : ℝ) ≤ 250*t := by
  classical
  let squares := familyHits (tannerFaceImage P J) (Metric.closedBall ((2 : ℝ) • center) 2)
  have hsub : familyHits (oldTriangleImage P (fun v => (1/2 : ℝ) • J v))
      (Metric.closedBall center 1) ⊆ squares ×ˢ (Finset.univ : Finset Two) := by
    intro s hs
    exact Finset.mem_product.mpr ⟨half_triangle_hit P J center s hs,Finset.mem_univ _⟩
  have hc := Finset.card_le_card hsub
  have htwo : (Finset.univ : Finset Two).card = 2 := by decide
  rw [Finset.card_product,htwo] at hc
  have hc' : ((familyHits (oldTriangleImage P (fun v => (1/2 : ℝ) • J v))
      (Metric.closedBall center 1)).card : ℝ) ≤ (squares.card : ℝ)*2 := by exact_mod_cast hc
  have hd := familyHits_integer_ball_le (tannerFaceImage P J) t hJ.2.2 2 ((2 : ℝ) • center)
  change (squares.card : ℝ) ≤ _ at hd
  norm_num at hd
  linarith

/-- Half scaling controls the diagonal as well as the two Tanner edges. -/
theorem half_triangle_sides (P : TannerSquarePresentation) (J : Vertex P → Space)
    (t : ℝ) (hJ : IsBoundedDensityLocalMap P J t) (a : Triangle P) (i j : Fin 3) :
    ‖(1/2 : ℝ) • J (triangleVertex P a i)-(1/2 : ℝ) • J (triangleVertex P a j)‖ ≤ 1 := by
  have hxq := hJ.1 (P.faceX a.1) (P.faceQ a.1 a.2) (P.data.faceQ_xq a.1 a.2)
  have hqz := hJ.2.1 (P.faceQ a.1 a.2) (P.faceZ a.1) (P.data.faceQ_qz a.1 a.2)
  have hxz : dist (J (.x (P.faceX a.1))) (J (.z (P.faceZ a.1))) ≤ 2 := by
    have h := dist_triangle (J (.x (P.faceX a.1))) (J (.q (P.faceQ a.1 a.2)))
      (J (.z (P.faceZ a.1)))
    linarith
  have hp : dist (J (triangleVertex P a i)) (J (triangleVertex P a j)) ≤ 2 := by
    fin_cases i <;> fin_cases j <;> simp_all [triangleVertex,dist_comm] <;> linarith
  rw [← smul_sub,norm_smul]
  norm_num
  rw [dist_eq_norm] at hp
  linarith

end QEC.Coding.BDL26RandomPerturbation
