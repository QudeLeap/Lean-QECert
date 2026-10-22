import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.Events

/-! # Local candidate counts from actual incidence and incoming density -/

namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem x_mem_triangleSupport (P : TannerSquarePresentation) (a : Triangle P) (x : P.X) :
    Vertex.x x ∈ triangleSupport P a ↔ P.faceX a.1 = x := by
  classical
  simp [triangleSupport,triangleVertex,Fin.exists_fin_succ,eq_comm]

theorem q_mem_triangleSupport (P : TannerSquarePresentation) (a : Triangle P) (q : P.Q) :
    Vertex.q q ∈ triangleSupport P a ↔ P.faceQ a.1 a.2 = q := by
  classical
  simp [triangleSupport,triangleVertex,Fin.exists_fin_succ,eq_comm]

theorem z_mem_triangleSupport (P : TannerSquarePresentation) (a : Triangle P) (z : P.Z) :
    Vertex.z z ∈ triangleSupport P a ↔ P.faceZ a.1 = z := by
  classical
  simp [triangleSupport,triangleVertex,Fin.exists_fin_succ,eq_comm]

noncomputable def incidentTriangles (P : TannerSquarePresentation) (v : Vertex P) :
    Finset (Triangle P) := by
  classical
  exact Finset.univ.filter (fun a => v ∈ triangleSupport P a)

/-- Each constructor's actual incidence fiber has the same universal upper bound. -/
theorem incidentTriangles_card_le (P : TannerSquarePresentation) (hv : BoundedValence P)
    (v : Vertex P) : (incidentTriangles P v).card ≤ 56 := by
  classical
  cases v with
  | x x =>
    have h := xTriangles_card_le P hv x
    simpa only [incidentTriangles,x_mem_triangleSupport,XTriangles,Fintype.card_subtype] using h
  | q q =>
    have h := qTriangles_card_le P hv q
    simpa only [incidentTriangles,q_mem_triangleSupport,QTriangles,Fintype.card_subtype] using h
  | z z =>
    have h := zTriangles_card_le P hv z
    simpa only [incidentTriangles,z_mem_triangleSupport,ZTriangles,Fintype.card_subtype] using h

noncomputable def localPool (P : TannerSquarePresentation) (J : Vertex P → Space)
    (K : ℕ) (a : Triangle P) : Finset (Triangle P) := by
  classical
  exact Finset.univ.filter (fun b => dist (oldAnchor P J a) (oldAnchor P J b) ≤ K)

/-- Every old anchor lies in its own actual triangle, including collapsed labels. -/
theorem oldAnchor_mem_triangle (P : TannerSquarePresentation) (J : Vertex P → Space)
    (a : Triangle P) :
    oldAnchor P J a ∈ oldTriangleImage P (fun v => (1/2 : ℝ) • J v) a := by
  rw [oldTriangleImage_eq]
  exact subset_convexHull ℝ _ ⟨0,rfl⟩

theorem localPool_subset_hits (P : TannerSquarePresentation) (J : Vertex P → Space)
    (K : ℕ) (a : Triangle P) :
    localPool P J K a ⊆ familyHits (oldTriangleImage P (fun v => (1/2 : ℝ) • J v))
      (Metric.closedBall (oldAnchor P J a) K) := by
  classical
  intro b hb
  have hd := (Finset.mem_filter.mp hb).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,oldAnchor P J b,
    oldAnchor_mem_triangle P J b,?_⟩
  simpa only [Metric.mem_closedBall,dist_comm] using hd

/-- Cover counts bound the local pool independently of the perturbation scale. -/
theorem localPool_card_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (t : ℝ) (hJ : IsBoundedDensityLocalMap P J t) (K : ℕ) (a : Triangle P) :
    ((localPool P J K a).card : ℝ) ≤ (2*K+1 : ℕ)^3*(250*t) := by
  have hc := Finset.card_le_card (localPool_subset_hits P J K a)
  have hc' : ((localPool P J K a).card : ℝ) ≤
      ((familyHits (oldTriangleImage P (fun v => (1/2 : ℝ) • J v))
        (Metric.closedBall (oldAnchor P J a) K)).card : ℝ) := by exact_mod_cast hc
  exact hc'.trans (familyHits_integer_ball_le _ (250*t)
    (half_triangle_density P J t hJ) K (oldAnchor P J a))

theorem localPool_card_le_integer (P : TannerSquarePresentation) (J : Vertex P → Space)
    (t : ℝ) (hJ : IsBoundedDensityLocalMap P J t) (K M : ℕ)
    (hM : (2*K+1 : ℕ)^3*(250*t) ≤ (M : ℝ)) (a : Triangle P) :
    (localPool P J K a).card ≤ M := by
  exact_mod_cast (localPool_card_le P J t hJ K a).trans hM

/-- The common integer pool bound is selected from t and K, before lambda. -/
theorem exists_local_pool_bound (t : ℝ) (K : ℕ) :
    ∃ M : ℕ, (2*K+1 : ℕ)^3*(250*t) ≤ (M : ℝ) := by
  obtain ⟨M,hM⟩ := exists_nat_gt ((2*K+1 : ℕ)^3*(250*t))
  exact ⟨M,hM.le⟩

end QEC.Coding.BDL26RandomPerturbation
