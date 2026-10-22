import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.HitGeometry

/-! # The fixed finite radius-two net catches every four-label unit-ball hit -/

namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem four_hits_mem_event (P : TannerSquarePresentation) (J p : Vertex P → Space)
    (t radius : ℝ) (alpha lambda : ℕ)
    (hJ : IsBoundedDensityLocalMap P J t) (hl : 1 ≤ lambda)
    (hp : ∀ v, ‖p v‖ ≤ (alpha : ℝ)*lambda) (e : Event P J radius) (z : Space)
    (hits : ∀ a ∈ e.val,
      (oldTriangleImage P (perturbedMap P J lambda p) a ∩ Metric.closedBall z 1).Nonempty) :
    p ∈ localEvent (eventSupport P J radius)
      (eventBad P J radius lambda ((alpha+2)*lambda)) e := by
  have hlR : (1 : ℝ) ≤ lambda := by exact_mod_cast hl
  have hl0 : (0 : ℝ) ≤ lambda := by positivity
  have hz := hit_center_near_anchor P J p t ((alpha : ℝ)*lambda) lambda hJ hl0 hp
    (eventAnchor P J radius e) z (hits _ (eventAnchor_mem P J radius e))
  have hball : z ∈ Metric.closedBall ((lambda : ℝ) • oldAnchor P J (eventAnchor P J radius e))
      (((alpha+2)*lambda : ℕ) : ℝ) := by
    change dist z _ ≤ _
    push_cast
    nlinarith
  obtain ⟨g,hg⟩ := exists_grid_cover ((alpha+2)*lambda)
    ((lambda : ℝ) • oldAnchor P J (eventAnchor P J radius e)) z hball
  apply (mem_global_event P J radius lambda ((alpha+2)*lambda) e p).mpr
  refine ⟨g,?_⟩
  intro a
  obtain ⟨y,hy,hyz⟩ := hits a.val a.property
  have hnet : dist z (eventCenter P J radius lambda ((alpha+2)*lambda) e g) ≤ 1 := hg
  have hynet := unitBall_subset_radiusTwo z _ hnet hyz
  rw [oldTriangleImage_eq] at hy
  refine ⟨y,?_,hynet⟩
  exact hy

end QEC.Coding.BDL26RandomPerturbation
