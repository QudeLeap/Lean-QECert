import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.ConcreteParameters

/-! # The finite local lemma applied to the concrete geometric events -/

namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory

theorem actual_event_criterion (P : TannerSquarePresentation) (J : Vertex P → Space)
    {densityLower : ℝ} (p : GeometricParameters densityLower)
    (hJ : IsBoundedDensityLocalMap P J p.t) (hv : BoundedValence P)
    (e : Event P J (anchorRadius p.m)) :
    (Measure.pi (vertexLaw P ((6*p.m : ℕ)* (p.lambda : ℝ)) (capCutoff p.m))).real
      (localEvent (eventSupport P J (anchorRadius p.m))
        (eventBad P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) e) ≤
      lllWeight (dependencyBound p.M)*
        ∏ _j ∈ (supportGraph (eventSupport P J (anchorRadius p.m))).neighborFinset e,
          (1-lllWeight (dependencyBound p.M)) := by
  have hc := capCutoff_bounds p.m_two
  have ha : 0 < 6*p.m := by
    have hm := p.m_two
    omega
  have hb := event_probability_real_decay P J (anchorRadius p.m) (6*p.m) p.lambda
    ha p.lambda_one e hc.1 hc.2
  apply uniform_lll_criterion (dependencyBound p.M) _
    (event_degree_le_of_density P J (anchorRadius p.m) p.M p.t hJ hv p.pool e)
  exact hb.trans p.probability_ratio

/-- The actual continuous product law gives positive mass to simultaneous avoidance.
All dependency and probability hypotheses are derived from the incoming density and valence. -/
theorem actual_avoidance_positive (P : TannerSquarePresentation) (J : Vertex P → Space)
    {densityLower : ℝ} (p : GeometricParameters densityLower)
    (hJ : IsBoundedDensityLocalMap P J p.t) (hv : BoundedValence P) :
    0 < (Measure.pi (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m))).real
      (avoid (localEvent (eventSupport P J (anchorRadius p.m))
        (eventBad P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda))) Finset.univ) := by
  have hc := capCutoff_bounds p.m_two
  letI (v : Vertex P) := vertexLaw_probability P
    ((6*p.m : ℕ)*(p.lambda : ℝ)) hc.2 v
  have h := product_localLemma
    (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m))
    (eventSupport P J (anchorRadius p.m))
    (eventBad P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda))
    (measurableSet_eventBad P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda))
    (fun _ => lllWeight (dependencyBound p.M))
    (fun _ => (lllWeight_bounds (dependencyBound p.M)).1.le)
    (fun _ => (lllWeight_bounds (dependencyBound p.M)).2.2)
    (actual_event_criterion P J p hJ hv)
  exact h.2.1 Finset.univ

end QEC.Coding.BDL26RandomPerturbation
