import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.AvoidanceDensity

/-! # Positive probability of actual cap-supported good assignments -/

namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory

noncomputable def geometricLaw (P : TannerSquarePresentation) {L : ℝ}
    (p : GeometricParameters L) :=
  Measure.pi (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m))

def geometricSupport (P : TannerSquarePresentation) {L : ℝ}
    (p : GeometricParameters L) : Set (Vertex P → Space) :=
  {w | ∀ v, w v ∈ displacementCap ((6*p.m : ℕ)*(p.lambda : ℝ))
    (vertexAxis P v) (capCutoff p.m)}

noncomputable def geometricAvoidance (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L) : Set (Vertex P → Space) :=
  avoid (localEvent (eventSupport P J (anchorRadius p.m))
    (eventBad P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda))) Finset.univ

theorem measurableSet_geometricSupport (P : TannerSquarePresentation) {L : ℝ}
    (p : GeometricParameters L) : MeasurableSet (geometricSupport P p) := by
  simp only [geometricSupport,Set.setOf_forall]
  exact MeasurableSet.iInter (fun v =>
    (measurableSet_displacementCap _ _ _).preimage (measurable_pi_apply v))

theorem measurableSet_geometricAvoidance (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L) : MeasurableSet (geometricAvoidance P J p) := by
  apply measurableSet_avoid
  exact measurableSet_localEvent _ _ (measurableSet_eventBad P J _ _ _)

theorem geometricSupport_ae (P : TannerSquarePresentation) {L : ℝ}
    (p : GeometricParameters L) : ∀ᵐ w ∂geometricLaw P p, w ∈ geometricSupport P p := by
  have hm : (0 : ℝ) < p.m := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) p.m_two)
  have hl : (0 : ℝ) < p.lambda := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one p.lambda_one)
  have hmn : 0 < 6*p.m := by
    have hmN := p.m_two
    omega
  have hm6 : (0 : ℝ) < (6*p.m : ℕ) := by exact_mod_cast hmn
  exact finite_cap_support P (mul_pos hm6 hl) (capCutoff_bounds p.m_two).2

/-- Intersecting with the cap-supported assignments preserves all positive avoidance mass. -/
theorem supported_avoidance_positive (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap P J p.t) (hv : BoundedValence P) :
    0 < (geometricLaw P p).real (geometricSupport P p ∩ geometricAvoidance P J p) := by
  have he := Measure.measure_inter_eq_of_ae (s := geometricAvoidance P J p) (geometricSupport_ae P p)
  change 0 < ((geometricLaw P p) (geometricSupport P p ∩ geometricAvoidance P J p)).toReal
  rw [he]
  exact actual_avoidance_positive P J p hJ hv

/-- An actual finite-product sample has all cap constraints, avoids every geometric event,
and obeys the desired density of labeled auxiliary triangles. -/
theorem exists_supported_dense_assignment (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap P J p.t) (hv : BoundedValence P) :
    ∃ w : Vertex P → Space, w ∈ geometricSupport P p ∧ w ∈ geometricAvoidance P J p ∧
      ∀ z, ((familyHits (oldTriangleImage P (perturbedMap P J p.lambda w))
        (Metric.closedBall z 1)).card : ℝ) ≤ triangleDensityBound := by
  have hpos := supported_avoidance_positive P J p hJ hv
  have hn : (geometricSupport P p ∩ geometricAvoidance P J p).Nonempty := by
    by_contra h
    have he := Set.not_nonempty_iff_eq_empty.mp h
    simpa only [he,measureReal_empty,lt_self_iff_false] using hpos
  obtain ⟨w,hw,ha⟩ := hn
  refine ⟨w,hw,ha,?_⟩
  intro z
  exact avoidance_triangle_density P J w p hJ hv (fun v => (hw v).1.le)
    (fun e => ha e (Finset.mem_univ e)) z

/-- Every actual supported assignment has the source side, diagonal and three width bounds. -/
theorem geometricSupport_incoming_geometry (P : TannerSquarePresentation)
    (J : Vertex P → Space) {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap P J p.t) (S : OddScale)
    (hscale : (2*(6*(p.m : ℝ))+1)*(p.lambda : ℝ) ≤ S.ell)
    (w : Vertex P → Space) (hw : w ∈ geometricSupport P p) :
    IncomingFaceGeometry P S (perturbedMap P J p.lambda w)
      (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda) := by
  have hl : (0 : ℝ) < p.lambda := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one p.lambda_one)
  apply supported_incoming_geometry P J p.t hJ p.m_two hl S hscale w
  intro v
  simpa only [Nat.cast_mul,Nat.cast_ofNat,capCutoff] using hw v

end QEC.Coding.BDL26RandomPerturbation
