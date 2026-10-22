import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.KeyedGeometricProbability
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.KeyedGeometricCounts
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.GoodAssignments
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.RandomizedEmbeddingStep

/-!
Project-derived internal/API primitive-key event closure, pinned BDL26 paper.tex
1409–1424. Speculative stacked source over audited PR1608 H7aec; no kernel,
recursive embedding, execution-law or expected-time completion is claimed.
-/
namespace QEC.Coding.BDL26KeyedGeometric
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory ProbabilityTheory
theorem key_actual_event_criterion (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    {densityLower : ℝ} (p : GeometricParameters densityLower)
    (hJ : IsBoundedDensityLocalMap P J p.t) (hv : BoundedValence P)
    (e : KeyEvent P key hk J (anchorRadius p.m)) :
    (Measure.pi (vertexLaw P ((6*p.m : ℕ)* (p.lambda : ℝ)) (capCutoff p.m))).real
      (localEvent (keySupport P key hk J (anchorRadius p.m))
        (keyBad P key hk J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) e) ≤
      lllWeight (dependencyBound p.M)*
        ∏ _j ∈ (supportGraph (keySupport P key hk J (anchorRadius p.m))).neighborFinset e,
          (1-lllWeight (dependencyBound p.M)) := by
  have hc := capCutoff_bounds p.m_two
  have ha : 0 < 6*p.m := by
    have hm := p.m_two
    omega
  have hb := key_event_probability_real_decay P key hk J (anchorRadius p.m) (6*p.m) p.lambda
    ha p.lambda_one e hc.1 hc.2
  apply uniform_lll_criterion (dependencyBound p.M) _
    (key_event_degree_le_of_density P key hk J (anchorRadius p.m) p.M p.t hJ hv p.pool e)
  exact hb.trans p.probability_ratio

/-- The actual continuous product law gives positive mass to simultaneous avoidance.
All dependency and probability hypotheses are derived from the incoming density and valence. -/
theorem key_actual_avoidance_positive (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    {densityLower : ℝ} (p : GeometricParameters densityLower)
    (hJ : IsBoundedDensityLocalMap P J p.t) (hv : BoundedValence P) :
    0 < (Measure.pi (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m))).real
      (avoid (localEvent (keySupport P key hk J (anchorRadius p.m))
        (keyBad P key hk J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda))) Finset.univ) := by
  have hc := capCutoff_bounds p.m_two
  letI (v : Vertex P) := vertexLaw_probability P
    ((6*p.m : ℕ)*(p.lambda : ℝ)) hc.2 v
  have h := product_localLemma
    (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m))
    (keySupport P key hk J (anchorRadius p.m))
    (keyBad P key hk J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda))
    (measurableSet_keyBad P key hk J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda))
    (fun _ => lllWeight (dependencyBound p.M))
    (fun _ => (lllWeight_bounds (dependencyBound p.M)).1.le)
    (fun _ => (lllWeight_bounds (dependencyBound p.M)).2.2)
    (key_actual_event_criterion P key hk J p hJ hv)
  exact h.2.1 Finset.univ

theorem key_four_hits_mem_event (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J p : Vertex P → Space)
    (t radius : ℝ) (alpha lambda : ℕ)
    (hJ : IsBoundedDensityLocalMap P J t) (hl : 1 ≤ lambda)
    (hp : ∀ v, ‖p v‖ ≤ (alpha : ℝ)*lambda) (e : KeyEvent P key hk J radius) (z : Space)
    (hits : ∀ a ∈ e.val,
      (oldTriangleImage P (perturbedMap P J lambda p) a ∩ Metric.closedBall z 1).Nonempty) :
    p ∈ localEvent (keySupport P key hk J radius)
      (keyBad P key hk J radius lambda ((alpha+2)*lambda)) e := by
  have hlR : (1 : ℝ) ≤ lambda := by exact_mod_cast hl
  have hl0 : (0 : ℝ) ≤ lambda := by positivity
  have hz := hit_center_near_anchor P J p t ((alpha : ℝ)*lambda) lambda hJ hl0 hp
    (keyAnchor P key hk J radius e) z (hits _ (keyAnchor_mem P key hk J radius e))
  have hball : z ∈ Metric.closedBall ((lambda : ℝ) • oldAnchor P J (keyAnchor P key hk J radius e))
      (((alpha+2)*lambda : ℕ) : ℝ) := by
    change dist z _ ≤ _
    push_cast
    nlinarith
  obtain ⟨g,hg⟩ := exists_grid_cover ((alpha+2)*lambda)
    ((lambda : ℝ) • oldAnchor P J (keyAnchor P key hk J radius e)) z hball
  apply (mem_keyEvent P key hk J radius lambda ((alpha+2)*lambda) e p).mpr
  refine ⟨g,?_⟩
  intro a
  obtain ⟨y,hy,hyz⟩ := hits a.val a.property
  have hnet : dist z (keyCenter P key hk J radius lambda ((alpha+2)*lambda) e g) ≤ 1 := hg
  have hynet := unitBall_subset_radiusTwo z _ hnet hyz
  rw [oldTriangleImage_eq] at hy
  refine ⟨y,?_,hynet⟩
  exact hy

theorem key_avoidance_triangle_density (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J w : Vertex P → Space)
    {densityLower : ℝ} (p : GeometricParameters densityLower)
    (hJ : IsBoundedDensityLocalMap P J p.t) (hv : BoundedValence P)
    (hw : ∀ v, ‖w v‖ ≤ (6*p.m : ℕ)*(p.lambda : ℝ))
    (havoid : ∀ e : KeyEvent P key hk J (anchorRadius p.m),
      w ∉ localEvent (keySupport P key hk J (anchorRadius p.m))
        (keyBad P key hk J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) e)
    (z : Space) :
    ((familyHits (oldTriangleImage P (perturbedMap P J p.lambda w))
      (Metric.closedBall z 1)).card : ℝ) ≤ triangleDensityBound := by
  classical
  let hits := familyHits (oldTriangleImage P (perturbedMap P J p.lambda w))
    (Metric.closedBall z 1)
  have hfiber : ∀ c : Fin 3 → Fin 56,
      (hits.filter (fun a => BDL26NativeTriangleColors.boundedPolicyColor P key hv a = c)).card ≤ 3 := by
    intro c
    by_contra h
    have hfour : 4 ≤ (hits.filter (fun a => BDL26NativeTriangleColors.boundedPolicyColor P key hv a = c)).card := by omega
    obtain ⟨s,hsub,hcard⟩ := Finset.exists_subset_card_eq hfour
    have hsHit : ∀ a ∈ s,
        (oldTriangleImage P (perturbedMap P J p.lambda w) a ∩ Metric.closedBall z 1).Nonempty := by
      intro a ha
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp (hsub ha)).1).2
    have hsColor : ∀ a ∈ s, ∀ b ∈ s, BDL26NativeTriangleColors.policyColor P key a = BDL26NativeTriangleColors.policyColor P key b := by
      intro a ha b hb
      have he := (Finset.mem_filter.mp (hsub ha)).2.trans
        (Finset.mem_filter.mp (hsub hb)).2.symm
      funext i
      exact congrArg Fin.val (congrFun he i)
    have hsClose : ∀ a ∈ s, ∀ b ∈ s,
        dist (oldAnchor P J a) (oldAnchor P J b) ≤ (anchorRadius p.m : ℝ) := by
      intro a ha b hb
      have hl : (1 : ℝ) ≤ p.lambda := by exact_mod_cast p.lambda_one
      have hd := common_hits_anchor_distance P J w p.t (6*p.m : ℕ) p.lambda
        hJ hl hw a b z (hsHit a ha) (hsHit b hb)
      simp only [Nat.cast_mul,Nat.cast_ofNat] at hd
      simp only [anchorRadius,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
      linarith
    let e : KeyEvent P key hk J (anchorRadius p.m) := ⟨s,hcard,hsColor,hsClose⟩
    exact havoid e (key_four_hits_mem_event P key hk J w p.t (anchorRadius p.m) (6*p.m) p.lambda
      hJ p.lambda_one hw e z hsHit)
  have hc := Finset.card_le_mul_card_image hits 3 (fun c _ => hfiber c)
  have himage : (hits.image (BDL26NativeTriangleColors.boundedPolicyColor P key hv)).card ≤ 56^3 := by
    calc
      _ ≤ Fintype.card (Fin 3 → Fin 56) := Finset.card_le_univ _
      _ = _ := BDL26NativeTriangleColors.palette_card
  have hn : hits.card ≤ triangleDensityBound := by
    have hbound := hc.trans (Nat.mul_le_mul_left 3 himage)
    norm_num [triangleDensityBound] at hbound ⊢
    omega
  exact_mod_cast hn

noncomputable def KeyAvoid (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L) : Set (Vertex P → Space) :=
  avoid (localEvent (keySupport P key hk J (anchorRadius p.m))
    (keyBad P key hk J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda))) Finset.univ

theorem measurableSet_KeyAvoid (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L) : MeasurableSet (KeyAvoid P key hk J p) := by
  apply measurableSet_avoid
  exact measurableSet_localEvent _ _ (measurableSet_keyBad P key hk J _ _ _)

/-- Intersecting with the cap-supported assignments preserves all positive avoidance mass. -/
theorem key_supported_avoidance_positive (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap P J p.t) (hv : BoundedValence P) :
    0 < (geometricLaw P p).real (geometricSupport P p ∩ KeyAvoid P key hk J p) := by
  have he := Measure.measure_inter_eq_of_ae (s := KeyAvoid P key hk J p) (geometricSupport_ae P p)
  change 0 < ((geometricLaw P p) (geometricSupport P p ∩ KeyAvoid P key hk J p)).toReal
  rw [he]
  exact key_actual_avoidance_positive P key hk J p hJ hv

/-- An actual finite-product sample has all cap constraints, avoids every geometric event,
and obeys the desired density of labeled auxiliary triangles. -/
theorem key_exists_supported_dense_assignment (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap P J p.t) (hv : BoundedValence P) :
    ∃ w : Vertex P → Space, w ∈ geometricSupport P p ∧ w ∈ KeyAvoid P key hk J p ∧
      ∀ z, ((familyHits (oldTriangleImage P (perturbedMap P J p.lambda w))
        (Metric.closedBall z 1)).card : ℝ) ≤ triangleDensityBound := by
  have hpos := key_supported_avoidance_positive P key hk J p hJ hv
  have hn : (geometricSupport P p ∩ KeyAvoid P key hk J p).Nonempty := by
    by_contra h
    have he := Set.not_nonempty_iff_eq_empty.mp h
    simpa only [he,measureReal_empty,lt_self_iff_false] using hpos
  obtain ⟨w,hw,ha⟩ := hn
  refine ⟨w,hw,ha,?_⟩
  intro z
  exact key_avoidance_triangle_density P key hk J w p hJ hv (fun v => (hw v).1.le)
    (fun e => ha e (Finset.mem_univ e)) z


/-- The actual cap support and finite avoidance are both retained in the good set. -/
noncomputable def KeyGood (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space) {L : ℝ}
    (p : GeometricParameters L) : Set (Vertex P → Space) :=
  geometricSupport P p ∩ KeyAvoid P key hk J p

theorem measurableSet_KeyGood (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space) {L : ℝ}
    (p : GeometricParameters L) : MeasurableSet (KeyGood P key hk J p) :=
  (measurableSet_geometricSupport P p).inter (measurableSet_KeyAvoid P key hk J p)

theorem keyGood_positive (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space) {L : ℝ}
    (p : GeometricParameters L) (hJ : IsBoundedDensityLocalMap P J p.t)
    (hv : BoundedValence P) : 0 < (geometricLaw P p).real (KeyGood P key hk J p) :=
  key_supported_avoidance_positive P key hk J p hJ hv

/-- Full deterministic geometry AND labeled density for every actual good assignment. -/
theorem keyGood_geometry_density (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space) {L : ℝ}
    (p : GeometricParameters L) (hJ : IsBoundedDensityLocalMap P J p.t)
    (hv : BoundedValence P) (w : Vertex P → Space) (hw : w ∈ KeyGood P key hk J p) :
    IncomingFaceGeometry P (perturbationOddScale p) (perturbedMap P J p.lambda w)
      (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda) ∧
    ∀ z, ((familyHits (oldTriangleImage P (perturbedMap P J p.lambda w))
      (Metric.closedBall z 1)).card : ℝ) ≤ triangleDensityBound := by
  refine ⟨geometricSupport_incoming_geometry P J p hJ (perturbationOddScale p)
    (perturbationOddScale_bounds p).1.le w hw.1,?_⟩
  intro z
  exact key_avoidance_triangle_density P key hk J w p hJ hv (fun v => (hw.1 v).1.le)
    (fun e => hw.2 e (Finset.mem_univ e)) z

/-- Existence follows from the positive ORIGINAL product measure, never from a supplied witness. -/
theorem exists_keyGood_geometry_density (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space) {L : ℝ}
    (p : GeometricParameters L) (hJ : IsBoundedDensityLocalMap P J p.t)
    (hv : BoundedValence P) :
    ∃ w : Vertex P → Space, w ∈ KeyGood P key hk J p ∧
      IncomingFaceGeometry P (perturbationOddScale p) (perturbedMap P J p.lambda w)
        (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda) ∧
      ∀ z, ((familyHits (oldTriangleImage P (perturbedMap P J p.lambda w))
        (Metric.closedBall z 1)).card : ℝ) ≤ triangleDensityBound := by
  have hpos := keyGood_positive P key hk J p hJ hv
  have hn : (KeyGood P key hk J p).Nonempty := by
    by_contra h
    have he := Set.not_nonempty_iff_eq_empty.mp h
    simpa only [he,measureReal_empty,lt_self_iff_false] using hpos
  obtain ⟨w,hw⟩ := hn
  exact ⟨w,hw,keyGood_geometry_density P key hk J p hJ hv w hw⟩

end QEC.Coding.BDL26KeyedGeometric
