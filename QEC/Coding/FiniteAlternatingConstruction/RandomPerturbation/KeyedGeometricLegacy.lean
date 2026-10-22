import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.KeyedGeometricAvoidance

/-! Exact legacy specialization of the ENTIRE primitive-key event, including
its dependent support predicate. No equality with a different native key is asserted. -/
namespace QEC.Coding.BDL26KeyedGeometric
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory

theorem legacy_eligible_iff (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (s : Finset (Triangle P)) :
    KeyEligible P (triangleKey P) (triangleKey_injective P) J r s ↔ Eligible P J r s := Iff.rfl

/-- Underlying labels and every membership proof are retained in both directions. -/
def legacyEventEquiv (P : TannerSquarePresentation) (J : Vertex P → Space) (r : ℝ) :
    KeyEvent P (triangleKey P) (triangleKey_injective P) J r ≃ Event P J r where
  toFun e := ⟨e.val,(legacy_eligible_iff P J r e.val).mp e.property⟩
  invFun e := ⟨e.val,(legacy_eligible_iff P J r e.val).mpr e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem legacy_event_finset (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e : KeyEvent P (triangleKey P) (triangleKey_injective P) J r) :
    (legacyEventEquiv P J r e).val = e.val := rfl

theorem legacy_support (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e : KeyEvent P (triangleKey P) (triangleKey_injective P) J r) :
    keySupport P (triangleKey P) (triangleKey_injective P) J r e =
      eventSupport P J r (legacyEventEquiv P J r e) := rfl

theorem legacy_anchor (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e : KeyEvent P (triangleKey P) (triangleKey_injective P) J r) :
    keyAnchor P (triangleKey P) (triangleKey_injective P) J r e =
      eventAnchor P J r (legacyEventEquiv P J r e) := rfl

theorem legacy_center (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r l : ℝ) (K : ℕ) (e : KeyEvent P (triangleKey P) (triangleKey_injective P) J r)
    (g : Grid K) :
    keyCenter P (triangleKey P) (triangleKey_injective P) J r l K e g =
      eventCenter P J r l K (legacyEventEquiv P J r e) g := rfl

/-- The dependent coordinate type is transported by its original vertex value. -/
def legacySupportEquiv (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e : KeyEvent P (triangleKey P) (triangleKey_injective P) J r) :
    keySupport P (triangleKey P) (triangleKey_injective P) J r e ≃
      eventSupport P J r (legacyEventEquiv P J r e) where
  toFun v := ⟨v.val,v.property⟩
  invFun v := ⟨v.val,v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem legacy_eventVertex (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e : KeyEvent P (triangleKey P) (triangleKey_injective P) J r)
    (a : e.val) (i : Fin 3) :
    legacySupportEquiv P J r e (keyVertex P (triangleKey P) (triangleKey_injective P) J r e a i) =
      eventVertex P J r (legacyEventEquiv P J r e) ⟨a.val,a.property⟩ i := rfl

/-- Whole local assignments, rather than selected coordinates, are transported. -/
def legacyAssignmentEquiv (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e : KeyEvent P (triangleKey P) (triangleKey_injective P) J r) :
    (keySupport P (triangleKey P) (triangleKey_injective P) J r e → Space) ≃
      (eventSupport P J r (legacyEventEquiv P J r e) → Space) where
  toFun w v := w ((legacySupportEquiv P J r e).symm v)
  invFun w v := w (legacySupportEquiv P J r e v)
  left_inv w := by funext v; rfl
  right_inv w := by funext v; rfl

/-- Exact union of ALL grid centers and intersection of ALL triangles/coordinates. -/
theorem legacy_bad_predicate (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r l : ℝ) (K : ℕ) (e : KeyEvent P (triangleKey P) (triangleKey_injective P) J r) :
    (legacyAssignmentEquiv P J r e) ⁻¹'
      eventBad P J r l K (legacyEventEquiv P J r e) =
      keyBad P (triangleKey P) (triangleKey_injective P) J r l K e := rfl

theorem legacy_global_event (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r l : ℝ) (K : ℕ) (e : KeyEvent P (triangleKey P) (triangleKey_injective P) J r) :
    localEvent (X := fun _ : Vertex P => Space)
      (keySupport P (triangleKey P) (triangleKey_injective P) J r)
      (keyBad P (triangleKey P) (triangleKey_injective P) J r l K) e =
      localEvent (X := fun _ : Vertex P => Space)
        (eventSupport P J r) (eventBad P J r l K) (legacyEventEquiv P J r e) := rfl

theorem legacy_supportGraph (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e f : KeyEvent P (triangleKey P) (triangleKey_injective P) J r) :
    (supportGraph (keySupport P (triangleKey P) (triangleKey_injective P) J r)).Adj e f ↔
      (supportGraph (eventSupport P J r)).Adj
        (legacyEventEquiv P J r e) (legacyEventEquiv P J r f) := Iff.rfl

theorem legacy_neighbors (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e : KeyEvent P (triangleKey P) (triangleKey_injective P) J r) :
    ((supportGraph (keySupport P (triangleKey P) (triangleKey_injective P) J r)).neighborFinset e).image
      (legacyEventEquiv P J r) =
      (supportGraph (eventSupport P J r)).neighborFinset (legacyEventEquiv P J r e) := by
  classical
  ext f
  constructor
  · intro hf
    rcases Finset.mem_image.mp hf with ⟨g,hg,rfl⟩
    simpa only [SimpleGraph.mem_neighborFinset] using
      (legacy_supportGraph P J r e g).mp
        (by simpa only [SimpleGraph.mem_neighborFinset] using hg)
  · intro hf
    obtain ⟨g,rfl⟩ := (legacyEventEquiv P J r).surjective f
    refine Finset.mem_image.mpr ⟨g,?_,rfl⟩
    simpa only [SimpleGraph.mem_neighborFinset] using
      (legacy_supportGraph P J r e g).mpr
        (by simpa only [SimpleGraph.mem_neighborFinset] using hf)

theorem legacy_avoidance (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L) :
    KeyAvoid P (triangleKey P) (triangleKey_injective P) J p = geometricAvoidance P J p := rfl

/-- Arbitrary finite event selections, not only the full-universe avoidance set. -/
theorem legacy_finite_avoidance (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r l : ℝ) (K : ℕ)
    (s : Finset (KeyEvent P (triangleKey P) (triangleKey_injective P) J r)) :
    avoid (localEvent (X := fun _ : Vertex P => Space)
      (keySupport P (triangleKey P) (triangleKey_injective P) J r)
      (keyBad P (triangleKey P) (triangleKey_injective P) J r l K)) s =
      avoid (localEvent (X := fun _ : Vertex P => Space)
        (eventSupport P J r) (eventBad P J r l K))
        (s.image (legacyEventEquiv P J r)) := by
  classical
  ext w
  constructor
  · intro hw f hf
    rcases Finset.mem_image.mp hf with ⟨e,he,rfl⟩
    rw [← legacy_global_event P J r l K e]
    exact hw e he
  · intro hw e he
    rw [legacy_global_event P J r l K e]
    exact hw _ (Finset.mem_image.mpr ⟨e,he,rfl⟩)

theorem legacy_good (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L) :
    KeyGood P (triangleKey P) (triangleKey_injective P) J p =
      geometricSupport P p ∩ geometricAvoidance P J p := rfl

/-- The new probability proof recovers the original WHOLE legacy event. -/
theorem legacy_probability (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L) (e : Event P J (anchorRadius p.m)) :
    (geometricLaw P p).real (localEvent (eventSupport P J (anchorRadius p.m))
      (eventBad P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) e) ≤
      probabilityCoefficient (6*p.m) (capCutoff p.m)/(p.lambda : ℝ) :=
  key_probability_real_bound P (triangleKey P) (triangleKey_injective P) J p e

theorem legacy_criterion (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L) (hJ : IsBoundedDensityLocalMap P J p.t)
    (hv : BoundedValence P) (e : Event P J (anchorRadius p.m)) :
    (geometricLaw P p).real (localEvent (eventSupport P J (anchorRadius p.m))
      (eventBad P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) e) ≤
      lllWeight (dependencyBound p.M) *
        ∏ _f ∈ (supportGraph (eventSupport P J (anchorRadius p.m))).neighborFinset e,
          (1-lllWeight (dependencyBound p.M)) :=
  key_actual_event_criterion P (triangleKey P) (triangleKey_injective P) J p hJ hv e

theorem legacy_supported_geometry_density (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L) (hJ : IsBoundedDensityLocalMap P J p.t)
    (hv : BoundedValence P) :
    0 < (geometricLaw P p).real (geometricSupport P p ∩ geometricAvoidance P J p) ∧
    ∀ w ∈ geometricSupport P p ∩ geometricAvoidance P J p,
      IncomingFaceGeometry P (perturbationOddScale p) (perturbedMap P J p.lambda w)
        (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda) ∧
      ∀ z, ((familyHits (oldTriangleImage P (perturbedMap P J p.lambda w))
        (Metric.closedBall z 1)).card : ℝ) ≤ triangleDensityBound :=
  ⟨keyGood_positive P (triangleKey P) (triangleKey_injective P) J p hJ hv,
    keyGood_geometry_density P (triangleKey P) (triangleKey_injective P) J p hJ hv⟩

end QEC.Coding.BDL26KeyedGeometric
