import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.KeyedGeometricLegacy

/-! Universal native primitive-key supported avoidance at every actual alternating
state. The native key and valence proofs are discharged internally; the geometric
input map J and its legitimate incoming density/locality premise remain explicit. -/
namespace QEC.Coding.BDL26NativeGeometricAvoidance
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26FiniteAlternatingCore BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26KeyedGeometric
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory

noncomputable abbrev Presentation (S : OddScale) (n : ℕ) := (QEC.Coding.BDL26DecodingGraph.state S n).presentation
noncomputable abbrev Key (S : OddScale) (n : ℕ) := BDL26NativeTriangleColors.nativeKey S n
abbrev NativeEvent (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space) (r : ℝ) :=
  KeyEvent (Presentation S n) (Key S n) (BDL26NativeTriangleColors.nativeKey_injective S n) J r
noncomputable abbrev NativeSupport (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r : ℝ) :=
  keySupport (Presentation S n) (Key S n) (BDL26NativeTriangleColors.nativeKey_injective S n) J r
noncomputable abbrev NativeBad (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r l : ℝ) (K : ℕ) :=
  keyBad (Presentation S n) (Key S n) (BDL26NativeTriangleColors.nativeKey_injective S n) J r l K
noncomputable abbrev NativeGood (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {L : ℝ} (p : GeometricParameters L) :=
  KeyGood (Presentation S n) (Key S n) (BDL26NativeTriangleColors.nativeKey_injective S n) J p

theorem native_twelve_addresses (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r : ℝ) (e : NativeEvent S n J r) :
    (NativeSupport S n J r e).card = 12 ∧
      Function.Injective (fun s : (a : e.val) × Fin 3 =>
        triangleVertex (Presentation S n) s.1.val s.2) :=
  ⟨keySupport_card_eq_twelve _ _ (BDL26NativeTriangleColors.nativeKey_injective S n) J r e,
    keyEvent_addresses_injective _ _ (BDL26NativeTriangleColors.nativeKey_injective S n) J r e⟩

theorem native_joint_law (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r : ℝ) (e : NativeEvent S n J r)
    (ν : Vertex (Presentation S n) → Measure Space) [∀ v, IsProbabilityMeasure (ν v)] :
    (Measure.pi ν).map (fun w (a : e.val) i => w (triangleVertex (Presentation S n) a.val i)) =
      Measure.pi (fun a : e.val =>
        Measure.pi (fun i => ν (triangleVertex (Presentation S n) a.val i))) :=
  keyEvent_joint_law _ _ (BDL26NativeTriangleColors.nativeKey_injective S n) J r e ν

theorem native_dependency (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r l : ℝ) (K : ℕ)
    (ν : Vertex (Presentation S n) → Measure Space) [∀ v, IsProbabilityMeasure (ν v)] :
    HasDependencyGraph (Measure.pi ν) (localEvent (NativeSupport S n J r) (NativeBad S n J r l K))
      (supportGraph (NativeSupport S n J r)) :=
  keyEvents_have_dependency_graph _ _ (BDL26NativeTriangleColors.nativeKey_injective S n) J r l K ν

theorem native_probability (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {L : ℝ} (p : GeometricParameters L)
    (e : NativeEvent S n J (anchorRadius p.m)) :
    (geometricLaw (Presentation S n) p).real
      (localEvent (NativeSupport S n J (anchorRadius p.m))
        (NativeBad S n J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) e) ≤
      probabilityCoefficient (6*p.m) (capCutoff p.m)/(p.lambda : ℝ) :=
  key_probability_real_bound _ _ (BDL26NativeTriangleColors.nativeKey_injective S n) J p e

theorem native_degree (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap (Presentation S n) J p.t)
    (e : NativeEvent S n J (anchorRadius p.m)) :
    ((supportGraph (NativeSupport S n J (anchorRadius p.m))).neighborFinset e).card ≤
      dependencyBound p.M :=
  key_event_degree_le_of_density _ _ (BDL26NativeTriangleColors.nativeKey_injective S n)
    J (anchorRadius p.m) p.M p.t hJ (state_boundedValence S n) p.pool e

theorem native_criterion (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap (Presentation S n) J p.t)
    (e : NativeEvent S n J (anchorRadius p.m)) :
    (geometricLaw (Presentation S n) p).real
      (localEvent (NativeSupport S n J (anchorRadius p.m))
        (NativeBad S n J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) e) ≤
      lllWeight (dependencyBound p.M) *
        ∏ _f ∈ (supportGraph (NativeSupport S n J (anchorRadius p.m))).neighborFinset e,
          (1-lllWeight (dependencyBound p.M)) :=
  key_actual_event_criterion _ _ (BDL26NativeTriangleColors.nativeKey_injective S n)
    J p hJ (state_boundedValence S n) e

/-- Every level, parity, copy and odd scale is retained; no caller key/valence/probability witness. -/
theorem native_supported_avoidance (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap (Presentation S n) J p.t) :
    MeasurableSet (NativeGood S n J p) ∧
    0 < (geometricLaw (Presentation S n) p).real (NativeGood S n J p) ∧
    ∀ w ∈ NativeGood S n J p,
      IncomingFaceGeometry (Presentation S n) (perturbationOddScale p)
        (perturbedMap (Presentation S n) J p.lambda w)
        (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda) ∧
      ∀ z, ((familyHits (oldTriangleImage (Presentation S n)
        (perturbedMap (Presentation S n) J p.lambda w))
        (Metric.closedBall z 1)).card : ℝ) ≤ triangleDensityBound :=
  ⟨measurableSet_KeyGood _ _ (BDL26NativeTriangleColors.nativeKey_injective S n) J p,
    keyGood_positive _ _ (BDL26NativeTriangleColors.nativeKey_injective S n) J p hJ (state_boundedValence S n),
    keyGood_geometry_density _ _ (BDL26NativeTriangleColors.nativeKey_injective S n) J p hJ (state_boundedValence S n)⟩

theorem native_exists_geometry_density (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap (Presentation S n) J p.t) :
    ∃ w : Vertex (Presentation S n) → Space, w ∈ NativeGood S n J p ∧
      IncomingFaceGeometry (Presentation S n) (perturbationOddScale p)
        (perturbedMap (Presentation S n) J p.lambda w)
        (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda) ∧
      ∀ z, ((familyHits (oldTriangleImage (Presentation S n)
        (perturbedMap (Presentation S n) J p.lambda w))
        (Metric.closedBall z 1)).card : ℝ) ≤ triangleDensityBound :=
  exists_keyGood_geometry_density _ _ (BDL26NativeTriangleColors.nativeKey_injective S n)
    J p hJ (state_boundedValence S n)

end QEC.Coding.BDL26NativeGeometricAvoidance
