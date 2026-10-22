import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.EventEncoding
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.EventPriority
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.FullEventQuery
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.GoodAssignments
import QEC.Coding.ProbabilisticConstruction.Resampling.Termination

/-! # Actual continuous-table resampling and its supported dense output

The finite enumeration fixes a deterministic scan order. Cost of representing the
finite input and deciding geometric predicates is accounted for separately; no
cost bound is asserted here for classical enumeration or predicate selection.
-/

namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory

noncomputable instance geometricEventOrder (P : TannerSquarePresentation)
    (J : Vertex P → Space) (radius : ℝ) : LinearOrder (Event P J radius) :=
  let order := LinearOrder.lift' (eventScanKey P J radius) (eventScanKey_injective P J radius)
  { order.toPartialOrder with
    le_total := order.le_total
    toDecidableLE := order.toDecidableLE
    toDecidableLT := order.toDecidableLT
    toDecidableEq := Subtype.instDecidableEq
    compare := fun a b => @compareOfLessAndEq (Event P J radius) a b order.toLT
      (order.toDecidableLT a b) Subtype.instDecidableEq
    compare_eq_compareOfLessAndEq := by intro a b; rfl }

/-- The named priority is definitionally the merged resampling order dictionary. -/
theorem geometricEventOrder_priority (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e f : Event P J r) :
    (geometricEventOrder P J r).toLE.le e f ↔ eventPriorityLE P J r e f := Iff.rfl

instance geometricEventMeasurableSpace (P : TannerSquarePresentation)
    (J : Vertex P → Space) (radius : ℝ) : MeasurableSpace (Event P J radius) := ⊤

instance geometricEventMeasurableSingleton (P : TannerSquarePresentation)
    (J : Vertex P → Space) (radius : ℝ) : MeasurableSingletonClass (Event P J radius) :=
  ⟨fun _ => trivial⟩

noncomputable instance geometricBadDecidable (P : TannerSquarePresentation)
    (J : Vertex P → Space) (radius lambda : ℝ) (K : ℕ) (e : Event P J radius) :
    DecidablePred (· ∈ eventBad P J radius lambda K e) := fun p =>
  if h : (fullEventQuery P J radius lambda K e p).1 = true then
    isTrue ((fullEventQuery_correct P J radius lambda K e p).mp h)
  else isFalse (fun hp => h ((fullEventQuery_correct P J radius lambda K e p).mpr hp))

noncomputable def geometricOutput (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L) (T : Table (X := fun _ : Vertex P => Space)) :
    Vertex P → Space :=
  output (eventSupport P J (anchorRadius p.m))
    (eventBad P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T

theorem measurable_geometricOutput (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L) : Measurable (geometricOutput P J p) :=
  measurable_output _ _ (measurableSet_eventBad P J _ _ _)

theorem geometric_halts_and_avoids_ae (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap P J p.t) (hv : BoundedValence P) :
    letI (v : Vertex P) := vertexLaw_probability P
      ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
    ∀ᵐ T ∂tableLaw (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m)),
      Halts (eventSupport P J (anchorRadius p.m))
        (eventBad P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T ∧
      geometricOutput P J p T ∈ geometricAvoidance P J p := by
  letI (v : Vertex P) := vertexLaw_probability P
    ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
  have hrun := halts_and_output_good_ae
    (eventSupport P J (anchorRadius p.m))
    (eventBad P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda))
    (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m))
    (measurableSet_eventBad P J _ _ _) (fun _ => lllWeight (dependencyBound p.M))
    (fun _ => (lllWeight_bounds _).1.le) (fun _ => (lllWeight_bounds _).2.2)
    (by
      intro e
      simpa only [eventProbability,measureReal_def] using actual_event_criterion P J p hJ hv e)
  filter_upwards [hrun] with T hT
  exact ⟨hT.1,fun e _ => hT.2 e⟩

theorem geometric_output_support_ae (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L) :
    letI (v : Vertex P) := vertexLaw_probability P
      ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
    ∀ᵐ T ∂tableLaw (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m)),
      geometricOutput P J p T ∈ geometricSupport P p := by
  letI (v : Vertex P) := vertexLaw_probability P
    ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
  have hmn : 0 < 6*p.m := by have hm := p.m_two; omega
  have hmR : (0 : ℝ) < (6*p.m : ℕ) := by exact_mod_cast hmn
  have hlR : (0 : ℝ) < p.lambda := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one p.lambda_one)
  have hsupport := assignment_cap_support P (mul_pos hmR hlR) (capCutoff_bounds p.m_two).2
  filter_upwards [hsupport] with T hs
  exact hs _

theorem geometric_execution_good_ae (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap P J p.t) (hv : BoundedValence P) :
    letI (v : Vertex P) := vertexLaw_probability P
      ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
    ∀ᵐ T ∂tableLaw (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m)),
      Halts (eventSupport P J (anchorRadius p.m))
        (eventBad P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T ∧
      geometricOutput P J p T ∈ geometricSupport P p ∧
      geometricOutput P J p T ∈ geometricAvoidance P J p := by
  letI (v : Vertex P) := vertexLaw_probability P
    ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
  filter_upwards [geometric_halts_and_avoids_ae P J p hJ hv,
    geometric_output_support_ae P J p] with T hT hs
  exact ⟨hT.1,hs,hT.2⟩

theorem geometric_output_density_ae (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap P J p.t) (hv : BoundedValence P) :
    letI (v : Vertex P) := vertexLaw_probability P
      ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
    ∀ᵐ T ∂tableLaw (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m)),
      ∀ z, ((familyHits (oldTriangleImage P
        (perturbedMap P J p.lambda (geometricOutput P J p T)))
          (Metric.closedBall z 1)).card : ℝ) ≤ triangleDensityBound := by
  letI (v : Vertex P) := vertexLaw_probability P
    ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
  filter_upwards [geometric_execution_good_ae P J p hJ hv] with T hT
  intro z
  exact avoidance_triangle_density P J _ p hJ hv (fun v => (hT.2.1 v).1.le)
    (fun e => hT.2.2 e (Finset.mem_univ e)) z

end QEC.Coding.BDL26RandomPerturbation
