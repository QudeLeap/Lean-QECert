import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.KeyedGeometricAvoidance
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.Execution
import QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling

/-!
# Original primitive-key table execution

The internal execution priority compares the four sorted
primitive keys.  Native execution below constructs this order through its paid
master-row interpreter; the finite sort here specifies its mathematical order.
The bound counts resampling transitions, not primitive operations or time.
-/
noncomputable section
namespace QEC.Coding.BDL26KeyedGeometricExecution
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26KeyedGeometric
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped Classical BigOperators ENNReal

def scanKey (P : TannerSquarePresentation) (k : Triangle P → ℕ)
    (hk : Function.Injective k) (J : Vertex P → Space) (r : ℝ)
    (e : KeyEvent P k hk J r) : List ℕ := (e.val.image k).sort (· ≤ ·)

theorem scanKey_injective (P : TannerSquarePresentation) (k : Triangle P → ℕ)
    (hk : Function.Injective k) (J : Vertex P → Space) (r : ℝ) :
    Function.Injective (scanKey P k hk J r) := by
  intro e f h
  have he := congrArg List.toFinset h
  simp only [scanKey, Finset.sort_toFinset] at he
  exact Subtype.ext (Finset.image_injective hk he)

theorem scanKey_length (P : TannerSquarePresentation) (k : Triangle P → ℕ)
    (hk : Function.Injective k) (J : Vertex P → Space) (r : ℝ)
    (e : KeyEvent P k hk J r) : (scanKey P k hk J r e).length = 4 := by
  rw [scanKey, Finset.length_sort, Finset.card_image_of_injective _ hk]
  exact e.property.1

/-- A named priority avoids the unrelated inherited finite-set inclusion. -/
def keyPriorityLE (P : TannerSquarePresentation) (k : Triangle P → ℕ)
    (hk : Function.Injective k) (J : Vertex P → Space) (r : ℝ)
    (e f : KeyEvent P k hk J r) : Prop := scanKey P k hk J r e ≤ scanKey P k hk J r f

instance keyPriorityDecidable (P : TannerSquarePresentation) (k : Triangle P → ℕ)
    (hk : Function.Injective k) (J : Vertex P → Space) (r : ℝ) :
    DecidableRel (keyPriorityLE P k hk J r) := fun _ _ => Classical.propDecidable _
instance keyPriorityTrans (P : TannerSquarePresentation) (k : Triangle P → ℕ)
    (hk : Function.Injective k) (J : Vertex P → Space) (r : ℝ) :
    IsTrans (KeyEvent P k hk J r) (keyPriorityLE P k hk J r) :=
  ⟨fun _ _ _ h1 h2 => le_trans h1 h2⟩
instance keyPriorityAntisymm (P : TannerSquarePresentation) (k : Triangle P → ℕ)
    (hk : Function.Injective k) (J : Vertex P → Space) (r : ℝ) :
    Std.Antisymm (keyPriorityLE P k hk J r) :=
  ⟨fun _ _ h1 h2 => scanKey_injective P k hk J r (le_antisymm h1 h2)⟩
instance keyPriorityTotal (P : TannerSquarePresentation) (k : Triangle P → ℕ)
    (hk : Function.Injective k) (J : Vertex P → Space) (r : ℝ) :
    Std.Total (keyPriorityLE P k hk J r) := ⟨fun _ _ => le_total _ _⟩

instance keyExecutionOrder (P : TannerSquarePresentation) (k : Triangle P → ℕ)
    (hk : Function.Injective k) (J : Vertex P → Space) (r : ℝ) :
    LinearOrder (KeyEvent P k hk J r) :=
  let order := LinearOrder.lift' (scanKey P k hk J r) (scanKey_injective P k hk J r)
  { order.toPartialOrder with
    le_total := order.le_total
    toDecidableLE := order.toDecidableLE
    toDecidableLT := order.toDecidableLT
    toDecidableEq := Subtype.instDecidableEq
    compare := fun a b => @compareOfLessAndEq (KeyEvent P k hk J r) a b order.toLT
      (order.toDecidableLT a b) Subtype.instDecidableEq
    compare_eq_compareOfLessAndEq := by intro a b; rfl }

theorem priority_iff (P : TannerSquarePresentation) (k : Triangle P → ℕ)
    (hk : Function.Injective k) (J : Vertex P → Space) (r : ℝ)
    (e f : KeyEvent P k hk J r) :
    (keyExecutionOrder P k hk J r).toLE.le e f ↔
      scanKey P k hk J r e ≤ scanKey P k hk J r f := Iff.rfl

instance keyEventMeasurable (P : TannerSquarePresentation) (k : Triangle P → ℕ)
    (hk : Function.Injective k) (J : Vertex P → Space) (r : ℝ) :
    MeasurableSpace (KeyEvent P k hk J r) := ⊤
instance keyEventSingleton (P : TannerSquarePresentation) (k : Triangle P → ℕ)
    (hk : Function.Injective k) (J : Vertex P → Space) (r : ℝ) :
    MeasurableSingletonClass (KeyEvent P k hk J r) := ⟨fun _ => trivial⟩
instance keyBadDecidable (P : TannerSquarePresentation) (k : Triangle P → ℕ)
    (hk : Function.Injective k) (J : Vertex P → Space) (r l : ℝ) (K : ℕ)
    (e : KeyEvent P k hk J r) : DecidablePred (· ∈ keyBad P k hk J r l K e) :=
  fun _ => Classical.propDecidable _

abbrev originalTable (P : TannerSquarePresentation) := Table (X := fun _ : Vertex P => Space)
def tableMeasure (P : TannerSquarePresentation) {L : ℝ} (p : GeometricParameters L) :
    Measure (originalTable P) := by
  letI (v : Vertex P) := vertexLaw_probability P
    ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
  exact tableLaw (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m))

def result (P : TannerSquarePresentation) (k : Triangle P → ℕ)
    (hk : Function.Injective k) (J : Vertex P → Space) {L : ℝ}
    (p : GeometricParameters L) (T : originalTable P) : Vertex P → Space :=
  output (keySupport P k hk J (anchorRadius p.m))
    (keyBad P k hk J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T

theorem measurable_result (P : TannerSquarePresentation) (k : Triangle P → ℕ)
    (hk : Function.Injective k) (J : Vertex P → Space) {L : ℝ}
    (p : GeometricParameters L) : Measurable (result P k hk J p) :=
  measurable_output _ _ (measurableSet_keyBad P k hk J _ _ _)

/-- On a nonterminating table the original default is its column-zero assignment. -/
theorem result_nonhalting (P : TannerSquarePresentation) (k : Triangle P → ℕ)
    (hk : Function.Injective k) (J : Vertex P → Space) {L : ℝ}
    (p : GeometricParameters L) (T : originalTable P)
    (h : ¬ Halts (keySupport P k hk J (anchorRadius p.m))
      (keyBad P k hk J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T) :
    result P k hk J p T = fun v => T (v,0) := by
  simp only [result, Resampling.output, Resampling.haltTime, dif_neg h,
    Resampling.counters]
  change Resampling.assignment T (fun _ : Vertex P => 0) = (fun v => T (v,0))
  rfl

theorem result_support_ae (P : TannerSquarePresentation) (k : Triangle P → ℕ)
    (hk : Function.Injective k) (J : Vertex P → Space) {L : ℝ}
    (p : GeometricParameters L) :
    ∀ᵐ T ∂tableMeasure P p, result P k hk J p T ∈ geometricSupport P p := by
  letI (v : Vertex P) := vertexLaw_probability P
    ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
  have hm : 0 < 6*p.m := by have h := p.m_two; omega
  have hmR : (0 : ℝ) < (6*p.m : ℕ) := by exact_mod_cast hm
  have hlR : (0 : ℝ) < p.lambda := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one p.lambda_one)
  filter_upwards [assignment_cap_support P (mul_pos hmR hlR)
    (capCutoff_bounds p.m_two).2] with T hT
  exact hT _

theorem halts_good_ae (P : TannerSquarePresentation) (k : Triangle P → ℕ)
    (hk : Function.Injective k) (J : Vertex P → Space) {L : ℝ}
    (p : GeometricParameters L) (hJ : IsBoundedDensityLocalMap P J p.t)
    (hv : BoundedValence P) :
    ∀ᵐ T ∂tableMeasure P p,
      Halts (keySupport P k hk J (anchorRadius p.m))
        (keyBad P k hk J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T ∧
      result P k hk J p T ∈ KeyGood P k hk J p := by
  letI (v : Vertex P) := vertexLaw_probability P
    ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
  have hrun := halts_and_output_good_ae
    (keySupport P k hk J (anchorRadius p.m))
    (keyBad P k hk J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda))
    (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m))
    (measurableSet_keyBad P k hk J _ _ _) (fun _ => lllWeight (dependencyBound p.M))
    (fun _ => (lllWeight_bounds _).1.le) (fun _ => (lllWeight_bounds _).2.2)
    (by
      intro e
      simpa only [eventProbability, measureReal_def] using
        key_actual_event_criterion P k hk J p hJ hv e)
  filter_upwards [hrun, result_support_ae P k hk J p] with T hT hs
  exact ⟨hT.1, hs, fun e _ => hT.2 e⟩

/-- The actual event-cardinality budget, with no caller-supplied step estimate. -/
theorem expected_steps_le (P : TannerSquarePresentation) (k : Triangle P → ℕ)
    (hk : Function.Injective k) (J : Vertex P → Space) {L : ℝ}
    (p : GeometricParameters L) (hJ : IsBoundedDensityLocalMap P J p.t)
    (hv : BoundedValence P) :
    (∫⁻ T, totalSteps (keySupport P k hk J (anchorRadius p.m))
      (keyBad P k hk J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T
      ∂tableMeasure P p) ≤
    ENNReal.ofReal ((Fintype.card (KeyEvent P k hk J (anchorRadius p.m)) : ℝ) *
      (lllWeight (dependencyBound p.M) / (1-lllWeight (dependencyBound p.M)))) := by
  letI (v : Vertex P) := vertexLaw_probability P
    ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
  have h := expected_totalSteps_le
    (keySupport P k hk J (anchorRadius p.m))
    (keyBad P k hk J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda))
    (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m))
    (measurableSet_keyBad P k hk J _ _ _) (fun _ => lllWeight (dependencyBound p.M))
    (fun _ => (lllWeight_bounds _).1.le) (fun _ => (lllWeight_bounds _).2.2)
    (by
      intro e
      simpa only [eventProbability, measureReal_def] using
        key_actual_event_criterion P k hk J p hJ hv e)
  simpa [resamplingBudget, tableMeasure] using h

theorem expected_steps_explicit_finite (P : TannerSquarePresentation) (k : Triangle P → ℕ)
    (hk : Function.Injective k) (J : Vertex P → Space) {L : ℝ}
    (p : GeometricParameters L) (hJ : IsBoundedDensityLocalMap P J p.t)
    (hv : BoundedValence P) :
    (∫⁻ T, totalSteps (keySupport P k hk J (anchorRadius p.m))
      (keyBad P k hk J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T
      ∂tableMeasure P p) ≤
      ENNReal.ofReal ((Fintype.card (Triangle P) : ℝ)^4 *
        (lllWeight (dependencyBound p.M)/(1-lllWeight (dependencyBound p.M)))) ∧
    ENNReal.ofReal ((Fintype.card (Triangle P) : ℝ)^4 *
        (lllWeight (dependencyBound p.M)/(1-lllWeight (dependencyBound p.M)))) < ∞ := by
  refine ⟨(expected_steps_le P k hk J p hJ hv).trans ?_, ENNReal.ofReal_lt_top⟩
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast keyEvent_card_le P k hk J (anchorRadius p.m)
  · exact div_nonneg (lllWeight_bounds _).1.le (sub_pos.mpr (lllWeight_bounds _).2.2).le

/-- Whole generic execution endpoint: actual table law, halting, cap support,
complete face geometry, and every-center labeled density for this output. -/
theorem execution_geometry_ae (P : TannerSquarePresentation) (k : Triangle P → ℕ)
    (hk : Function.Injective k) (J : Vertex P → Space) {L : ℝ}
    (p : GeometricParameters L) (hJ : IsBoundedDensityLocalMap P J p.t)
    (hv : BoundedValence P) :
    Measurable (result P k hk J p) ∧
    ∀ᵐ T ∂tableMeasure P p,
      Halts (keySupport P k hk J (anchorRadius p.m))
        (keyBad P k hk J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T ∧
      result P k hk J p T ∈ KeyGood P k hk J p ∧
      IncomingFaceGeometry P (perturbationOddScale p)
        (perturbedMap P J p.lambda (result P k hk J p T))
        (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda) ∧
      ∀ z, ((familyHits (oldTriangleImage P
        (perturbedMap P J p.lambda (result P k hk J p T)))
        (Metric.closedBall z 1)).card : ℝ) ≤ triangleDensityBound := by
  refine ⟨measurable_result P k hk J p, ?_⟩
  filter_upwards [halts_good_ae P k hk J p hJ hv] with T hT
  exact ⟨hT.1, hT.2, keyGood_geometry_density P k hk J p hJ hv _ hT.2⟩

end QEC.Coding.BDL26KeyedGeometricExecution
