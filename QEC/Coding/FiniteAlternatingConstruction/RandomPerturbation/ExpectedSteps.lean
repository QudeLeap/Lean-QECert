import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.Execution
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.InputSize

/-! # Polynomial bound for the actual resampling count

This counts resampling steps. Arithmetic query, preprocessing, initialization,
and final-scan costs require the separate predicate/cost bridge.
-/

namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal BigOperators

theorem lll_resampling_budget_le_one {I : Type*} (D : ℕ) (i : I) :
    resamplingBudget (fun _ : I => lllWeight D) i ≤ 1 := by
  have hx := lllWeight_bounds D
  unfold resamplingBudget
  apply (div_le_iff₀ (sub_pos.mpr hx.2.2)).mpr
  linarith [hx.2.1]

theorem geometric_expected_steps_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap P J p.t) (hv : BoundedValence P) :
    letI (v : Vertex P) := vertexLaw_probability P
      ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
    (∫⁻ T, totalSteps (eventSupport P J (anchorRadius p.m))
      (eventBad P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T
      ∂tableLaw (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m))) ≤
        (Fintype.card (Triangle P)^4 : ℕ) := by
  letI (v : Vertex P) := vertexLaw_probability P
    ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
  have hsteps := expected_totalSteps_le
    (eventSupport P J (anchorRadius p.m))
    (eventBad P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda))
    (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m))
    (measurableSet_eventBad P J _ _ _) (fun _ => lllWeight (dependencyBound p.M))
    (fun _ => (lllWeight_bounds _).1.le) (fun _ => (lllWeight_bounds _).2.2)
    (by
      intro e
      simpa only [eventProbability,measureReal_def] using actual_event_criterion P J p hJ hv e)
  have hsum : (∑ e : Event P J (anchorRadius p.m),
      resamplingBudget (fun _ => lllWeight (dependencyBound p.M)) e) ≤
      (Fintype.card (Event P J (anchorRadius p.m)) : ℝ) := by
    calc
      _ ≤ ∑ _e : Event P J (anchorRadius p.m), (1 : ℝ) :=
        Finset.sum_le_sum (fun e _ => lll_resampling_budget_le_one _ e)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  calc
    _ ≤ _ := hsteps
    _ ≤ ENNReal.ofReal (Fintype.card (Event P J (anchorRadius p.m)) : ℝ) :=
      ENNReal.ofReal_le_ofReal hsum
    _ = (Fintype.card (Event P J (anchorRadius p.m)) : ℕ) := by simp
    _ ≤ _ := by exact_mod_cast event_card_le P J (anchorRadius p.m)

/-- The actual admissibility roots rule out isolated-check inflation of the input size. -/
theorem triangle_labels_le_qubits (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (hv : BoundedValence P) : Fintype.card (Triangle P) ≤ 65*Fintype.card P.Q := by
  have h := input_labels_le_qubits P A hv
  omega

end QEC.Coding.BDL26RandomPerturbation
