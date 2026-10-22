import QEC.Coding.ProbabilisticConstruction.Resampling.OccurrenceCounting
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Expected counts for measurable product-variable resampling

The finite count estimate follows from an injection into compatible witnesses,
their product probabilities, and the finite tree partition bound. Monotone
convergence then gives the expectation of the actual unbounded execution.
-/

namespace QEC.Coding.ProbabilisticConstruction.Resampling

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable [MeasurableSpace I] [MeasurableSingletonClass I]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]

theorem prefixCount_eq_indicator_sum (R : Table (X := X)) (T : ℕ) (i : I) :
    (prefixCount vars bad R T i : ℝ≥0∞) =
      ∑ n ∈ Finset.range T, ({R : Table (X := X) | selected vars bad R n = some i}).indicator
        (fun _ => (1 : ℝ≥0∞)) R := by
  classical
  simp only [prefixCount, occurrences, Finset.natCast_card_filter,
    Set.indicator_apply, Set.mem_setOf_eq]

theorem measurable_prefixCount (hbad : ∀ i, MeasurableSet (bad i)) (T : ℕ) (i : I) :
    Measurable (fun R : Table (X := X) => (prefixCount vars bad R T i : ℝ≥0∞)) := by
  classical
  simp_rw [prefixCount_eq_indicator_sum]
  apply Finset.measurable_sum
  intro n hn
  exact measurable_const.indicator
    ((measurable_selected vars bad hbad n) (measurableSet_singleton (some i)))

variable (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)]
variable (hbad : ∀ i, MeasurableSet (bad i))
variable (x : I → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
variable (hcrit : ∀ i, eventProbability vars ν bad i ≤
  x i * ∏ j ∈ (supportGraph vars).neighborFinset i, (1 - x j))

include hbad hx0 hx1 hcrit in
/-- Every finite prefix obeys the same asymmetric resampling expectation budget. -/
theorem expected_prefixCount_le (T : ℕ) (i : I) :
    (∫⁻ R, (prefixCount vars bad R T i : ℝ≥0∞) ∂tableLaw ν) ≤
      ENNReal.ofReal (resamplingBudget x i) := by
  classical
  let S : WitnessTree (supportGraph vars) (T + 1) i → Set (Table (X := X)) :=
    fun t => compatible vars bad i (witnessPaths (supportGraph vars) (T + 1) i t)
  have hS : ∀ t, MeasurableSet (S t) := fun t => measurableSet_compatible vars bad hbad i _
  calc
    (∫⁻ R, (prefixCount vars bad R T i : ℝ≥0∞) ∂tableLaw ν) ≤
        ∫⁻ R, ∑ t, (S t).indicator (fun _ => (1 : ℝ≥0∞)) R ∂tableLaw ν := by
      apply lintegral_mono
      intro R
      have hc := prefixCount_le_compatible vars bad R T i
      have hcast := (Nat.cast_le (α := ℝ≥0∞)).mpr hc
      simpa only [Finset.natCast_card_filter, Set.indicator_apply] using hcast
    _ = ∑ t, tableLaw ν (S t) := by
      rw [lintegral_finsetSum _ (fun t _ => measurable_const.indicator (hS t))]
      apply Finset.sum_congr rfl
      intro t ht
      change (∫⁻ R, (S t).indicator 1 R ∂tableLaw ν) = _
      exact lintegral_indicator_one (μ := tableLaw ν) (hS t)
    _ ≤ ∑ t : WitnessTree (supportGraph vars) (T + 1) i,
        ENNReal.ofReal (witnessWeight (supportGraph vars) (eventProbability vars ν bad) (T + 1) i t) := by
      apply Finset.sum_le_sum
      intro t ht
      exact tree_compatibility_probability_le vars ν bad hbad (T + 1) i t
    _ = ENNReal.ofReal (witnessPartition (supportGraph vars)
        (eventProbability vars ν bad) (T + 1) i) := by
      symm
      exact ENNReal.ofReal_sum_of_nonneg
        (fun t _ => witnessWeight_nonneg _ _ (eventProbability_nonneg vars ν bad) _ _ t)
    _ ≤ ENNReal.ofReal (resamplingBudget x i) := ENNReal.ofReal_le_ofReal
      (witnessPartition_le_budget _ _ x (eventProbability_nonneg vars ν bad)
        hx0 hx1 hcrit (T + 1) i)

/-- Total actual occurrences, allowing infinity for a nonterminating run. -/
noncomputable def totalCount (R : Table (X := X)) (i : I) : ℝ≥0∞ :=
  ⨆ T : ℕ, (prefixCount vars bad R T i : ℝ≥0∞)

include hbad in
theorem measurable_totalCount (i : I) :
    Measurable (fun R : Table (X := X) => totalCount vars bad R i) :=
  Measurable.iSup (fun T => measurable_prefixCount vars bad hbad T i)

include hbad hx0 hx1 hcrit in
/-- Moser--Tardos bound for each event on arbitrary measurable product coordinates. -/
theorem expected_totalCount_le (i : I) :
    (∫⁻ R, totalCount vars bad R i ∂tableLaw ν) ≤ ENNReal.ofReal (resamplingBudget x i) := by
  unfold totalCount
  rw [lintegral_iSup (fun T => measurable_prefixCount vars bad hbad T i)]
  · exact iSup_le (fun T => expected_prefixCount_le vars bad ν hbad x hx0 hx1 hcrit T i)
  · intro a b hab R
    exact (Nat.cast_le (α := ℝ≥0∞)).mpr (prefixCount_monotone vars bad R i hab)

/-- The total number of actual resampling transitions. -/
noncomputable def totalSteps (R : Table (X := X)) : ℝ≥0∞ :=
  ∑ i, totalCount vars bad R i

include hbad in
theorem measurable_totalSteps : Measurable (totalSteps vars bad (X := X)) :=
  Finset.measurable_sum _ (fun i _ => measurable_totalCount vars bad hbad i)

include hbad hx0 hx1 hcrit in
/-- Summing the per-event budgets bounds the actual total resampling expectation. -/
theorem expected_totalSteps_le :
    (∫⁻ R, totalSteps vars bad R ∂tableLaw ν) ≤
      ENNReal.ofReal (∑ i, resamplingBudget x i) := by
  unfold totalSteps
  rw [lintegral_finsetSum _ (fun i _ => measurable_totalCount vars bad hbad i)]
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => resamplingBudget_nonneg x hx0 hx1 i)]
  exact Finset.sum_le_sum (fun i _ => expected_totalCount_le vars bad ν hbad x hx0 hx1 hcrit i)

include hbad hx0 hx1 hcrit in
theorem totalSteps_finite_ae : ∀ᵐ R ∂tableLaw ν, totalSteps vars bad R < ∞ := by
  apply ae_lt_top (measurable_totalSteps vars bad hbad)
  exact (lt_of_le_of_lt (expected_totalSteps_le vars bad ν hbad x hx0 hx1 hcrit)
    ENNReal.ofReal_lt_top).ne

end QEC.Coding.ProbabilisticConstruction.Resampling
