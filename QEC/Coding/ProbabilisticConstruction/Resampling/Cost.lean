import QEC.Coding.ProbabilisticConstruction.Resampling.Termination

/-!
# Idealized continuous primitive cost

Costs describe exact continuous samples, local predicate queries and their finite
bookkeeping. They are primitive costs, not a bound assumed for the whole run.
The measured execution includes every active scan, its coordinate refreshes,
the final clean scan, initial samples and output. No finite-bit claim is made.
-/

namespace QEC.Coding.ProbabilisticConstruction.Resampling

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

section Scan

variable {Ω I : Type*} (B : I → Set Ω) [∀ i, DecidablePred (· ∈ B i)]

/-- Sum actual query costs until the first true predicate, or the end of the scan. -/
def scanCost (queryCost : I → ℝ≥0∞) : List I → Ω → ℝ≥0∞
  | [], _ => 0
  | i :: tail, ω => queryCost i + if ω ∈ B i then 0 else scanCost queryCost tail ω

theorem scanCost_le (queryCost : I → ℝ≥0∞) (C : ℝ≥0∞)
    (hC : ∀ i, queryCost i ≤ C) (L : List I) (ω : Ω) :
    scanCost B queryCost L ω ≤ (L.length : ℝ≥0∞) * C := by
  induction L with
  | nil => simp [scanCost]
  | cons i L ih =>
    simp only [scanCost, List.length_cons, Nat.cast_add, Nat.cast_one]
    calc
      queryCost i + (if ω ∈ B i then 0 else scanCost B queryCost L ω) ≤
          C + (L.length : ℝ≥0∞) * C := add_le_add (hC i) (by split_ifs <;> simp_all)
      _ = ((L.length : ℝ≥0∞) + 1) * C := by ring

theorem measurable_scanCost [MeasurableSpace Ω] (hB : ∀ i, MeasurableSet (B i))
    (queryCost : I → ℝ≥0∞) (L : List I) : Measurable (scanCost B queryCost L) := by
  induction L with
  | nil => exact measurable_const
  | cons i L ih => exact measurable_const.add (Measurable.ite (hB i) measurable_const ih)

end Scan

variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]

/-- Actual finite scan at one execution state. -/
def executionScanCost (queryCost : I → ℝ≥0∞) (R : Table (X := X)) (n : ℕ) : ℝ≥0∞ :=
  scanCost (localEvent vars bad) queryCost (Finset.univ.sort (· ≤ ·))
    (assignment R (counters vars bad R n))

/-- Actual refreshed-coordinate primitive costs for one transition. -/
noncomputable def executionRefreshCost (sampleCost : V → ℝ≥0∞) (R : Table (X := X)) (n : ℕ) : ℝ≥0∞ :=
  match selected vars bad R n with
  | none => 0
  | some i => ∑ v ∈ vars i, sampleCost v

open scoped Classical in
/-- Cost of the actual run, with infinity for nontermination. -/
noncomputable def executionCost (queryCost : I → ℝ≥0∞) (sampleCost : V → ℝ≥0∞)
    (outputCost : ℝ≥0∞) (R : Table (X := X)) : ℝ≥0∞ :=
  if Halts vars bad R then
    (∑ v, sampleCost v) + outputCost +
      (∑ n ∈ Finset.range (haltTime vars bad R + 1), executionScanCost vars bad queryCost R n) +
      ∑ n ∈ Finset.range (haltTime vars bad R), executionRefreshCost vars bad sampleCost R n
  else ∞

theorem executionScanCost_le (queryCost : I → ℝ≥0∞) (C : ℝ≥0∞)
    (hC : ∀ i, queryCost i ≤ C) (R : Table (X := X)) (n : ℕ) :
    executionScanCost vars bad queryCost R n ≤ (Fintype.card I : ℝ≥0∞) * C := by
  simpa [executionScanCost] using scanCost_le (localEvent vars bad) queryCost C hC
    (Finset.univ.sort (· ≤ ·)) (assignment R (counters vars bad R n))

theorem executionRefreshCost_le (sampleCost : V → ℝ≥0∞) (C : ℝ≥0∞)
    (hC : ∀ v, sampleCost v ≤ C) (q : ℕ) (hq : ∀ i, (vars i).card ≤ q)
    (R : Table (X := X)) (n : ℕ) :
    executionRefreshCost vars bad sampleCost R n ≤ (q : ℝ≥0∞) * C := by
  unfold executionRefreshCost
  split
  · exact zero_le
  · rename_i i hi
    calc
      ∑ v ∈ vars i, sampleCost v ≤ ∑ _v ∈ vars i, C := Finset.sum_le_sum (fun v _ => hC v)
      _ = ((vars i).card : ℝ≥0∞) * C := by simp [nsmul_eq_mul]
      _ ≤ (q : ℝ≥0∞) * C := mul_le_mul' ((Nat.cast_le (α := ℝ≥0∞)).mpr (hq i)) le_rfl

/-- Primitive bounds give a pointwise affine cost bound for every terminating run. -/
theorem executionCost_le (queryCost : I → ℝ≥0∞) (sampleCost : V → ℝ≥0∞)
    (initialCost outputCost C : ℝ≥0∞) (hinit : ∑ v, sampleCost v ≤ initialCost)
    (hquery : ∀ i, queryCost i ≤ C)
    (hsample : ∀ v, sampleCost v ≤ C) (q : ℕ) (hq : ∀ i, (vars i).card ≤ q)
    (R : Table (X := X)) (hR : Halts vars bad R) :
    executionCost vars bad queryCost sampleCost outputCost R ≤
      initialCost + outputCost + (Fintype.card I : ℝ≥0∞) * C +
        ((Fintype.card I : ℝ≥0∞) * C + (q : ℝ≥0∞) * C) * totalSteps vars bad R := by
  rw [executionCost, if_pos hR, totalSteps_eq_haltTime vars bad R hR]
  calc
    _ ≤ initialCost + outputCost +
        (∑ _n ∈ Finset.range (haltTime vars bad R + 1), (Fintype.card I : ℝ≥0∞) * C) +
        ∑ _n ∈ Finset.range (haltTime vars bad R), (q : ℝ≥0∞) * C := by
      apply add_le_add
      · exact add_le_add (add_le_add hinit le_rfl)
          (Finset.sum_le_sum (fun n _ => executionScanCost_le vars bad queryCost C hquery R n))
      · exact Finset.sum_le_sum (fun n _ => executionRefreshCost_le vars bad sampleCost C hsample q hq R n)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one]; ring

variable [MeasurableSpace I] [MeasurableSingletonClass I]
variable (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)]
variable (hbad : ∀ i, MeasurableSet (bad i))

include hbad in
theorem measurable_executionScanCost (queryCost : I → ℝ≥0∞) (n : ℕ) :
    Measurable (fun R : Table (X := X) => executionScanCost vars bad queryCost R n) :=
  (measurable_scanCost _ (measurableSet_localEvent vars bad hbad) queryCost _).comp
    (measurable_assignment (measurable_counters vars bad hbad n))

include hbad in
theorem measurable_executionRefreshCost (sampleCost : V → ℝ≥0∞) (n : ℕ) :
    Measurable (fun R : Table (X := X) => executionRefreshCost vars bad sampleCost R n) := by
  have hm : Measurable (fun j : Option I => match j with
      | none => (0 : ℝ≥0∞) | some i => ∑ v ∈ vars i, sampleCost v) :=
    measurable_of_countable _
  exact hm.comp (measurable_selected vars bad hbad n)

include hbad in
theorem measurable_executionCost (queryCost : I → ℝ≥0∞) (sampleCost : V → ℝ≥0∞)
    (outputCost : ℝ≥0∞) :
    Measurable (executionCost vars bad queryCost sampleCost outputCost (X := X)) := by
  have hscan : Measurable (fun z : Table (X := X) × ℕ =>
      ∑ n ∈ Finset.range (z.2 + 1), executionScanCost vars bad queryCost z.1 n) :=
    measurable_from_prod_countable_left (fun N => Finset.measurable_sum (Finset.range (N + 1))
      (fun n _ => measurable_executionScanCost vars bad hbad queryCost n))
  have hrefresh : Measurable (fun z : Table (X := X) × ℕ =>
      ∑ n ∈ Finset.range z.2, executionRefreshCost vars bad sampleCost z.1 n) :=
    measurable_from_prod_countable_left (fun N => Finset.measurable_sum (Finset.range N)
      (fun n _ => measurable_executionRefreshCost vars bad hbad sampleCost n))
  have ht := measurable_id.prodMk (measurable_haltTime vars bad hbad)
  exact Measurable.ite (measurableSet_halts vars bad hbad)
    ((measurable_const.add (hscan.comp ht)).add (hrefresh.comp ht)) measurable_const

variable (x : I → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
variable (hcrit : ∀ i, eventProbability vars ν bad i ≤
  x i * ∏ j ∈ (supportGraph vars).neighborFinset i, (1 - x j))

include hbad hx0 hx1 hcrit in
/-- Explicit idealized expected cost, including initialization, the last scan, and output. -/
theorem expected_executionCost_le (queryCost : I → ℝ≥0∞) (sampleCost : V → ℝ≥0∞)
    (initialCost outputCost C : ℝ≥0∞) (hinit : ∑ v, sampleCost v ≤ initialCost)
    (hquery : ∀ i, queryCost i ≤ C)
    (hsample : ∀ v, sampleCost v ≤ C) (q : ℕ) (hq : ∀ i, (vars i).card ≤ q) :
    (∫⁻ R, executionCost vars bad queryCost sampleCost outputCost R ∂tableLaw ν) ≤
      initialCost + outputCost + (Fintype.card I : ℝ≥0∞) * C +
        ((Fintype.card I : ℝ≥0∞) * C + (q : ℝ≥0∞) * C) *
          ENNReal.ofReal (∑ i, resamplingBudget x i) := by
  calc
    _ ≤ ∫⁻ R, initialCost + outputCost + (Fintype.card I : ℝ≥0∞) * C +
        ((Fintype.card I : ℝ≥0∞) * C + (q : ℝ≥0∞) * C) * totalSteps vars bad R ∂tableLaw ν := by
      apply lintegral_mono_ae
      filter_upwards [halts_and_output_good_ae vars bad ν hbad x hx0 hx1 hcrit] with R hR
      exact executionCost_le vars bad queryCost sampleCost initialCost outputCost C
        hinit hquery hsample q hq R hR.1
    _ = initialCost + outputCost + (Fintype.card I : ℝ≥0∞) * C +
        ((Fintype.card I : ℝ≥0∞) * C + (q : ℝ≥0∞) * C) *
          (∫⁻ R, totalSteps vars bad R ∂tableLaw ν) := by
      rw [lintegral_add_left measurable_const, lintegral_const_mul _
        (measurable_totalSteps vars bad hbad)]
      simp
    _ ≤ _ := add_le_add le_rfl (mul_le_mul' le_rfl
      (expected_totalSteps_le vars bad ν hbad x hx0 hx1 hcrit))

end QEC.Coding.ProbabilisticConstruction.Resampling
