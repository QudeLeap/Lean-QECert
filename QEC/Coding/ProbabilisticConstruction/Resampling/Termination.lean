import QEC.Coding.ProbabilisticConstruction.Resampling.Expectation

/-! # Almost-sure termination and the actual returned assignment -/

namespace QEC.Coding.ProbabilisticConstruction.Resampling

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]

theorem prefixCount_succ (R : Table (X := X)) (T : ℕ) (i : I) :
    prefixCount vars bad R (T + 1) i = prefixCount vars bad R T i +
      if selected vars bad R T = some i then 1 else 0 := by
  classical
  by_cases h : selected vars bad R T = some i <;>
    simp [prefixCount, occurrences, Finset.range_add_one, Finset.filter_insert, h]

theorem sum_prefixCount_eq (R : Table (X := X)) (T : ℕ)
    (hactive : ∀ n < T, ∃ i, selected vars bad R n = some i) :
    ∑ i, prefixCount vars bad R T i = T := by
  induction T with
  | zero => simp [prefixCount, occurrences]
  | succ T ih =>
    obtain ⟨j, hj⟩ := hactive T (Nat.lt_succ_self _)
    simp_rw [prefixCount_succ, hj, Option.some.injEq]
    rw [Finset.sum_add_distrib, ih (fun n hn => hactive n (Nat.lt_succ_of_lt hn))]
    simp

/-- A finite execution reaches a clean scan. -/
def Halts (R : Table (X := X)) : Prop := ∃ n, selected vars bad R n = none

/-- An endless active execution would have at least n resamplings for every n. -/
theorem halts_of_totalSteps_lt_top (R : Table (X := X))
    (hf : totalSteps vars bad R < ∞) : Halts vars bad R := by
  by_contra hn
  have hactive : ∀ n, ∃ i, selected vars bad R n = some i := by
    intro n
    cases he : selected vars bad R n with
    | none => exact False.elim (hn ⟨n, he⟩)
    | some i => exact ⟨i, rfl⟩
  have hl : ∀ T : ℕ, (T : ℝ≥0∞) ≤ totalSteps vars bad R := by
    intro T
    have he := sum_prefixCount_eq vars bad R T (fun n _ => hactive n)
    calc
      (T : ℝ≥0∞) = ∑ i, (prefixCount vars bad R T i : ℝ≥0∞) := by exact_mod_cast he.symm
      _ ≤ totalSteps vars bad R := Finset.sum_le_sum (fun i _ => le_iSup
        (fun N => (prefixCount vars bad R N i : ℝ≥0∞)) T)
  have htop : ∞ ≤ totalSteps vars bad R := by
    rw [← ENNReal.iSup_natCast]
    exact iSup_le hl
  exact hf.not_ge htop

/-- Least clean scan; its value on a nonterminating table is a proof-side default. -/
noncomputable def haltTime (R : Table (X := X)) : ℕ := by
  classical
  exact if h : Halts vars bad R then Nat.find h else 0

theorem haltTime_spec (R : Table (X := X)) (h : Halts vars bad R) :
    selected vars bad R (haltTime vars bad R) = none := by
  simp only [haltTime, dif_pos h]
  exact Nat.find_spec h

theorem active_before_haltTime (R : Table (X := X)) (h : Halts vars bad R)
    (n : ℕ) (hn : n < haltTime vars bad R) : ∃ i, selected vars bad R n = some i := by
  cases he : selected vars bad R n with
  | some i => exact ⟨i, rfl⟩
  | none =>
    have hle : haltTime vars bad R ≤ n := by
      simpa [haltTime, h] using Nat.find_min' h he
    omega

theorem prefixCount_stable (R : Table (X := X)) (n : ℕ)
    (hn : selected vars bad R n = none) (k : ℕ) (i : I) :
    prefixCount vars bad R (n + k) i = prefixCount vars bad R n i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← Nat.add_assoc, prefixCount_succ, (halt_absorbing vars bad R n hn k).2]
    simpa using ih

theorem totalCount_eq_at_halt (R : Table (X := X)) (n : ℕ)
    (hn : selected vars bad R n = none) (i : I) :
    totalCount vars bad R i = (prefixCount vars bad R n i : ℝ≥0∞) := by
  apply le_antisymm
  · apply iSup_le
    intro T
    by_cases hT : T ≤ n
    · exact_mod_cast prefixCount_monotone vars bad R i hT
    · have he := prefixCount_stable vars bad R n hn (T - n) i
      rw [Nat.add_sub_of_le (by omega)] at he
      exact le_of_eq (congrArg (fun k : ℕ => (k : ℝ≥0∞)) he)
  · exact le_iSup (fun T => (prefixCount vars bad R T i : ℝ≥0∞)) n

/-- The total count equals the number of transitions before the least clean scan. -/
theorem totalSteps_eq_haltTime (R : Table (X := X)) (h : Halts vars bad R) :
    totalSteps vars bad R = (haltTime vars bad R : ℝ≥0∞) := by
  unfold totalSteps
  simp_rw [totalCount_eq_at_halt vars bad R _ (haltTime_spec vars bad R h)]
  exact_mod_cast sum_prefixCount_eq vars bad R (haltTime vars bad R)
    (active_before_haltTime vars bad R h)

/-- Actual returned assignment on terminating tables. -/
noncomputable def output (R : Table (X := X)) : ∀ v, X v :=
  assignment R (counters vars bad R (haltTime vars bad R))

theorem output_good (R : Table (X := X)) (h : Halts vars bad R) :
    ∀ i, output vars bad R ∉ localEvent vars bad i :=
  selected_none_good vars bad R _ (haltTime_spec vars bad R h)

variable [MeasurableSpace I] [MeasurableSingletonClass I]
variable (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)]
variable (hbad : ∀ i, MeasurableSet (bad i))

include hbad in
theorem measurableSet_halts : MeasurableSet {R : Table (X := X) | Halts vars bad R} := by
  have he : {R : Table (X := X) | Halts vars bad R} =
      ⋃ n : ℕ, {R | selected vars bad R n = none} := by ext R; simp [Halts]
  rw [he]
  exact MeasurableSet.iUnion (fun n => (measurable_selected vars bad hbad n)
    (measurableSet_singleton none))

include hbad in
theorem measurable_haltTime : Measurable (haltTime vars bad (X := X)) := by
  classical
  let p : Table (X := X) → ℕ → Prop := fun R n =>
    selected vars bad R n = none ∨ ¬ Halts vars bad R
  have hp : ∀ R, ∃ n, p R n := by
    intro R
    by_cases hR : Halts vars bad R
    · obtain ⟨n, hn⟩ := hR; exact ⟨n, Or.inl hn⟩
    · exact ⟨0, Or.inr hR⟩
  have hm : Measurable (fun R => Nat.find (hp R)) := measurable_find hp (fun n =>
    ((measurable_selected vars bad hbad n) (measurableSet_singleton none)).union
      (measurableSet_halts vars bad hbad).compl)
  convert hm using 1
  funext R
  by_cases hR : Halts vars bad R
  · simp only [haltTime, dif_pos hR]
    symm
    exact Nat.find_congr' (by intro n; simp [p, hR])
  · simp only [haltTime, dif_neg hR]
    symm
    exact Nat.find_eq_zero (hp R) |>.mpr (Or.inr hR)

include hbad in
theorem measurable_output : Measurable (output vars bad (X := X)) := by
  have hm : Measurable (fun z : Table (X := X) × ℕ => counters vars bad z.1 z.2) :=
    measurable_from_prod_countable_left (fun n => measurable_counters vars bad hbad n)
  exact measurable_assignment (hm.comp (measurable_id.prodMk (measurable_haltTime vars bad hbad)))

variable (x : I → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
variable (hcrit : ∀ i, eventProbability vars ν bad i ≤
  x i * ∏ j ∈ (supportGraph vars).neighborFinset i, (1 - x j))

include hbad hx0 hx1 hcrit in
/-- The actual product-table resampling algorithm halts and returns a good assignment almost surely. -/
theorem halts_and_output_good_ae :
    ∀ᵐ R ∂tableLaw ν, Halts vars bad R ∧ ∀ i, output vars bad R ∉ localEvent vars bad i := by
  filter_upwards [totalSteps_finite_ae vars bad ν hbad x hx0 hx1 hcrit] with R hR
  have hh := halts_of_totalSteps_lt_top vars bad R hR
  exact ⟨hh, output_good vars bad R hh⟩

end QEC.Coding.ProbabilisticConstruction.Resampling
