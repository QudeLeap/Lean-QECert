import QEC.Coding.ProbabilisticConstruction.Resampling.HistoryCounters
import Mathlib.Data.List.OfFn

/-!
# Actual executions produce compatible witnesses

A log is extracted from the real selected events. Absorption proves that every
entry before a selected event exists; counter agreement is then an induction on
the actual transition function.
-/

namespace QEC.Coding.ProbabilisticConstruction.Resampling

variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]

theorem selected_some_before (R : Table (X := X)) (n : ℕ) (i : I)
    (hi : selected vars bad R n = some i) (k : ℕ) (hk : k ≤ n) :
    ∃ j, selected vars bad R k = some j := by
  cases he : selected vars bad R k with
  | some j => exact ⟨j, rfl⟩
  | none =>
    have hn := (halt_absorbing vars bad R k he (n - k)).2
    rw [Nat.add_sub_of_le hk, hi] at hn
    cases hn

/-- The actual selected-event prefix before an occurrence, used only for proof. -/
noncomputable def occurrenceHistory (R : Table (X := X)) (n : ℕ) (i : I)
    (hi : selected vars bad R n = some i) : List I :=
  List.ofFn (fun k : Fin n => Classical.choose
    (selected_some_before vars bad R n i hi k.val (Nat.le_of_lt k.isLt)))

@[simp] theorem occurrenceHistory_length (R : Table (X := X)) (n : ℕ) (i : I)
    (hi : selected vars bad R n = some i) :
    (occurrenceHistory vars bad R n i hi).length = n := by
  simp [occurrenceHistory]

theorem occurrenceHistory_matches (R : Table (X := X)) (n : ℕ) (i : I)
    (hi : selected vars bad R n = some i) (k : ℕ) (hk : k ≤ n) :
    selected vars bad R k = some (historyLabel i (occurrenceHistory vars bad R n i hi) k) := by
  by_cases hkn : k < n
  · have hs := Classical.choose_spec (selected_some_before vars bad R n i hi k
      (Nat.le_of_lt hkn))
    simpa [historyLabel, occurrenceHistory, List.getElem?_eq_getElem, hkn] using hs
  · have he : k = n := by omega
    subst k
    simpa [historyLabel, List.getElem?_eq_none] using hi

theorem historyCounter_zero (root : I) (L : List I) (v : V) :
    historyCounter vars root L 0 v = 0 := by simp [historyCounter]

theorem historyCounter_succ (root : I) (L : List I) (n : ℕ) (v : V) :
    historyCounter vars root L (n + 1) v = historyCounter vars root L n v +
      if v ∈ vars (historyLabel root L n) then 1 else 0 := by
  classical
  by_cases h : v ∈ vars (historyLabel root L n)
  · simp [historyCounter, Finset.range_add_one, Finset.filter_insert, h]
  · simp [historyCounter, Finset.range_add_one, Finset.filter_insert, h]

/-- An actual finite log determines each table counter by counting prior support uses. -/
theorem counters_eq_historyCounter (R : Table (X := X)) (root : I) (L : List I)
    (hlog : ∀ k ≤ L.length, selected vars bad R k = some (historyLabel root L k))
    (n : ℕ) (hn : n ≤ L.length) (v : V) :
    counters vars bad R n v = historyCounter vars root L n v := by
  induction n with
  | zero => simp [counters, historyCounter]
  | succ n ih =>
    have hnl : n ≤ L.length := by omega
    rw [counters_succ_of_some vars bad R n _ (hlog n hnl), advance,
      historyCounter_succ, ih hnl]

/-- Every node of a real history witness reads the same table entries as its execution step. -/
theorem history_compatible (R : Table (X := X)) (root : I) (L : List I)
    (hlog : ∀ k ≤ L.length, selected vars bad R k = some (historyLabel root L k)) :
    R ∈ compatible vars bad root (historyWitness (supportGraph vars) root L) := by
  classical
  refine ⟨historyWitness_distinctVariableDepth vars root L, ?_⟩
  intro q
  have hq : q.val ∈ (timedHistoryWitness (supportGraph vars) root 0 L).image Prod.fst := by
    simpa only [timedHistoryWitness_paths] using q.property
  obtain ⟨p, hp, hpq⟩ := Finset.mem_image.mp hq
  have hpt : p.2 ≤ L.length := by
    simpa using (timedHistoryWitness_time_bounds (supportGraph vars) root 0 L p hp).2
  have hlabel : pathLabel root q.val = historyLabel root L p.2 := by
    simpa [hpq] using timedHistoryWitness_label (supportGraph vars) root 0 L p hp
  have hselected : selected vars bad R p.2 = some (pathLabel root q.val) := by
    rw [hlabel]; exact hlog p.2 hpt
  have hb := selected_some_bad vars bad R p.2 (pathLabel root q.val) hselected
  change (fun v : vars (pathLabel root q.val) =>
    R (v.val, variableRank vars root (historyWitness (supportGraph vars) root L)
      q.val v.val)) ∈ bad (pathLabel root q.val)
  have he : (fun v : vars (pathLabel root q.val) =>
      R (v.val, variableRank vars root (historyWitness (supportGraph vars) root L)
        q.val v.val)) =
      (fun v : vars (pathLabel root q.val) => assignment R (counters vars bad R p.2) v.val) := by
    funext v
    have hpv : v.val ∈ vars (pathLabel root p.1) := hpq.symm ▸ v.property
    have hr := variableRank_eq_historyCounter vars root L p hp v.val hpv
    rw [hpq] at hr
    rw [hr, ← counters_eq_historyCounter vars bad R root L hlog p.2 hpt v.val]
    rfl
  rw [he]
  exact hb

/-- Compatibility for the witness extracted from an actual selected occurrence. -/
theorem occurrenceHistory_compatible (R : Table (X := X)) (n : ℕ) (i : I)
    (hi : selected vars bad R n = some i) :
    R ∈ compatible vars bad i
      (historyWitness (supportGraph vars) i (occurrenceHistory vars bad R n i hi)) := by
  apply history_compatible vars bad R i _
  intro k hk
  exact occurrenceHistory_matches vars bad R n i hi k (by simpa using hk)

end QEC.Coding.ProbabilisticConstruction.Resampling
