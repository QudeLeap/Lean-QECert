import QEC.Coding.ProbabilisticConstruction.Resampling.WitnessCompatibility

/-!
# Actual history counters equal witness table ranks

The two finite bijections below identify deeper shared-variable nodes first with
earlier stamped nodes and then with all earlier uses of the variable in the log.
No counter agreement is supplied as a hypothesis.
-/

namespace QEC.Coding.ProbabilisticConstruction.Resampling

variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
variable (vars : I → Finset V)

/-- Number of uses of a variable strictly before a position in a finite log. -/
def historyCounter (root : I) (L : List I) (n : ℕ) (v : V) : ℕ :=
  ((Finset.range n).filter (fun k => v ∈ vars (historyLabel root L k))).card

/-- Earlier stamped nodes and deeper paths are in bijection for a shared variable. -/
theorem earlier_nodes_card_eq_rank (root : I) (L : List I) (p : List I × ℕ)
    (hp : p ∈ timedHistoryWitness (supportGraph vars) root 0 L)
    (v : V) (hpv : v ∈ vars (pathLabel root p.1)) :
    ((timedHistoryWitness (supportGraph vars) root 0 L).filter
      (fun q => v ∈ vars (pathLabel root q.1) ∧ q.2 < p.2)).card =
      variableRank vars root (historyWitness (supportGraph vars) root L) p.1 v := by
  unfold variableRank
  apply Finset.card_bij (fun q _ => q.1)
  · intro q hq
    obtain ⟨hqW, hqv, hqt⟩ := Finset.mem_filter.mp hq
    refine Finset.mem_filter.mpr ⟨?_, hqv, ?_⟩
    · rw [← timedHistoryWitness_paths (supportGraph vars) root 0 L]
      exact Finset.mem_image_of_mem Prod.fst hqW
    · exact (timedHistoryWitness_depth_time vars root 0 L q p hqW hp v hqv hpv).mp hqt
  · intro q hq r hr he
    exact timedHistoryWitness_path_injective (supportGraph vars) root 0 L
      (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hr).1 he
  · intro q hq
    obtain ⟨hqP, hqv, hqd⟩ := Finset.mem_filter.mp hq
    rw [← timedHistoryWitness_paths (supportGraph vars) root 0 L] at hqP
    obtain ⟨r, hr, he⟩ := Finset.mem_image.mp hqP
    have hrv : v ∈ vars (pathLabel root r.1) := he.symm ▸ hqv
    refine ⟨r, Finset.mem_filter.mpr ⟨hr, hrv, ?_⟩, he⟩
    apply (timedHistoryWitness_depth_time vars root 0 L r p hr hp v hrv hpv).mpr
    simpa [he] using hqd

/-- Backward closure includes exactly every earlier use of each represented variable. -/
theorem earlier_nodes_card_eq_counter (root : I) (L : List I) (p : List I × ℕ)
    (hp : p ∈ timedHistoryWitness (supportGraph vars) root 0 L)
    (v : V) (hpv : v ∈ vars (pathLabel root p.1)) :
    ((timedHistoryWitness (supportGraph vars) root 0 L).filter
      (fun q => v ∈ vars (pathLabel root q.1) ∧ q.2 < p.2)).card =
      historyCounter vars root L p.2 v := by
  unfold historyCounter
  apply Finset.card_bij (fun q _ => q.2)
  · intro q hq
    obtain ⟨hqW, hqv, hqt⟩ := Finset.mem_filter.mp hq
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hqt, ?_⟩
    have he := timedHistoryWitness_label (supportGraph vars) root 0 L q hqW
    simpa only [Nat.sub_zero] using he ▸ hqv
  · intro q hq r hr he
    exact timedHistoryWitness_time_injective (supportGraph vars) root 0 L
      (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hr).1 he
  · intro k hk
    obtain ⟨hkr, hkv⟩ := Finset.mem_filter.mp hk
    obtain ⟨q, hq, hqk, hqv⟩ := timedHistoryWitness_earlier_variable vars root 0 L
      p hp v hpv k (Nat.zero_le _) (Finset.mem_range.mp hkr) (by simpa using hkv)
    exact ⟨q, Finset.mem_filter.mpr ⟨hq, hqv, by simpa [hqk] using hkr⟩, hqk⟩

/-- Compatibility reads the exact actual-history column at every represented node. -/
theorem variableRank_eq_historyCounter (root : I) (L : List I) (p : List I × ℕ)
    (hp : p ∈ timedHistoryWitness (supportGraph vars) root 0 L)
    (v : V) (hpv : v ∈ vars (pathLabel root p.1)) :
    variableRank vars root (historyWitness (supportGraph vars) root L) p.1 v =
      historyCounter vars root L p.2 v :=
  (earlier_nodes_card_eq_rank vars root L p hp v hpv).symm.trans
    (earlier_nodes_card_eq_counter vars root L p hp v hpv)

end QEC.Coding.ProbabilisticConstruction.Resampling
