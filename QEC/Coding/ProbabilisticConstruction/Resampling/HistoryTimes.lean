import QEC.Coding.ProbabilisticConstruction.Resampling.HistoryWitness

/-!
# Time stamps of backward history witnesses

The path projection is the previously constructed proper witness. Time stamps
retain the actual position of each included resampling in the input history.
-/

namespace QEC.Coding.ProbabilisticConstruction.Resampling

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]

/-- Paths with their actual chronological positions. The root is at offset + length. -/
noncomputable def timedHistoryWitness (root : I) : ℕ → List I → Finset (List I × ℕ)
  | offset, [] => {([], offset)}
  | offset, j :: rest =>
      let W := timedHistoryWitness root (offset + 1) rest
      let P := W.image Prod.fst
      if h : (attachmentCandidates G root j P).Nonempty then
        insert (attachmentParent G root j P h ++ [j], offset) W
      else W

theorem timedHistoryWitness_paths (root : I) (offset : ℕ) (L : List I) :
    (timedHistoryWitness G root offset L).image Prod.fst = historyWitness G root L := by
  induction L generalizing offset with
  | nil => simp [timedHistoryWitness, historyWitness]
  | cons j L ih =>
    simp only [timedHistoryWitness, historyWitness, extendWitness]
    rw [ih]
    split_ifs <;> simp [Finset.image_insert, ih]

theorem timedHistoryWitness_root (root : I) (offset : ℕ) (L : List I) :
    ([], offset + L.length) ∈ timedHistoryWitness G root offset L := by
  induction L generalizing offset with
  | nil => simp [timedHistoryWitness]
  | cons j L ih =>
    have hh := ih (offset + 1)
    simp only [timedHistoryWitness]
    split_ifs with h
    · apply Finset.mem_insert_of_mem
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
    · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

theorem timedHistoryWitness_time_bounds (root : I) (offset : ℕ) (L : List I)
    (p : List I × ℕ) (hp : p ∈ timedHistoryWitness G root offset L) :
    offset ≤ p.2 ∧ p.2 ≤ offset + L.length := by
  induction L generalizing offset with
  | nil =>
    have he : p = ([], offset) := by simpa [timedHistoryWitness] using hp
    simp [he]
  | cons j L ih =>
    simp only [timedHistoryWitness] at hp
    split_ifs at hp with h
    · rcases Finset.mem_insert.mp hp with he | hp
      · subst p; simp
      · have hb := ih (offset + 1) hp; simp only [List.length_cons]; omega
    · have hb := ih (offset + 1) hp; simp only [List.length_cons]; omega

/-- Every represented path has a unique time stamp. -/
theorem timedHistoryWitness_path_injective (root : I) (offset : ℕ) (L : List I) :
    Set.InjOn Prod.fst (timedHistoryWitness G root offset L : Set (List I × ℕ)) := by
  induction L generalizing offset with
  | nil => simp [timedHistoryWitness, Set.InjOn]
  | cons j L ih =>
    intro a ha b hb he
    simp only [timedHistoryWitness] at ha hb
    split_ifs at ha hb with h
    · have hn := newPath_not_mem G root j
        ((timedHistoryWitness G root (offset + 1) L).image Prod.fst) h
      rcases Finset.mem_insert.mp ha with rfl | ha
      · rcases Finset.mem_insert.mp hb with rfl | hb
        · rfl
        · apply False.elim
          apply hn
          have hm := Finset.mem_image_of_mem Prod.fst hb
          simpa only [← he] using hm
      · rcases Finset.mem_insert.mp hb with rfl | hb
        · apply False.elim
          apply hn
          have hm := Finset.mem_image_of_mem Prod.fst ha
          simpa only [he] using hm
        · exact ih (offset + 1) ha hb he
    · exact ih (offset + 1) ha hb he

/-- No two represented nodes originate at the same actual resampling time. -/
theorem timedHistoryWitness_time_injective (root : I) (offset : ℕ) (L : List I) :
    Set.InjOn Prod.snd (timedHistoryWitness G root offset L : Set (List I × ℕ)) := by
  induction L generalizing offset with
  | nil => simp [timedHistoryWitness, Set.InjOn]
  | cons j L ih =>
    intro a ha b hb he
    simp only [timedHistoryWitness] at ha hb
    split_ifs at ha hb with h
    · rcases Finset.mem_insert.mp ha with rfl | ha
      · rcases Finset.mem_insert.mp hb with rfl | hb
        · rfl
        · have ht := (timedHistoryWitness_time_bounds G root (offset + 1) L b hb).1
          simp only [Prod.snd] at he; omega
      · rcases Finset.mem_insert.mp hb with rfl | hb
        · have ht := (timedHistoryWitness_time_bounds G root (offset + 1) L a ha).1
          simp only [Prod.snd] at he; omega
        · exact ih (offset + 1) ha hb he
    · exact ih (offset + 1) ha hb he

/-- The root is the default label only at the end of the finite input history. -/
def historyLabel (root : I) (L : List I) (n : ℕ) : I := L[n]?.getD root

theorem timedHistoryWitness_label (root : I) (offset : ℕ) (L : List I)
    (p : List I × ℕ) (hp : p ∈ timedHistoryWitness G root offset L) :
    pathLabel root p.1 = historyLabel root L (p.2 - offset) := by
  induction L generalizing offset with
  | nil =>
    have he : p = ([], offset) := by simpa [timedHistoryWitness] using hp
    simp [he, historyLabel]
  | cons j L ih =>
    simp only [timedHistoryWitness] at hp
    split_ifs at hp with h
    · rcases Finset.mem_insert.mp hp with rfl | hp
      · simp [historyLabel]
      · have hb := (timedHistoryWitness_time_bounds G root (offset + 1) L p hp).1
        have he : p.2 - offset = (p.2 - (offset + 1)) + 1 := by omega
        simpa [historyLabel, he] using ih (offset + 1) hp
    · have hb := (timedHistoryWitness_time_bounds G root (offset + 1) L p hp).1
      have he : p.2 - offset = (p.2 - (offset + 1)) + 1 := by omega
      simpa [historyLabel, he] using ih (offset + 1) hp

section VariableSupports

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (vars : I → Finset V)

theorem candidate_of_shared_variable (root j : I) (P : Finset (List I))
    (p : List I) (hp : p ∈ P) (v : V) (hj : v ∈ vars j)
    (hv : v ∈ vars (pathLabel root p)) :
    p ∈ attachmentCandidates (supportGraph vars) root j P := by
  apply Finset.mem_filter.mpr
  refine ⟨hp, ?_⟩
  rw [mem_closedNeighbors]
  by_cases he : j = pathLabel root p
  · exact Or.inl he
  · exact Or.inr ⟨Ne.symm he, fun hd => Finset.disjoint_left.mp hd hv hj⟩

/-- Shared-variable nodes are ordered by depth in exactly the reverse chronological order. -/
theorem timedHistoryWitness_depth_time (root : I) (offset : ℕ) (L : List I)
    (p q : List I × ℕ)
    (hp : p ∈ timedHistoryWitness (supportGraph vars) root offset L)
    (hq : q ∈ timedHistoryWitness (supportGraph vars) root offset L)
    (v : V) (hpv : v ∈ vars (pathLabel root p.1)) (hqv : v ∈ vars (pathLabel root q.1)) :
    p.2 < q.2 ↔ q.1.length < p.1.length := by
  induction L generalizing offset with
  | nil =>
    have he : p = ([], offset) := by simpa [timedHistoryWitness] using hp
    have hf : q = ([], offset) := by simpa [timedHistoryWitness] using hq
    simp [he, hf]
  | cons j L ih =>
    simp only [timedHistoryWitness] at hp hq
    split_ifs at hp hq with h
    · rcases Finset.mem_insert.mp hp with rfl | hp
      · rcases Finset.mem_insert.mp hq with rfl | hq
        · simp
        · have ht := (timedHistoryWitness_time_bounds (supportGraph vars) root
            (offset + 1) L q hq).1
          have hjv : v ∈ vars j := by simpa using hpv
          have hc := candidate_of_shared_variable vars root j _ q.1
            (Finset.mem_image_of_mem Prod.fst hq) v hjv hqv
          have hd := newPath_deeper_than_candidate (supportGraph vars) root j _ h q.1 hc
          constructor
          · intro _; exact hd
          · intro _; simp only [Prod.snd]; omega
      · rcases Finset.mem_insert.mp hq with rfl | hq
        · have ht := (timedHistoryWitness_time_bounds (supportGraph vars) root
            (offset + 1) L p hp).1
          have hjv : v ∈ vars j := by simpa using hqv
          have hc := candidate_of_shared_variable vars root j _ p.1
            (Finset.mem_image_of_mem Prod.fst hp) v hjv hpv
          have hd := newPath_deeper_than_candidate (supportGraph vars) root j _ h p.1 hc
          constructor <;> intro he <;> simp only [Prod.snd, Prod.fst] at he ⊢ <;> omega
        · exact ih (offset + 1) hp hq
    · exact ih (offset + 1) hp hq

/-- The history construction never puts two nodes sharing a variable at the same depth. -/
theorem historyWitness_shared_depth_injective (root : I) (L : List I)
    (p q : List I) (hp : p ∈ historyWitness (supportGraph vars) root L)
    (hq : q ∈ historyWitness (supportGraph vars) root L)
    (v : V) (hpv : v ∈ vars (pathLabel root p)) (hqv : v ∈ vars (pathLabel root q))
    (hd : p.length = q.length) : p = q := by
  rw [← timedHistoryWitness_paths (supportGraph vars) root 0 L] at hp hq
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
  have hforward := timedHistoryWitness_depth_time vars root 0 L a b ha hb v hpv hqv
  have hback := timedHistoryWitness_depth_time vars root 0 L b a hb ha v hqv hpv
  have ht : a.2 = b.2 := by omega
  exact congrArg Prod.fst (timedHistoryWitness_time_injective (supportGraph vars) root 0 L ha hb ht)

/-- Every earlier use of a node's variable is included in its backward witness. -/
theorem timedHistoryWitness_earlier_variable (root : I) (offset : ℕ) (L : List I)
    (p : List I × ℕ) (hp : p ∈ timedHistoryWitness (supportGraph vars) root offset L)
    (v : V) (hpv : v ∈ vars (pathLabel root p.1)) (k : ℕ)
    (hk : offset ≤ k) (hkp : k < p.2)
    (hkv : v ∈ vars (historyLabel root L (k - offset))) :
    ∃ q ∈ timedHistoryWitness (supportGraph vars) root offset L,
      q.2 = k ∧ v ∈ vars (pathLabel root q.1) := by
  induction L generalizing offset with
  | nil =>
    have he : p = ([], offset) := by simpa [timedHistoryWitness] using hp
    simp only [he, Prod.snd] at hkp
    omega
  | cons j L ih =>
    simp only [timedHistoryWitness] at hp ⊢
    split_ifs at hp ⊢ with h
    · rcases Finset.mem_insert.mp hp with rfl | hp
      · simp only [Prod.snd] at hkp; omega
      · by_cases he : k = offset
        · subst k
          have hjv : v ∈ vars j := by simpa [historyLabel] using hkv
          refine ⟨_, Finset.mem_insert_self _ _, rfl, ?_⟩
          simpa using hjv
        · have hk' : offset + 1 ≤ k := by omega
          have hd : k - offset = (k - (offset + 1)) + 1 := by omega
          have hv' : v ∈ vars (historyLabel root L (k - (offset + 1))) := by
            simpa [historyLabel, hd] using hkv
          obtain ⟨q, hq, hqk, hqv⟩ := ih (offset + 1) hp hk' hv'
          exact ⟨q, Finset.mem_insert_of_mem hq, hqk, hqv⟩
    · by_cases he : k = offset
      · subst k
        have hjv : v ∈ vars j := by simpa [historyLabel] using hkv
        exact False.elim (h ⟨p.1, candidate_of_shared_variable vars root j _ p.1
          (Finset.mem_image_of_mem Prod.fst hp) v hjv hpv⟩)
      · have hk' : offset + 1 ≤ k := by omega
        have hd : k - offset = (k - (offset + 1)) + 1 := by omega
        have hv' : v ∈ vars (historyLabel root L (k - (offset + 1))) := by
          simpa [historyLabel, hd] using hkv
        exact ih (offset + 1) hp hk' hv'

end VariableSupports

end QEC.Coding.ProbabilisticConstruction.Resampling
