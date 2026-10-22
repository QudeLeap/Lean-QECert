import QEC.Coding.ProbabilisticConstruction.Resampling.WitnessTrees
import Mathlib.Data.Finset.Max

/-!
# Backward witnesses of a resampling history

Nodes are finite label paths from the root. Adding an earlier event chooses a
deepest dependent node and adds a child labeled by that event. Equal labels
count as dependencies. This is a proof-side finite construction, independent
of the executable ordered resampling scan.
-/

namespace QEC.Coding.ProbabilisticConstruction.Resampling

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]

/-- A path carries its final label; the empty path carries the root label. -/
def pathLabel (root : I) : List I → I
  | [] => root
  | j :: rest => pathLabel j rest

@[simp] theorem pathLabel_nil (root : I) : pathLabel root [] = root := rfl

@[simp] theorem pathLabel_append_singleton (root j : I) (p : List I) :
    pathLabel root (p ++ [j]) = j := by
  induction p generalizing root with
  | nil => rfl
  | cons k p ih => exact ih k

/-- Finite rooted paths closed under parents and respecting dependency labels. -/
def ProperPaths (root : I) (P : Finset (List I)) : Prop :=
  [] ∈ P ∧ ∀ p j, p ++ [j] ∈ P →
    p ∈ P ∧ j ∈ closedNeighbors G (pathLabel root p)

/-- Existing nodes to which an earlier event may attach. -/
def attachmentCandidates (root j : I) (P : Finset (List I)) : Finset (List I) :=
  P.filter (fun p => j ∈ closedNeighbors G (pathLabel root p))

/-- Select one deepest candidate. Choice is confined to the witness proof,
not the resampling algorithm or its sampling law. -/
noncomputable def attachmentParent (root j : I) (P : Finset (List I))
    (h : (attachmentCandidates G root j P).Nonempty) : List I :=
  Classical.choose ((attachmentCandidates G root j P).exists_max_image List.length h)

theorem attachmentParent_spec (root j : I) (P : Finset (List I))
    (h : (attachmentCandidates G root j P).Nonempty) :
    attachmentParent G root j P h ∈ attachmentCandidates G root j P ∧
      ∀ q ∈ attachmentCandidates G root j P,
        q.length ≤ (attachmentParent G root j P h).length :=
  Classical.choose_spec ((attachmentCandidates G root j P).exists_max_image List.length h)

/-- Add an earlier event exactly when it interacts with the current witness. -/
noncomputable def extendWitness (root j : I) (P : Finset (List I)) : Finset (List I) :=
  if h : (attachmentCandidates G root j P).Nonempty then
    insert (attachmentParent G root j P h ++ [j]) P
  else P

theorem subset_extendWitness (root j : I) (P : Finset (List I)) :
    P ⊆ extendWitness G root j P := by
  unfold extendWitness
  split_ifs <;> simp

theorem newPath_not_mem (root j : I) (P : Finset (List I))
    (h : (attachmentCandidates G root j P).Nonempty) :
    attachmentParent G root j P h ++ [j] ∉ P := by
  intro hm
  have hc : attachmentParent G root j P h ++ [j] ∈ attachmentCandidates G root j P := by
    apply Finset.mem_filter.mpr
    exact ⟨hm, by simp⟩
  have hd := (attachmentParent_spec G root j P h).2 _ hc
  simp only [List.length_append, List.length_singleton] at hd
  omega

theorem properPaths_extend (root j : I) (P : Finset (List I))
    (hP : ProperPaths G root P) : ProperPaths G root (extendWitness G root j P) := by
  refine ⟨subset_extendWitness G root j P hP.1, ?_⟩
  intro q k hq
  unfold extendWitness at hq ⊢
  split_ifs at hq ⊢ with h
  · rcases Finset.mem_insert.mp hq with he | hold
    · have hr : k :: q.reverse = j :: (attachmentParent G root j P h).reverse := by
        simpa only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
          List.singleton_append] using congrArg (fun l : List I => l.reverse) he
      have hk := (List.cons.inj hr).1
      have hp := List.reverse_injective (List.cons.inj hr).2
      subst k
      subst q
      have hs := Finset.mem_filter.mp (attachmentParent_spec G root j P h).1
      exact ⟨Finset.mem_insert_of_mem hs.1, hs.2⟩
    · have hs := hP.2 q k hold
      exact ⟨Finset.mem_insert_of_mem hs.1, hs.2⟩
  · exact hP.2 q k hq

/-- Inserting a dependency puts the new node deeper than every node it touches. -/
theorem newPath_deeper_than_candidate (root j : I) (P : Finset (List I))
    (h : (attachmentCandidates G root j P).Nonempty) (q : List I)
    (hq : q ∈ attachmentCandidates G root j P) :
    q.length < (attachmentParent G root j P h ++ [j]).length := by
  have hd := (attachmentParent_spec G root j P h).2 q hq
  simp only [List.length_append, List.length_singleton]
  omega

theorem extendWitness_depth (root j : I) (P : Finset (List I)) (d : ℕ)
    (hd : ∀ p ∈ P, p.length ≤ d) :
    ∀ p ∈ extendWitness G root j P, p.length ≤ d + 1 := by
  intro p hp
  unfold extendWitness at hp
  split_ifs at hp with h
  · rcases Finset.mem_insert.mp hp with rfl | hp
    · have hm := (Finset.mem_filter.mp (attachmentParent_spec G root j P h).1).1
      simpa using Nat.add_le_add_right (hd _ hm) 1
    · exact (hd p hp).trans (Nat.le_add_right _ _)
  · exact (hd p hp).trans (Nat.le_add_right _ _)

/-- Number of nodes carrying a given label, preserving repeated occurrences. -/
def labelCount (root k : I) (P : Finset (List I)) : ℕ :=
  (P.filter (fun p => pathLabel root p = k)).card

theorem labelCount_insert (root j k : I) (P : Finset (List I))
    (h : (attachmentCandidates G root j P).Nonempty) :
    labelCount root k (extendWitness G root j P) =
      labelCount root k P + if j = k then 1 else 0 := by
  have hn := newPath_not_mem G root j P h
  simp only [extendWitness, dif_pos h, labelCount, Finset.filter_insert,
    pathLabel_append_singleton]
  split_ifs with hj
  · rw [Finset.card_insert_of_notMem (fun hm => hn (Finset.mem_filter.mp hm).1)]
  · simp

/-- Every earlier occurrence of the root event is necessarily included. -/
theorem labelCount_extend_root (root j : I) (P : Finset (List I)) (hroot : [] ∈ P) :
    labelCount root root (extendWitness G root j P) =
      labelCount root root P + if j = root then 1 else 0 := by
  by_cases h : (attachmentCandidates G root j P).Nonempty
  · exact labelCount_insert G root j root P h
  · have hne : j ≠ root := by
      intro he
      subst j
      apply h
      exact ⟨[], Finset.mem_filter.mpr ⟨hroot, by simp⟩⟩
    simp [extendWitness, h, hne]

/-- Build a witness backward through a chronological list of earlier resamplings. -/
noncomputable def historyWitness (root : I) : List I → Finset (List I)
  | [] => {[]}
  | j :: rest => extendWitness G root j (historyWitness root rest)

theorem historyWitness_proper (root : I) (L : List I) :
    ProperPaths G root (historyWitness G root L) := by
  induction L with
  | nil =>
    refine ⟨by simp [historyWitness], ?_⟩
    intro p j h
    have he : p ++ [j] = [] := by simpa [historyWitness] using h
    have hn := congrArg List.length he
    simp at hn
  | cons j L ih => exact properPaths_extend G root j _ ih

theorem historyWitness_depth (root : I) (L : List I) :
    ∀ p ∈ historyWitness G root L, p.length ≤ L.length := by
  induction L with
  | nil => intro p hp; simpa [historyWitness] using hp
  | cons j L ih => exact extendWitness_depth G root j _ L.length ih

/-- Root-label multiplicity records its occurrence number in the input history. -/
theorem historyWitness_root_count (root : I) (L : List I) :
    labelCount root root (historyWitness G root L) = L.count root + 1 := by
  induction L with
  | nil =>
    change (Finset.filter (fun p => pathLabel root p = root) {[]}).card = 1
    have hf : Finset.filter (fun p => pathLabel root p = root) {[]} = {[]} := by
      apply Finset.filter_eq_self.mpr
      intro p hp
      have he : p = [] := Finset.mem_singleton.mp hp
      subst p
      rfl
    rw [hf, Finset.card_singleton]
  | cons j L ih =>
    rw [historyWitness, labelCount_extend_root G root j _ (historyWitness_proper G root L).1, ih]
    by_cases he : j = root <;> simp [he, List.count_cons, Nat.add_assoc, Nat.add_comm]

/-- Different occurrence numbers cannot share a root witness. -/
theorem historyWitness_ne_of_root_count_ne (root : I) (L K : List I)
    (h : L.count root ≠ K.count root) : historyWitness G root L ≠ historyWitness G root K := by
  intro he
  have hc := congrArg (labelCount root root) he
  rw [historyWitness_root_count, historyWitness_root_count] at hc
  exact h (Nat.add_right_cancel hc)

/-- Paths below the child whose label is j, with the first label removed. -/
def childPaths (P : Finset (List I)) (j : I) : Finset (List I) :=
  (P.filter (fun p => p.head? = some j)).image List.tail

@[simp] theorem mem_childPaths (P : Finset (List I)) (j : I) (p : List I) :
    p ∈ childPaths P j ↔ j :: p ∈ P := by
  constructor
  · intro hp
    obtain ⟨q, hq, he⟩ := Finset.mem_image.mp hp
    obtain ⟨hqP, hhead⟩ := Finset.mem_filter.mp hq
    cases q with
    | nil => simp at hhead
    | cons k q =>
      have hk : k = j := by simpa using hhead
      subst k
      have hq : q = p := he
      simpa [hq] using hqP
  · intro hp
    exact Finset.mem_image.mpr ⟨j :: p, Finset.mem_filter.mpr ⟨hp, rfl⟩, rfl⟩

theorem ProperPaths.child {root j : I} {P : Finset (List I)}
    (hP : ProperPaths G root P) (hj : [j] ∈ P) :
    ProperPaths G j (childPaths P j) := by
  refine ⟨(mem_childPaths P j []).mpr hj, ?_⟩
  intro p k hp
  have hh : (j :: p) ++ [k] ∈ P := by simpa using (mem_childPaths P j _).mp hp
  obtain ⟨hparent, hadj⟩ := hP.2 (j :: p) k hh
  exact ⟨(mem_childPaths P j p).mpr hparent, hadj⟩

theorem childPaths_depth (P : Finset (List I)) (j : I) (h : ℕ)
    (hd : ∀ p ∈ P, p.length < h + 1) :
    ∀ p ∈ childPaths P j, p.length < h := by
  intro p hp
  have hh := hd (j :: p) ((mem_childPaths P j p).mp hp)
  simp only [List.length_cons] at hh
  omega

/-- Encode a genuine finite proper path tree into the finite height-bounded tree type. -/
def pathsToTree : (h : ℕ) → (root : I) → (P : Finset (List I)) →
    ProperPaths G root P → (∀ p ∈ P, p.length < h) → WitnessTree G h root
  | 0, _, P, hP, hd => False.elim (Nat.not_lt_zero _ (hd [] hP.1))
  | h + 1, root, P, hP, hd => fun j =>
      if hj : [j.val] ∈ P then
        some (pathsToTree h j (childPaths P j) (ProperPaths.child G hP hj) (childPaths_depth P j h hd))
      else none

/-- Finite paths of a height-bounded proper tree. -/
def witnessPaths : (h : ℕ) → (root : I) → WitnessTree G h root → Finset (List I)
  | 0, _, t => PEmpty.elim t
  | h + 1, root, t => insert []
      (Finset.univ.biUnion (fun j : closedNeighbors G root =>
        match t j with
        | none => ∅
        | some child => (witnessPaths h j child).image (List.cons j.val)))

@[simp] theorem nil_mem_witnessPaths (h : ℕ) (root : I) (t : WitnessTree G (h + 1) root) :
    [] ∈ witnessPaths G (h + 1) root t := by simp [witnessPaths]

theorem cons_mem_witnessPaths (h : ℕ) (root j : I) (t : WitnessTree G (h + 1) root)
    (p : List I) :
    j :: p ∈ witnessPaths G (h + 1) root t ↔
      ∃ hj : j ∈ closedNeighbors G root, ∃ child,
        t ⟨j, hj⟩ = some child ∧ p ∈ witnessPaths G h j child := by
  constructor
  · intro hp
    have hm : j :: p ∈ Finset.univ.biUnion (fun k : closedNeighbors G root =>
        match t k with
        | none => ∅
        | some child => (witnessPaths G h k child).image (List.cons k.val)) := by
      simpa only [witnessPaths, Finset.mem_insert, List.cons_ne_nil, false_or] using hp
    obtain ⟨k, hk, hm⟩ := Finset.mem_biUnion.mp hm
    cases hc : t k with
    | none => simp [hc] at hm
    | some child =>
      have himg : j :: p ∈ (witnessPaths G h k child).image (List.cons k.val) := by
        simpa [hc] using hm
      obtain ⟨q, hq, he⟩ := Finset.mem_image.mp himg
      have hkj : k.val = j := (List.cons.inj he).1
      have hqp : q = p := (List.cons.inj he).2
      subst j
      subst p
      exact ⟨k.property, child, hc, hq⟩
  · rintro ⟨hj, child, hc, hp⟩
    apply Finset.mem_insert_of_mem
    apply Finset.mem_biUnion.mpr
    refine ⟨⟨j, hj⟩, Finset.mem_univ _, ?_⟩
    rw [hc]
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩

/-- Encoding retains every node and introduces none; hence it is injective on proper paths. -/
theorem witnessPaths_pathsToTree (h : ℕ) (root : I) (P : Finset (List I))
    (hP : ProperPaths G root P) (hd : ∀ p ∈ P, p.length < h) :
    witnessPaths G h root (pathsToTree G h root P hP hd) = P := by
  induction h generalizing root P with
  | zero => exact False.elim (Nat.not_lt_zero _ (hd [] hP.1))
  | succ h ih =>
    ext p
    cases p with
    | nil => simp only [nil_mem_witnessPaths, true_iff]; exact hP.1
    | cons j p =>
      rw [cons_mem_witnessPaths]
      constructor
      · rintro ⟨hj, child, hc, hp⟩
        change (if he : [j] ∈ P then some
          (pathsToTree G h j (childPaths P j) (ProperPaths.child G hP he) (childPaths_depth P j h hd))
          else none) = some child at hc
        split_ifs at hc with he
        · have hc' := Option.some.inj hc
          subst child
          rw [ih] at hp
          exact (mem_childPaths P j p).mp hp
      · intro hp
        have hjP : [j] ∈ P := by
          have hprefix : ∀ q : List I, j :: q ∈ P → [j] ∈ P := by
            intro q
            induction q using List.reverseRecOn with
            | nil => exact id
            | append_singleton q k ihq =>
              intro hh
              apply ihq
              exact (hP.2 (j :: q) k (by simpa using hh)).1
          exact hprefix p hp
        have hj : j ∈ closedNeighbors G root := by
          simpa using (hP.2 [] j hjP).2
        refine ⟨hj, pathsToTree G h j (childPaths P j) (ProperPaths.child G hP hjP)
          (childPaths_depth P j h hd), ?_, ?_⟩
        · simp [pathsToTree, hjP]
        · rw [ih]
          exact (mem_childPaths P j p).mpr hp

/-- The actual backward history yields a member of the finite witness-tree family. -/
noncomputable def encodedHistoryWitness (root : I) (L : List I) :
    WitnessTree G (L.length + 1) root :=
  pathsToTree G (L.length + 1) root (historyWitness G root L)
    (historyWitness_proper G root L)
    (fun p hp => Nat.lt_succ_of_le (historyWitness_depth G root L p hp))

theorem encodedHistoryWitness_paths (root : I) (L : List I) :
    witnessPaths G (L.length + 1) root (encodedHistoryWitness G root L) =
      historyWitness G root L :=
  witnessPaths_pathsToTree G _ _ _ _ _

end QEC.Coding.ProbabilisticConstruction.Resampling
