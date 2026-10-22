import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.CanonicalHistoryMarks.PhysicalMarks

/-! # Canonical marked subgraph and bottom root closure

This realizes the marked-subgraph definitions in BDL26 v1 paper.tex3525-3541
and the possibly empty root component in3622-3634, on the unchanged graph
and actual physical-C2-stopped history. Levels G1/G0 are only bottom graph
closure; no decoder or syndrome snapshots are invented below physical C2.
-/
namespace QEC.Coding.BDL26CanonicalHistoryMarks

open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical

variable (S : OddScale) (n : Nat) (sigma : Input S n)

/-- The original graph's literal Sigma carrier, independent of graph data. -/
abbrev Node := Σ i : LevelIndex (n + 2), GraphVertex S i.val

theorem node_carrier_eq : Node S n = (decodingGraph S (n + 2)).Node := rfl

def physicalNode (i : LevelIndex n) (v : GraphVertex S (i.val + 2)) : Node S n :=
  ⟨LevelTwoHistory.physicalLevel i, v⟩

def oneNode (v : GraphVertex S 1) : Node S n := ⟨⟨1, by omega⟩, v⟩
def root : Node S n := ⟨0, ()⟩

/-- The original singleton G0 vertex, with its graph-carrier type retained. -/
def rootVertex (S : OddScale) : GraphVertex S 0 := ()

theorem rootVertex_eq_unit : rootVertex S = () := rfl

/-- Only the intrinsic adjacent G2 parents are included at G1. -/
noncomputable def oneMarks : Finset (GraphVertex S 1) :=
  Finset.univ.filter (fun u => ∃ v ∈ baseMarks S n sigma, parent S 1 v = some u)

theorem mem_oneMarks (u : GraphVertex S 1) : u ∈ oneMarks S n sigma ↔
    ∃ v ∈ baseMarks S n sigma, parent S 1 v = some u := by
  simp only [oneMarks, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The root is included exactly when its immediately preceding level is nonempty. -/
noncomputable def rootMarks : Finset (GraphVertex S 0) := by
  letI : Decidable (oneMarks S n sigma).Nonempty := Classical.propDecidable _
  exact if (oneMarks S n sigma).Nonempty then {rootVertex S} else ∅

noncomputable def physicalNodes : Finset (Node S n) :=
  Finset.univ.biUnion (fun i : LevelIndex n =>
    (physicalMarks S n sigma i).image (physicalNode S n i))

noncomputable def marks : Finset (Node S n) :=
  physicalNodes S n sigma ∪ (oneMarks S n sigma).image (oneNode S n) ∪
    (rootMarks S n sigma).image (fun _ => root S n)

theorem marks_exact_union : marks S n sigma =
    (Finset.univ.biUnion (fun i : LevelIndex n =>
      (physicalMarks S n sigma i).image (physicalNode S n i))) ∪
    (oneMarks S n sigma).image (oneNode S n) ∪
    (rootMarks S n sigma).image (fun _ => root S n) := rfl

theorem rootImage_level (w : Node S n)
    (h : w ∈ (rootMarks S n sigma).image (fun _ => root S n)) : w.1.val = 0 := by
  letI : Decidable (oneMarks S n sigma).Nonempty := Classical.propDecidable _
  by_cases hn : (oneMarks S n sigma).Nonempty
  · have hs : w ∈ ({root S n} : Finset (Node S n)) := by
      simpa only [rootMarks, if_pos hn,
        Finset.image_singleton (fun _ : GraphVertex S 0 => root S n) (rootVertex S)] using h
    have hr : w = root S n := Finset.mem_singleton.mp hs
    exact congrArg (fun z : Node S n => z.1.val) hr
  · have he : w ∈ (∅ : Finset (Node S n)) := by
      simpa only [rootMarks, if_neg hn, Finset.image_empty] using h
    exact (Finset.notMem_empty w he).elim

theorem physicalNode_level (i : LevelIndex n) (v : GraphVertex S (i.val + 2)) :
    (physicalNode S n i v).1.val = i.val + 2 := rfl

theorem physical_levels_disjoint (i k : LevelIndex n) (h : i ≠ k)
    (u : GraphVertex S (i.val + 2)) (v : GraphVertex S (k.val + 2)) :
    physicalNode S n i u ≠ physicalNode S n k v := by
  intro he
  apply h
  apply Fin.ext
  have hl := congrArg (fun w : Node S n => w.1.val) he
  simpa only [physicalNode_level, Nat.add_right_cancel_iff] using hl

theorem mem_physicalNodes (i : LevelIndex n) (v : GraphVertex S (i.val + 2)) :
    physicalNode S n i v ∈ physicalNodes S n sigma ↔ v ∈ physicalMarks S n sigma i := by
  simp only [physicalNodes, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · rintro ⟨k, u, hu, he⟩
    have hk : k = i := by
      apply Fin.ext
      have hl := congrArg (fun w : Node S n => w.1.val) he
      simpa only [physicalNode_level, Nat.add_right_cancel_iff] using hl
    subst k
    have hv : u = v := by cases he; rfl
    simpa only [hv] using hu
  · intro hv
    exact ⟨i, v, hv, rfl⟩

theorem physicalNodes_min_level (w : Node S n) (hw : w ∈ physicalNodes S n sigma) :
    2 ≤ w.1.val := by
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hw
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hi
  simp only [physicalNode_level]
  omega

theorem mem_marks_physical (i : LevelIndex n) (v : GraphVertex S (i.val + 2)) :
    physicalNode S n i v ∈ marks S n sigma ↔ v ∈ physicalMarks S n sigma i := by
  constructor
  · intro hm
    rcases Finset.mem_union.mp hm with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact (mem_physicalNodes S n sigma i v).mp h
      · obtain ⟨u, _, he⟩ := Finset.mem_image.mp h
        have hl := congrArg (fun w : Node S n => w.1.val) he
        change 1 = i.val + 2 at hl
        omega
    · have hl : i.val + 2 = 0 := rootImage_level S n sigma _ h
      omega
  · intro hv
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
      (Or.inl ((mem_physicalNodes S n sigma i v).mpr hv))))

theorem mem_marks_one (u : GraphVertex S 1) :
    oneNode S n u ∈ marks S n sigma ↔ u ∈ oneMarks S n sigma := by
  constructor
  · intro hm
    rcases Finset.mem_union.mp hm with h | h
    · rcases Finset.mem_union.mp h with h | h
      · have hl := physicalNodes_min_level S n sigma _ h
        change 2 ≤ 1 at hl
        omega
      · obtain ⟨v, hv, he⟩ := Finset.mem_image.mp h
        have he' : v = u := by cases he; rfl
        simpa only [he'] using hv
    · have hl : (1 : Nat) = 0 := rootImage_level S n sigma _ h
      omega
  · intro hu
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
      (Or.inr (Finset.mem_image.mpr ⟨u, hu, rfl⟩))))

theorem root_marked_iff : root S n ∈ marks S n sigma ↔ (oneMarks S n sigma).Nonempty := by
  letI : Decidable (oneMarks S n sigma).Nonempty := Classical.propDecidable _
  constructor
  · intro hm
    rcases Finset.mem_union.mp hm with h | h
    · rcases Finset.mem_union.mp h with h | h
      · have hl := physicalNodes_min_level S n sigma _ h
        change 2 ≤ 0 at hl
        omega
      · obtain ⟨u, _, he⟩ := Finset.mem_image.mp h
        have hl := congrArg (fun w : Node S n => w.1.val) he
        change 1 = 0 at hl
        omega
    · by_cases hn : (oneMarks S n sigma).Nonempty
      · exact hn
      · have he : root S n ∈ (∅ : Finset (Node S n)) := by
          simpa only [rootMarks, if_neg hn, Finset.image_empty] using h
        exact (Finset.notMem_empty (root S n) he).elim
  · intro hn
    apply Finset.mem_union.mpr
    right
    have hs : root S n ∈ ({root S n} : Finset (Node S n)) := Finset.mem_singleton_self _
    simpa only [rootMarks, if_pos hn,
      Finset.image_singleton (fun _ : GraphVertex S 0 => root S n) (rootVertex S)] using hs

theorem root_marked_iff_parented_base : root S n ∈ marks S n sigma ↔
    ∃ v ∈ baseMarks S n sigma, ∃ u, parent S 1 v = some u := by
  rw [root_marked_iff]
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨v, hv, hp⟩ := (mem_oneMarks S n sigma u).mp hu
    exact ⟨v, hv, u, hp⟩
  · rintro ⟨v, hv, u, hp⟩
    exact ⟨u, (mem_oneMarks S n sigma u).mpr ⟨v, hv, hp⟩⟩

/-- Induced original adjacency, on original nodes with both endpoints marked. -/
def markedAdjacent (u v : Node S n) : Prop :=
  (decodingGraph S (n + 2)).adjacent u v ∧ u ∈ marks S n sigma ∧ v ∈ marks S n sigma

theorem markedAdjacent_iff (u v : Node S n) : markedAdjacent S n sigma u v ↔
    (decodingGraph S (n + 2)).adjacent u v ∧ u ∈ marks S n sigma ∧ v ∈ marks S n sigma := Iff.rfl

/-- The actual inherited edge, without changing the graph or saturating parents. -/
theorem base_parent_edge (v : GraphVertex S 2) (u : GraphVertex S 1)
    (hp : parent S 1 v = some u) :
    (decodingGraph S (n + 2)).adjacent (physicalNode S n 0 v) (oneNode S n u) := by
  apply Or.inr
  apply Or.inr
  refine ⟨⟨1, by omega⟩, ?_⟩
  exact (parent_interLevel_iff S (n + 2) ⟨1, by omega⟩ u v).mp hp

theorem one_root_edge (u : GraphVertex S 1) :
    (decodingGraph S (n + 2)).adjacent (oneNode S n u) (root S n) := by
  apply Or.inr
  apply Or.inr
  refine ⟨⟨0, by omega⟩, ?_⟩
  exact root_connected S (n + 2) (by omega) u

/-- The source bottom closure gives two genuine inherited marked edges. -/
theorem parented_base_two_edges (v : GraphVertex S 2) (hv : v ∈ baseMarks S n sigma)
    (u : GraphVertex S 1) (hp : parent S 1 v = some u) :
    markedAdjacent S n sigma (physicalNode S n 0 v) (oneNode S n u) ∧
    markedAdjacent S n sigma (oneNode S n u) (root S n) := by
  have hu := (mem_oneMarks S n sigma u).mpr ⟨v, hv, hp⟩
  have hroot := (root_marked_iff S n sigma).mpr ⟨u, hu⟩
  have hv' := (mem_marks_physical S n sigma 0 v).mpr hv
  have hu' := (mem_marks_one S n sigma u).mpr hu
  exact ⟨⟨base_parent_edge S n v u hp, hv', hu'⟩,
    ⟨one_root_edge S n u, hu', hroot⟩⟩

theorem parented_base_root_path (v : GraphVertex S 2) (hv : v ∈ baseMarks S n sigma)
    (u : GraphVertex S 1) (hp : parent S 1 v = some u) :
    Relation.ReflTransGen (markedAdjacent S n sigma) (physicalNode S n 0 v) (root S n) := by
  have he := parented_base_two_edges S n sigma v hv u hp
  exact (Relation.ReflTransGen.single he.1).trans (Relation.ReflTransGen.single he.2)

/-- Empty when the root is absent; otherwise reachability uses the induced graph. -/
noncomputable def rootComponent : Finset (Node S n) :=
  if root S n ∈ marks S n sigma then
    Finset.univ.filter (fun w => w ∈ marks S n sigma ∧
      Relation.ReflTransGen (markedAdjacent S n sigma) w (root S n))
  else ∅

theorem rootComponent_empty (h : root S n ∉ marks S n sigma) :
    rootComponent S n sigma = ∅ := by simp only [rootComponent, if_neg h]

theorem mem_rootComponent (w : Node S n) : w ∈ rootComponent S n sigma ↔
    root S n ∈ marks S n sigma ∧ w ∈ marks S n sigma ∧
      Relation.ReflTransGen (markedAdjacent S n sigma) w (root S n) := by
  by_cases h : root S n ∈ marks S n sigma <;> simp [rootComponent, h]

theorem oneMarks_in_rootComponent (u : GraphVertex S 1) (hu : u ∈ oneMarks S n sigma) :
    oneNode S n u ∈ rootComponent S n sigma := by
  have hr := (root_marked_iff S n sigma).mpr ⟨u, hu⟩
  have hm := (mem_marks_one S n sigma u).mpr hu
  exact (mem_rootComponent S n sigma _).mpr ⟨hr, hm,
    Relation.ReflTransGen.single ⟨one_root_edge S n u, hm, hr⟩⟩

theorem parented_base_in_rootComponent (v : GraphVertex S 2)
    (hv : v ∈ baseMarks S n sigma) (u : GraphVertex S 1) (hp : parent S 1 v = some u) :
    physicalNode S n 0 v ∈ rootComponent S n sigma := by
  exact (mem_rootComponent S n sigma _).mpr
    ⟨(root_marked_iff_parented_base S n sigma).mpr ⟨v, hv, u, hp⟩,
      (mem_marks_physical S n sigma 0 v).mpr hv,
      parented_base_root_path S n sigma v hv u hp⟩

/-- Actual even-depth endpoint; the caller supplies only the literal top syndrome. -/
noncomputable def actualMarks (j : Nat)
    (s : Input S (2 * j)) : Finset (Node S (2 * j)) := marks S (2 * j) s

noncomputable def actualRootComponent (j : Nat)
    (s : Input S (2 * j)) : Finset (Node S (2 * j)) := rootComponent S (2 * j) s

theorem actual_root_marked_iff (j : Nat) (s : Input S (2 * j)) :
    root S (2 * j) ∈ actualMarks S j s ↔
      ∃ v ∈ baseMarks S (2 * j) s, ∃ u, parent S 1 v = some u :=
  root_marked_iff_parented_base S (2 * j) s

/-- An endpoint takes the original actual vertex membership, without any
caller-supplied closure or root certificate. -/
theorem actual_marked_one_in_rootComponent (j : Nat) (s : Input S (2 * j))
    (u : GraphVertex S 1) (hu : oneNode S (2 * j) u ∈ actualMarks S j s) :
    oneNode S (2 * j) u ∈ actualRootComponent S j s :=
  oneMarks_in_rootComponent S (2 * j) s u ((mem_marks_one S (2 * j) s u).mp hu)

theorem actual_parented_base_in_rootComponent (j : Nat) (s : Input S (2 * j))
    (v : GraphVertex S 2) (hv : physicalNode S (2 * j) 0 v ∈ actualMarks S j s)
    (u : GraphVertex S 1) (hp : parent S 1 v = some u) :
    physicalNode S (2 * j) 0 v ∈ actualRootComponent S j s :=
  parented_base_in_rootComponent S (2 * j) s v
    ((mem_marks_physical S (2 * j) s 0 v).mp hv) u hp

end QEC.Coding.BDL26CanonicalHistoryMarks
