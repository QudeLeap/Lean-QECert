import QEC.Coding.FiniteAlternatingConstruction.TopOwnerIsolation

/-! # Uniform isolation at the actual top physical level -/
namespace QEC.Coding.BDL26UniformTopOwnerIsolation

open BDL26FiniteTannerSquare BDL26DecodingGraph MultiscaleDecoder
open scoped Classical

/-- The actual finite graph used by the isolation theorem. -/
noncomputable abbrev graph (S : OddScale) (n : Nat) := decodingGraph S (n + 1)

/-- The actual level union; its top carrier is the state-n Tanner vertex type. -/
abbrev Node (S : OddScale) (n : Nat) := (graph S n).Node

def topNode (S : OddScale) (n : Nat) (v : Vertex (state S n).presentation) : Node S n :=
  ⟨(Fin.last (n + 1)), v⟩

/-- No restriction is imposed on marks at every level strictly below the top. -/
def TopMarksAreZ (S : OddScale) (n : Nat) (M : Finset (Node S n)) : Prop :=
  ∀ v : Vertex (state S n).presentation,
    topNode S n v ∈ M → ∃ z, v = Vertex.z z

/-- Actual graph S n adjacency restricted to the marked subtype. -/
def markedAdjacent (S : OddScale) (n : Nat) (M : Finset (Node S n)) (u v : {w : Node S n // w ∈ M}) : Prop :=
  (graph S n).adjacent u.val v.val

@[simp] theorem markedAdjacent_iff (S : OddScale) (n : Nat) (M : Finset (Node S n))
    (u v : {w : Node S n // w ∈ M}) :
    markedAdjacent S n M u v ↔ (graph S n).adjacent u.val v.val := Iff.rfl

/-- A top Z node with no intrinsic parent cannot have any marked neighbor. -/
theorem no_marked_neighbor (S : OddScale) (n : Nat) (M : Finset (Node S n)) (hM : TopMarksAreZ S n M)
    (z : (state S n).presentation.Z)
    (hparent : parent S n (Vertex.z z) = none)
    (w : Node S n) (hw : w ∈ M) :
    ¬ (graph S n).adjacent (topNode S n (.z z)) w := by
  rcases w with ⟨i,w⟩
  intro hadj
  change ((if h : (Fin.last (n + 1)) = i then
      ((graph S n).level (Fin.last (n + 1))).skeleton.adjacent (Vertex.z z) (h ▸ w) else False) ∨
    (∃ s : Fin (n + 1), if h0 : (Fin.last (n + 1)) = s.castSucc then
      if h1 : i = s.succ then (graph S n).interLevel s (h0 ▸ Vertex.z z) (h1 ▸ w)
        = true else False else False) ∨
    (∃ s : Fin (n + 1), if h0 : i = s.castSucc then
      if h1 : (Fin.last (n + 1)) = s.succ then (graph S n).interLevel s (h0 ▸ w) (h1 ▸ Vertex.z z)
        = true else False else False)) at hadj
  rcases hadj with hsame | hup | hdown
  · split_ifs at hsame with hi
    · cases hi
      obtain ⟨z',rfl⟩ := hM w hw
      exact hsame
  · rcases hup with ⟨s,hs⟩
    split_ifs at hs with h0 h1 <;> try contradiction
    have hv := congrArg Fin.val h0
    have hlt := s.isLt
    change n + 1 = s.val at hv
    omega
  · rcases hdown with ⟨s,hs⟩
    split_ifs at hs with h0 h1 <;> try contradiction
    have hsLast : s = (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) := by
      apply Fin.ext
      have hv := congrArg Fin.val h1
      change n + 1 = s.val + 1 at hv
      change s.val = n
      omega
    subst s
    have hi : i = (⟨n, by omega⟩ : Fin (n + 2)) := h0
    subst i
    have hedge : (graph S n).interLevel (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) w (Vertex.z z) = true := by
      simpa using hs
    have hp := (parent_interLevel_iff S (n + 1) (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) w (Vertex.z z)).mpr hedge
    have hnone : (none : Option (GraphVertex S n)) = some w :=
      hparent.symm.trans hp
    cases hnone

/-- Reachability in the actual induced marked graph reduces to equality at this node. -/
theorem marked_path_iff_eq (S : OddScale) (n : Nat) (M : Finset (Node S n)) (hM : TopMarksAreZ S n M)
    (z : (state S n).presentation.Z)
    (hparent : parent S n (Vertex.z z) = none)
    (ha : topNode S n (.z z) ∈ M) (w : {w : Node S n // w ∈ M}) :
    Relation.ReflTransGen (markedAdjacent S n M) ⟨topNode S n (.z z),ha⟩ w ↔
      w = ⟨topNode S n (.z z),ha⟩ := by
  constructor
  · intro hpath
    rcases hpath.cases_head with heq | ⟨next,hedge,_⟩
    · exact heq.symm
    · exact (no_marked_neighbor S n M hM z hparent next.val next.property hedge).elim
  · rintro rfl
    exact Relation.ReflTransGen.refl

/-- The finite component uses reachability in the actual induced adjacency. -/
noncomputable def markedComponent (S : OddScale) (n : Nat) (M : Finset (Node S n)) (a : {w : Node S n // w ∈ M}) :
    Finset {w : Node S n // w ∈ M} :=
  Finset.univ.filter (Relation.ReflTransGen (markedAdjacent S n M) a)

/-- The marked component is a singleton, regardless of every lower-level mark. -/
theorem markedComponent_eq_singleton (S : OddScale) (n : Nat) (M : Finset (Node S n)) (hM : TopMarksAreZ S n M)
    (z : (state S n).presentation.Z)
    (hparent : parent S n (Vertex.z z) = none)
    (ha : topNode S n (.z z) ∈ M) :
    markedComponent S n M ⟨topNode S n (.z z),ha⟩ = {⟨topNode S n (.z z),ha⟩} := by
  ext w
  simp only [markedComponent, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton, marked_path_iff_eq S n M hM z hparent ha]

/-- The same component has exactly the one underlying node in the original (graph S n). -/
theorem markedComponent_image_eq_singleton (S : OddScale) (n : Nat) (M : Finset (Node S n)) (hM : TopMarksAreZ S n M)
    (z : (state S n).presentation.Z)
    (hparent : parent S n (Vertex.z z) = none)
    (ha : topNode S n (.z z) ∈ M) :
    (markedComponent S n M ⟨topNode S n (.z z),ha⟩).image Subtype.val = {topNode S n (.z z)} := by
  rw [markedComponent_eq_singleton S n M hM z hparent ha]
  simp

end QEC.Coding.BDL26UniformTopOwnerIsolation
