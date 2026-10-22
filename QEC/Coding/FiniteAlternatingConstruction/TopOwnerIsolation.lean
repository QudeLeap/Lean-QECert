import QEC.Coding.FiniteAlternatingConstruction.DecodingGraph

/-!
# Top Z owners with no intrinsic parent

In the actual scale-five depth-four graph, a top Z node with no parent has
no marked neighbor when all top marks are Z-type. Marking below the top is
arbitrary. These are graph statements, with no decoder-history assertion.
-/

namespace QEC.Coding.BDL26TopOwnerIsolation

open BDL26FiniteTannerSquare BDL26DecodingGraph MultiscaleDecoder
open scoped Classical

/-- The actual finite graph used by the isolation theorem. -/
noncomputable abbrev graph := decodingGraph scaleFive 4

/-- The actual level union; its top carrier is the state-three Tanner vertex type. -/
abbrev Node := graph.Node

def topNode (v : Vertex (state scaleFive 3).presentation) : Node :=
  ⟨(4 : Fin 5), v⟩

/-- No restriction is imposed on marks at levels zero through three. -/
def TopMarksAreZ (M : Finset Node) : Prop :=
  ∀ v : Vertex (state scaleFive 3).presentation,
    topNode v ∈ M → ∃ z, v = Vertex.z z

/-- Actual graph adjacency restricted to the marked subtype. -/
def markedAdjacent (M : Finset Node) (u v : {w : Node // w ∈ M}) : Prop :=
  graph.adjacent u.val v.val

@[simp] theorem markedAdjacent_iff (M : Finset Node)
    (u v : {w : Node // w ∈ M}) :
    markedAdjacent M u v ↔ graph.adjacent u.val v.val := Iff.rfl

/-- A top Z node with no intrinsic parent cannot have any marked neighbor. -/
theorem no_marked_neighbor (M : Finset Node) (hM : TopMarksAreZ M)
    (z : (state scaleFive 3).presentation.Z)
    (hparent : parent scaleFive 3 (Vertex.z z) = none)
    (w : Node) (hw : w ∈ M) :
    ¬ graph.adjacent (topNode (.z z)) w := by
  rcases w with ⟨i,w⟩
  intro hadj
  change ((if h : (4 : Fin 5) = i then
      (graph.level 4).skeleton.adjacent (Vertex.z z) (h ▸ w) else False) ∨
    (∃ s : Fin 4, if h0 : (4 : Fin 5) = s.castSucc then
      if h1 : i = s.succ then graph.interLevel s (h0 ▸ Vertex.z z) (h1 ▸ w)
        = true else False else False) ∨
    (∃ s : Fin 4, if h0 : i = s.castSucc then
      if h1 : (4 : Fin 5) = s.succ then graph.interLevel s (h0 ▸ w) (h1 ▸ Vertex.z z)
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
    simp only [Fin.val_castSucc] at hv
    omega
  · rcases hdown with ⟨s,hs⟩
    split_ifs at hs with h0 h1 <;> try contradiction
    have hs3 : s = (3 : Fin 4) := by
      apply Fin.ext
      have hv := congrArg Fin.val h1
      simp only [Fin.val_succ] at hv
      omega
    subst s
    have hi : i = (3 : Fin 5) := h0
    subst i
    have hedge : graph.interLevel (3 : Fin 4) w (Vertex.z z) = true := by
      simpa using hs
    have hp := (parent_interLevel_iff scaleFive 4 (3 : Fin 4) w (Vertex.z z)).mpr hedge
    have hnone : (none : Option (GraphVertex scaleFive 3)) = some w :=
      hparent.symm.trans hp
    cases hnone

/-- Reachability in the actual induced marked graph reduces to equality at this node. -/
theorem marked_path_iff_eq (M : Finset Node) (hM : TopMarksAreZ M)
    (z : (state scaleFive 3).presentation.Z)
    (hparent : parent scaleFive 3 (Vertex.z z) = none)
    (ha : topNode (.z z) ∈ M) (w : {w : Node // w ∈ M}) :
    Relation.ReflTransGen (markedAdjacent M) ⟨topNode (.z z),ha⟩ w ↔
      w = ⟨topNode (.z z),ha⟩ := by
  constructor
  · intro hpath
    rcases hpath.cases_head with heq | ⟨next,hedge,_⟩
    · exact heq.symm
    · exact (no_marked_neighbor M hM z hparent next.val next.property hedge).elim
  · rintro rfl
    exact Relation.ReflTransGen.refl

/-- The finite component uses reachability in the actual induced adjacency. -/
noncomputable def markedComponent (M : Finset Node) (a : {w : Node // w ∈ M}) :
    Finset {w : Node // w ∈ M} :=
  Finset.univ.filter (Relation.ReflTransGen (markedAdjacent M) a)

/-- The marked component is a singleton, regardless of every lower-level mark. -/
theorem markedComponent_eq_singleton (M : Finset Node) (hM : TopMarksAreZ M)
    (z : (state scaleFive 3).presentation.Z)
    (hparent : parent scaleFive 3 (Vertex.z z) = none)
    (ha : topNode (.z z) ∈ M) :
    markedComponent M ⟨topNode (.z z),ha⟩ = {⟨topNode (.z z),ha⟩} := by
  ext w
  simp only [markedComponent, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton, marked_path_iff_eq M hM z hparent ha]

/-- The same component has exactly the one underlying node in the original graph. -/
theorem markedComponent_image_eq_singleton (M : Finset Node) (hM : TopMarksAreZ M)
    (z : (state scaleFive 3).presentation.Z)
    (hparent : parent scaleFive 3 (Vertex.z z) = none)
    (ha : topNode (.z z) ∈ M) :
    (markedComponent M ⟨topNode (.z z),ha⟩).image Subtype.val = {topNode (.z z)} := by
  rw [markedComponent_eq_singleton M hM z hparent ha]
  simp

end QEC.Coding.BDL26TopOwnerIsolation
