import QEC.Coding.FiniteAlternatingConstruction.TannerSquare

/-!
# Constructive Tanner local regularity for BDL26

This module derives the finite connectedness and binary parity facts needed by
the RX/RZ local constructions.  Admissibility below stores only explicit raw
paths and nonempty incidences.  Exactness, representatives, chain laws, and
cell embeddings are theorem-derived from those data.
-/

namespace QEC
namespace Coding
namespace BDL26TannerLocalRegularity

open Module
open BDL26FiniteAlternatingCore
open BDL26FiniteTannerSquare

abbrev Field := BDL26FiniteTannerSquare.Field

private theorem two_eq_zero_or_one (i : Two) : i = 0 ∨ i = 1 := by
  fin_cases i <;> simp

universe u

private def finTwoElim {motive : Fin 2 → Sort u}
    (zero : motive 0) (one : motive 1) (i : Fin 2) : motive i := by
  rcases i with ⟨i, hi⟩
  rcases i with _ | i
  · exact zero
  · rcases i with _ | i
    · exact one
    · omega

private def finFiveElim {motive : Fin 5 → Sort u}
    (c0 : motive 0) (c1 : motive 1) (c2 : motive 2)
    (c3 : motive 3) (c4 : motive 4) (i : Fin 5) : motive i := by
  rcases i with ⟨i, hi⟩
  rcases i with _ | i
  · exact c0
  · rcases i with _ | i
    · exact c1
    · rcases i with _ | i
      · exact c2
      · rcases i with _ | i
        · exact c3
        · rcases i with _ | i
          · exact c4
          · omega

/-! ## Choice-free finite graph paths and binary parity -/

/-- An edge joins two vertices without choosing an orientation. -/
def EdgeConnects {Vertex Edge : Type}
    (edgeStart edgeEnd : Edge → Vertex) (e : Edge) (u v : Vertex) : Prop :=
  (edgeStart e = u ∧ edgeEnd e = v) ∨
    (edgeStart e = v ∧ edgeEnd e = u)

/-- A finite path built step-by-step from actual graph edges. -/
inductive UndirectedPath {Vertex Edge : Type}
    (edgeStart edgeEnd : Edge → Vertex) (root : Vertex) : Vertex → Type
  | nil : UndirectedPath edgeStart edgeEnd root root
  | step {u v : Vertex}
      (path : UndirectedPath edgeStart edgeEnd root u)
      (edge : Edge) (connects : EdgeConnects edgeStart edgeEnd edge u v) :
      UndirectedPath edgeStart edgeEnd root v

/-- The binary edge word traversed by a constructive path. -/
def pathChain {Vertex Edge : Type} [DecidableEq Edge]
    {edgeStart edgeEnd : Edge → Vertex} {root : Vertex} :
    {v : Vertex} → UndirectedPath edgeStart edgeEnd root v → Word Field Edge
  | _, .nil => 0
  | _, .step path edge _ => pathChain path + Pi.single edge 1

/-- The two-endpoint binary boundary of one graph edge. -/
def graphEdgeBoundary {Vertex Edge : Type} [DecidableEq Vertex]
    (edgeStart edgeEnd : Edge → Vertex) (e : Edge) : Word Field Vertex :=
  Pi.single (edgeStart e) 1 + Pi.single (edgeEnd e) 1

/-- The edge-to-vertex boundary constructed from explicit endpoints. -/
noncomputable def graphBoundary {Vertex Edge : Type}
    [Fintype Edge] [DecidableEq Vertex]
    (edgeStart edgeEnd : Edge → Vertex) :
    Word Field Edge →ₗ[Field] Word Field Vertex where
  toFun := fun chain vertex =>
    ∑ edge : Edge, chain edge * graphEdgeBoundary edgeStart edgeEnd edge vertex
  map_add' := by
    intro a b
    ext vertex
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro coefficient chain
    ext vertex
    simp [Finset.mul_sum, mul_assoc]

@[simp]
theorem graphBoundary_single {Vertex Edge : Type}
    [Fintype Edge] [DecidableEq Edge] [DecidableEq Vertex]
    (edgeStart edgeEnd : Edge → Vertex) (edge : Edge) :
    graphBoundary edgeStart edgeEnd (Pi.single edge 1) =
      graphEdgeBoundary edgeStart edgeEnd edge := by
  classical
  ext vertex
  unfold graphBoundary
  dsimp
  rw [Fintype.sum_eq_single edge]
  · simp
  · intro edge' hne
    simp [Pi.single_eq_of_ne hne]

/-- Sum all binary vertex coordinates. -/
def totalParity {Vertex : Type} [Fintype Vertex] :
    Word Field Vertex →ₗ[Field] Field where
  toFun := fun word => ∑ vertex : Vertex, word vertex
  map_add' := by
    intro a b
    simp [Finset.sum_add_distrib]
  map_smul' := by
    intro coefficient word
    simp [Finset.mul_sum]

@[simp]
theorem totalParity_apply {Vertex : Type} [Fintype Vertex]
    (word : Word Field Vertex) :
    totalParity word = ∑ vertex : Vertex, word vertex := rfl

@[simp]
theorem totalParity_graphEdgeBoundary {Vertex Edge : Type}
    [Fintype Vertex] [DecidableEq Vertex]
    (edgeStart edgeEnd : Edge → Vertex) (edge : Edge) :
    totalParity (graphEdgeBoundary edgeStart edgeEnd edge) = 0 := by
  classical
  simp only [graphEdgeBoundary, totalParity_apply, Pi.add_apply,
    Finset.sum_add_distrib]
  simp
  change (1 : ZMod 2) + 1 = 0
  decide

/-- Every constructed graph boundary has even total parity. -/
theorem totalParity_graphBoundary {Vertex Edge : Type}
    [Fintype Vertex] [Fintype Edge] [DecidableEq Vertex]
    (edgeStart edgeEnd : Edge → Vertex) (chain : Word Field Edge) :
    totalParity (graphBoundary edgeStart edgeEnd chain) = 0 := by
  classical
  change (∑ vertex : Vertex, ∑ edge : Edge,
    chain edge * graphEdgeBoundary edgeStart edgeEnd edge vertex) = 0
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro edge _
  rw [← Finset.mul_sum]
  change chain edge * totalParity
    (graphEdgeBoundary edgeStart edgeEnd edge) = 0
  rw [totalParity_graphEdgeBoundary, mul_zero]

/-- A path chain has exactly its root and target as boundary. -/
theorem graphBoundary_pathChain {Vertex Edge : Type}
    [Fintype Edge] [DecidableEq Edge] [DecidableEq Vertex]
    (edgeStart edgeEnd : Edge → Vertex) (root : Vertex)
    {target : Vertex}
    (path : UndirectedPath edgeStart edgeEnd root target) :
    graphBoundary edgeStart edgeEnd (pathChain path) =
      Pi.single root 1 + Pi.single target 1 := by
  induction path with
  | nil =>
      simp only [pathChain, map_zero]
      exact (ZModModule.add_self (Pi.single root 1)).symm
  | @step u v path edge connects ih =>
      rw [pathChain, map_add, ih, graphBoundary_single]
      rcases connects with h | h
      · rw [graphEdgeBoundary, h.1, h.2]
        calc
          (Pi.single root 1 + Pi.single u 1) +
              (Pi.single u 1 + Pi.single v 1) =
              Pi.single root 1 +
                (Pi.single u 1 + Pi.single u 1) + Pi.single v 1 := by abel
          _ = Pi.single root 1 + Pi.single v 1 := by
            rw [ZModModule.add_self]
            simp
      · rw [graphEdgeBoundary, h.1, h.2]
        calc
          (Pi.single root 1 + Pi.single u 1) +
              (Pi.single v 1 + Pi.single u 1) =
              Pi.single root 1 +
                (Pi.single u 1 + Pi.single u 1) + Pi.single v 1 := by abel
          _ = Pi.single root 1 + Pi.single v 1 := by
            rw [ZModModule.add_self]
            simp

/-- Every word differs from the root parity representative by an explicit
boundary.  The witness is local to the theorem; no global section is exported. -/
theorem exists_graphBoundary_eq_add_rootParity {Vertex Edge : Type}
    [Fintype Vertex] [Fintype Edge]
    [DecidableEq Vertex] [DecidableEq Edge]
    (edgeStart edgeEnd : Edge → Vertex) (root : Vertex)
    (paths : ∀ vertex, UndirectedPath edgeStart edgeEnd root vertex)
    (word : Word Field Vertex) :
    ∃ chain : Word Field Edge,
      graphBoundary edgeStart edgeEnd chain =
        word + Pi.single root (totalParity word) := by
  classical
  let chain : Word Field Edge :=
    ∑ vertex : Vertex, word vertex • pathChain (paths vertex)
  refine ⟨chain, ?_⟩
  rw [show graphBoundary edgeStart edgeEnd chain =
      ∑ vertex : Vertex,
        word vertex • graphBoundary edgeStart edgeEnd (pathChain (paths vertex)) by
    simp [chain]]
  simp_rw [graphBoundary_pathChain edgeStart edgeEnd root]
  simp_rw [smul_add]
  rw [Finset.sum_add_distrib]
  have hroot :
      (∑ vertex : Vertex, word vertex • Pi.single root 1) =
        Pi.single root (totalParity word) := by
    ext vertex
    by_cases hvertex : vertex = root
    · subst vertex
      simp [totalParity]
    · simp [hvertex]
  have hword :
      (∑ vertex : Vertex, word vertex • Pi.single vertex 1) = word := by
    calc
      (∑ vertex : Vertex, word vertex • Pi.single vertex 1) =
          ∑ vertex : Vertex, Pi.single vertex (word vertex) := by
        apply Finset.sum_congr rfl
        intro vertex _
        ext target
        by_cases htarget : target = vertex
        · subst target
          simp
        · simp [htarget]
      _ = word := word_eq_sum_single (F := Field) word
  rw [hroot, hword, add_comm]

/-- In the boundary quotient, every word equals its explicit root-parity
representative.  This is an equality of quotient representatives only; it
does not define a section or a quotient equivalence. -/
theorem graphBoundary_quotient_mk_eq_single_root_totalParity
    {Vertex Edge : Type}
    [Fintype Vertex] [Fintype Edge]
    [DecidableEq Vertex] [DecidableEq Edge]
    (edgeStart edgeEnd : Edge → Vertex) (root : Vertex)
    (paths : ∀ vertex, UndirectedPath edgeStart edgeEnd root vertex)
    (word : Word Field Vertex) :
    (LinearMap.range (graphBoundary edgeStart edgeEnd)).mkQ word =
      (LinearMap.range (graphBoundary edgeStart edgeEnd)).mkQ
        (Pi.single root (totalParity word)) := by
  change (Submodule.Quotient.mk word :
      Word Field Vertex ⧸ LinearMap.range (graphBoundary edgeStart edgeEnd)) =
    Submodule.Quotient.mk (Pi.single root (totalParity word))
  rw [Submodule.Quotient.eq]
  obtain ⟨chain, hchain⟩ :=
    exists_graphBoundary_eq_add_rootParity edgeStart edgeEnd root paths word
  refine ⟨chain, ?_⟩
  rw [hchain]
  ext vertex
  change word vertex +
      (Pi.single root (totalParity word) : Word Field Vertex) vertex =
    word vertex -
      (Pi.single root (totalParity word) : Word Field Vertex) vertex
  rw [ZModModule.sub_eq_add]

/-- Constructive connectedness proves binary graph exactness. -/
theorem graphBoundary_range_eq_totalParity_ker {Vertex Edge : Type}
    [Fintype Vertex] [Fintype Edge]
    [DecidableEq Vertex] [DecidableEq Edge]
    (edgeStart edgeEnd : Edge → Vertex) (root : Vertex)
    (paths : ∀ vertex, UndirectedPath edgeStart edgeEnd root vertex) :
    LinearMap.range (graphBoundary edgeStart edgeEnd) =
      LinearMap.ker totalParity := by
  ext word
  constructor
  · rintro ⟨chain, rfl⟩
    change totalParity (graphBoundary edgeStart edgeEnd chain) = 0
    exact totalParity_graphBoundary edgeStart edgeEnd chain
  · intro hword
    rw [LinearMap.mem_ker] at hword
    obtain ⟨chain, hchain⟩ :=
      exists_graphBoundary_eq_add_rootParity edgeStart edgeEnd root paths word
    refine ⟨chain, ?_⟩
    simpa [hword] using hchain

/-! ## Explicit X/Z boundary paths and the six-field admissible domain -/

/-- Transport an explicit undirected path along endpoint-preserving maps. -/
noncomputable def UndirectedPath.map {Vertex Edge Vertex' Edge' : Type}
    {edgeStart edgeEnd : Edge → Vertex}
    {edgeStart' edgeEnd' : Edge' → Vertex'}
    (vertexMap : Vertex → Vertex') (edgeMap : Edge → Edge')
    (start_commutes : ∀ edge, edgeStart' (edgeMap edge) = vertexMap (edgeStart edge))
    (end_commutes : ∀ edge, edgeEnd' (edgeMap edge) = vertexMap (edgeEnd edge))
    {root target : Vertex}
    (path : UndirectedPath edgeStart edgeEnd root target) :
    UndirectedPath edgeStart' edgeEnd' (vertexMap root) (vertexMap target) := by
  induction path with
  | nil => exact .nil
  | @step u v path edge connects ih =>
      apply UndirectedPath.step ih (edgeMap edge)
      rcases connects with h | h
      · exact Or.inl ⟨by rw [start_commutes, h.1], by rw [end_commutes, h.2]⟩
      · exact Or.inr ⟨by rw [start_commutes, h.1], by rw [end_commutes, h.2]⟩

/-- Undirected paths do not depend on the selected endpoint orientation. -/
noncomputable def UndirectedPath.swapEndpoints {Vertex Edge : Type}
    {edgeStart edgeEnd : Edge → Vertex} {root target : Vertex}
    (path : UndirectedPath edgeStart edgeEnd root target) :
    UndirectedPath edgeEnd edgeStart root target := by
  induction path with
  | nil => exact .nil
  | @step u v path edge connects ih =>
      apply UndirectedPath.step ih edge
      rcases connects with h | h
      · exact Or.inr ⟨h.2, h.1⟩
      · exact Or.inl ⟨h.2, h.1⟩

/-- Concatenate two explicit paths at their common endpoint. -/
noncomputable def UndirectedPath.append {Vertex Edge : Type}
    {edgeStart edgeEnd : Edge → Vertex} {root middle target : Vertex}
    (first : UndirectedPath edgeStart edgeEnd root middle)
    (second : UndirectedPath edgeStart edgeEnd middle target) :
    UndirectedPath edgeStart edgeEnd root target := by
  induction second with
  | nil => exact first
  | @step u v path edge connects ih =>
      exact .step ih edge connects

/-- Reverse a path without choosing any new edge. -/
noncomputable def UndirectedPath.reverse {Vertex Edge : Type}
    {edgeStart edgeEnd : Edge → Vertex} {root target : Vertex}
    (path : UndirectedPath edgeStart edgeEnd root target) :
    UndirectedPath edgeStart edgeEnd target root := by
  induction path with
  | nil => exact .nil
  | @step u v path edge connects ih =>
      let first : UndirectedPath edgeStart edgeEnd v u :=
        .step .nil edge (by
          rcases connects with h | h
          · exact Or.inr h
          · exact Or.inl h)
      exact first.append ih

/-- Q endpoint of an X-star boundary Q-Z edge. -/
def xBoundaryEdgeStart (P : TannerSquarePresentation) (x : P.X) :
    XStarBoundaryEdge P x → XStarBoundaryVertex P x := fun edge => by
  rcases edge with ⟨edge, hedge⟩
  rcases edge with edge | edge
  · simp [xStarBoundaryEdgeMember] at hedge
  · refine ⟨Vertex.q edge.1.1, ?_⟩
    change decide (∃ face : P.Face, xStarFaceMember P x face = true ∧
      decide (edge = faceQZEdge P face 0 ∨ edge = faceQZEdge P face 1) = true) = true at hedge
    rcases of_decide_eq_true hedge with ⟨face, hface, huse⟩
    have huse' : edge = faceQZEdge P face 0 ∨ edge = faceQZEdge P face 1 :=
      of_decide_eq_true huse
    change decide (∃ face : P.Face, xStarFaceMember P x face = true ∧
      (edge.1.1 = P.faceQ face 0 ∨ edge.1.1 = P.faceQ face 1)) = true
    rw [decide_eq_true_eq]
    refine ⟨face, hface, ?_⟩
    rcases huse' with huse | huse
    · exact Or.inl (congrArg (fun e : QZEdge P => e.1.1) huse)
    · exact Or.inr (congrArg (fun e : QZEdge P => e.1.1) huse)

/-- Z endpoint of an X-star boundary Q-Z edge. -/
def xBoundaryEdgeEnd (P : TannerSquarePresentation) (x : P.X) :
    XStarBoundaryEdge P x → XStarBoundaryVertex P x := fun edge => by
  rcases edge with ⟨edge, hedge⟩
  rcases edge with edge | edge
  · simp [xStarBoundaryEdgeMember] at hedge
  · refine ⟨Vertex.z edge.1.2, ?_⟩
    change decide (∃ face : P.Face, xStarFaceMember P x face = true ∧
      decide (edge = faceQZEdge P face 0 ∨ edge = faceQZEdge P face 1) = true) = true at hedge
    rcases of_decide_eq_true hedge with ⟨face, hface, huse⟩
    have huse' : edge = faceQZEdge P face 0 ∨ edge = faceQZEdge P face 1 :=
      of_decide_eq_true huse
    change decide (∃ face : P.Face, xStarFaceMember P x face = true ∧
      edge.1.2 = P.faceZ face) = true
    rw [decide_eq_true_eq]
    refine ⟨face, hface, ?_⟩
    rcases huse' with huse | huse
    · exact congrArg (fun e : QZEdge P => e.1.2) huse
    · exact congrArg (fun e : QZEdge P => e.1.2) huse

/-- X endpoint of a Z-star boundary X-Q edge. -/
def zBoundaryEdgeStart (P : TannerSquarePresentation) (z : P.Z) :
    ZStarBoundaryEdge P z → ZStarBoundaryVertex P z := fun edge => by
  rcases edge with ⟨edge, hedge⟩
  rcases edge with edge | edge
  · refine ⟨Vertex.x edge.1.1, ?_⟩
    change decide (∃ face : P.Face, zStarFaceMember P z face = true ∧
      decide (edge = faceXQEdge P face 0 ∨ edge = faceXQEdge P face 1) = true) = true at hedge
    rcases of_decide_eq_true hedge with ⟨face, hface, huse⟩
    have huse' : edge = faceXQEdge P face 0 ∨ edge = faceXQEdge P face 1 :=
      of_decide_eq_true huse
    change decide (∃ face : P.Face, zStarFaceMember P z face = true ∧
      edge.1.1 = P.faceX face) = true
    rw [decide_eq_true_eq]
    refine ⟨face, hface, ?_⟩
    rcases huse' with huse | huse
    · exact congrArg (fun e : XQEdge P => e.1.1) huse
    · exact congrArg (fun e : XQEdge P => e.1.1) huse
  · simp [zStarBoundaryEdgeMember] at hedge

/-- Q endpoint of a Z-star boundary X-Q edge. -/
def zBoundaryEdgeEnd (P : TannerSquarePresentation) (z : P.Z) :
    ZStarBoundaryEdge P z → ZStarBoundaryVertex P z := fun edge => by
  rcases edge with ⟨edge, hedge⟩
  rcases edge with edge | edge
  · refine ⟨Vertex.q edge.1.2, ?_⟩
    change decide (∃ face : P.Face, zStarFaceMember P z face = true ∧
      decide (edge = faceXQEdge P face 0 ∨ edge = faceXQEdge P face 1) = true) = true at hedge
    rcases of_decide_eq_true hedge with ⟨face, hface, huse⟩
    have huse' : edge = faceXQEdge P face 0 ∨ edge = faceXQEdge P face 1 :=
      of_decide_eq_true huse
    change decide (∃ face : P.Face, zStarFaceMember P z face = true ∧
      (edge.1.2 = P.faceQ face 0 ∨ edge.1.2 = P.faceQ face 1)) = true
    rw [decide_eq_true_eq]
    refine ⟨face, hface, ?_⟩
    rcases huse' with huse | huse
    · exact Or.inl (congrArg (fun e : XQEdge P => e.1.2) huse)
    · exact Or.inr (congrArg (fun e : XQEdge P => e.1.2) huse)
  · simp [zStarBoundaryEdgeMember] at hedge

/-- The exact raw local-regularity domain frozen by #878.

There are exactly six fields.  Paths and incidences are data; no chain law,
exactness, quotient, cohomology, map, or preservation conclusion is stored.
-/
structure TannerSquareAdmissible (P : TannerSquarePresentation) where
  xBoundaryRoot : ∀ x : P.X, XStarBoundaryVertex P x
  xBoundaryPath : ∀ (x : P.X) (vertex : XStarBoundaryVertex P x),
    UndirectedPath (xBoundaryEdgeStart P x) (xBoundaryEdgeEnd P x)
      (xBoundaryRoot x) vertex
  zBoundaryRoot : ∀ z : P.Z, ZStarBoundaryVertex P z
  zBoundaryPath : ∀ (z : P.Z) (vertex : ZStarBoundaryVertex P z),
    UndirectedPath (zBoundaryEdgeStart P z) (zBoundaryEdgeEnd P z)
      (zBoundaryRoot z) vertex
  qzRoot : ∀ q : P.Q, {z : P.Z // P.qz q z = true}
  xqRoot : ∀ q : P.Q, {x : P.X // P.xq x q = true}

/-- Select one of the two explicitly oriented endpoints of an edge. -/
def edgeEndpoint {Vertex Edge : Type}
    (edgeStart edgeEnd : Edge → Vertex) (edge : Edge) (endpoint : Two) : Vertex :=
  finTwoElim (motive := fun _ => Vertex) (edgeStart edge) (edgeEnd edge) endpoint

@[simp] theorem edgeEndpoint_zero {Vertex Edge : Type}
    (edgeStart edgeEnd : Edge → Vertex) (edge : Edge) :
    edgeEndpoint edgeStart edgeEnd edge 0 = edgeStart edge := rfl

@[simp] theorem edgeEndpoint_one {Vertex Edge : Type}
    (edgeStart edgeEnd : Edge → Vertex) (edge : Edge) :
    edgeEndpoint edgeStart edgeEnd edge 1 = edgeEnd edge := rfl

/-- Transposition reverses the old boundary-edge orientation. -/
def flipEndpoint (endpoint : Two) : Two :=
  finTwoElim (motive := fun _ => Two) 1 0 endpoint

@[simp] theorem flipEndpoint_zero : flipEndpoint 0 = 1 := rfl
@[simp] theorem flipEndpoint_one : flipEndpoint 1 = 0 := rfl

/-- The versioned endpoint-tagged admissibility domain frozen by #904.

The historical six-field domain is retained verbatim through `toTannerSquareAdmissible`.
The two new fields are Type-valued raw witnesses, not conclusions reconstructed
from endpoint-incidence propositions.
-/
structure TannerSquareAdmissibleV2 (P : TannerSquarePresentation)
    extends TannerSquareAdmissible P where
  xBoundaryIncidentEdge : ∀ (x : P.X) (vertex : XStarBoundaryVertex P x),
    {owned : XStarBoundaryEdge P x × Two //
      edgeEndpoint (xBoundaryEdgeStart P x) (xBoundaryEdgeEnd P x)
        owned.1 owned.2 = vertex}
  zBoundaryIncidentEdge : ∀ (z : P.Z) (vertex : ZStarBoundaryVertex P z),
    {owned : ZStarBoundaryEdge P z × Two //
      edgeEndpoint (zBoundaryEdgeStart P z) (zBoundaryEdgeEnd P z)
        owned.1 owned.2 = vertex}

/-- The versioned radial-owner domain frozen by #908.

The historical and endpoint-tagged admissibility data are retained through
`toTannerSquareAdmissibleV2`.  The two new fields contain only an old star
face, its ordered radial corner, and the exact old radial-edge equality.
-/
structure TannerSquareAdmissibleV3 (P : TannerSquarePresentation)
    extends TannerSquareAdmissibleV2 P where
  xRadialFaceOwner : ∀ (x : P.X) (e : XQEdge P)
      (he : xStarEdgeMember P x (Sum.inl e) = true),
    {owner : XStarFace P x × Two //
      xStarFaceXQEdge P x owner.1 owner.2 = ⟨Sum.inl e, he⟩}
  zRadialFaceOwner : ∀ (z : P.Z) (e : QZEdge P)
      (he : zStarEdgeMember P z (Sum.inr e) = true),
    {owner : ZStarFace P z × Two //
      zStarFaceQZEdge P z owner.1 owner.2 = ⟨Sum.inr e, he⟩}

/-- The versioned boundary-face owner domain frozen by #931.

The historical, endpoint-tagged, and radial-owner data are retained through
`toTannerSquareAdmissibleV3`.  The two new fields contain only an old star
face, its ordered boundary corner, and the exact old boundary-edge equality.
-/
structure TannerSquareAdmissibleV4 (P : TannerSquarePresentation)
    extends TannerSquareAdmissibleV3 P where
  xBoundaryFaceOwner : ∀ (x : P.X) (edge : QZEdge P)
      (member : xStarEdgeMember P x (Sum.inr edge) = true),
    {owner : XStarFace P x × Two //
      xStarFaceQZEdge P x owner.1 owner.2 = ⟨Sum.inr edge, member⟩}
  zBoundaryFaceOwner : ∀ (z : P.Z) (edge : XQEdge P)
      (member : zStarEdgeMember P z (Sum.inl edge) = true),
    {owner : ZStarFace P z × Two //
      zStarFaceXQEdge P z owner.1 owner.2 = ⟨Sum.inl edge, member⟩}

@[simp] theorem transpose_zStarBoundaryVertexMember
    (P : TannerSquarePresentation) (x : P.X)
    (vertex : Vertex (transposePresentation P)) :
    zStarBoundaryVertexMember (transposePresentation P) x vertex =
      xStarBoundaryVertexMember P x (transposeVertexEquiv P vertex) := by
  rcases vertex with z | q | x' <;> rfl

@[simp] theorem transpose_zStarBoundaryEdgeMember
    (P : TannerSquarePresentation) (x : P.X)
    (edge : Edge (transposePresentation P)) :
    zStarBoundaryEdgeMember (transposePresentation P) x edge =
      xStarBoundaryEdgeMember P x (transposeEdgeEquiv P edge) := by
  rcases edge with edge | edge
  · simp only [zStarBoundaryEdgeMember, xStarBoundaryEdgeMember, transposeEdgeEquiv]
    apply Bool.decide_congr
    constructor
    · rintro ⟨face, hface, hedge⟩
      refine ⟨face, hface, ?_⟩
      erw [decide_eq_true_eq]
      rcases of_decide_eq_true hedge with hedge | hedge
      · left
        rw [hedge]
        exact transposeXQEdgeEquiv_faceXQEdge P face 0
      · right
        rw [hedge]
        exact transposeXQEdgeEquiv_faceXQEdge P face 1
    · rintro ⟨face, hface, hedge⟩
      refine ⟨face, hface, ?_⟩
      erw [decide_eq_true_eq]
      rcases of_decide_eq_true hedge with hedge | hedge
      · left
        apply (transposeXQEdgeEquiv P).injective
        simpa using hedge
      · right
        apply (transposeXQEdgeEquiv P).injective
        simpa using hedge
  · rfl

/-- Transposed Z-boundary vertices are original X-boundary vertices. -/
noncomputable def transposeZStarBoundaryVertexEquiv
    (P : TannerSquarePresentation) (x : P.X) :
    ZStarBoundaryVertex (transposePresentation P) x ≃
      XStarBoundaryVertex P x where
  toFun := fun vertex =>
    ⟨transposeVertexEquiv P vertex.1, by simpa using vertex.2⟩
  invFun := fun vertex =>
    ⟨(transposeVertexEquiv P).symm vertex.1, by
      rw [transpose_zStarBoundaryVertexMember, Equiv.apply_symm_apply]
      exact vertex.2⟩
  left_inv := fun vertex => Subtype.ext (Equiv.symm_apply_apply _ _)
  right_inv := fun vertex => Subtype.ext (Equiv.apply_symm_apply _ _)

/-- Transposed Z-boundary edges are original X-boundary edges. -/
noncomputable def transposeZStarBoundaryEdgeEquiv
    (P : TannerSquarePresentation) (x : P.X) :
    ZStarBoundaryEdge (transposePresentation P) x ≃
      XStarBoundaryEdge P x where
  toFun := fun edge =>
    ⟨transposeEdgeEquiv P edge.1, by simpa using edge.2⟩
  invFun := fun edge =>
    ⟨(transposeEdgeEquiv P).symm edge.1, by
      rw [transpose_zStarBoundaryEdgeMember, Equiv.apply_symm_apply]
      exact edge.2⟩
  left_inv := fun edge => Subtype.ext (Equiv.symm_apply_apply _ _)
  right_inv := fun edge => Subtype.ext (Equiv.apply_symm_apply _ _)

@[simp] theorem transpose_xBoundaryEdgeStart
    (P : TannerSquarePresentation) (z : P.Z)
    (edge : XStarBoundaryEdge (transposePresentation P) z) :
    transposeXStarBoundaryVertexEquiv P z
        (xBoundaryEdgeStart (transposePresentation P) z edge) =
      zBoundaryEdgeEnd P z (transposeXStarBoundaryEdgeEquiv P z edge) := by
  rcases edge with ⟨edge, hedge⟩
  rcases edge with edge | edge
  · simp [xStarBoundaryEdgeMember] at hedge
  apply Subtype.ext
  rfl

@[simp] theorem transpose_xBoundaryEdgeEnd
    (P : TannerSquarePresentation) (z : P.Z)
    (edge : XStarBoundaryEdge (transposePresentation P) z) :
    transposeXStarBoundaryVertexEquiv P z
        (xBoundaryEdgeEnd (transposePresentation P) z edge) =
      zBoundaryEdgeStart P z (transposeXStarBoundaryEdgeEquiv P z edge) := by
  rcases edge with ⟨edge, hedge⟩
  rcases edge with edge | edge
  · simp [xStarBoundaryEdgeMember] at hedge
  apply Subtype.ext
  rfl

@[simp] theorem transpose_zBoundaryEdgeStart
    (P : TannerSquarePresentation) (x : P.X)
    (edge : ZStarBoundaryEdge (transposePresentation P) x) :
    transposeZStarBoundaryVertexEquiv P x
        (zBoundaryEdgeStart (transposePresentation P) x edge) =
      xBoundaryEdgeEnd P x (transposeZStarBoundaryEdgeEquiv P x edge) := by
  rcases edge with ⟨edge, hedge⟩
  rcases edge with edge | edge
  · apply Subtype.ext
    rfl
  · simp [zStarBoundaryEdgeMember] at hedge

@[simp] theorem transpose_zBoundaryEdgeEnd
    (P : TannerSquarePresentation) (x : P.X)
    (edge : ZStarBoundaryEdge (transposePresentation P) x) :
    transposeZStarBoundaryVertexEquiv P x
        (zBoundaryEdgeEnd (transposePresentation P) x edge) =
      xBoundaryEdgeStart P x (transposeZStarBoundaryEdgeEquiv P x edge) := by
  rcases edge with ⟨edge, hedge⟩
  rcases edge with edge | edge
  · apply Subtype.ext
    rfl
  · simp [zStarBoundaryEdgeMember] at hedge

@[simp] theorem transpose_xBoundaryEdgeEnd_symm
    (P : TannerSquarePresentation) (z : P.Z)
    (edge : ZStarBoundaryEdge P z) :
    xBoundaryEdgeEnd (transposePresentation P) z
        ((transposeXStarBoundaryEdgeEquiv P z).symm edge) =
      (transposeXStarBoundaryVertexEquiv P z).symm
        (zBoundaryEdgeStart P z edge) := by
  apply (transposeXStarBoundaryVertexEquiv P z).injective
  rw [transpose_xBoundaryEdgeEnd, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]

@[simp] theorem transpose_xBoundaryEdgeStart_symm
    (P : TannerSquarePresentation) (z : P.Z)
    (edge : ZStarBoundaryEdge P z) :
    xBoundaryEdgeStart (transposePresentation P) z
        ((transposeXStarBoundaryEdgeEquiv P z).symm edge) =
      (transposeXStarBoundaryVertexEquiv P z).symm
        (zBoundaryEdgeEnd P z edge) := by
  apply (transposeXStarBoundaryVertexEquiv P z).injective
  rw [transpose_xBoundaryEdgeStart, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]

@[simp] theorem transpose_zBoundaryEdgeEnd_symm
    (P : TannerSquarePresentation) (x : P.X)
    (edge : XStarBoundaryEdge P x) :
    zBoundaryEdgeEnd (transposePresentation P) x
        ((transposeZStarBoundaryEdgeEquiv P x).symm edge) =
      (transposeZStarBoundaryVertexEquiv P x).symm
        (xBoundaryEdgeStart P x edge) := by
  apply (transposeZStarBoundaryVertexEquiv P x).injective
  rw [transpose_zBoundaryEdgeEnd, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]

@[simp] theorem transpose_zBoundaryEdgeStart_symm
    (P : TannerSquarePresentation) (x : P.X)
    (edge : XStarBoundaryEdge P x) :
    zBoundaryEdgeStart (transposePresentation P) x
        ((transposeZStarBoundaryEdgeEquiv P x).symm edge) =
      (transposeZStarBoundaryVertexEquiv P x).symm
        (xBoundaryEdgeEnd P x edge) := by
  apply (transposeZStarBoundaryVertexEquiv P x).injective
  rw [transpose_zBoundaryEdgeStart, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]

private noncomputable def transposeXBoundaryPath
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (z : P.Z)
    (vertex : XStarBoundaryVertex (transposePresentation P) z) :
    UndirectedPath
      (xBoundaryEdgeStart (transposePresentation P) z)
      (xBoundaryEdgeEnd (transposePresentation P) z)
      ((transposeXStarBoundaryVertexEquiv P z).symm (A.zBoundaryRoot z))
      vertex := by
  let mapped := UndirectedPath.map
    (transposeXStarBoundaryVertexEquiv P z).symm
    (transposeXStarBoundaryEdgeEquiv P z).symm
    (transpose_xBoundaryEdgeEnd_symm P z)
    (transpose_xBoundaryEdgeStart_symm P z)
    (A.zBoundaryPath z (transposeXStarBoundaryVertexEquiv P z vertex))
  simpa using mapped.swapEndpoints

private noncomputable def transposeZBoundaryPath
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (x : P.X)
    (vertex : ZStarBoundaryVertex (transposePresentation P) x) :
    UndirectedPath
      (zBoundaryEdgeStart (transposePresentation P) x)
      (zBoundaryEdgeEnd (transposePresentation P) x)
      ((transposeZStarBoundaryVertexEquiv P x).symm (A.xBoundaryRoot x))
      vertex := by
  let mapped := UndirectedPath.map
    (transposeZStarBoundaryVertexEquiv P x).symm
    (transposeZStarBoundaryEdgeEquiv P x).symm
    (transpose_zBoundaryEdgeEnd_symm P x)
    (transpose_zBoundaryEdgeStart_symm P x)
    (A.xBoundaryPath x (transposeZStarBoundaryVertexEquiv P x vertex))
  simpa using mapped.swapEndpoints

/-- Admissibility is preserved by the theorem-derived X/Z transpose. -/
noncomputable def transposeTannerSquareAdmissible
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) :
    TannerSquareAdmissible (transposePresentation P) where
  xBoundaryRoot := fun z =>
    (transposeXStarBoundaryVertexEquiv P z).symm (A.zBoundaryRoot z)
  xBoundaryPath := transposeXBoundaryPath P A
  zBoundaryRoot := fun x =>
    (transposeZStarBoundaryVertexEquiv P x).symm (A.xBoundaryRoot x)
  zBoundaryPath := transposeZBoundaryPath P A
  qzRoot := fun q => ⟨(A.xqRoot q).1, (A.xqRoot q).2⟩
  xqRoot := fun q => ⟨(A.qzRoot q).1, (A.qzRoot q).2⟩

private noncomputable def transposeXBoundaryIncidentEdge
    (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV2 P)
    (z : P.Z) (vertex : XStarBoundaryVertex (transposePresentation P) z) :
    {owned : XStarBoundaryEdge (transposePresentation P) z × Two //
      edgeEndpoint
        (xBoundaryEdgeStart (transposePresentation P) z)
        (xBoundaryEdgeEnd (transposePresentation P) z)
        owned.1 owned.2 = vertex} := by
  obtain ⟨⟨edge, endpoint⟩, hendpoint⟩ :=
    A.zBoundaryIncidentEdge z (transposeXStarBoundaryVertexEquiv P z vertex)
  refine ⟨⟨(transposeXStarBoundaryEdgeEquiv P z).symm edge,
    flipEndpoint endpoint⟩, ?_⟩
  fin_cases endpoint <;>
    simpa [edgeEndpoint, flipEndpoint, finTwoElim] using
      congrArg (transposeXStarBoundaryVertexEquiv P z).symm hendpoint

private noncomputable def transposeZBoundaryIncidentEdge
    (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV2 P)
    (x : P.X) (vertex : ZStarBoundaryVertex (transposePresentation P) x) :
    {owned : ZStarBoundaryEdge (transposePresentation P) x × Two //
      edgeEndpoint
        (zBoundaryEdgeStart (transposePresentation P) x)
        (zBoundaryEdgeEnd (transposePresentation P) x)
        owned.1 owned.2 = vertex} := by
  obtain ⟨⟨edge, endpoint⟩, hendpoint⟩ :=
    A.xBoundaryIncidentEdge x (transposeZStarBoundaryVertexEquiv P x vertex)
  refine ⟨⟨(transposeZStarBoundaryEdgeEquiv P x).symm edge,
    flipEndpoint endpoint⟩, ?_⟩
  fin_cases endpoint <;>
    simpa [edgeEndpoint, flipEndpoint, finTwoElim] using
      congrArg (transposeZStarBoundaryVertexEquiv P x).symm hendpoint

/-- Endpoint-tagged admissibility is transported through transpose, with the
endpoint bit flipped because the boundary-edge orientation is reversed. -/
noncomputable def transposeTannerSquareAdmissibleV2
    (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV2 P) :
    TannerSquareAdmissibleV2 (transposePresentation P) where
  toTannerSquareAdmissible :=
    transposeTannerSquareAdmissible P A.toTannerSquareAdmissible
  xBoundaryIncidentEdge := transposeXBoundaryIncidentEdge P A
  zBoundaryIncidentEdge := transposeZBoundaryIncidentEdge P A

/-- Ordered radial face corners are invariant under X/Z transpose.  This is
separate from the oriented V2 boundary endpoint, which is flipped. -/
def transposeRadialCorner (corner : Two) : Two := corner

@[simp] theorem transposeRadialCorner_eq (corner : Two) :
    transposeRadialCorner corner = corner := rfl

private noncomputable def transposeXRadialFaceOwner
    (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV3 P)
    (z : P.Z) (e : XQEdge (transposePresentation P))
    (he : xStarEdgeMember (transposePresentation P) z (Sum.inl e) = true) :
    {owner : XStarFace (transposePresentation P) z × Two //
      xStarFaceXQEdge (transposePresentation P) z owner.1 owner.2 =
        ⟨Sum.inl e, he⟩} := by
  let mapped : QZEdge P := transposeXQEdgeEquiv P e
  have hmapped : zStarEdgeMember P z (Sum.inr mapped) = true := by
    exact (transpose_xStarEdgeMember P z (Sum.inl e)) ▸ he
  obtain ⟨⟨face, corner⟩, hedge⟩ := A.zRadialFaceOwner z mapped hmapped
  refine ⟨((transposeXStarFaceEquiv P z).symm face,
    transposeRadialCorner corner), ?_⟩
  apply Subtype.ext
  simp only [xStarFaceXQEdge]
  apply congrArg Sum.inl
  apply (transposeXQEdgeEquiv P).injective
  have hraw := congrArg Subtype.val hedge
  have hqz := Sum.inr.inj hraw
  erw [transposeXQEdgeEquiv_faceXQEdge]
  exact hqz

private theorem transpose_zStar_qz_member
    (P : TannerSquarePresentation) (x : P.X)
    (e : QZEdge (transposePresentation P))
    (he : zStarEdgeMember (transposePresentation P) x (Sum.inr e) = true) :
    xStarEdgeMember P x (Sum.inl (transposeQZEdgeEquiv P e)) = true := by
  simp only [zStarEdgeMember] at he
  simp only [xStarEdgeMember]
  rw [decide_eq_true_eq] at he ⊢
  obtain ⟨face, hface, hedge⟩ := he
  refine ⟨face, hface, ?_⟩
  erw [decide_eq_true_eq] at hedge ⊢
  rcases hedge with hedge | hedge
  · left
    rw [hedge]
    exact transposeQZEdgeEquiv_faceQZEdge P face 0
  · right
    rw [hedge]
    exact transposeQZEdgeEquiv_faceQZEdge P face 1

private noncomputable def transposeZRadialFaceOwner
    (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV3 P)
    (x : P.X) (e : QZEdge (transposePresentation P))
    (he : zStarEdgeMember (transposePresentation P) x (Sum.inr e) = true) :
    {owner : ZStarFace (transposePresentation P) x × Two //
      zStarFaceQZEdge (transposePresentation P) x owner.1 owner.2 =
        ⟨Sum.inr e, he⟩} := by
  let mapped : XQEdge P := transposeQZEdgeEquiv P e
  have hmapped : xStarEdgeMember P x (Sum.inl mapped) = true := by
    exact transpose_zStar_qz_member P x e he
  obtain ⟨⟨face, corner⟩, hedge⟩ := A.xRadialFaceOwner x mapped hmapped
  let transposedFace : ZStarFace (transposePresentation P) x :=
    ⟨face.1, face.2⟩
  refine ⟨(transposedFace, transposeRadialCorner corner), ?_⟩
  apply Subtype.ext
  simp only [zStarFaceQZEdge]
  apply congrArg Sum.inr
  apply (transposeQZEdgeEquiv P).injective
  have hraw := congrArg Subtype.val hedge
  have hxq := Sum.inl.inj hraw
  simpa [mapped, transposedFace] using hxq

/-- Transpose swaps radial sectors while retaining the same ordered radial
corner.  Endpoint flipping remains solely a V2 boundary-edge operation. -/
noncomputable def transposeTannerSquareAdmissibleV3
    (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV3 P) :
    TannerSquareAdmissibleV3 (transposePresentation P) where
  toTannerSquareAdmissibleV2 :=
    transposeTannerSquareAdmissibleV2 P A.toTannerSquareAdmissibleV2
  xRadialFaceOwner := transposeXRadialFaceOwner P A
  zRadialFaceOwner := transposeZRadialFaceOwner P A

private noncomputable def transposeXBoundaryFaceOwner
    (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (z : P.Z) (edge : QZEdge (transposePresentation P))
    (member : xStarEdgeMember (transposePresentation P) z
      (Sum.inr edge) = true) :
    {owner : XStarFace (transposePresentation P) z × Two //
      xStarFaceQZEdge (transposePresentation P) z owner.1 owner.2 =
        ⟨Sum.inr edge, member⟩} := by
  let mapped : XQEdge P := transposeQZEdgeEquiv P edge
  have mappedMember : zStarEdgeMember P z (Sum.inl mapped) = true := by
    exact (transpose_xStarEdgeMember P z (Sum.inr edge)) ▸ member
  obtain ⟨⟨face, corner⟩, edgeExact⟩ :=
    A.zBoundaryFaceOwner z mapped mappedMember
  refine ⟨((transposeXStarFaceEquiv P z).symm face, corner), ?_⟩
  apply Subtype.ext
  simp only [xStarFaceQZEdge]
  apply congrArg Sum.inr
  apply (transposeQZEdgeEquiv P).injective
  have rawExact := congrArg Subtype.val edgeExact
  have xqExact := Sum.inl.inj rawExact
  erw [transposeQZEdgeEquiv_faceQZEdge]
  exact xqExact

private theorem transpose_zStar_xq_member
    (P : TannerSquarePresentation) (x : P.X)
    (edge : XQEdge (transposePresentation P))
    (member : zStarEdgeMember (transposePresentation P) x
      (Sum.inl edge) = true) :
    xStarEdgeMember P x (Sum.inr (transposeXQEdgeEquiv P edge)) = true := by
  simp only [zStarEdgeMember] at member
  simp only [xStarEdgeMember]
  rw [decide_eq_true_eq] at member ⊢
  obtain ⟨face, faceMember, edgeMember⟩ := member
  refine ⟨face, faceMember, ?_⟩
  erw [decide_eq_true_eq] at edgeMember ⊢
  rcases edgeMember with edgeExact | edgeExact
  · left
    rw [edgeExact]
    exact transposeXQEdgeEquiv_faceXQEdge P face 0
  · right
    rw [edgeExact]
    exact transposeXQEdgeEquiv_faceXQEdge P face 1

private noncomputable def transposeZBoundaryFaceOwner
    (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (x : P.X) (edge : XQEdge (transposePresentation P))
    (member : zStarEdgeMember (transposePresentation P) x
      (Sum.inl edge) = true) :
    {owner : ZStarFace (transposePresentation P) x × Two //
      zStarFaceXQEdge (transposePresentation P) x owner.1 owner.2 =
        ⟨Sum.inl edge, member⟩} := by
  let mapped : QZEdge P := transposeXQEdgeEquiv P edge
  have mappedMember : xStarEdgeMember P x (Sum.inr mapped) = true := by
    exact transpose_zStar_xq_member P x edge member
  obtain ⟨⟨face, corner⟩, edgeExact⟩ :=
    A.xBoundaryFaceOwner x mapped mappedMember
  let transposedFace : ZStarFace (transposePresentation P) x :=
    ⟨face.1, face.2⟩
  refine ⟨(transposedFace, corner), ?_⟩
  apply Subtype.ext
  simp only [zStarFaceXQEdge]
  apply congrArg Sum.inl
  apply (transposeXQEdgeEquiv P).injective
  have rawExact := congrArg Subtype.val edgeExact
  have qzExact := Sum.inr.inj rawExact
  simpa [mapped, transposedFace] using qzExact

/-- Transpose swaps the two boundary-face owner sectors while preserving the
ordered face corner.  Endpoint flipping remains solely a V2 operation. -/
noncomputable def transposeTannerSquareAdmissibleV4
    (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P) :
    TannerSquareAdmissibleV4 (transposePresentation P) where
  toTannerSquareAdmissibleV3 :=
    transposeTannerSquareAdmissibleV3 P A.toTannerSquareAdmissibleV3
  xBoundaryFaceOwner := transposeXBoundaryFaceOwner P A
  zBoundaryFaceOwner := transposeZBoundaryFaceOwner P A

@[simp] theorem xBoundaryEdgeStart_toStar
    (P : TannerSquarePresentation) (x : P.X)
    (edge : XStarBoundaryEdge P x) :
    xStarBoundaryVertexToStar P x (xBoundaryEdgeStart P x edge) =
      xStarEdgeStart P x (xStarBoundaryEdgeToStar P x edge) := by
  rcases edge with ⟨edge, hedge⟩
  rcases edge with edge | edge
  · simp [xStarBoundaryEdgeMember] at hedge
  · apply Subtype.ext
    rfl

@[simp] theorem xBoundaryEdgeEnd_toStar
    (P : TannerSquarePresentation) (x : P.X)
    (edge : XStarBoundaryEdge P x) :
    xStarBoundaryVertexToStar P x (xBoundaryEdgeEnd P x edge) =
      xStarEdgeEnd P x (xStarBoundaryEdgeToStar P x edge) := by
  rcases edge with ⟨edge, hedge⟩
  rcases edge with edge | edge
  · simp [xStarBoundaryEdgeMember] at hedge
  · apply Subtype.ext
    rfl

private def lastSubdivisionBoundarySegment (S : OddScale) : Fin S.half :=
  ⟨S.half - 1, by have := S.half_pos; omega⟩

private def precedingSubdivisionBoundarySegment (S : OddScale)
    (interior : Fin (S.half - 1)) : Fin S.half :=
  ⟨interior.1, by have := interior.2; omega⟩

private def endpointPairSelect {T : Type} (zero one : T) (endpoint : Two) : T :=
  finTwoElim (motive := fun _ => T) zero one endpoint

@[simp] private theorem endpointPairSelect_zero {T : Type} (zero one : T) :
    endpointPairSelect zero one 0 = zero := rfl

@[simp] private theorem endpointPairSelect_one {T : Type} (zero one : T) :
    endpointPairSelect zero one 1 = one := rfl

/-- Every tagged subdivision-boundary vertex has a choice-free incident
boundary segment and an explicit endpoint tag.  Original vertices use the
endpoint-tagged v2 input; path-interior vertices use their preceding segment. -/
def subdivisionBoundaryIncidentEdge
    (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV2 P)
    (x : P.X) (S : OddScale)
    (vertex : SubdivisionBoundaryVertex P x S) :
    {owned : SubdivisionBoundaryEdge P x S × Two //
      edgeEndpoint
        (subdivisionBoundaryEdgeStart P x S)
        (subdivisionBoundaryEdgeEnd P x S)
        owned.1 owned.2 = vertex} := by
  rcases vertex with ⟨vertex, hboundary⟩
  rcases vertex with original | remaining
  · let oldVertex : XStarBoundaryVertex P x := ⟨original.1, hboundary⟩
    obtain ⟨⟨edge, endpoint⟩, hendpoint⟩ :=
      A.xBoundaryIncidentEdge x oldVertex
    let first : Fin S.half := ⟨0, S.half_pos⟩
    let last := lastSubdivisionBoundarySegment S
    let selected : Two → SubdivisionBoundaryEdge P x S × Two := fun endpoint =>
      endpointPairSelect
        (subdivisionOriginalBoundaryEdge P x S edge first, 0)
        (subdivisionOriginalBoundaryEdge P x S edge last, 1)
        endpoint
    refine ⟨selected endpoint, ?_⟩
    let zeroCase :
        edgeEndpoint (xBoundaryEdgeStart P x) (xBoundaryEdgeEnd P x)
            edge 0 = oldVertex →
          edgeEndpoint
            (subdivisionBoundaryEdgeStart P x S)
            (subdivisionBoundaryEdgeEnd P x S)
            (selected 0).1 (selected 0).2 =
              ⟨Sum.inl original, hboundary⟩ := fun hendpoint => by
      dsimp [selected]
      apply Subtype.ext
      change subdivisionSegmentStart P x S
          (xStarBoundaryEdgeToStar P x edge) first = Sum.inl original
      have hstar := congrArg (xStarBoundaryVertexToStar P x) hendpoint
      have hstart :
          xStarEdgeStart P x (xStarBoundaryEdgeToStar P x edge) = original := by
        rw [edgeEndpoint_zero, xBoundaryEdgeStart_toStar] at hstar
        exact hstar
      simp [subdivisionSegmentStart, first, hstart]
    let oneCase :
        edgeEndpoint (xBoundaryEdgeStart P x) (xBoundaryEdgeEnd P x)
            edge 1 = oldVertex →
          edgeEndpoint
            (subdivisionBoundaryEdgeStart P x S)
            (subdivisionBoundaryEdgeEnd P x S)
            (selected 1).1 (selected 1).2 =
              ⟨Sum.inl original, hboundary⟩ := fun hendpoint => by
      dsimp [selected]
      apply Subtype.ext
      change subdivisionSegmentEnd P x S
          (xStarBoundaryEdgeToStar P x edge) last = Sum.inl original
      have hstar := congrArg (xStarBoundaryVertexToStar P x) hendpoint
      have hend :
          xStarEdgeEnd P x (xStarBoundaryEdgeToStar P x edge) = original := by
        rw [edgeEndpoint_one, xBoundaryEdgeEnd_toStar] at hstar
        exact hstar
      have hlast : last.1 + 1 = S.half := by
        dsimp [last, lastSubdivisionBoundarySegment]
        have := S.half_pos
        omega
      simp [subdivisionSegmentEnd, hlast, hend]
    exact finTwoElim
      (motive := fun endpoint =>
        edgeEndpoint (xBoundaryEdgeStart P x) (xBoundaryEdgeEnd P x)
            edge endpoint = oldVertex →
          edgeEndpoint
            (subdivisionBoundaryEdgeStart P x S)
            (subdivisionBoundaryEdgeEnd P x S)
            (selected endpoint).1 (selected endpoint).2 =
              ⟨Sum.inl original, hboundary⟩)
      zeroCase oneCase endpoint hendpoint
  · rcases remaining with edgeInterior | faceInterior
    · let edge : XStarBoundaryEdge P x := ⟨edgeInterior.1.1, hboundary⟩
      let preceding :=
        precedingSubdivisionBoundarySegment S edgeInterior.2
      refine ⟨⟨subdivisionOriginalBoundaryEdge P x S edge preceding, 1⟩, ?_⟩
      rw [edgeEndpoint_one]
      apply Subtype.ext
      have hnot : edgeInterior.2.1 + 1 ≠ S.half := by
        have := edgeInterior.2.2
        omega
      change subdivisionSegmentEnd P x S
          (xStarBoundaryEdgeToStar P x edge) preceding =
        Sum.inr (Sum.inl edgeInterior)
      simp only [subdivisionSegmentEnd, preceding,
        precedingSubdivisionBoundarySegment, hnot, ↓reduceDIte, Sum.inr.injEq,
        Sum.inl.injEq]
      apply Prod.ext
      · apply Subtype.ext
        rfl
      · rfl
    · simp [subdivisionBoundaryVertexMember] at hboundary

/-- On an original boundary vertex tagged at the start of its owned old edge,
the subdivision incident-edge selector returns the first segment and endpoint
zero. -/
theorem subdivisionBoundaryIncidentEdge_original_zero
    (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV2 P)
    (x : P.X) (S : OddScale) (vertex : XStarBoundaryVertex P x)
    (hzero : (A.xBoundaryIncidentEdge x vertex).1.2 = 0) :
    (subdivisionBoundaryIncidentEdge P A x S
      (subdivisionOriginalBoundaryVertex P x S vertex)).1 =
      (subdivisionOriginalBoundaryEdge P x S
        (A.xBoundaryIncidentEdge x vertex).1.1 ⟨0, S.half_pos⟩, 0) := by
  have hvertexProof (h : xStarBoundaryVertexMember P x vertex.1 = true) :
      (⟨vertex.1, h⟩ : XStarBoundaryVertex P x) = vertex := Subtype.ext (by rfl)
  have hownerEdge (h : xStarBoundaryVertexMember P x vertex.1 = true) :
      (A.xBoundaryIncidentEdge x ⟨vertex.1, h⟩).1.1 =
        (A.xBoundaryIncidentEdge x vertex).1.1 := by
    cases hvertexProof h
    rfl
  have hownerEndpoint (h : xStarBoundaryVertexMember P x vertex.1 = true) :
      (A.xBoundaryIncidentEdge x ⟨vertex.1, h⟩).1.2 = 0 := by
    cases hvertexProof h
    exact hzero
  simp [subdivisionBoundaryIncidentEdge, subdivisionOriginalBoundaryVertex,
    xStarBoundaryVertexToStar, hownerEdge, hownerEndpoint]
  change endpointPairSelect _ _ (A.xBoundaryIncidentEdge x vertex).1.2 = _
  rw [hzero]
  rfl

/-- On an original boundary vertex tagged at the end of its owned old edge,
the subdivision incident-edge selector returns the last segment and endpoint
one. -/
theorem subdivisionBoundaryIncidentEdge_original_one
    (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV2 P)
    (x : P.X) (S : OddScale) (vertex : XStarBoundaryVertex P x)
    (hone : (A.xBoundaryIncidentEdge x vertex).1.2 = 1) :
    (subdivisionBoundaryIncidentEdge P A x S
      (subdivisionOriginalBoundaryVertex P x S vertex)).1 =
      (subdivisionOriginalBoundaryEdge P x S
        (A.xBoundaryIncidentEdge x vertex).1.1
          ⟨S.half - 1, by have := S.half_pos; omega⟩, 1) := by
  have hvertexProof (h : xStarBoundaryVertexMember P x vertex.1 = true) :
      (⟨vertex.1, h⟩ : XStarBoundaryVertex P x) = vertex := Subtype.ext (by rfl)
  have hownerEdge (h : xStarBoundaryVertexMember P x vertex.1 = true) :
      (A.xBoundaryIncidentEdge x ⟨vertex.1, h⟩).1.1 =
        (A.xBoundaryIncidentEdge x vertex).1.1 := by
    cases hvertexProof h
    rfl
  have hownerEndpoint (h : xStarBoundaryVertexMember P x vertex.1 = true) :
      (A.xBoundaryIncidentEdge x ⟨vertex.1, h⟩).1.2 = 1 := by
    cases hvertexProof h
    exact hone
  simp [subdivisionBoundaryIncidentEdge, subdivisionOriginalBoundaryVertex,
    xStarBoundaryVertexToStar, hownerEdge, hownerEndpoint,
    lastSubdivisionBoundarySegment]
  change endpointPairSelect _ _ (A.xBoundaryIncidentEdge x vertex).1.2 = _
  rw [hone]
  rfl

/-- Exactness of every admissible X-star boundary is theorem-derived. -/
theorem xBoundary_range_eq_totalParity_ker
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (x : P.X) :
    LinearMap.range (graphBoundary (xBoundaryEdgeStart P x) (xBoundaryEdgeEnd P x)) =
      LinearMap.ker totalParity :=
  graphBoundary_range_eq_totalParity_ker
    (xBoundaryEdgeStart P x) (xBoundaryEdgeEnd P x)
    (A.xBoundaryRoot x) (A.xBoundaryPath x)

/-- Exactness of every admissible Z-star boundary is theorem-derived. -/
theorem zBoundary_range_eq_totalParity_ker
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (z : P.Z) :
    LinearMap.range (graphBoundary (zBoundaryEdgeStart P z) (zBoundaryEdgeEnd P z)) =
      LinearMap.ker totalParity :=
  graphBoundary_range_eq_totalParity_ker
    (zBoundaryEdgeStart P z) (zBoundaryEdgeEnd P z)
    (A.zBoundaryRoot z) (A.zBoundaryPath z)

/-! ## Explicit base admissibility -/

private def baseXBoundaryEdge (x : BaseX) (q : BaseQubit) (z : BaseZ)
    (hqz : baseTannerSquarePresentation.qz q z = true)
    (hmember : xStarBoundaryEdgeMember baseTannerSquarePresentation x
      (Sum.inr ⟨(q, z), hqz⟩) = true) :
    XStarBoundaryEdge baseTannerSquarePresentation x :=
  ⟨Sum.inr ⟨(q, z), hqz⟩, hmember⟩

private def baseZBoundaryEdge (z : BaseZ) (x : BaseX) (q : BaseQubit)
    (hxq : baseTannerSquarePresentation.xq x q = true)
    (hmember : zStarBoundaryEdgeMember baseTannerSquarePresentation z
      (Sum.inl ⟨(x, q), hxq⟩) = true) :
    ZStarBoundaryEdge baseTannerSquarePresentation z :=
  ⟨Sum.inl ⟨(x, q), hxq⟩, hmember⟩

private def baseXBoundaryRoot (x : BaseX) :
    XStarBoundaryVertex baseTannerSquarePresentation x :=
  finTwoElim (motive := fun x =>
      XStarBoundaryVertex baseTannerSquarePresentation x)
    ⟨Vertex.q (4 : BaseQubit), by native_decide⟩
    ⟨Vertex.q (4 : BaseQubit), by native_decide⟩ x

private def baseZBoundaryRoot (z : BaseZ) :
    ZStarBoundaryVertex baseTannerSquarePresentation z :=
  finTwoElim (motive := fun z =>
      ZStarBoundaryVertex baseTannerSquarePresentation z)
    ⟨Vertex.q (4 : BaseQubit), by native_decide⟩
    ⟨Vertex.q (4 : BaseQubit), by native_decide⟩ z

private def baseX0BoundaryPath
    (vertex : XStarBoundaryVertex baseTannerSquarePresentation (0 : BaseX)) :
    UndirectedPath
      (xBoundaryEdgeStart baseTannerSquarePresentation (0 : BaseX))
      (xBoundaryEdgeEnd baseTannerSquarePresentation (0 : BaseX))
      (baseXBoundaryRoot (0 : BaseX)) vertex := by
  rcases vertex with ⟨vertex, hvertex⟩
  rcases vertex with x' | q | z
  · simp [xStarBoundaryVertexMember] at hvertex
  · refine finFiveElim (motive := fun q => ∀ hvertex :
        xStarBoundaryVertexMember baseTannerSquarePresentation (0 : BaseX)
          (Vertex.q q) = true,
        UndirectedPath
          (xBoundaryEdgeStart baseTannerSquarePresentation (0 : BaseX))
          (xBoundaryEdgeEnd baseTannerSquarePresentation (0 : BaseX))
          (baseXBoundaryRoot (0 : BaseX)) ⟨Vertex.q q, hvertex⟩)
      ?_ ?_ ?_ ?_ ?_ q hvertex
    · intro _
      exact .step
        (.step .nil
          (baseXBoundaryEdge 0 4 0 (by native_decide) (by native_decide))
          (Or.inl ⟨rfl, rfl⟩))
        (baseXBoundaryEdge 0 0 0 (by native_decide) (by native_decide))
        (Or.inr ⟨rfl, rfl⟩)
    · intro _
      exact .step
        (.step .nil
          (baseXBoundaryEdge 0 4 1 (by native_decide) (by native_decide))
          (Or.inl ⟨rfl, rfl⟩))
        (baseXBoundaryEdge 0 1 1 (by native_decide) (by native_decide))
        (Or.inr ⟨rfl, rfl⟩)
    · intro h; change false = true at h; simp at h
    · intro h; change false = true at h; simp at h
    · intro _; exact .nil
  · refine finTwoElim (motive := fun z => ∀ hvertex :
        xStarBoundaryVertexMember baseTannerSquarePresentation (0 : BaseX)
          (Vertex.z z) = true,
        UndirectedPath
          (xBoundaryEdgeStart baseTannerSquarePresentation (0 : BaseX))
          (xBoundaryEdgeEnd baseTannerSquarePresentation (0 : BaseX))
          (baseXBoundaryRoot (0 : BaseX)) ⟨Vertex.z z, hvertex⟩)
      ?_ ?_ z hvertex
    · intro _
      exact .step .nil
        (baseXBoundaryEdge 0 4 0 (by native_decide) (by native_decide))
        (Or.inl ⟨rfl, rfl⟩)
    · intro _
      exact .step .nil
        (baseXBoundaryEdge 0 4 1 (by native_decide) (by native_decide))
        (Or.inl ⟨rfl, rfl⟩)

private def baseX1BoundaryPath
    (vertex : XStarBoundaryVertex baseTannerSquarePresentation (1 : BaseX)) :
    UndirectedPath
      (xBoundaryEdgeStart baseTannerSquarePresentation (1 : BaseX))
      (xBoundaryEdgeEnd baseTannerSquarePresentation (1 : BaseX))
      (baseXBoundaryRoot (1 : BaseX)) vertex := by
  rcases vertex with ⟨vertex, hvertex⟩
  rcases vertex with x' | q | z
  · simp [xStarBoundaryVertexMember] at hvertex
  · refine finFiveElim (motive := fun q => ∀ hvertex :
        xStarBoundaryVertexMember baseTannerSquarePresentation (1 : BaseX)
          (Vertex.q q) = true,
        UndirectedPath
          (xBoundaryEdgeStart baseTannerSquarePresentation (1 : BaseX))
          (xBoundaryEdgeEnd baseTannerSquarePresentation (1 : BaseX))
          (baseXBoundaryRoot (1 : BaseX)) ⟨Vertex.q q, hvertex⟩)
      ?_ ?_ ?_ ?_ ?_ q hvertex
    · intro h; change false = true at h; simp at h
    · intro h; change false = true at h; simp at h
    · intro _
      exact .step
        (.step .nil
          (baseXBoundaryEdge 1 4 0 (by native_decide) (by native_decide))
          (Or.inl ⟨rfl, rfl⟩))
        (baseXBoundaryEdge 1 2 0 (by native_decide) (by native_decide))
        (Or.inr ⟨rfl, rfl⟩)
    · intro _
      exact .step
        (.step .nil
          (baseXBoundaryEdge 1 4 1 (by native_decide) (by native_decide))
          (Or.inl ⟨rfl, rfl⟩))
        (baseXBoundaryEdge 1 3 1 (by native_decide) (by native_decide))
        (Or.inr ⟨rfl, rfl⟩)
    · intro _; exact .nil
  · refine finTwoElim (motive := fun z => ∀ hvertex :
        xStarBoundaryVertexMember baseTannerSquarePresentation (1 : BaseX)
          (Vertex.z z) = true,
        UndirectedPath
          (xBoundaryEdgeStart baseTannerSquarePresentation (1 : BaseX))
          (xBoundaryEdgeEnd baseTannerSquarePresentation (1 : BaseX))
          (baseXBoundaryRoot (1 : BaseX)) ⟨Vertex.z z, hvertex⟩)
      ?_ ?_ z hvertex
    · intro _
      exact .step .nil
        (baseXBoundaryEdge 1 4 0 (by native_decide) (by native_decide))
        (Or.inl ⟨rfl, rfl⟩)
    · intro _
      exact .step .nil
        (baseXBoundaryEdge 1 4 1 (by native_decide) (by native_decide))
        (Or.inl ⟨rfl, rfl⟩)

private def baseXBoundaryPath (x : BaseX)
    (vertex : XStarBoundaryVertex baseTannerSquarePresentation x) :
    UndirectedPath
      (xBoundaryEdgeStart baseTannerSquarePresentation x)
      (xBoundaryEdgeEnd baseTannerSquarePresentation x)
      (baseXBoundaryRoot x) vertex :=
  finTwoElim (motive := fun x =>
      ∀ vertex : XStarBoundaryVertex baseTannerSquarePresentation x,
        UndirectedPath
          (xBoundaryEdgeStart baseTannerSquarePresentation x)
          (xBoundaryEdgeEnd baseTannerSquarePresentation x)
          (baseXBoundaryRoot x) vertex)
    baseX0BoundaryPath baseX1BoundaryPath x vertex

private def baseZ0BoundaryPath
    (vertex : ZStarBoundaryVertex baseTannerSquarePresentation (0 : BaseZ)) :
    UndirectedPath
      (zBoundaryEdgeStart baseTannerSquarePresentation (0 : BaseZ))
      (zBoundaryEdgeEnd baseTannerSquarePresentation (0 : BaseZ))
      (baseZBoundaryRoot (0 : BaseZ)) vertex := by
  rcases vertex with ⟨vertex, hvertex⟩
  rcases vertex with x | q | z'
  · refine finTwoElim (motive := fun x => ∀ hvertex :
        zStarBoundaryVertexMember baseTannerSquarePresentation (0 : BaseZ)
          (Vertex.x x) = true,
        UndirectedPath
          (zBoundaryEdgeStart baseTannerSquarePresentation (0 : BaseZ))
          (zBoundaryEdgeEnd baseTannerSquarePresentation (0 : BaseZ))
          (baseZBoundaryRoot (0 : BaseZ)) ⟨Vertex.x x, hvertex⟩)
      ?_ ?_ x hvertex
    · intro _
      exact .step .nil
        (baseZBoundaryEdge 0 0 4 (by native_decide) (by native_decide))
        (Or.inr ⟨rfl, rfl⟩)
    · intro _
      exact .step .nil
        (baseZBoundaryEdge 0 1 4 (by native_decide) (by native_decide))
        (Or.inr ⟨rfl, rfl⟩)
  · refine finFiveElim (motive := fun q => ∀ hvertex :
        zStarBoundaryVertexMember baseTannerSquarePresentation (0 : BaseZ)
          (Vertex.q q) = true,
        UndirectedPath
          (zBoundaryEdgeStart baseTannerSquarePresentation (0 : BaseZ))
          (zBoundaryEdgeEnd baseTannerSquarePresentation (0 : BaseZ))
          (baseZBoundaryRoot (0 : BaseZ)) ⟨Vertex.q q, hvertex⟩)
      ?_ ?_ ?_ ?_ ?_ q hvertex
    · intro _
      exact .step
        (.step .nil
          (baseZBoundaryEdge 0 0 4 (by native_decide) (by native_decide))
          (Or.inr ⟨rfl, rfl⟩))
        (baseZBoundaryEdge 0 0 0 (by native_decide) (by native_decide))
        (Or.inl ⟨rfl, rfl⟩)
    · intro h; change false = true at h; simp at h
    · intro _
      exact .step
        (.step .nil
          (baseZBoundaryEdge 0 1 4 (by native_decide) (by native_decide))
          (Or.inr ⟨rfl, rfl⟩))
        (baseZBoundaryEdge 0 1 2 (by native_decide) (by native_decide))
        (Or.inl ⟨rfl, rfl⟩)
    · intro h; change false = true at h; simp at h
    · intro _; exact .nil
  · simp [zStarBoundaryVertexMember] at hvertex

private def baseZ1BoundaryPath
    (vertex : ZStarBoundaryVertex baseTannerSquarePresentation (1 : BaseZ)) :
    UndirectedPath
      (zBoundaryEdgeStart baseTannerSquarePresentation (1 : BaseZ))
      (zBoundaryEdgeEnd baseTannerSquarePresentation (1 : BaseZ))
      (baseZBoundaryRoot (1 : BaseZ)) vertex := by
  rcases vertex with ⟨vertex, hvertex⟩
  rcases vertex with x | q | z'
  · refine finTwoElim (motive := fun x => ∀ hvertex :
        zStarBoundaryVertexMember baseTannerSquarePresentation (1 : BaseZ)
          (Vertex.x x) = true,
        UndirectedPath
          (zBoundaryEdgeStart baseTannerSquarePresentation (1 : BaseZ))
          (zBoundaryEdgeEnd baseTannerSquarePresentation (1 : BaseZ))
          (baseZBoundaryRoot (1 : BaseZ)) ⟨Vertex.x x, hvertex⟩)
      ?_ ?_ x hvertex
    · intro _
      exact .step .nil
        (baseZBoundaryEdge 1 0 4 (by native_decide) (by native_decide))
        (Or.inr ⟨rfl, rfl⟩)
    · intro _
      exact .step .nil
        (baseZBoundaryEdge 1 1 4 (by native_decide) (by native_decide))
        (Or.inr ⟨rfl, rfl⟩)
  · refine finFiveElim (motive := fun q => ∀ hvertex :
        zStarBoundaryVertexMember baseTannerSquarePresentation (1 : BaseZ)
          (Vertex.q q) = true,
        UndirectedPath
          (zBoundaryEdgeStart baseTannerSquarePresentation (1 : BaseZ))
          (zBoundaryEdgeEnd baseTannerSquarePresentation (1 : BaseZ))
          (baseZBoundaryRoot (1 : BaseZ)) ⟨Vertex.q q, hvertex⟩)
      ?_ ?_ ?_ ?_ ?_ q hvertex
    · intro h; change false = true at h; simp at h
    · intro _
      exact .step
        (.step .nil
          (baseZBoundaryEdge 1 0 4 (by native_decide) (by native_decide))
          (Or.inr ⟨rfl, rfl⟩))
        (baseZBoundaryEdge 1 0 1 (by native_decide) (by native_decide))
        (Or.inl ⟨rfl, rfl⟩)
    · intro h; change false = true at h; simp at h
    · intro _
      exact .step
        (.step .nil
          (baseZBoundaryEdge 1 1 4 (by native_decide) (by native_decide))
          (Or.inr ⟨rfl, rfl⟩))
        (baseZBoundaryEdge 1 1 3 (by native_decide) (by native_decide))
        (Or.inl ⟨rfl, rfl⟩)
    · intro _; exact .nil
  · simp [zStarBoundaryVertexMember] at hvertex

private def baseZBoundaryPath (z : BaseZ)
    (vertex : ZStarBoundaryVertex baseTannerSquarePresentation z) :
    UndirectedPath
      (zBoundaryEdgeStart baseTannerSquarePresentation z)
      (zBoundaryEdgeEnd baseTannerSquarePresentation z)
      (baseZBoundaryRoot z) vertex :=
  finTwoElim (motive := fun z =>
      ∀ vertex : ZStarBoundaryVertex baseTannerSquarePresentation z,
        UndirectedPath
          (zBoundaryEdgeStart baseTannerSquarePresentation z)
          (zBoundaryEdgeEnd baseTannerSquarePresentation z)
          (baseZBoundaryRoot z) vertex)
    baseZ0BoundaryPath baseZ1BoundaryPath z vertex

private def baseQZRoot (q : BaseQubit) :
    {z : BaseZ // baseTannerSquarePresentation.qz q z = true} :=
  finFiveElim (motive := fun q =>
      {z : BaseZ // baseTannerSquarePresentation.qz q z = true})
    ⟨0, by native_decide⟩ ⟨1, by native_decide⟩
    ⟨0, by native_decide⟩ ⟨1, by native_decide⟩
    ⟨0, by native_decide⟩ q

private def baseXQRoot (q : BaseQubit) :
    {x : BaseX // baseTannerSquarePresentation.xq x q = true} :=
  finFiveElim (motive := fun q =>
      {x : BaseX // baseTannerSquarePresentation.xq x q = true})
    ⟨0, by native_decide⟩ ⟨0, by native_decide⟩
    ⟨1, by native_decide⟩ ⟨1, by native_decide⟩
    ⟨0, by native_decide⟩ q

/-- Explicit path witnesses make the owner-verified base presentation admissible. -/
def baseTannerSquareAdmissible :
    TannerSquareAdmissible baseTannerSquarePresentation where
  xBoundaryRoot := baseXBoundaryRoot
  xBoundaryPath := baseXBoundaryPath
  zBoundaryRoot := baseZBoundaryRoot
  zBoundaryPath := baseZBoundaryPath
  qzRoot := baseQZRoot
  xqRoot := baseXQRoot

private abbrev BaseXBoundaryIncident
    (x : BaseX)
    (vertex : XStarBoundaryVertex baseTannerSquarePresentation x) :=
  {owned : XStarBoundaryEdge baseTannerSquarePresentation x × Two //
    edgeEndpoint
      (xBoundaryEdgeStart baseTannerSquarePresentation x)
      (xBoundaryEdgeEnd baseTannerSquarePresentation x)
      owned.1 owned.2 = vertex}

private abbrev BaseZBoundaryIncident
    (z : BaseZ)
    (vertex : ZStarBoundaryVertex baseTannerSquarePresentation z) :=
  {owned : ZStarBoundaryEdge baseTannerSquarePresentation z × Two //
    edgeEndpoint
      (zBoundaryEdgeStart baseTannerSquarePresentation z)
      (zBoundaryEdgeEnd baseTannerSquarePresentation z)
      owned.1 owned.2 = vertex}

private def baseXBoundaryIncidentAtStart
    (x : BaseX) (q : BaseQubit) (z : BaseZ)
    (hqz : baseTannerSquarePresentation.qz q z = true)
    (hmember : xStarBoundaryEdgeMember baseTannerSquarePresentation x
      (Sum.inr ⟨(q, z), hqz⟩) = true)
    (hvertex : xStarBoundaryVertexMember baseTannerSquarePresentation x
      (Vertex.q q) = true) :
    BaseXBoundaryIncident x ⟨Vertex.q q, hvertex⟩ :=
  ⟨⟨baseXBoundaryEdge x q z hqz hmember, 0⟩, by
    rw [edgeEndpoint_zero]
    apply Subtype.ext
    rfl⟩

private def baseXBoundaryIncidentAtEnd
    (x : BaseX) (q : BaseQubit) (z : BaseZ)
    (hqz : baseTannerSquarePresentation.qz q z = true)
    (hmember : xStarBoundaryEdgeMember baseTannerSquarePresentation x
      (Sum.inr ⟨(q, z), hqz⟩) = true)
    (hvertex : xStarBoundaryVertexMember baseTannerSquarePresentation x
      (Vertex.z z) = true) :
    BaseXBoundaryIncident x ⟨Vertex.z z, hvertex⟩ :=
  ⟨⟨baseXBoundaryEdge x q z hqz hmember, 1⟩, by
    rw [edgeEndpoint_one]
    apply Subtype.ext
    rfl⟩

private def baseZBoundaryIncidentAtStart
    (z : BaseZ) (x : BaseX) (q : BaseQubit)
    (hxq : baseTannerSquarePresentation.xq x q = true)
    (hmember : zStarBoundaryEdgeMember baseTannerSquarePresentation z
      (Sum.inl ⟨(x, q), hxq⟩) = true)
    (hvertex : zStarBoundaryVertexMember baseTannerSquarePresentation z
      (Vertex.x x) = true) :
    BaseZBoundaryIncident z ⟨Vertex.x x, hvertex⟩ :=
  ⟨⟨baseZBoundaryEdge z x q hxq hmember, 0⟩, by
    rw [edgeEndpoint_zero]
    apply Subtype.ext
    rfl⟩

private def baseZBoundaryIncidentAtEnd
    (z : BaseZ) (x : BaseX) (q : BaseQubit)
    (hxq : baseTannerSquarePresentation.xq x q = true)
    (hmember : zStarBoundaryEdgeMember baseTannerSquarePresentation z
      (Sum.inl ⟨(x, q), hxq⟩) = true)
    (hvertex : zStarBoundaryVertexMember baseTannerSquarePresentation z
      (Vertex.q q) = true) :
    BaseZBoundaryIncident z ⟨Vertex.q q, hvertex⟩ :=
  ⟨⟨baseZBoundaryEdge z x q hxq hmember, 1⟩, by
    rw [edgeEndpoint_one]
    apply Subtype.ext
    rfl⟩

private def baseX0BoundaryIncident
    (vertex :
      XStarBoundaryVertex baseTannerSquarePresentation (0 : BaseX)) :
    BaseXBoundaryIncident 0 vertex := by
  rcases vertex with ⟨vertex, hvertex⟩
  rcases vertex with x | q | z
  · simp [xStarBoundaryVertexMember] at hvertex
  · refine finFiveElim (motive := fun q => ∀ hvertex :
        xStarBoundaryVertexMember baseTannerSquarePresentation (0 : BaseX)
          (Vertex.q q) = true,
        BaseXBoundaryIncident 0 ⟨Vertex.q q, hvertex⟩)
      ?_ ?_ ?_ ?_ ?_ q hvertex
    · intro h
      exact baseXBoundaryIncidentAtStart 0 0 0
        (by native_decide) (by native_decide) h
    · intro h
      exact baseXBoundaryIncidentAtStart 0 1 1
        (by native_decide) (by native_decide) h
    · intro h; change false = true at h; simp at h
    · intro h; change false = true at h; simp at h
    · intro h
      exact baseXBoundaryIncidentAtStart 0 4 0
        (by native_decide) (by native_decide) h
  · refine finTwoElim (motive := fun z => ∀ hvertex :
        xStarBoundaryVertexMember baseTannerSquarePresentation (0 : BaseX)
          (Vertex.z z) = true,
        BaseXBoundaryIncident 0 ⟨Vertex.z z, hvertex⟩)
      ?_ ?_ z hvertex
    · intro h
      exact baseXBoundaryIncidentAtEnd 0 4 0
        (by native_decide) (by native_decide) h
    · intro h
      exact baseXBoundaryIncidentAtEnd 0 4 1
        (by native_decide) (by native_decide) h

private def baseX1BoundaryIncident
    (vertex :
      XStarBoundaryVertex baseTannerSquarePresentation (1 : BaseX)) :
    BaseXBoundaryIncident 1 vertex := by
  rcases vertex with ⟨vertex, hvertex⟩
  rcases vertex with x | q | z
  · simp [xStarBoundaryVertexMember] at hvertex
  · refine finFiveElim (motive := fun q => ∀ hvertex :
        xStarBoundaryVertexMember baseTannerSquarePresentation (1 : BaseX)
          (Vertex.q q) = true,
        BaseXBoundaryIncident 1 ⟨Vertex.q q, hvertex⟩)
      ?_ ?_ ?_ ?_ ?_ q hvertex
    · intro h; change false = true at h; simp at h
    · intro h; change false = true at h; simp at h
    · intro h
      exact baseXBoundaryIncidentAtStart 1 2 0
        (by native_decide) (by native_decide) h
    · intro h
      exact baseXBoundaryIncidentAtStart 1 3 1
        (by native_decide) (by native_decide) h
    · intro h
      exact baseXBoundaryIncidentAtStart 1 4 0
        (by native_decide) (by native_decide) h
  · refine finTwoElim (motive := fun z => ∀ hvertex :
        xStarBoundaryVertexMember baseTannerSquarePresentation (1 : BaseX)
          (Vertex.z z) = true,
        BaseXBoundaryIncident 1 ⟨Vertex.z z, hvertex⟩)
      ?_ ?_ z hvertex
    · intro h
      exact baseXBoundaryIncidentAtEnd 1 4 0
        (by native_decide) (by native_decide) h
    · intro h
      exact baseXBoundaryIncidentAtEnd 1 4 1
        (by native_decide) (by native_decide) h

private def baseXBoundaryIncidentEdge
    (x : BaseX)
    (vertex : XStarBoundaryVertex baseTannerSquarePresentation x) :
    BaseXBoundaryIncident x vertex :=
  finTwoElim (motive := fun x =>
      ∀ vertex : XStarBoundaryVertex baseTannerSquarePresentation x,
        BaseXBoundaryIncident x vertex)
    baseX0BoundaryIncident baseX1BoundaryIncident x vertex

private def baseZ0BoundaryIncident
    (vertex :
      ZStarBoundaryVertex baseTannerSquarePresentation (0 : BaseZ)) :
    BaseZBoundaryIncident 0 vertex := by
  rcases vertex with ⟨vertex, hvertex⟩
  rcases vertex with x | q | z
  · refine finTwoElim (motive := fun x => ∀ hvertex :
        zStarBoundaryVertexMember baseTannerSquarePresentation (0 : BaseZ)
          (Vertex.x x) = true,
        BaseZBoundaryIncident 0 ⟨Vertex.x x, hvertex⟩)
      ?_ ?_ x hvertex
    · intro h
      exact baseZBoundaryIncidentAtStart 0 0 4
        (by native_decide) (by native_decide) h
    · intro h
      exact baseZBoundaryIncidentAtStart 0 1 4
        (by native_decide) (by native_decide) h
  · refine finFiveElim (motive := fun q => ∀ hvertex :
        zStarBoundaryVertexMember baseTannerSquarePresentation (0 : BaseZ)
          (Vertex.q q) = true,
        BaseZBoundaryIncident 0 ⟨Vertex.q q, hvertex⟩)
      ?_ ?_ ?_ ?_ ?_ q hvertex
    · intro h
      exact baseZBoundaryIncidentAtEnd 0 0 0
        (by native_decide) (by native_decide) h
    · intro h; change false = true at h; simp at h
    · intro h
      exact baseZBoundaryIncidentAtEnd 0 1 2
        (by native_decide) (by native_decide) h
    · intro h; change false = true at h; simp at h
    · intro h
      exact baseZBoundaryIncidentAtEnd 0 0 4
        (by native_decide) (by native_decide) h
  · simp [zStarBoundaryVertexMember] at hvertex

private def baseZ1BoundaryIncident
    (vertex :
      ZStarBoundaryVertex baseTannerSquarePresentation (1 : BaseZ)) :
    BaseZBoundaryIncident 1 vertex := by
  rcases vertex with ⟨vertex, hvertex⟩
  rcases vertex with x | q | z
  · refine finTwoElim (motive := fun x => ∀ hvertex :
        zStarBoundaryVertexMember baseTannerSquarePresentation (1 : BaseZ)
          (Vertex.x x) = true,
        BaseZBoundaryIncident 1 ⟨Vertex.x x, hvertex⟩)
      ?_ ?_ x hvertex
    · intro h
      exact baseZBoundaryIncidentAtStart 1 0 4
        (by native_decide) (by native_decide) h
    · intro h
      exact baseZBoundaryIncidentAtStart 1 1 4
        (by native_decide) (by native_decide) h
  · refine finFiveElim (motive := fun q => ∀ hvertex :
        zStarBoundaryVertexMember baseTannerSquarePresentation (1 : BaseZ)
          (Vertex.q q) = true,
        BaseZBoundaryIncident 1 ⟨Vertex.q q, hvertex⟩)
      ?_ ?_ ?_ ?_ ?_ q hvertex
    · intro h; change false = true at h; simp at h
    · intro h
      exact baseZBoundaryIncidentAtEnd 1 0 1
        (by native_decide) (by native_decide) h
    · intro h; change false = true at h; simp at h
    · intro h
      exact baseZBoundaryIncidentAtEnd 1 1 3
        (by native_decide) (by native_decide) h
    · intro h
      exact baseZBoundaryIncidentAtEnd 1 0 4
        (by native_decide) (by native_decide) h
  · simp [zStarBoundaryVertexMember] at hvertex

private def baseZBoundaryIncidentEdge
    (z : BaseZ)
    (vertex : ZStarBoundaryVertex baseTannerSquarePresentation z) :
    BaseZBoundaryIncident z vertex :=
  finTwoElim (motive := fun z =>
      ∀ vertex : ZStarBoundaryVertex baseTannerSquarePresentation z,
        BaseZBoundaryIncident z vertex)
    baseZ0BoundaryIncident baseZ1BoundaryIncident z vertex

/-- Explicit endpoint-tagged incident edges extend the owner-verified base
presentation to the #904 v2 admissibility domain. -/
def baseTannerSquareAdmissibleV2 :
    TannerSquareAdmissibleV2 baseTannerSquarePresentation where
  toTannerSquareAdmissible := baseTannerSquareAdmissible
  xBoundaryIncidentEdge := baseXBoundaryIncidentEdge
  zBoundaryIncidentEdge := baseZBoundaryIncidentEdge

private def baseXOwnerAt (x : baseTannerSquarePresentation.X)
    (e : XQEdge baseTannerSquarePresentation)
    (he : xStarEdgeMember baseTannerSquarePresentation x (Sum.inl e) = true)
    (face : BaseFace) (corner : Two)
    (hface : xStarFaceMember baseTannerSquarePresentation x face = true)
    (hedge : faceXQEdge baseTannerSquarePresentation face corner = e) :
    {owner : XStarFace baseTannerSquarePresentation x × Two //
      xStarFaceXQEdge baseTannerSquarePresentation x owner.1 owner.2 =
        ⟨Sum.inl e, he⟩} := by
  refine ⟨(⟨face, hface⟩, corner), ?_⟩
  apply Subtype.ext
  exact congrArg Sum.inl hedge

private def baseZOwnerAt (z : baseTannerSquarePresentation.Z)
    (e : QZEdge baseTannerSquarePresentation)
    (he : zStarEdgeMember baseTannerSquarePresentation z (Sum.inr e) = true)
    (face : BaseFace) (corner : Two)
    (hface : zStarFaceMember baseTannerSquarePresentation z face = true)
    (hedge : faceQZEdge baseTannerSquarePresentation face corner = e) :
    {owner : ZStarFace baseTannerSquarePresentation z × Two //
      zStarFaceQZEdge baseTannerSquarePresentation z owner.1 owner.2 =
        ⟨Sum.inr e, he⟩} := by
  refine ⟨(⟨face, hface⟩, corner), ?_⟩
  apply Subtype.ext
  exact congrArg Sum.inr hedge

private abbrev BaseXOwnerResult (x : BaseX)
    (e : XQEdge baseTannerSquarePresentation)
    (he : xStarEdgeMember baseTannerSquarePresentation x (Sum.inl e) = true) :=
  {owner : XStarFace baseTannerSquarePresentation x × Two //
    xStarFaceXQEdge baseTannerSquarePresentation x owner.1 owner.2 =
      ⟨Sum.inl e, he⟩}

private def baseX0RadialFaceOwner (e : XQEdge baseTannerSquarePresentation)
    (he : xStarEdgeMember baseTannerSquarePresentation (0 : BaseX)
      (Sum.inl e) = true) : BaseXOwnerResult 0 e he := by
  rcases e with ⟨⟨edgeX, q⟩, hedge⟩
  change baseTannerSquarePresentation.xq edgeX q = true at hedge
  change xStarEdgeMember baseTannerSquarePresentation (0 : BaseX)
    (Sum.inl ⟨(edgeX, q), hedge⟩) = true at he
  refine finTwoElim (motive := fun edgeX => ∀ (q : BaseQubit)
      (hedge : baseTannerSquarePresentation.xq edgeX q = true)
      (he : xStarEdgeMember baseTannerSquarePresentation (0 : BaseX)
        (Sum.inl ⟨(edgeX, q), hedge⟩) = true),
      BaseXOwnerResult 0 ⟨(edgeX, q), hedge⟩ he) ?_ ?_ edgeX q hedge he
  · intro q hedge he
    refine finFiveElim (motive := fun q => ∀
        (hedge : baseTannerSquarePresentation.xq (0 : BaseX) q = true)
        (he : xStarEdgeMember baseTannerSquarePresentation (0 : BaseX)
          (Sum.inl ⟨((0 : BaseX), q), hedge⟩) = true),
        BaseXOwnerResult 0 ⟨((0 : BaseX), q), hedge⟩ he)
      ?_ ?_ ?_ ?_ ?_ q hedge he
    · intro hedge he; exact baseXOwnerAt (0 : BaseX)
        ⟨((0 : BaseX), (0 : BaseQubit)), hedge⟩ he (0 : BaseFace) (0 : Two)
        (by native_decide) (by apply Subtype.ext; native_decide +revert)
    · intro hedge he; exact baseXOwnerAt (0 : BaseX)
        ⟨((0 : BaseX), (1 : BaseQubit)), hedge⟩ he (1 : BaseFace) (0 : Two)
        (by native_decide) (by apply Subtype.ext; native_decide +revert)
    · intro hedge _; change false = true at hedge; simp at hedge
    · intro hedge _; change false = true at hedge; simp at hedge
    · intro hedge he; exact baseXOwnerAt (0 : BaseX)
        ⟨((0 : BaseX), (4 : BaseQubit)), hedge⟩ he (0 : BaseFace) (1 : Two)
        (by native_decide) (by apply Subtype.ext; native_decide +revert)
  · intro q hedge he
    refine finFiveElim (motive := fun q => ∀
        (hedge : baseTannerSquarePresentation.xq (1 : BaseX) q = true)
        (he : xStarEdgeMember baseTannerSquarePresentation (0 : BaseX)
          (Sum.inl ⟨((1 : BaseX), q), hedge⟩) = true),
        BaseXOwnerResult 0 ⟨((1 : BaseX), q), hedge⟩ he)
      ?_ ?_ ?_ ?_ ?_ q hedge he
    · intro hedge _; change false = true at hedge; simp at hedge
    · intro hedge _; change false = true at hedge; simp at hedge
    · intro _ he; change false = true at he; simp at he
    · intro _ he; change false = true at he; simp at he
    · intro _ he; change false = true at he; simp at he

private def baseX1RadialFaceOwner (e : XQEdge baseTannerSquarePresentation)
    (he : xStarEdgeMember baseTannerSquarePresentation (1 : BaseX)
      (Sum.inl e) = true) : BaseXOwnerResult 1 e he := by
  rcases e with ⟨⟨edgeX, q⟩, hedge⟩
  change baseTannerSquarePresentation.xq edgeX q = true at hedge
  change xStarEdgeMember baseTannerSquarePresentation (1 : BaseX)
    (Sum.inl ⟨(edgeX, q), hedge⟩) = true at he
  refine finTwoElim (motive := fun edgeX => ∀ (q : BaseQubit)
      (hedge : baseTannerSquarePresentation.xq edgeX q = true)
      (he : xStarEdgeMember baseTannerSquarePresentation (1 : BaseX)
        (Sum.inl ⟨(edgeX, q), hedge⟩) = true),
      BaseXOwnerResult 1 ⟨(edgeX, q), hedge⟩ he) ?_ ?_ edgeX q hedge he
  · intro q hedge he
    refine finFiveElim (motive := fun q => ∀
        (hedge : baseTannerSquarePresentation.xq (0 : BaseX) q = true)
        (he : xStarEdgeMember baseTannerSquarePresentation (1 : BaseX)
          (Sum.inl ⟨((0 : BaseX), q), hedge⟩) = true),
        BaseXOwnerResult 1 ⟨((0 : BaseX), q), hedge⟩ he)
      ?_ ?_ ?_ ?_ ?_ q hedge he
    · intro _ he; change false = true at he; simp at he
    · intro _ he; change false = true at he; simp at he
    · intro hedge _; change false = true at hedge; simp at hedge
    · intro hedge _; change false = true at hedge; simp at hedge
    · intro _ he; change false = true at he; simp at he
  · intro q hedge he
    refine finFiveElim (motive := fun q => ∀
        (hedge : baseTannerSquarePresentation.xq (1 : BaseX) q = true)
        (he : xStarEdgeMember baseTannerSquarePresentation (1 : BaseX)
          (Sum.inl ⟨((1 : BaseX), q), hedge⟩) = true),
        BaseXOwnerResult 1 ⟨((1 : BaseX), q), hedge⟩ he)
      ?_ ?_ ?_ ?_ ?_ q hedge he
    · intro hedge _; change false = true at hedge; simp at hedge
    · intro hedge _; change false = true at hedge; simp at hedge
    · intro hedge he; exact baseXOwnerAt (1 : BaseX)
        ⟨((1 : BaseX), (2 : BaseQubit)), hedge⟩ he (2 : BaseFace) (0 : Two)
        (by native_decide) (by apply Subtype.ext; native_decide +revert)
    · intro hedge he; exact baseXOwnerAt (1 : BaseX)
        ⟨((1 : BaseX), (3 : BaseQubit)), hedge⟩ he (3 : BaseFace) (0 : Two)
        (by native_decide) (by apply Subtype.ext; native_decide +revert)
    · intro hedge he; exact baseXOwnerAt (1 : BaseX)
        ⟨((1 : BaseX), (4 : BaseQubit)), hedge⟩ he (2 : BaseFace) (1 : Two)
        (by native_decide) (by apply Subtype.ext; native_decide +revert)

/-- Total explicit base X-radial selector assembled from six face/corner rows. -/
def baseXRadialFaceOwner (x : baseTannerSquarePresentation.X)
    (e : XQEdge baseTannerSquarePresentation)
    (he : xStarEdgeMember baseTannerSquarePresentation x (Sum.inl e) = true) :
    {owner : XStarFace baseTannerSquarePresentation x × Two //
      xStarFaceXQEdge baseTannerSquarePresentation x owner.1 owner.2 =
        ⟨Sum.inl e, he⟩} := by
  exact finTwoElim (motive := fun x => ∀
      (e : XQEdge baseTannerSquarePresentation)
      (he : xStarEdgeMember baseTannerSquarePresentation x (Sum.inl e) = true),
      BaseXOwnerResult x e he)
    baseX0RadialFaceOwner baseX1RadialFaceOwner x e he

private abbrev BaseZOwnerResult (z : BaseZ)
    (e : QZEdge baseTannerSquarePresentation)
    (he : zStarEdgeMember baseTannerSquarePresentation z (Sum.inr e) = true) :=
  {owner : ZStarFace baseTannerSquarePresentation z × Two //
    zStarFaceQZEdge baseTannerSquarePresentation z owner.1 owner.2 =
      ⟨Sum.inr e, he⟩}

private def baseZ0RadialFaceOwner (e : QZEdge baseTannerSquarePresentation)
    (he : zStarEdgeMember baseTannerSquarePresentation (0 : BaseZ)
      (Sum.inr e) = true) : BaseZOwnerResult 0 e he := by
  rcases e with ⟨⟨q, edgeZ⟩, hedge⟩
  change baseTannerSquarePresentation.qz q edgeZ = true at hedge
  change zStarEdgeMember baseTannerSquarePresentation (0 : BaseZ)
    (Sum.inr ⟨(q, edgeZ), hedge⟩) = true at he
  refine finTwoElim (motive := fun edgeZ => ∀ (q : BaseQubit)
      (hedge : baseTannerSquarePresentation.qz q edgeZ = true)
      (he : zStarEdgeMember baseTannerSquarePresentation (0 : BaseZ)
        (Sum.inr ⟨(q, edgeZ), hedge⟩) = true),
      BaseZOwnerResult 0 ⟨(q, edgeZ), hedge⟩ he) ?_ ?_ edgeZ q hedge he
  · intro q hedge he
    refine finFiveElim (motive := fun q => ∀
        (hedge : baseTannerSquarePresentation.qz q (0 : BaseZ) = true)
        (he : zStarEdgeMember baseTannerSquarePresentation (0 : BaseZ)
          (Sum.inr ⟨(q, (0 : BaseZ)), hedge⟩) = true),
        BaseZOwnerResult 0 ⟨(q, (0 : BaseZ)), hedge⟩ he)
      ?_ ?_ ?_ ?_ ?_ q hedge he
    · intro hedge he; exact baseZOwnerAt (0 : BaseZ)
        ⟨((0 : BaseQubit), (0 : BaseZ)), hedge⟩ he (0 : BaseFace) (0 : Two)
        (by native_decide) (by apply Subtype.ext; native_decide +revert)
    · intro hedge _; change false = true at hedge; simp at hedge
    · intro hedge he; exact baseZOwnerAt (0 : BaseZ)
        ⟨((2 : BaseQubit), (0 : BaseZ)), hedge⟩ he (2 : BaseFace) (0 : Two)
        (by native_decide) (by apply Subtype.ext; native_decide +revert)
    · intro hedge _; change false = true at hedge; simp at hedge
    · intro hedge he; exact baseZOwnerAt (0 : BaseZ)
        ⟨((4 : BaseQubit), (0 : BaseZ)), hedge⟩ he (0 : BaseFace) (1 : Two)
        (by native_decide) (by apply Subtype.ext; native_decide +revert)
  · intro q hedge he
    refine finFiveElim (motive := fun q => ∀
        (hedge : baseTannerSquarePresentation.qz q (1 : BaseZ) = true)
        (he : zStarEdgeMember baseTannerSquarePresentation (0 : BaseZ)
          (Sum.inr ⟨(q, (1 : BaseZ)), hedge⟩) = true),
        BaseZOwnerResult 0 ⟨(q, (1 : BaseZ)), hedge⟩ he)
      ?_ ?_ ?_ ?_ ?_ q hedge he
    · intro hedge _; change false = true at hedge; simp at hedge
    · intro _ he; change false = true at he; simp at he
    · intro hedge _; change false = true at hedge; simp at hedge
    · intro _ he; change false = true at he; simp at he
    · intro _ he; change false = true at he; simp at he

private def baseZ1RadialFaceOwner (e : QZEdge baseTannerSquarePresentation)
    (he : zStarEdgeMember baseTannerSquarePresentation (1 : BaseZ)
      (Sum.inr e) = true) : BaseZOwnerResult 1 e he := by
  rcases e with ⟨⟨q, edgeZ⟩, hedge⟩
  change baseTannerSquarePresentation.qz q edgeZ = true at hedge
  change zStarEdgeMember baseTannerSquarePresentation (1 : BaseZ)
    (Sum.inr ⟨(q, edgeZ), hedge⟩) = true at he
  refine finTwoElim (motive := fun edgeZ => ∀ (q : BaseQubit)
      (hedge : baseTannerSquarePresentation.qz q edgeZ = true)
      (he : zStarEdgeMember baseTannerSquarePresentation (1 : BaseZ)
        (Sum.inr ⟨(q, edgeZ), hedge⟩) = true),
      BaseZOwnerResult 1 ⟨(q, edgeZ), hedge⟩ he) ?_ ?_ edgeZ q hedge he
  · intro q hedge he
    refine finFiveElim (motive := fun q => ∀
        (hedge : baseTannerSquarePresentation.qz q (0 : BaseZ) = true)
        (he : zStarEdgeMember baseTannerSquarePresentation (1 : BaseZ)
          (Sum.inr ⟨(q, (0 : BaseZ)), hedge⟩) = true),
        BaseZOwnerResult 1 ⟨(q, (0 : BaseZ)), hedge⟩ he)
      ?_ ?_ ?_ ?_ ?_ q hedge he
    · intro _ he; change false = true at he; simp at he
    · intro hedge _; change false = true at hedge; simp at hedge
    · intro _ he; change false = true at he; simp at he
    · intro hedge _; change false = true at hedge; simp at hedge
    · intro _ he; change false = true at he; simp at he
  · intro q hedge he
    refine finFiveElim (motive := fun q => ∀
        (hedge : baseTannerSquarePresentation.qz q (1 : BaseZ) = true)
        (he : zStarEdgeMember baseTannerSquarePresentation (1 : BaseZ)
          (Sum.inr ⟨(q, (1 : BaseZ)), hedge⟩) = true),
        BaseZOwnerResult 1 ⟨(q, (1 : BaseZ)), hedge⟩ he)
      ?_ ?_ ?_ ?_ ?_ q hedge he
    · intro hedge _; change false = true at hedge; simp at hedge
    · intro hedge he; exact baseZOwnerAt (1 : BaseZ)
        ⟨((1 : BaseQubit), (1 : BaseZ)), hedge⟩ he (1 : BaseFace) (0 : Two)
        (by native_decide) (by apply Subtype.ext; native_decide +revert)
    · intro hedge _; change false = true at hedge; simp at hedge
    · intro hedge he; exact baseZOwnerAt (1 : BaseZ)
        ⟨((3 : BaseQubit), (1 : BaseZ)), hedge⟩ he (3 : BaseFace) (0 : Two)
        (by native_decide) (by apply Subtype.ext; native_decide +revert)
    · intro hedge he; exact baseZOwnerAt (1 : BaseZ)
        ⟨((4 : BaseQubit), (1 : BaseZ)), hedge⟩ he (1 : BaseFace) (1 : Two)
        (by native_decide) (by apply Subtype.ext; native_decide +revert)

/-- Total explicit base Z-radial selector assembled from six face/corner rows. -/
def baseZRadialFaceOwner (z : baseTannerSquarePresentation.Z)
    (e : QZEdge baseTannerSquarePresentation)
    (he : zStarEdgeMember baseTannerSquarePresentation z (Sum.inr e) = true) :
    {owner : ZStarFace baseTannerSquarePresentation z × Two //
      zStarFaceQZEdge baseTannerSquarePresentation z owner.1 owner.2 =
        ⟨Sum.inr e, he⟩} := by
  exact finTwoElim (motive := fun z => ∀
      (e : QZEdge baseTannerSquarePresentation)
      (he : zStarEdgeMember baseTannerSquarePresentation z (Sum.inr e) = true),
      BaseZOwnerResult z e he)
    baseZ0RadialFaceOwner baseZ1RadialFaceOwner z e he

/-- The owner-verified base presentation has total choice-free V3 data. -/
def baseTannerSquareAdmissibleV3 :
    TannerSquareAdmissibleV3 baseTannerSquarePresentation where
  toTannerSquareAdmissibleV2 := baseTannerSquareAdmissibleV2
  xRadialFaceOwner := baseXRadialFaceOwner
  zRadialFaceOwner := baseZRadialFaceOwner

private def baseXBoundaryOwnerAt (x : BaseX)
    (edge : QZEdge baseTannerSquarePresentation)
    (member : xStarEdgeMember baseTannerSquarePresentation x
      (Sum.inr edge) = true)
    (face : BaseFace) (corner : Two)
    (faceMember : xStarFaceMember baseTannerSquarePresentation x face = true)
    (edgeExact : faceQZEdge baseTannerSquarePresentation face corner = edge) :
    {owner : XStarFace baseTannerSquarePresentation x × Two //
      xStarFaceQZEdge baseTannerSquarePresentation x owner.1 owner.2 =
        ⟨Sum.inr edge, member⟩} := by
  refine ⟨(⟨face, faceMember⟩, corner), ?_⟩
  apply Subtype.ext
  exact congrArg Sum.inr edgeExact

private abbrev BaseXBoundaryOwnerResult (x : BaseX)
    (edge : QZEdge baseTannerSquarePresentation)
    (member : xStarEdgeMember baseTannerSquarePresentation x
      (Sum.inr edge) = true) :=
  {owner : XStarFace baseTannerSquarePresentation x × Two //
    xStarFaceQZEdge baseTannerSquarePresentation x owner.1 owner.2 =
      ⟨Sum.inr edge, member⟩}

private def baseX0BoundaryFaceOwner (edge : QZEdge baseTannerSquarePresentation)
    (member : xStarEdgeMember baseTannerSquarePresentation (0 : BaseX)
      (Sum.inr edge) = true) : BaseXBoundaryOwnerResult 0 edge member := by
  rcases edge with ⟨⟨q, z⟩, incidence⟩
  refine finTwoElim (motive := fun z => ∀ (q : BaseQubit)
      (incidence : baseTannerSquarePresentation.qz q z = true)
      (member : xStarEdgeMember baseTannerSquarePresentation (0 : BaseX)
        (Sum.inr ⟨(q, z), incidence⟩) = true),
      BaseXBoundaryOwnerResult 0 ⟨(q, z), incidence⟩ member) ?_ ?_
    z q incidence member
  · intro q incidence member
    refine finFiveElim (motive := fun q => ∀
        (incidence : baseTannerSquarePresentation.qz q (0 : BaseZ) = true)
        (member : xStarEdgeMember baseTannerSquarePresentation (0 : BaseX)
          (Sum.inr ⟨(q, (0 : BaseZ)), incidence⟩) = true),
        BaseXBoundaryOwnerResult 0 ⟨(q, (0 : BaseZ)), incidence⟩ member)
      ?_ ?_ ?_ ?_ ?_ q incidence member
    · intro incidence member; exact baseXBoundaryOwnerAt 0
        ⟨((0 : BaseQubit), (0 : BaseZ)), incidence⟩ member 0 0
        (by native_decide) (by apply Subtype.ext; native_decide +revert)
    · intro incidence _; change false = true at incidence; simp at incidence
    · intro _ member; change false = true at member; simp at member
    · intro incidence _; change false = true at incidence; simp at incidence
    · intro incidence member; exact baseXBoundaryOwnerAt 0
        ⟨((4 : BaseQubit), (0 : BaseZ)), incidence⟩ member 0 1
        (by native_decide) (by apply Subtype.ext; native_decide +revert)
  · intro q incidence member
    refine finFiveElim (motive := fun q => ∀
        (incidence : baseTannerSquarePresentation.qz q (1 : BaseZ) = true)
        (member : xStarEdgeMember baseTannerSquarePresentation (0 : BaseX)
          (Sum.inr ⟨(q, (1 : BaseZ)), incidence⟩) = true),
        BaseXBoundaryOwnerResult 0 ⟨(q, (1 : BaseZ)), incidence⟩ member)
      ?_ ?_ ?_ ?_ ?_ q incidence member
    · intro incidence _; change false = true at incidence; simp at incidence
    · intro incidence member; exact baseXBoundaryOwnerAt 0
        ⟨((1 : BaseQubit), (1 : BaseZ)), incidence⟩ member 1 0
        (by native_decide) (by apply Subtype.ext; native_decide +revert)
    · intro incidence _; change false = true at incidence; simp at incidence
    · intro _ member; change false = true at member; simp at member
    · intro incidence member; exact baseXBoundaryOwnerAt 0
        ⟨((4 : BaseQubit), (1 : BaseZ)), incidence⟩ member 1 1
        (by native_decide) (by apply Subtype.ext; native_decide +revert)

private def baseX1BoundaryFaceOwner (edge : QZEdge baseTannerSquarePresentation)
    (member : xStarEdgeMember baseTannerSquarePresentation (1 : BaseX)
      (Sum.inr edge) = true) : BaseXBoundaryOwnerResult 1 edge member := by
  rcases edge with ⟨⟨q, z⟩, incidence⟩
  refine finTwoElim (motive := fun z => ∀ (q : BaseQubit)
      (incidence : baseTannerSquarePresentation.qz q z = true)
      (member : xStarEdgeMember baseTannerSquarePresentation (1 : BaseX)
        (Sum.inr ⟨(q, z), incidence⟩) = true),
      BaseXBoundaryOwnerResult 1 ⟨(q, z), incidence⟩ member) ?_ ?_
    z q incidence member
  · intro q incidence member
    refine finFiveElim (motive := fun q => ∀
        (incidence : baseTannerSquarePresentation.qz q (0 : BaseZ) = true)
        (member : xStarEdgeMember baseTannerSquarePresentation (1 : BaseX)
          (Sum.inr ⟨(q, (0 : BaseZ)), incidence⟩) = true),
        BaseXBoundaryOwnerResult 1 ⟨(q, (0 : BaseZ)), incidence⟩ member)
      ?_ ?_ ?_ ?_ ?_ q incidence member
    · intro _ member; change false = true at member; simp at member
    · intro incidence _; change false = true at incidence; simp at incidence
    · intro incidence member; exact baseXBoundaryOwnerAt 1
        ⟨((2 : BaseQubit), (0 : BaseZ)), incidence⟩ member 2 0
        (by native_decide) (by apply Subtype.ext; native_decide +revert)
    · intro incidence _; change false = true at incidence; simp at incidence
    · intro incidence member; exact baseXBoundaryOwnerAt 1
        ⟨((4 : BaseQubit), (0 : BaseZ)), incidence⟩ member 2 1
        (by native_decide) (by apply Subtype.ext; native_decide +revert)
  · intro q incidence member
    refine finFiveElim (motive := fun q => ∀
        (incidence : baseTannerSquarePresentation.qz q (1 : BaseZ) = true)
        (member : xStarEdgeMember baseTannerSquarePresentation (1 : BaseX)
          (Sum.inr ⟨(q, (1 : BaseZ)), incidence⟩) = true),
        BaseXBoundaryOwnerResult 1 ⟨(q, (1 : BaseZ)), incidence⟩ member)
      ?_ ?_ ?_ ?_ ?_ q incidence member
    · intro incidence _; change false = true at incidence; simp at incidence
    · intro _ member; change false = true at member; simp at member
    · intro incidence _; change false = true at incidence; simp at incidence
    · intro incidence member; exact baseXBoundaryOwnerAt 1
        ⟨((3 : BaseQubit), (1 : BaseZ)), incidence⟩ member 3 0
        (by native_decide) (by apply Subtype.ext; native_decide +revert)
    · intro incidence member; exact baseXBoundaryOwnerAt 1
        ⟨((4 : BaseQubit), (1 : BaseZ)), incidence⟩ member 3 1
        (by native_decide) (by apply Subtype.ext; native_decide +revert)

/-- Total explicit base X-boundary selector assembled from the frozen eight
face/corner rows. -/
def baseXBoundaryFaceOwner (x : baseTannerSquarePresentation.X)
    (edge : QZEdge baseTannerSquarePresentation)
    (member : xStarEdgeMember baseTannerSquarePresentation x
      (Sum.inr edge) = true) : BaseXBoundaryOwnerResult x edge member :=
  finTwoElim (motive := fun x => ∀ (edge : QZEdge baseTannerSquarePresentation)
      (member : xStarEdgeMember baseTannerSquarePresentation x
        (Sum.inr edge) = true), BaseXBoundaryOwnerResult x edge member)
    baseX0BoundaryFaceOwner baseX1BoundaryFaceOwner x edge member

private def baseZBoundaryOwnerAt (z : BaseZ)
    (edge : XQEdge baseTannerSquarePresentation)
    (member : zStarEdgeMember baseTannerSquarePresentation z
      (Sum.inl edge) = true)
    (face : BaseFace) (corner : Two)
    (faceMember : zStarFaceMember baseTannerSquarePresentation z face = true)
    (edgeExact : faceXQEdge baseTannerSquarePresentation face corner = edge) :
    {owner : ZStarFace baseTannerSquarePresentation z × Two //
      zStarFaceXQEdge baseTannerSquarePresentation z owner.1 owner.2 =
        ⟨Sum.inl edge, member⟩} := by
  refine ⟨(⟨face, faceMember⟩, corner), ?_⟩
  apply Subtype.ext
  exact congrArg Sum.inl edgeExact

private abbrev BaseZBoundaryOwnerResult (z : BaseZ)
    (edge : XQEdge baseTannerSquarePresentation)
    (member : zStarEdgeMember baseTannerSquarePresentation z
      (Sum.inl edge) = true) :=
  {owner : ZStarFace baseTannerSquarePresentation z × Two //
    zStarFaceXQEdge baseTannerSquarePresentation z owner.1 owner.2 =
      ⟨Sum.inl edge, member⟩}

private def baseZ0BoundaryFaceOwner (edge : XQEdge baseTannerSquarePresentation)
    (member : zStarEdgeMember baseTannerSquarePresentation (0 : BaseZ)
      (Sum.inl edge) = true) : BaseZBoundaryOwnerResult 0 edge member := by
  rcases edge with ⟨⟨x, q⟩, incidence⟩
  refine finTwoElim (motive := fun x => ∀ (q : BaseQubit)
      (incidence : baseTannerSquarePresentation.xq x q = true)
      (member : zStarEdgeMember baseTannerSquarePresentation (0 : BaseZ)
        (Sum.inl ⟨(x, q), incidence⟩) = true),
      BaseZBoundaryOwnerResult 0 ⟨(x, q), incidence⟩ member) ?_ ?_
    x q incidence member
  · intro q incidence member
    refine finFiveElim (motive := fun q => ∀
        (incidence : baseTannerSquarePresentation.xq (0 : BaseX) q = true)
        (member : zStarEdgeMember baseTannerSquarePresentation (0 : BaseZ)
          (Sum.inl ⟨((0 : BaseX), q), incidence⟩) = true),
        BaseZBoundaryOwnerResult 0 ⟨((0 : BaseX), q), incidence⟩ member)
      ?_ ?_ ?_ ?_ ?_ q incidence member
    · intro incidence member; exact baseZBoundaryOwnerAt 0
        ⟨((0 : BaseX), (0 : BaseQubit)), incidence⟩ member 0 0
        (by native_decide) (by apply Subtype.ext; native_decide +revert)
    · intro _ member; change false = true at member; simp at member
    · intro incidence _; change false = true at incidence; simp at incidence
    · intro incidence _; change false = true at incidence; simp at incidence
    · intro incidence member; exact baseZBoundaryOwnerAt 0
        ⟨((0 : BaseX), (4 : BaseQubit)), incidence⟩ member 0 1
        (by native_decide) (by apply Subtype.ext; native_decide +revert)
  · intro q incidence member
    refine finFiveElim (motive := fun q => ∀
        (incidence : baseTannerSquarePresentation.xq (1 : BaseX) q = true)
        (member : zStarEdgeMember baseTannerSquarePresentation (0 : BaseZ)
          (Sum.inl ⟨((1 : BaseX), q), incidence⟩) = true),
        BaseZBoundaryOwnerResult 0 ⟨((1 : BaseX), q), incidence⟩ member)
      ?_ ?_ ?_ ?_ ?_ q incidence member
    · intro incidence _; change false = true at incidence; simp at incidence
    · intro incidence _; change false = true at incidence; simp at incidence
    · intro incidence member; exact baseZBoundaryOwnerAt 0
        ⟨((1 : BaseX), (2 : BaseQubit)), incidence⟩ member 2 0
        (by native_decide) (by apply Subtype.ext; native_decide +revert)
    · intro _ member; change false = true at member; simp at member
    · intro incidence member; exact baseZBoundaryOwnerAt 0
        ⟨((1 : BaseX), (4 : BaseQubit)), incidence⟩ member 2 1
        (by native_decide) (by apply Subtype.ext; native_decide +revert)

private def baseZ1BoundaryFaceOwner (edge : XQEdge baseTannerSquarePresentation)
    (member : zStarEdgeMember baseTannerSquarePresentation (1 : BaseZ)
      (Sum.inl edge) = true) : BaseZBoundaryOwnerResult 1 edge member := by
  rcases edge with ⟨⟨x, q⟩, incidence⟩
  refine finTwoElim (motive := fun x => ∀ (q : BaseQubit)
      (incidence : baseTannerSquarePresentation.xq x q = true)
      (member : zStarEdgeMember baseTannerSquarePresentation (1 : BaseZ)
        (Sum.inl ⟨(x, q), incidence⟩) = true),
      BaseZBoundaryOwnerResult 1 ⟨(x, q), incidence⟩ member) ?_ ?_
    x q incidence member
  · intro q incidence member
    refine finFiveElim (motive := fun q => ∀
        (incidence : baseTannerSquarePresentation.xq (0 : BaseX) q = true)
        (member : zStarEdgeMember baseTannerSquarePresentation (1 : BaseZ)
          (Sum.inl ⟨((0 : BaseX), q), incidence⟩) = true),
        BaseZBoundaryOwnerResult 1 ⟨((0 : BaseX), q), incidence⟩ member)
      ?_ ?_ ?_ ?_ ?_ q incidence member
    · intro _ member; change false = true at member; simp at member
    · intro incidence member; exact baseZBoundaryOwnerAt 1
        ⟨((0 : BaseX), (1 : BaseQubit)), incidence⟩ member 1 0
        (by native_decide) (by apply Subtype.ext; native_decide +revert)
    · intro incidence _; change false = true at incidence; simp at incidence
    · intro incidence _; change false = true at incidence; simp at incidence
    · intro incidence member; exact baseZBoundaryOwnerAt 1
        ⟨((0 : BaseX), (4 : BaseQubit)), incidence⟩ member 1 1
        (by native_decide) (by apply Subtype.ext; native_decide +revert)
  · intro q incidence member
    refine finFiveElim (motive := fun q => ∀
        (incidence : baseTannerSquarePresentation.xq (1 : BaseX) q = true)
        (member : zStarEdgeMember baseTannerSquarePresentation (1 : BaseZ)
          (Sum.inl ⟨((1 : BaseX), q), incidence⟩) = true),
        BaseZBoundaryOwnerResult 1 ⟨((1 : BaseX), q), incidence⟩ member)
      ?_ ?_ ?_ ?_ ?_ q incidence member
    · intro incidence _; change false = true at incidence; simp at incidence
    · intro incidence _; change false = true at incidence; simp at incidence
    · intro _ member; change false = true at member; simp at member
    · intro incidence member; exact baseZBoundaryOwnerAt 1
        ⟨((1 : BaseX), (3 : BaseQubit)), incidence⟩ member 3 0
        (by native_decide) (by apply Subtype.ext; native_decide +revert)
    · intro incidence member; exact baseZBoundaryOwnerAt 1
        ⟨((1 : BaseX), (4 : BaseQubit)), incidence⟩ member 3 1
        (by native_decide) (by apply Subtype.ext; native_decide +revert)

/-- Total explicit base Z-boundary selector assembled from the frozen eight
face/corner rows. -/
def baseZBoundaryFaceOwner (z : baseTannerSquarePresentation.Z)
    (edge : XQEdge baseTannerSquarePresentation)
    (member : zStarEdgeMember baseTannerSquarePresentation z
      (Sum.inl edge) = true) : BaseZBoundaryOwnerResult z edge member :=
  finTwoElim (motive := fun z => ∀ (edge : XQEdge baseTannerSquarePresentation)
      (member : zStarEdgeMember baseTannerSquarePresentation z
        (Sum.inl edge) = true), BaseZBoundaryOwnerResult z edge member)
    baseZ0BoundaryFaceOwner baseZ1BoundaryFaceOwner z edge member

/-- The owner-verified base presentation has total choice-free V4 data. -/
def baseTannerSquareAdmissibleV4 :
    TannerSquareAdmissibleV4 baseTannerSquarePresentation where
  toTannerSquareAdmissibleV3 := baseTannerSquareAdmissibleV3
  xBoundaryFaceOwner := baseXBoundaryFaceOwner
  zBoundaryFaceOwner := baseZBoundaryFaceOwner

/-! ## Shared Q-side one-dimensional constructions -/

/-- The Q-side star is the cone on the Q-Z incidences at `q`. -/
abbrev QStarVertex (P : TannerSquarePresentation) (q : P.Q) :=
  Unit ⊕ {z : P.Z // P.qz q z = true}

abbrev QStarEdge (P : TannerSquarePresentation) (q : P.Q) :=
  {z : P.Z // P.qz q z = true}

/-- The Q-side recipe is one-dimensional; it has no two-cells. -/
abbrev QStarFace (_P : TannerSquarePresentation) (_q : _P.Q) := Fin 0

def qStarEdgeStart (P : TannerSquarePresentation) (q : P.Q) :
    QStarEdge P q → QStarVertex P q := fun _ => Sum.inl ()

def qStarEdgeEnd (P : TannerSquarePresentation) (q : P.Q) :
    QStarEdge P q → QStarVertex P q := Sum.inr

/-- Every Q-side star vertex has a one-edge constructive path from the cone point. -/
def qStarPath (P : TannerSquarePresentation) (q : P.Q)
    (vertex : QStarVertex P q) :
    UndirectedPath (qStarEdgeStart P q) (qStarEdgeEnd P q)
      (Sum.inl ()) vertex := by
  rcases vertex with center | endpoint
  · exact .nil
  · exact .step .nil endpoint (Or.inl ⟨rfl, rfl⟩)

noncomputable def qStarBoundary1 (P : TannerSquarePresentation) (q : P.Q) :
    Word Field (QStarEdge P q) →ₗ[Field] Word Field (QStarVertex P q) :=
  graphBoundary (qStarEdgeStart P q) (qStarEdgeEnd P q)

noncomputable def qStarBoundary2 (P : TannerSquarePresentation) (q : P.Q) :
    Word Field (QStarFace P q) →ₗ[Field] Word Field (QStarEdge P q) := 0

theorem qStarBoundary_squared (P : TannerSquarePresentation) (q : P.Q) :
    (qStarBoundary1 P q).comp (qStarBoundary2 P q) = 0 := by
  simp [qStarBoundary2]

/-- Binary parity exactness of the connected Q-side cone. -/
theorem qStarBoundary_range_eq_totalParity_ker
    (P : TannerSquarePresentation) (q : P.Q) :
    LinearMap.range (qStarBoundary1 P q) = LinearMap.ker totalParity :=
  graphBoundary_range_eq_totalParity_ker
    (qStarEdgeStart P q) (qStarEdgeEnd P q) (Sum.inl ()) (qStarPath P q)

/-! The Q-side edge embeddings keep the underlying incidence edge.  The
perfect-pairing surjectivity is eliminated only inside the membership proof;
no face inverse, chosen preimage, or section is defined. -/

/-- Embed a Q-Z incidence into the boundary of the selected X-star. -/
def qToXBoundaryEdge (P : TannerSquarePresentation)
    (q : P.Q) (x : P.X) (hxq : P.xq x q = true)
    (edge : QStarEdge P q) : XStarBoundaryEdge P x :=
  ⟨Sum.inr ⟨(q, edge.1), edge.2⟩, by
    let shared : SharedQ P.data x edge.1 :=
      ⟨q, by simp [hxq, edge.2]⟩
    change decide (∃ face : P.Face,
      xStarFaceMember P x face = true ∧
        decide ((⟨(q, edge.1), edge.2⟩ : QZEdge P) = faceQZEdge P face 0 ∨
          (⟨(q, edge.1), edge.2⟩ : QZEdge P) = faceQZEdge P face 1) = true) = true
    rw [decide_eq_true_eq]
    obtain ⟨corner, hcorner⟩ := (P.perfectPairing x edge.1).2 shared
    have hq : P.faceQ corner.1.1 corner.2 = q :=
      congrArg Subtype.val hcorner
    refine ⟨corner.1.1, ?_, ?_⟩
    · simpa [xStarFaceMember] using corner.1.2.1
    · rw [decide_eq_true_eq]
      have hi : corner.2 = 0 ∨ corner.2 = 1 := two_eq_zero_or_one corner.2
      rcases hi with hi | hi
      · have hq0 : P.faceQ corner.1.1 0 = q := by simpa [hi] using hq
        left
        apply Subtype.ext
        simp [faceQZEdge, hq0, corner.1.2.2]
      · have hq1 : P.faceQ corner.1.1 1 = q := by simpa [hi] using hq
        right
        apply Subtype.ext
        simp [faceQZEdge, hq1, corner.1.2.2]⟩

@[simp] theorem qToXBoundaryEdge_value (P : TannerSquarePresentation)
    (q : P.Q) (x : P.X) (hxq : P.xq x q = true)
    (edge : QStarEdge P q) :
    (qToXBoundaryEdge P q x hxq edge).1 =
      (Sum.inr ⟨(q, edge.1), edge.2⟩ : Edge P) := rfl

/-- The same-edge Q-to-X edge map is injective. -/
theorem qToXBoundaryEdge_injective (P : TannerSquarePresentation)
    (q : P.Q) (x : P.X) (hxq : P.xq x q = true) :
    Function.Injective (qToXBoundaryEdge P q x hxq) := by
  intro first second h
  apply Subtype.ext
  have hvalue := congrArg Subtype.val h
  simp only [qToXBoundaryEdge_value] at hvalue
  injection hvalue with hedge
  exact congrArg (fun edge : QZEdge P => edge.1.2) hedge

/-- One-way Q-to-X embedding of raw boundary edges. -/
def qToXBoundaryEdgeEmbedding (P : TannerSquarePresentation)
    (q : P.Q) (x : P.X) (hxq : P.xq x q = true) :
    QStarEdge P q ↪ XStarBoundaryEdge P x :=
  ⟨qToXBoundaryEdge P q x hxq,
    qToXBoundaryEdge_injective P q x hxq⟩

/-- Embed an X-Q incidence into the boundary of the selected Z-star. -/
def qToZBoundaryEdge (P : TannerSquarePresentation)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true)
    (edge : QStarEdge (transposePresentation P) q) :
    ZStarBoundaryEdge P z :=
  ⟨Sum.inl ⟨(edge.1, q), edge.2⟩, by
    let x : {x : P.X // P.xq x q = true} := ⟨edge.1, edge.2⟩
    let shared : SharedQ P.data x z :=
      ⟨q, by simp [x.2, hqz]⟩
    change decide (∃ face : P.Face,
      zStarFaceMember P z face = true ∧
        decide ((⟨(x.1, q), x.2⟩ : XQEdge P) = faceXQEdge P face 0 ∨
          (⟨(x.1, q), x.2⟩ : XQEdge P) = faceXQEdge P face 1) = true) = true
    rw [decide_eq_true_eq]
    obtain ⟨corner, hcorner⟩ := (P.perfectPairing x z).2 shared
    have hq : P.faceQ corner.1.1 corner.2 = q :=
      congrArg Subtype.val hcorner
    refine ⟨corner.1.1, ?_, ?_⟩
    · simpa [zStarFaceMember] using corner.1.2.2
    · rw [decide_eq_true_eq]
      have hi : corner.2 = 0 ∨ corner.2 = 1 := two_eq_zero_or_one corner.2
      rcases hi with hi | hi
      · have hq0 : P.faceQ corner.1.1 0 = q := by simpa [hi] using hq
        left
        apply Subtype.ext
        simp [faceXQEdge, hq0, corner.1.2.1]
      · have hq1 : P.faceQ corner.1.1 1 = q := by simpa [hi] using hq
        right
        apply Subtype.ext
        simp [faceXQEdge, hq1, corner.1.2.1]⟩

@[simp] theorem qToZBoundaryEdge_value (P : TannerSquarePresentation)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true)
    (edge : QStarEdge (transposePresentation P) q) :
    (qToZBoundaryEdge P q z hqz edge).1 =
      (Sum.inl ⟨(edge.1, q), edge.2⟩ : Edge P) := rfl

/-- The same-edge Q-to-Z edge map is injective. -/
theorem qToZBoundaryEdge_injective (P : TannerSquarePresentation)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) :
    Function.Injective (qToZBoundaryEdge P q z hqz) := by
  intro first second h
  apply Subtype.ext
  have hvalue := congrArg Subtype.val h
  simp only [qToZBoundaryEdge_value] at hvalue
  injection hvalue with hedge
  exact congrArg (fun edge : XQEdge P => edge.1.1) hedge

/-- One-way Q-to-Z embedding of raw boundary edges. -/
def qToZBoundaryEdgeEmbedding (P : TannerSquarePresentation)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) :
    QStarEdge (transposePresentation P) q ↪ ZStarBoundaryEdge P z :=
  ⟨qToZBoundaryEdge P q z hqz,
    qToZBoundaryEdge_injective P q z hqz⟩

/-- Vertex map accompanying the same-edge Q-to-X embedding. -/
def qToXBoundaryVertex (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q)
    (x : P.X) (hxq : P.xq x q = true) :
    QStarVertex P q → XStarBoundaryVertex P x
  | Sum.inl _ =>
      xBoundaryEdgeStart P x
        (qToXBoundaryEdge P q x hxq (A.qzRoot q))
  | Sum.inr edge =>
      xBoundaryEdgeEnd P x (qToXBoundaryEdge P q x hxq edge)

/-- Vertex map accompanying the same-edge Q-to-Z embedding. -/
def qToZBoundaryVertex (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q)
    (z : P.Z) (hqz : P.qz q z = true) :
    QStarVertex (transposePresentation P) q →
      ZStarBoundaryVertex P z
  | Sum.inl _ =>
      zBoundaryEdgeEnd P z
        (qToZBoundaryEdge P q z hqz ⟨(A.xqRoot q).1, (A.xqRoot q).2⟩)
  | Sum.inr edge =>
      zBoundaryEdgeStart P z (qToZBoundaryEdge P q z hqz edge)

@[simp] theorem qToXBoundaryVertex_center_value
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (q : P.Q)
    (x : P.X) (hxq : P.xq x q = true) :
    (qToXBoundaryVertex P A q x hxq (Sum.inl ())).1 = Vertex.q q := by
  rfl

@[simp] theorem qToXBoundaryVertex_endpoint_value
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (q : P.Q)
    (x : P.X) (hxq : P.xq x q = true)
    (edge : QStarEdge P q) :
    (qToXBoundaryVertex P A q x hxq (Sum.inr edge)).1 = Vertex.z edge.1 := by
  rfl

@[simp] theorem qToZBoundaryVertex_center_value
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (q : P.Q)
    (z : P.Z) (hqz : P.qz q z = true) :
    (qToZBoundaryVertex P A q z hqz (Sum.inl ())).1 = Vertex.q q := by
  rfl

@[simp] theorem qToZBoundaryVertex_endpoint_value
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (q : P.Q)
    (z : P.Z) (hqz : P.qz q z = true)
    (edge : QStarEdge (transposePresentation P) q) :
    (qToZBoundaryVertex P A q z hqz (Sum.inr edge)).1 = Vertex.x edge.1 := by
  rfl

/-- The Q-to-X vertex map is injective on its center/endpoint tags. -/
theorem qToXBoundaryVertex_injective
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (q : P.Q)
    (x : P.X) (hxq : P.xq x q = true) :
    Function.Injective (qToXBoundaryVertex P A q x hxq) := by
  intro first second h
  have hvalue := congrArg Subtype.val h
  rcases first with ⟨⟩ | first <;> rcases second with ⟨⟩ | second
  · rfl
  · simp only [qToXBoundaryVertex_endpoint_value] at hvalue
    cases hvalue
  · simp only [qToXBoundaryVertex_endpoint_value] at hvalue
    cases hvalue
  · congr 1
    apply Subtype.ext
    simpa only [qToXBoundaryVertex_endpoint_value] using Vertex.z.inj hvalue

/-- One-way Q-to-X embedding of raw boundary vertices. -/
def qToXBoundaryVertexEmbedding
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (q : P.Q)
    (x : P.X) (hxq : P.xq x q = true) :
    QStarVertex P q ↪ XStarBoundaryVertex P x :=
  ⟨qToXBoundaryVertex P A q x hxq,
    qToXBoundaryVertex_injective P A q x hxq⟩

/-- The transpose-derived Q-to-Z vertex map is injective. -/
theorem qToZBoundaryVertex_injective
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (q : P.Q)
    (z : P.Z) (hqz : P.qz q z = true) :
    Function.Injective (qToZBoundaryVertex P A q z hqz) := by
  intro first second h
  have hvalue := congrArg Subtype.val h
  rcases first with ⟨⟩ | first <;> rcases second with ⟨⟩ | second
  · rfl
  · simp only [qToZBoundaryVertex_endpoint_value] at hvalue
    cases hvalue
  · simp only [qToZBoundaryVertex_endpoint_value] at hvalue
    cases hvalue
  · congr 1
    apply Subtype.ext
    exact Vertex.x.inj hvalue

/-- One-way Q-to-Z embedding of raw boundary vertices. -/
def qToZBoundaryVertexEmbedding
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (q : P.Q)
    (z : P.Z) (hqz : P.qz q z = true) :
    QStarVertex (transposePresentation P) q ↪ ZStarBoundaryVertex P z :=
  ⟨qToZBoundaryVertex P A q z hqz,
    qToZBoundaryVertex_injective P A q z hqz⟩

noncomputable def qStarChainComplex (P : TannerSquarePresentation) (q : P.Q) :
    ChainComplexData Field
      (Word Field (QStarVertex P q))
      (Word Field (QStarEdge P q))
      (Word Field (QStarFace P q)) where
  boundary1 := qStarBoundary1 P q
  boundary2 := qStarBoundary2 P q
  boundary_squared := qStarBoundary_squared P q

/-- Canonical path subdivision of the Q-side cone. -/
abbrev QSubdivisionVertex (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) :=
  QStarVertex P q ⊕ (QStarEdge P q × Fin (S.half - 1))

abbrev QSubdivisionEdge (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) := QStarEdge P q × Fin S.half

abbrev QSubdivisionFace (_P : TannerSquarePresentation) (_q : _P.Q)
    (_S : OddScale) := Fin 0

/-- Same-edge embedding of the Q-side subdivision into an X-star boundary. -/
def qToXSubdivisionBoundaryEdge
    (P : TannerSquarePresentation) (q : P.Q)
    (x : P.X) (hxq : P.xq x q = true)
    (S : OddScale) (edge : QSubdivisionEdge P q S) :
    SubdivisionBoundaryEdge P x S :=
  subdivisionOriginalBoundaryEdge P x S
    (qToXBoundaryEdge P q x hxq edge.1) edge.2

/-- The transpose route gives the matching Q-to-Z subdivision embedding. -/
noncomputable def qToZSubdivisionBoundaryEdge
    (P : TannerSquarePresentation) (q : P.Q)
    (z : P.Z) (hqz : P.qz q z = true) (S : OddScale)
    (edge : QSubdivisionEdge (transposePresentation P) q S) :
    ZSubdivisionBoundaryEdge P z S :=
  subdivisionOriginalBoundaryEdge (transposePresentation P) z S
    ((transposeXStarBoundaryEdgeEquiv P z).symm
      (qToZBoundaryEdge P q z hqz edge.1)) edge.2

/-- Vertex embedding into the tagged X-star subdivision. -/
def qToXSubdivisionVertex
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (x : P.X) (hxq : P.xq x q = true) (S : OddScale) :
    QSubdivisionVertex P q S → SubdivisionVertex P x S
  | Sum.inl vertex =>
      Sum.inl (xStarBoundaryVertexToStar P x
        (qToXBoundaryVertex P A q x hxq vertex))
  | Sum.inr edgeInterior =>
      Sum.inr (Sum.inl
        (xStarBoundaryEdgeToStar P x
          (qToXBoundaryEdge P q x hxq edgeInterior.1), edgeInterior.2))

/-- Vertex embedding into the tagged Z-star subdivision via transpose. -/
noncomputable def qToZSubdivisionVertex
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale) :
    QSubdivisionVertex (transposePresentation P) q S →
      ZSubdivisionVertex P z S
  | Sum.inl vertex =>
      Sum.inl (xStarBoundaryVertexToStar (transposePresentation P) z
        ((transposeXStarBoundaryVertexEquiv P z).symm
          (qToZBoundaryVertex P A q z hqz vertex)))
  | Sum.inr edgeInterior =>
      Sum.inr (Sum.inl
        (xStarBoundaryEdgeToStar (transposePresentation P) z
          ((transposeXStarBoundaryEdgeEquiv P z).symm
            (qToZBoundaryEdge P q z hqz edgeInterior.1)), edgeInterior.2))

/-- The tagged Q-to-X subdivision edge map is injective. -/
theorem qToXSubdivisionBoundaryEdge_injective
    (P : TannerSquarePresentation) (q : P.Q)
    (x : P.X) (hxq : P.xq x q = true) (S : OddScale) :
    Function.Injective (qToXSubdivisionBoundaryEdge P q x hxq S) := by
  rintro ⟨first, firstIndex⟩ ⟨second, secondIndex⟩ h
  have hvalue := congrArg Subtype.val h
  change Sum.inl
      (xStarBoundaryEdgeToStar P x (qToXBoundaryEdge P q x hxq first),
        firstIndex) =
    Sum.inl
      (xStarBoundaryEdgeToStar P x (qToXBoundaryEdge P q x hxq second),
        secondIndex) at hvalue
  injection hvalue with hpair
  injection hpair with hedge hindex
  apply Prod.ext
  · apply qToXBoundaryEdge_injective P q x hxq
    apply Subtype.ext
    exact congrArg (fun edge : XStarEdge P x => edge.1) hedge
  · exact hindex

/-- One-way embedding of Q-side subdivision edges into an X boundary. -/
def qToXSubdivisionBoundaryEdgeEmbedding
    (P : TannerSquarePresentation) (q : P.Q)
    (x : P.X) (hxq : P.xq x q = true) (S : OddScale) :
    QSubdivisionEdge P q S ↪ SubdivisionBoundaryEdge P x S :=
  ⟨qToXSubdivisionBoundaryEdge P q x hxq S,
    qToXSubdivisionBoundaryEdge_injective P q x hxq S⟩

/-- The transpose-derived Q-to-Z subdivision edge map is injective. -/
theorem qToZSubdivisionBoundaryEdge_injective
    (P : TannerSquarePresentation) (q : P.Q)
    (z : P.Z) (hqz : P.qz q z = true) (S : OddScale) :
    Function.Injective (qToZSubdivisionBoundaryEdge P q z hqz S) := by
  rintro ⟨first, firstIndex⟩ ⟨second, secondIndex⟩ h
  have hvalue := congrArg Subtype.val h
  change Sum.inl
      (xStarBoundaryEdgeToStar (transposePresentation P) z
        ((transposeXStarBoundaryEdgeEquiv P z).symm
          (qToZBoundaryEdge P q z hqz first)), firstIndex) =
    Sum.inl
      (xStarBoundaryEdgeToStar (transposePresentation P) z
        ((transposeXStarBoundaryEdgeEquiv P z).symm
          (qToZBoundaryEdge P q z hqz second)), secondIndex) at hvalue
  injection hvalue with hpair
  injection hpair with hedge hindex
  apply Prod.ext
  · apply qToZBoundaryEdge_injective P q z hqz
    apply (transposeXStarBoundaryEdgeEquiv P z).symm.injective
    apply Subtype.ext
    exact congrArg
      (fun edge : XStarEdge (transposePresentation P) z => edge.1) hedge
  · exact hindex

/-- One-way embedding of transpose Q-side subdivision edges into a Z boundary. -/
noncomputable def qToZSubdivisionBoundaryEdgeEmbedding
    (P : TannerSquarePresentation) (q : P.Q)
    (z : P.Z) (hqz : P.qz q z = true) (S : OddScale) :
    QSubdivisionEdge (transposePresentation P) q S ↪
      ZSubdivisionBoundaryEdge P z S :=
  ⟨qToZSubdivisionBoundaryEdge P q z hqz S,
    qToZSubdivisionBoundaryEdge_injective P q z hqz S⟩

/-- The tagged Q-to-X subdivision vertex map is injective. -/
theorem qToXSubdivisionVertex_injective
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (x : P.X) (hxq : P.xq x q = true) (S : OddScale) :
    Function.Injective (qToXSubdivisionVertex P A q x hxq S) := by
  intro first second h
  rcases first with first | first <;> rcases second with second | second
  · apply congrArg Sum.inl
    apply qToXBoundaryVertex_injective P A q x hxq
    apply Subtype.ext
    have hstar :
        xStarBoundaryVertexToStar P x
            (qToXBoundaryVertex P A q x hxq first) =
          xStarBoundaryVertexToStar P x
            (qToXBoundaryVertex P A q x hxq second) := Sum.inl.inj h
    exact congrArg (fun vertex : XStarVertex P x => vertex.1) hstar
  · cases h
  · cases h
  · apply congrArg Sum.inr
    rcases first with ⟨first, firstIndex⟩
    rcases second with ⟨second, secondIndex⟩
    have hpair := Sum.inl.inj (Sum.inr.inj h)
    injection hpair with hedge hindex
    apply Prod.ext
    · apply qToXBoundaryEdge_injective P q x hxq
      apply Subtype.ext
      exact congrArg (fun edge : XStarEdge P x => edge.1) hedge
    · exact hindex

/-- One-way embedding of Q-side subdivision vertices into an X subdivision. -/
def qToXSubdivisionVertexEmbedding
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (x : P.X) (hxq : P.xq x q = true) (S : OddScale) :
    QSubdivisionVertex P q S ↪ SubdivisionVertex P x S :=
  ⟨qToXSubdivisionVertex P A q x hxq S,
    qToXSubdivisionVertex_injective P A q x hxq S⟩

/-- The transpose-derived Q-to-Z subdivision vertex map is injective. -/
theorem qToZSubdivisionVertex_injective
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale) :
    Function.Injective (qToZSubdivisionVertex P A q z hqz S) := by
  intro first second h
  rcases first with first | first <;> rcases second with second | second
  · apply congrArg Sum.inl
    apply qToZBoundaryVertex_injective P A q z hqz
    apply (transposeXStarBoundaryVertexEquiv P z).symm.injective
    apply Subtype.ext
    have hstar :
        xStarBoundaryVertexToStar (transposePresentation P) z
            ((transposeXStarBoundaryVertexEquiv P z).symm
              (qToZBoundaryVertex P A q z hqz first)) =
          xStarBoundaryVertexToStar (transposePresentation P) z
            ((transposeXStarBoundaryVertexEquiv P z).symm
              (qToZBoundaryVertex P A q z hqz second)) := Sum.inl.inj h
    exact congrArg
      (fun vertex : XStarVertex (transposePresentation P) z => vertex.1) hstar
  · cases h
  · cases h
  · apply congrArg Sum.inr
    rcases first with ⟨first, firstIndex⟩
    rcases second with ⟨second, secondIndex⟩
    have hpair := Sum.inl.inj (Sum.inr.inj h)
    injection hpair with hedge hindex
    apply Prod.ext
    · apply qToZBoundaryEdge_injective P q z hqz
      apply (transposeXStarBoundaryEdgeEquiv P z).symm.injective
      apply Subtype.ext
      exact congrArg
        (fun edge : XStarEdge (transposePresentation P) z => edge.1) hedge
    · exact hindex

/-- One-way embedding of transpose Q-side vertices into a Z subdivision. -/
noncomputable def qToZSubdivisionVertexEmbedding
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale) :
    QSubdivisionVertex (transposePresentation P) q S ↪
      ZSubdivisionVertex P z S :=
  ⟨qToZSubdivisionVertex P A q z hqz S,
    qToZSubdivisionVertex_injective P A q z hqz S⟩

def qSubdivisionEdgeStart (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (edge : QSubdivisionEdge P q S) :
    QSubdivisionVertex P q S :=
  if h : edge.2.1 = 0 then
    Sum.inl (qStarEdgeStart P q edge.1)
  else
    Sum.inr (edge.1, ⟨edge.2.1 - 1, by have := edge.2.2; omega⟩)

def qSubdivisionEdgeEnd (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (edge : QSubdivisionEdge P q S) :
    QSubdivisionVertex P q S :=
  if h : edge.2.1 + 1 = S.half then
    Sum.inl (qStarEdgeEnd P q edge.1)
  else
    Sum.inr (edge.1, ⟨edge.2.1, by have := edge.2.2; omega⟩)

theorem qToXSubdivisionEdge_start
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (x : P.X) (hxq : P.xq x q = true)
    (S : OddScale) (edge : QSubdivisionEdge P q S) :
    qToXSubdivisionVertex P A q x hxq S (qSubdivisionEdgeStart P q S edge) =
      subdivisionEdgeStart P x S
        (qToXSubdivisionBoundaryEdge P q x hxq S edge).1 := by
  rcases edge with ⟨edge, index⟩
  by_cases hindex : index.1 = 0
  · simp [qSubdivisionEdgeStart, qToXSubdivisionVertex,
      qToXSubdivisionBoundaryEdge, subdivisionOriginalBoundaryEdge,
      subdivisionEdgeStart, subdivisionSegmentStart, hindex,
      qToXBoundaryVertex]
    apply Subtype.ext
    rfl
  · simp [qSubdivisionEdgeStart, qToXSubdivisionVertex,
      qToXSubdivisionBoundaryEdge, subdivisionOriginalBoundaryEdge,
      subdivisionEdgeStart, subdivisionSegmentStart, hindex]

theorem qToXSubdivisionEdge_end
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (x : P.X) (hxq : P.xq x q = true)
    (S : OddScale) (edge : QSubdivisionEdge P q S) :
    qToXSubdivisionVertex P A q x hxq S (qSubdivisionEdgeEnd P q S edge) =
      subdivisionEdgeEnd P x S
        (qToXSubdivisionBoundaryEdge P q x hxq S edge).1 := by
  rcases edge with ⟨edge, index⟩
  by_cases hindex : index.1 + 1 = S.half
  · simp [qSubdivisionEdgeEnd, qToXSubdivisionVertex,
      qToXSubdivisionBoundaryEdge, subdivisionOriginalBoundaryEdge,
      subdivisionEdgeEnd, subdivisionSegmentEnd, hindex,
      qToXBoundaryVertex]
    apply Subtype.ext
    rfl
  · simp [qSubdivisionEdgeEnd, qToXSubdivisionVertex,
      qToXSubdivisionBoundaryEdge, subdivisionOriginalBoundaryEdge,
      subdivisionEdgeEnd, subdivisionSegmentEnd, hindex]

theorem qToZSubdivisionEdge_start
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale)
    (edge : QSubdivisionEdge (transposePresentation P) q S) :
    qToZSubdivisionVertex P A q z hqz S
        (qSubdivisionEdgeStart (transposePresentation P) q S edge) =
      subdivisionEdgeStart (transposePresentation P) z S
        (qToZSubdivisionBoundaryEdge P q z hqz S edge).1 := by
  rcases edge with ⟨edge, index⟩
  by_cases hindex : index.1 = 0
  · simp [qSubdivisionEdgeStart, qToZSubdivisionVertex,
      qToZSubdivisionBoundaryEdge, subdivisionOriginalBoundaryEdge,
      subdivisionEdgeStart, subdivisionSegmentStart, hindex,
      qToZBoundaryVertex]
    apply Subtype.ext
    rfl
  · simp [qSubdivisionEdgeStart, qToZSubdivisionVertex,
      qToZSubdivisionBoundaryEdge, subdivisionOriginalBoundaryEdge,
      subdivisionEdgeStart, subdivisionSegmentStart, hindex]

theorem qToZSubdivisionEdge_end
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale)
    (edge : QSubdivisionEdge (transposePresentation P) q S) :
    qToZSubdivisionVertex P A q z hqz S
        (qSubdivisionEdgeEnd (transposePresentation P) q S edge) =
      subdivisionEdgeEnd (transposePresentation P) z S
        (qToZSubdivisionBoundaryEdge P q z hqz S edge).1 := by
  rcases edge with ⟨edge, index⟩
  by_cases hindex : index.1 + 1 = S.half
  · simp [qSubdivisionEdgeEnd, qToZSubdivisionVertex,
      qToZSubdivisionBoundaryEdge, subdivisionOriginalBoundaryEdge,
      subdivisionEdgeEnd, subdivisionSegmentEnd, hindex,
      qToZBoundaryVertex]
    apply Subtype.ext
    rfl
  · simp [qSubdivisionEdgeEnd, qToZSubdivisionVertex,
      qToZSubdivisionBoundaryEdge, subdivisionOriginalBoundaryEdge,
      subdivisionEdgeEnd, subdivisionSegmentEnd, hindex]

/-- Vertex after traversing `step` segments of one subdivided Q-side edge. -/
private def qSubdivisionSegmentVertex
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (edge : QStarEdge P q) (step : Nat) (hstep : step ≤ S.half) :
    QSubdivisionVertex P q S :=
  if hzero : step = 0 then
    Sum.inl (qStarEdgeStart P q edge)
  else if hlast : step = S.half then
    Sum.inl (qStarEdgeEnd P q edge)
  else
    Sum.inr (edge, ⟨step - 1, by omega⟩)

/-- Traverse an explicit prefix of one subdivided Q-side edge. -/
private noncomputable def qSubdivisionSegmentPath
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (edge : QStarEdge P q) :
    (step : Nat) → (hstep : step ≤ S.half) →
      UndirectedPath (qSubdivisionEdgeStart P q S)
        (qSubdivisionEdgeEnd P q S) (Sum.inl (Sum.inl ()))
        (qSubdivisionSegmentVertex P q S edge step hstep)
  | 0, _ => .nil
  | step + 1, hstep => by
      have hindex : step < S.half := by omega
      let index : Fin S.half := ⟨step, hindex⟩
      apply UndirectedPath.step
        (qSubdivisionSegmentPath P q S edge step (by omega)) (edge, index)
      exact Or.inl ⟨by
        have hnotlast : step ≠ S.half := by omega
        simp [qSubdivisionSegmentVertex, qSubdivisionEdgeStart, index,
          hnotlast], by
        simp [qSubdivisionSegmentVertex, qSubdivisionEdgeEnd, index]⟩

/-- Every subdivided Q-side vertex has an explicit path from the cone point. -/
noncomputable def qSubdivisionPath
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (vertex : QSubdivisionVertex P q S) :
    UndirectedPath (qSubdivisionEdgeStart P q S)
      (qSubdivisionEdgeEnd P q S) (Sum.inl (Sum.inl ())) vertex := by
  rcases vertex with vertex | interior
  · rcases vertex with ⟨⟩ | edge
    · exact .nil
    · simpa [qSubdivisionSegmentVertex, qStarEdgeEnd, S.half_pos.ne'] using
        qSubdivisionSegmentPath P q S edge S.half (le_refl S.half)
  · rcases interior with ⟨edge, index⟩
    have hstep : index.1 + 1 ≤ S.half := by
      have := index.2
      have hhalf := S.half_pos
      omega
    have hzero : index.1 + 1 ≠ 0 := by omega
    have hlast : index.1 + 1 ≠ S.half := by
      have := index.2
      omega
    simpa [qSubdivisionSegmentVertex, hzero, hlast] using
      qSubdivisionSegmentPath P q S edge (index.1 + 1) hstep

noncomputable def qSubdivisionBoundary1 (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) :
    Word Field (QSubdivisionEdge P q S) →ₗ[Field]
      Word Field (QSubdivisionVertex P q S) :=
  graphBoundary (qSubdivisionEdgeStart P q S) (qSubdivisionEdgeEnd P q S)

/-- Binary parity exactness for the explicitly connected Q subdivision. -/
theorem qSubdivisionBoundary_range_eq_totalParity_ker
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale) :
    LinearMap.range (qSubdivisionBoundary1 P q S) =
      LinearMap.ker totalParity :=
  graphBoundary_range_eq_totalParity_ker
    (qSubdivisionEdgeStart P q S) (qSubdivisionEdgeEnd P q S)
    (Sum.inl (Sum.inl ())) (qSubdivisionPath P q S)

noncomputable def qSubdivisionBoundary2 (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) :
    Word Field (QSubdivisionFace P q S) →ₗ[Field]
      Word Field (QSubdivisionEdge P q S) := 0

theorem qSubdivisionBoundary_squared (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) :
    (qSubdivisionBoundary1 P q S).comp (qSubdivisionBoundary2 P q S) = 0 := by
  simp [qSubdivisionBoundary2]

noncomputable def qSubdivisionChainComplex (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) :
    ChainComplexData Field
      (Word Field (QSubdivisionVertex P q S))
      (Word Field (QSubdivisionEdge P q S))
      (Word Field (QSubdivisionFace P q S)) where
  boundary1 := qSubdivisionBoundary1 P q S
  boundary2 := qSubdivisionBoundary2 P q S
  boundary_squared := qSubdivisionBoundary_squared P q S

/-- Two copies of the subdivided Q-side cone. -/
abbrev QDoubleCylinderVertex (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) := Two × QSubdivisionVertex P q S

/-- End-copy edges plus one vertical edge at every Q-Z endpoint. -/
abbrev QDoubleCylinderEdge (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) :=
  (Two × QSubdivisionEdge P q S) ⊕ QStarEdge P q

/-- This one-dimensional cylinder normal form has no two-cells. -/
abbrev QDoubleCylinderFace (_P : TannerSquarePresentation) (_q : _P.Q)
    (_S : OddScale) := Fin 0

/-- Explicit endpoints whose incidence is the #871 Tanner cylinder matrix. -/
def tannerDoubleCylinderEdgeStart
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    DoubleCylinderEdge P x S → DoubleCylinderVertex P x S
  | Sum.inl edge => (edge.1, subdivisionEdgeStart P x S edge.2)
  | Sum.inr vertex => (0, vertex.1)

def tannerDoubleCylinderEdgeEnd
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    DoubleCylinderEdge P x S → DoubleCylinderVertex P x S
  | Sum.inl edge => (edge.1, subdivisionEdgeEnd P x S edge.2)
  | Sum.inr vertex => (1, vertex.1)

def qDoubleCylinderEdgeStart (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) : QDoubleCylinderEdge P q S → QDoubleCylinderVertex P q S
  | Sum.inl edge => (edge.1, qSubdivisionEdgeStart P q S edge.2)
  | Sum.inr endpoint => (0, Sum.inl (qStarEdgeEnd P q endpoint))

def qDoubleCylinderEdgeEnd (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) : QDoubleCylinderEdge P q S → QDoubleCylinderVertex P q S
  | Sum.inl edge => (edge.1, qSubdivisionEdgeEnd P q S edge.2)
  | Sum.inr endpoint => (1, Sum.inl (qStarEdgeEnd P q endpoint))

/-- Lift a Q-subdivision path to one tagged cylinder end. -/
noncomputable def qSubdivisionPathAtCopy
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale) (copy : Two)
    (vertex : QSubdivisionVertex P q S) :
    UndirectedPath (qDoubleCylinderEdgeStart P q S)
      (qDoubleCylinderEdgeEnd P q S) (copy, Sum.inl (Sum.inl ()))
      (copy, vertex) :=
  UndirectedPath.map
    (edgeStart := qSubdivisionEdgeStart P q S)
    (edgeEnd := qSubdivisionEdgeEnd P q S)
    (edgeStart' := qDoubleCylinderEdgeStart P q S)
    (edgeEnd' := qDoubleCylinderEdgeEnd P q S)
    (fun subdivisionVertex => (copy, subdivisionVertex))
    (fun subdivisionEdge => Sum.inl (copy, subdivisionEdge))
    (fun _ => rfl) (fun _ => rfl) (qSubdivisionPath P q S vertex)

/-- The selected Q-Z root supplies an actual two-copy vertical bridge. -/
def qDoubleCylinderVerticalBridge
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (S : OddScale) :
    UndirectedPath (qDoubleCylinderEdgeStart P q S)
      (qDoubleCylinderEdgeEnd P q S)
      (0, Sum.inl (qStarEdgeEnd P q (A.qzRoot q)))
      (1, Sum.inl (qStarEdgeEnd P q (A.qzRoot q))) :=
  .step .nil (Sum.inr (A.qzRoot q)) (Or.inl ⟨rfl, rfl⟩)

/-- Every double-cylinder vertex has an explicit path from end-zero's cone
point.  The only inter-copy step is the admissibility record's Q-Z root edge. -/
noncomputable def qDoubleCylinderPath
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (S : OddScale) (vertex : QDoubleCylinderVertex P q S) :
    UndirectedPath (qDoubleCylinderEdgeStart P q S)
      (qDoubleCylinderEdgeEnd P q S) (0, Sum.inl (Sum.inl ())) vertex := by
  rcases vertex with ⟨copy, vertex⟩
  refine finTwoElim (motive := fun copy =>
      UndirectedPath (qDoubleCylinderEdgeStart P q S)
        (qDoubleCylinderEdgeEnd P q S) (0, Sum.inl (Sum.inl ()))
        (copy, vertex)) ?_ ?_ copy
  · exact qSubdivisionPathAtCopy P q S 0 vertex
  · let bridge : QSubdivisionVertex P q S :=
        Sum.inl (qStarEdgeEnd P q (A.qzRoot q))
    exact ((qSubdivisionPathAtCopy P q S 0 bridge).append
      ((qDoubleCylinderVerticalBridge P A q S).append
        ((qSubdivisionPathAtCopy P q S 1 bridge).reverse.append
          (qSubdivisionPathAtCopy P q S 1 vertex))))

/-- Preserve the end-copy tag and the tagged subdivision vertex. -/
def qToXDoubleCylinderVertex
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (x : P.X) (hxq : P.xq x q = true) (S : OddScale) :
    QDoubleCylinderVertex P q S →
      DoubleCylinderVertex P x S := fun vertex =>
  (vertex.1, qToXSubdivisionVertex P A q x hxq S vertex.2)

/-- Preserve copy/vertical tags in the one-way Q-to-X cell embedding. -/
def qToXDoubleCylinderEdge
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (x : P.X) (hxq : P.xq x q = true) (S : OddScale) :
    QDoubleCylinderEdge P q S → DoubleCylinderEdge P x S
  | Sum.inl edge =>
      Sum.inl (edge.1, (qToXSubdivisionBoundaryEdge P q x hxq S edge.2).1)
  | Sum.inr endpoint =>
      Sum.inr (subdivisionOriginalBoundaryVertex P x S
        (qToXBoundaryVertex P A q x hxq (Sum.inr endpoint)))

/-- Preserve the end-copy tag along the transpose-derived Q-to-Z route. -/
noncomputable def qToZDoubleCylinderVertex
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale) :
    QDoubleCylinderVertex (transposePresentation P) q S →
      ZDoubleCylinderVertex P z S := fun vertex =>
  (vertex.1, qToZSubdivisionVertex P A q z hqz S vertex.2)

/-- Preserve copy/vertical tags in the one-way Q-to-Z cell embedding. -/
noncomputable def qToZDoubleCylinderEdge
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale) :
    QDoubleCylinderEdge (transposePresentation P) q S →
      ZDoubleCylinderEdge P z S
  | Sum.inl edge =>
      Sum.inl (edge.1, (qToZSubdivisionBoundaryEdge P q z hqz S edge.2).1)
  | Sum.inr endpoint =>
      Sum.inr (subdivisionOriginalBoundaryVertex (transposePresentation P)
        z S
        ((transposeXStarBoundaryVertexEquiv P z).symm
          (qToZBoundaryVertex P A q z hqz (Sum.inr endpoint))))

/-- The Q-to-X double-cylinder vertex map preserves both tags injectively. -/
theorem qToXDoubleCylinderVertex_injective
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (x : P.X) (hxq : P.xq x q = true) (S : OddScale) :
    Function.Injective (qToXDoubleCylinderVertex P A q x hxq S) := by
  rintro ⟨firstCopy, first⟩ ⟨secondCopy, second⟩ h
  apply Prod.ext
  · exact congrArg (fun vertex : DoubleCylinderVertex P x S => vertex.1) h
  · apply qToXSubdivisionVertex_injective P A q x hxq S
    exact congrArg Prod.snd h

/-- One-way embedding of Q-side cylinder vertices into the X cylinder. -/
def qToXDoubleCylinderVertexEmbedding
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (x : P.X) (hxq : P.xq x q = true) (S : OddScale) :
    QDoubleCylinderVertex P q S ↪ DoubleCylinderVertex P x S :=
  ⟨qToXDoubleCylinderVertex P A q x hxq S,
    qToXDoubleCylinderVertex_injective P A q x hxq S⟩

/-- The transpose-derived Q-to-Z cylinder vertex map is injective. -/
theorem qToZDoubleCylinderVertex_injective
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale) :
    Function.Injective (qToZDoubleCylinderVertex P A q z hqz S) := by
  rintro ⟨firstCopy, first⟩ ⟨secondCopy, second⟩ h
  apply Prod.ext
  · exact congrArg (fun vertex : ZDoubleCylinderVertex P z S => vertex.1) h
  · apply qToZSubdivisionVertex_injective P A q z hqz S
    exact congrArg Prod.snd h

/-- One-way embedding of transpose Q-side vertices into the Z cylinder. -/
noncomputable def qToZDoubleCylinderVertexEmbedding
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale) :
    QDoubleCylinderVertex (transposePresentation P) q S ↪
      ZDoubleCylinderVertex P z S :=
  ⟨qToZDoubleCylinderVertex P A q z hqz S,
    qToZDoubleCylinderVertex_injective P A q z hqz S⟩

/-- The copy/vertical tagged Q-to-X cylinder edge map is injective. -/
theorem qToXDoubleCylinderEdge_injective
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (x : P.X) (hxq : P.xq x q = true) (S : OddScale) :
    Function.Injective (qToXDoubleCylinderEdge P A q x hxq S) := by
  intro first second h
  rcases first with first | first <;> rcases second with second | second
  · apply congrArg Sum.inl
    rcases first with ⟨firstCopy, first⟩
    rcases second with ⟨secondCopy, second⟩
    have hpair := Sum.inl.inj h
    apply Prod.ext
    · exact congrArg
        (fun edge : Two × SubdivisionEdge P x S => edge.1) hpair
    · apply qToXSubdivisionBoundaryEdge_injective P q x hxq S
      apply Subtype.ext
      exact congrArg Prod.snd hpair
  · cases h
  · cases h
  · apply congrArg Sum.inr
    apply Sum.inr.inj
    apply qToXBoundaryVertex_injective P A q x hxq
    have hboundary := Sum.inr.inj h
    have hsubdivision := congrArg Subtype.val hboundary
    have hstar := Sum.inl.inj hsubdivision
    apply Subtype.ext
    exact congrArg (fun vertex : XStarVertex P x => vertex.1) hstar

/-- One-way embedding of Q-side cylinder edges into the X cylinder. -/
def qToXDoubleCylinderEdgeEmbedding
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (x : P.X) (hxq : P.xq x q = true) (S : OddScale) :
    QDoubleCylinderEdge P q S ↪ DoubleCylinderEdge P x S :=
  ⟨qToXDoubleCylinderEdge P A q x hxq S,
    qToXDoubleCylinderEdge_injective P A q x hxq S⟩

/-- The copy/vertical tagged Q-to-Z cylinder edge map is injective. -/
theorem qToZDoubleCylinderEdge_injective
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale) :
    Function.Injective (qToZDoubleCylinderEdge P A q z hqz S) := by
  intro first second h
  rcases first with first | first <;> rcases second with second | second
  · apply congrArg Sum.inl
    rcases first with ⟨firstCopy, first⟩
    rcases second with ⟨secondCopy, second⟩
    have hpair := Sum.inl.inj h
    apply Prod.ext
    · exact congrArg
        (fun edge : Two × SubdivisionEdge (transposePresentation P) z S => edge.1)
        hpair
    · apply qToZSubdivisionBoundaryEdge_injective P q z hqz S
      apply Subtype.ext
      exact congrArg Prod.snd hpair
  · cases h
  · cases h
  · apply congrArg Sum.inr
    apply Sum.inr.inj
    apply qToZBoundaryVertex_injective P A q z hqz
    have hboundary := Sum.inr.inj h
    have hsubdivision := congrArg Subtype.val hboundary
    have hstar := Sum.inl.inj hsubdivision
    apply (transposeXStarBoundaryVertexEquiv P z).symm.injective
    apply Subtype.ext
    exact congrArg
      (fun vertex : XStarVertex (transposePresentation P) z => vertex.1) hstar

/-- One-way embedding of transpose Q-side cylinder edges into the Z cylinder. -/
noncomputable def qToZDoubleCylinderEdgeEmbedding
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale) :
    QDoubleCylinderEdge (transposePresentation P) q S ↪
      ZDoubleCylinderEdge P z S :=
  ⟨qToZDoubleCylinderEdge P A q z hqz S,
    qToZDoubleCylinderEdge_injective P A q z hqz S⟩

/-- The Q-to-X cylinder cell embedding commutes with start endpoints. -/
theorem qToXDoubleCylinderEdge_start
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (x : P.X) (hxq : P.xq x q = true)
    (S : OddScale) (edge : QDoubleCylinderEdge P q S) :
    qToXDoubleCylinderVertex P A q x hxq S
        (qDoubleCylinderEdgeStart P q S edge) =
      tannerDoubleCylinderEdgeStart P x S
        (qToXDoubleCylinderEdge P A q x hxq S edge) := by
  rcases edge with edge | endpoint
  · rcases edge with ⟨copy, edge⟩
    simp [qDoubleCylinderEdgeStart, qToXDoubleCylinderVertex,
      qToXDoubleCylinderEdge, tannerDoubleCylinderEdgeStart,
      qToXSubdivisionEdge_start]
  · rfl

/-- The Q-to-X cylinder cell embedding commutes with end endpoints. -/
theorem qToXDoubleCylinderEdge_end
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (x : P.X) (hxq : P.xq x q = true)
    (S : OddScale) (edge : QDoubleCylinderEdge P q S) :
    qToXDoubleCylinderVertex P A q x hxq S
        (qDoubleCylinderEdgeEnd P q S edge) =
      tannerDoubleCylinderEdgeEnd P x S
        (qToXDoubleCylinderEdge P A q x hxq S edge) := by
  rcases edge with edge | endpoint
  · rcases edge with ⟨copy, edge⟩
    simp [qDoubleCylinderEdgeEnd, qToXDoubleCylinderVertex,
      qToXDoubleCylinderEdge, tannerDoubleCylinderEdgeEnd,
      qToXSubdivisionEdge_end]
  · rfl

/-- The transpose-derived Q-to-Z embedding commutes with start endpoints. -/
theorem qToZDoubleCylinderEdge_start
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale)
    (edge : QDoubleCylinderEdge (transposePresentation P) q S) :
    qToZDoubleCylinderVertex P A q z hqz S
        (qDoubleCylinderEdgeStart (transposePresentation P) q S edge) =
      tannerDoubleCylinderEdgeStart (transposePresentation P) z S
        (qToZDoubleCylinderEdge P A q z hqz S edge) := by
  rcases edge with edge | endpoint
  · rcases edge with ⟨copy, edge⟩
    simp [qDoubleCylinderEdgeStart, qToZDoubleCylinderVertex,
      qToZDoubleCylinderEdge, tannerDoubleCylinderEdgeStart,
      qToZSubdivisionEdge_start]
  · rfl

/-- The transpose-derived Q-to-Z embedding commutes with end endpoints. -/
theorem qToZDoubleCylinderEdge_end
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale)
    (edge : QDoubleCylinderEdge (transposePresentation P) q S) :
    qToZDoubleCylinderVertex P A q z hqz S
        (qDoubleCylinderEdgeEnd (transposePresentation P) q S edge) =
      tannerDoubleCylinderEdgeEnd (transposePresentation P) z S
        (qToZDoubleCylinderEdge P A q z hqz S edge) := by
  rcases edge with edge | endpoint
  · rcases edge with ⟨copy, edge⟩
    simp [qDoubleCylinderEdgeEnd, qToZDoubleCylinderVertex,
      qToZDoubleCylinderEdge, tannerDoubleCylinderEdgeEnd,
      qToZSubdivisionEdge_end]
  · rfl

noncomputable def qDoubleCylinderBoundary1
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale) :
    Word Field (QDoubleCylinderEdge P q S) →ₗ[Field]
      Word Field (QDoubleCylinderVertex P q S) :=
  graphBoundary (qDoubleCylinderEdgeStart P q S)
    (qDoubleCylinderEdgeEnd P q S)

/-- Binary parity exactness for the connected Q-side double cylinder. -/
theorem qDoubleCylinderBoundary_range_eq_totalParity_ker
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (S : OddScale) :
    LinearMap.range (qDoubleCylinderBoundary1 P q S) =
      LinearMap.ker totalParity :=
  graphBoundary_range_eq_totalParity_ker
    (qDoubleCylinderEdgeStart P q S) (qDoubleCylinderEdgeEnd P q S)
    (0, Sum.inl (Sum.inl ())) (qDoubleCylinderPath P A q S)

/-- The transpose route uses the original admissibility record's X-Q root as
its vertical bridge and inherits the same explicit parity exactness. -/
theorem qTransposeDoubleCylinderBoundary_range_eq_totalParity_ker
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (S : OddScale) :
    LinearMap.range
        (qDoubleCylinderBoundary1 (transposePresentation P) q S) =
      LinearMap.ker totalParity :=
  qDoubleCylinderBoundary_range_eq_totalParity_ker
    (transposePresentation P) (transposeTannerSquareAdmissible P A) q S

noncomputable def qDoubleCylinderBoundary2
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale) :
    Word Field (QDoubleCylinderFace P q S) →ₗ[Field]
      Word Field (QDoubleCylinderEdge P q S) := 0

theorem qDoubleCylinderBoundary_squared
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale) :
    (qDoubleCylinderBoundary1 P q S).comp
      (qDoubleCylinderBoundary2 P q S) = 0 := by
  simp [qDoubleCylinderBoundary2]

noncomputable def qDoubleCylinderChainComplex
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale) :
    ChainComplexData Field
      (Word Field (QDoubleCylinderVertex P q S))
      (Word Field (QDoubleCylinderEdge P q S))
      (Word Field (QDoubleCylinderFace P q S)) where
  boundary1 := qDoubleCylinderBoundary1 P q S
  boundary2 := qDoubleCylinderBoundary2 P q S
  boundary_squared := qDoubleCylinderBoundary_squared P q S

/-- One-way coordinate restriction to either end copy. -/
def qDoubleCylinderEndRestriction
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale) (endIndex : Two) :
    Word Field (QDoubleCylinderVertex P q S) →ₗ[Field]
      Word Field (QSubdivisionVertex P q S) where
  toFun := fun word vertex => word (endIndex, vertex)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp] theorem qDoubleCylinderEndRestriction_apply
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale) (endIndex : Two)
    (word : Word Field (QDoubleCylinderVertex P q S))
    (vertex : QSubdivisionVertex P q S) :
    qDoubleCylinderEndRestriction P q S endIndex word vertex =
      word (endIndex, vertex) := rfl

@[simp] theorem baseQ0StarVertex_card :
    Fintype.card (QStarVertex baseTannerSquarePresentation (0 : BaseQubit)) = 2 := by
  native_decide

@[simp] theorem baseQ0StarEdge_card :
    Fintype.card (QStarEdge baseTannerSquarePresentation (0 : BaseQubit)) = 1 := by
  native_decide

@[simp] theorem baseQ4StarVertex_card :
    Fintype.card (QStarVertex baseTannerSquarePresentation (4 : BaseQubit)) = 3 := by
  native_decide

@[simp] theorem baseQ4StarEdge_card :
    Fintype.card (QStarEdge baseTannerSquarePresentation (4 : BaseQubit)) = 2 := by
  native_decide

@[simp] theorem baseQ0SubdivisionVertex_card :
    Fintype.card (QSubdivisionVertex baseTannerSquarePresentation
      (0 : BaseQubit) scaleFive) = 3 := by
  native_decide

@[simp] theorem baseQ0SubdivisionEdge_card :
    Fintype.card (QSubdivisionEdge baseTannerSquarePresentation
      (0 : BaseQubit) scaleFive) = 2 := by
  native_decide

@[simp] theorem baseQ4SubdivisionVertex_card :
    Fintype.card (QSubdivisionVertex baseTannerSquarePresentation
      (4 : BaseQubit) scaleFive) = 5 := by
  native_decide

@[simp] theorem baseQ4SubdivisionEdge_card :
    Fintype.card (QSubdivisionEdge baseTannerSquarePresentation
      (4 : BaseQubit) scaleFive) = 4 := by
  native_decide

@[simp] theorem baseQ0DoubleCylinderVertex_card :
    Fintype.card (QDoubleCylinderVertex baseTannerSquarePresentation
      (0 : BaseQubit) scaleFive) = 6 := by
  native_decide

@[simp] theorem baseQ0DoubleCylinderEdge_card :
    Fintype.card (QDoubleCylinderEdge baseTannerSquarePresentation
      (0 : BaseQubit) scaleFive) = 5 := by
  native_decide

@[simp] theorem baseQ4DoubleCylinderVertex_card :
    Fintype.card (QDoubleCylinderVertex baseTannerSquarePresentation
      (4 : BaseQubit) scaleFive) = 10 := by
  native_decide

@[simp] theorem baseQ4DoubleCylinderEdge_card :
    Fintype.card (QDoubleCylinderEdge baseTannerSquarePresentation
      (4 : BaseQubit) scaleFive) = 10 := by
  native_decide

/-- The one-way obligation owned by each concrete RX/RZ replacement branch. -/
abbrev PreservesTannerSquareAdmissibility
    (replacement : TannerSquarePresentation → TannerSquarePresentation) :=
  ∀ P, TannerSquareAdmissible P → TannerSquareAdmissible (replacement P)

end BDL26TannerLocalRegularity
end Coding
end QEC
