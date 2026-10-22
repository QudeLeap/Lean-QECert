import QEC.Coding.ExpanderCodes.TannerGlobalExpansion

/-!
# Labelled vertical edges in the PK22 Tanner product

This module formalizes the vertical-edge graph used in PK22's
`lemma:lbl-edge`.  Its vertices are physical vertical edges and its weighted
edges are incident faces, with parallel local directions retained as
multiplicity.
-/

namespace QEC.Coding.TannerLiftedProduct

universe u v

variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']

/-- The endpoint with prescribed second double-cover side of a physical
vertical edge. -/
def verticalEdgeEndpoint (label : W → G) (e : VerticalEdgeIndex W G)
    (endpointSide : Fin 2) : VertexIndex G :=
  match e with
  | (side, b, g) =>
      (side, endpointSide, doubleCoverVoltage label endpointSide b * g)

omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W]
    [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R'] in
@[simp] theorem verticalEdgeAtVertex_verticalEdgeEndpoint
    (label : W → G) (e : VerticalEdgeIndex W G)
    (endpointSide : Fin 2) :
    verticalEdgeAtVertex label (verticalEdgeEndpoint label e endpointSide)
      e.2.1 = e := by
  rcases e with ⟨side, b, g⟩
  simp [verticalEdgeAtVertex, verticalEdgeEndpoint]

omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W]
    [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R'] in
@[simp] theorem verticalEdgeAtVertex_direction
    (label : W → G) (v : VertexIndex G) (b : W) :
    (verticalEdgeAtVertex label v b).2.1 = b := by
  rcases v with ⟨side, side', g⟩
  rfl

omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W]
    [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R'] in
@[simp] theorem verticalNeighbor_verticalNeighbor
    (label : W → G) (v : VertexIndex G) (b : W) :
    verticalNeighbor label (verticalNeighbor label v b) b = v := by
  rcases v with ⟨side, side', g⟩
  simp [verticalNeighbor, mul_assoc]

omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W]
    [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R'] in
/-- Horizontal and vertical moves commute around every Tanner square. -/
theorem verticalNeighbor_horizontalNeighbor_commute
    (label : W → G) (v : VertexIndex G) (a b : W) :
    verticalNeighbor label (horizontalNeighbor label v a) b =
      horizontalNeighbor label (verticalNeighbor label v b) a := by
  rcases v with ⟨side, side', g⟩
  simp [verticalNeighbor, horizontalNeighbor, mul_assoc]

/-- The physical vertical edge across the face in horizontal direction `a`.
The distinguished endpoint side is fixed only to choose a canonical
representative; the resulting physical edge is the opposite vertical side
of that face. -/
def verticalFaceNeighbor (label : W → G) (e : VerticalEdgeIndex W G)
    (a : W) : VerticalEdgeIndex W G :=
  verticalEdgeAtVertex label
    (horizontalNeighbor label (verticalEdgeEndpoint label e 0) a) e.2.1

/-- The active face between a physical vertical edge and its face-neighbour
in horizontal direction `a`. -/
def faceAtVerticalEdge (label : W → G) (e : VerticalEdgeIndex W G)
    (a : W) : FaceIndex W G :=
  faceAtVertex label (verticalEdgeEndpoint label e 0) a e.2.1

omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W]
    [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R'] in
@[simp] theorem verticalEdgeEndpoint_verticalFaceNeighbor_zero
    (label : W → G) (e : VerticalEdgeIndex W G) (a : W) :
    verticalEdgeEndpoint label (verticalFaceNeighbor label e a) 0 =
      horizontalNeighbor label (verticalEdgeEndpoint label e 0) a := by
  rcases e with ⟨side, b, g⟩
  simp [verticalFaceNeighbor, verticalEdgeEndpoint, verticalEdgeAtVertex,
    horizontalNeighbor, mul_assoc]

omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W]
    [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R'] in
@[simp] theorem verticalFaceNeighbor_direction
    (label : W → G) (e : VerticalEdgeIndex W G) (a : W) :
    (verticalFaceNeighbor label e a).2.1 = e.2.1 := by
  rcases e with ⟨side, b, g⟩
  rfl

omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W]
    [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R'] in
@[simp] theorem verticalNeighbor_verticalFaceNeighbor_endpoint
    (label : W → G) (e : VerticalEdgeIndex W G) (a : W) :
    verticalNeighbor label
        (verticalEdgeEndpoint label (verticalFaceNeighbor label e a) 0)
        (verticalFaceNeighbor label e a).2.1 =
      horizontalNeighbor label
        (verticalNeighbor label (verticalEdgeEndpoint label e 0) e.2.1) a := by
  rw [verticalEdgeEndpoint_verticalFaceNeighbor_zero,
    verticalFaceNeighbor_direction,
    verticalNeighbor_horizontalNeighbor_commute]

omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W]
    [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R'] in
@[simp] theorem faceAtVerticalEdge_verticalFaceNeighbor
    (label : W → G) (e : VerticalEdgeIndex W G) (a : W) :
    faceAtVerticalEdge label (verticalFaceNeighbor label e a) a =
      faceAtVerticalEdge label e a := by
  simp [faceAtVerticalEdge]

/-- The graph whose vertices are physical vertical edges and whose edges are
faces.  It is the source graph `𝒱_E`, represented as a weighted multigraph. -/
def verticalFaceGraph (label : W → G) :
    SmallSetExpansion.WeightedGraph (VerticalEdgeIndex W G) :=
  fun e e' =>
    (Finset.univ.filter fun a : W => verticalFaceNeighbor label e a = e').card

/-- One of the two physical vertical edges incident to a global face. -/
def verticalEdgeOfFace (label : W → G) (p : FaceIndex W G)
    (side : Fin 2) : VerticalEdgeIndex W G :=
  match p with
  | (a, b, g) => (side, b, g * doubleCoverVoltage label side a)

/-- The unique vertex with prescribed two double-cover sides incident to a
given face. -/
def vertexAtFaceSides (label : W → G) (p : FaceIndex W G)
    (side side' : Fin 2) : VertexIndex G :=
  match p with
  | (a, b, g) =>
      (side, side', doubleCoverVoltage label side' b * g *
        doubleCoverVoltage label side a)

omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] [DecidableEq W]
    [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R'] in
/-- Face incidence determines the vertex once its two side bits are known. -/
theorem vertexAtFaceSides_eq_of_mem_faceStar
    (label : W → G) (v : VertexIndex G) (p : FaceIndex W G)
    (hp : p ∈ faceStar label v) :
    vertexAtFaceSides label p v.1 v.2.1 = v := by
  obtain ⟨a, b, rfl⟩ := (mem_faceStar_iff label v _).mp hp
  rcases v with ⟨side, side', g⟩
  simp [vertexAtFaceSides, faceAtVertex, mul_assoc]

omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W]
    [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R'] in
@[simp] theorem verticalEdgeOfFace_faceAtVerticalEdge
    (label : W → G) (e : VerticalEdgeIndex W G) (a : W) :
    verticalEdgeOfFace label (faceAtVerticalEdge label e a) e.1 = e := by
  rcases e with ⟨side, b, g⟩
  fin_cases side <;>
    simp [verticalEdgeOfFace, faceAtVerticalEdge, faceAtVertex,
      verticalEdgeEndpoint, doubleCoverVoltage, mul_assoc]

omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W]
    [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R'] in
@[simp] theorem verticalEdgeAtVertex_verticalNeighbor
    (label : W → G) (v : VertexIndex G) (b : W) :
    verticalEdgeAtVertex label (verticalNeighbor label v b) b =
      verticalEdgeAtVertex label v b := by
  rcases v with ⟨side, side', g⟩
  simp [verticalEdgeAtVertex, verticalNeighbor, mul_assoc]

omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
/-- Outgoing face multiplicity into a physical-edge set counts exactly the
local horizontal directions whose opposite vertical edge lies in that set. -/
theorem sum_verticalFaceGraph_eq_card_filter
    (label : W → G) (A : Finset (VerticalEdgeIndex W G))
    (e : VerticalEdgeIndex W G) :
    ∑ e' ∈ A, verticalFaceGraph label e e' =
      (Finset.univ.filter fun a : W =>
        verticalFaceNeighbor label e a ∈ A).card := by
  classical
  have hFiber := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset W) A (verticalFaceNeighbor label e)
  simpa [verticalFaceGraph] using hFiber

/-- A physical vertical edge carries at least one active face. -/
def CarriesActiveFaceVerticalEdge (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (e : VerticalEdgeIndex W G) : Prop :=
  ∃ a, localFaceMatrix label c (verticalEdgeEndpoint label e 0) e.2.1 a ≠ 0

/-- A physical vertical edge is active when it has an active endpoint vertex
or carries an active face. -/
def IsActiveVerticalEdge (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (e : VerticalEdgeIndex W G) : Prop :=
  verticalEdgeEndpoint label e 0 ∈ vertexBlockSupport c ∨
    verticalNeighbor label (verticalEdgeEndpoint label e 0) e.2.1 ∈
      vertexBlockSupport c ∨
    CarriesActiveFaceVerticalEdge label c e

/-- Source-exact face-active predicate on physical vertical edges. -/
def IsFaceActiveVerticalEdge (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (e : VerticalEdgeIndex W G) : Prop :=
  IsFaceActiveVerticalEdgeAt label c
    (verticalEdgeEndpoint label e 0) e.2.1

/-- The finite set of active physical vertical edges. -/
noncomputable def activeVerticalEdges (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) :
    Finset (VerticalEdgeIndex W G) := by
  classical
  exact Finset.univ.filter (IsActiveVerticalEdge label c)

/-- Physical vertical edges incident to an active vertex block. -/
noncomputable def activeVertexIncidentVerticalEdges (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) :
    Finset (VerticalEdgeIndex W G) := by
  classical
  exact (vertexBlockSupport c ×ˢ (Finset.univ : Finset W)).image fun p =>
    verticalEdgeAtVertex label p.1 p.2

/-- Physical vertical edges incident to an active face scalar. -/
noncomputable def activeFaceIncidentVerticalEdges (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) :
    Finset (VerticalEdgeIndex W G) := by
  classical
  exact (faceSupport c ×ˢ (Finset.univ : Finset (Fin 2))).image fun p =>
    verticalEdgeOfFace label p.1 p.2

omit [Fintype F] [DecidableEq R] [DecidableEq R'] in
/-- Every active physical vertical edge is covered by an active endpoint
vertex or one of the two vertical sides of an active face. -/
theorem activeVerticalEdges_subset_incident_union
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) :
    activeVerticalEdges label c ⊆
      activeVertexIncidentVerticalEdges label c ∪
        activeFaceIncidentVerticalEdges label c := by
  classical
  intro e he
  have heActive : IsActiveVerticalEdge label c e := by
    simpa [activeVerticalEdges] using he
  rcases heActive with hSource | hTarget | ⟨a, ha⟩
  · apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨(verticalEdgeEndpoint label e 0, e.2.1), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨hSource, Finset.mem_univ _⟩
    · exact verticalEdgeAtVertex_verticalEdgeEndpoint label e 0
  · apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨(verticalNeighbor label (verticalEdgeEndpoint label e 0) e.2.1,
      e.2.1), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨hTarget, Finset.mem_univ _⟩
    · rw [verticalEdgeAtVertex_verticalNeighbor,
        verticalEdgeAtVertex_verticalEdgeEndpoint]
  · apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨(faceAtVerticalEdge label e a, e.1), ?_, ?_⟩
    · apply Finset.mem_product.mpr
      refine ⟨?_, Finset.mem_univ _⟩
      simpa [faceSupport, faceAtVerticalEdge, localFaceMatrix] using ha
    · exact verticalEdgeOfFace_faceAtVerticalEdge label e a

omit [Fintype F] [DecidableEq R] [DecidableEq R'] in
/-- Active-edge cardinality before folding it into block weight. -/
theorem card_activeVerticalEdges_le
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) :
    (activeVerticalEdges label c).card ≤
      (vertexBlockSupport c).card * Fintype.card W +
        (faceSupport c).card * 2 := by
  classical
  have hVertexCard :
      (activeVertexIncidentVerticalEdges label c).card ≤
        (vertexBlockSupport c).card * Fintype.card W := by
    calc
      (activeVertexIncidentVerticalEdges label c).card ≤
          (vertexBlockSupport c ×ˢ (Finset.univ : Finset W)).card := by
        exact Finset.card_image_le
      _ = (vertexBlockSupport c).card * Fintype.card W := by simp
  have hFaceCard :
      (activeFaceIncidentVerticalEdges label c).card ≤
        (faceSupport c).card * 2 := by
    calc
      (activeFaceIncidentVerticalEdges label c).card ≤
          (faceSupport c ×ˢ (Finset.univ : Finset (Fin 2))).card := by
        exact Finset.card_image_le
      _ = (faceSupport c).card * 2 := by simp
  calc
    (activeVerticalEdges label c).card ≤
        (activeVertexIncidentVerticalEdges label c ∪
          activeFaceIncidentVerticalEdges label c).card :=
      Finset.card_le_card (activeVerticalEdges_subset_incident_union label c)
    _ ≤ (activeVertexIncidentVerticalEdges label c).card +
        (activeFaceIncidentVerticalEdges label c).card :=
      Finset.card_union_le _ _
    _ ≤ (vertexBlockSupport c).card * Fintype.card W +
        (faceSupport c).card * 2 := Nat.add_le_add hVertexCard hFaceCard

omit [Fintype F] [DecidableEq R] [DecidableEq R'] in
/-- For local degree at least two, the number of active vertical edges is at
most `w` times the PK22 block weight. -/
theorem card_activeVerticalEdges_le_card_mul_blockWeight
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hTwo : 2 ≤ Fintype.card W) :
    (activeVerticalEdges label c).card ≤ Fintype.card W * blockWeight c := by
  have hCard := card_activeVerticalEdges_le label c
  unfold blockWeight
  calc
    (activeVerticalEdges label c).card ≤
        (vertexBlockSupport c).card * Fintype.card W +
          (faceSupport c).card * 2 := hCard
    _ ≤ (vertexBlockSupport c).card * Fintype.card W +
          (faceSupport c).card * Fintype.card W :=
      Nat.add_le_add_left
        (Nat.mul_le_mul_left (faceSupport c).card hTwo) _
    _ = Fintype.card W *
          ((faceSupport c).card + (vertexBlockSupport c).card) := by
      simp [Nat.mul_add, Nat.mul_comm, Nat.add_comm]

omit [Fintype F] [DecidableEq W] [DecidableEq R] [DecidableEq R'] in
/-- A non-active member of the least labelled closure must have entered via
the face-active-edge closure rule, not merely satisfy its degree conclusion. -/
theorem labelledVertices_nonactive_incident
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (m : Nat) (v : VertexIndex G)
    (hv : v ∈ labelledVertices label c m)
    (hvInactive : v ∉ vertexBlockSupport c) :
    IsIncidentToFaceActiveVerticalEdge label c v := by
  by_contra hvIncident
  let L := labelledVertices label c m
  have hClosed := labelledVertices_isClosed label c m
  have hEraseClosed : IsClosedLabelledSet label c m (L.erase v) := by
    constructor
    · intro u hu
      exact Finset.mem_erase.mpr ⟨by
        intro huv
        subst u
        exact hvInactive hu, hClosed.1 hu⟩
    · intro u huIncident huDegree
      have huDegreeL : m ≤ ∑ x ∈ L, adjacencyGraph label u x :=
        huDegree.trans (Finset.sum_le_sum_of_subset (Finset.erase_subset v L))
      have huL : u ∈ L := hClosed.2 u huIncident huDegreeL
      have huv : u ≠ v := by
        intro huv
        subst u
        exact hvIncident huIncident
      exact Finset.mem_erase.mpr ⟨huv, huL⟩
  have hvErase : v ∈ L.erase v :=
    (mem_labelledVertices_iff label c m v).mp hv (L.erase v) hEraseClosed
  simp at hvErase

/-- Incidences between a selected vertex set and active faces. -/
noncomputable def activeFaceIncidences (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (L : Finset (VertexIndex G)) :
    Finset (VertexIndex G × FaceIndex W G) := by
  classical
  exact (L ×ˢ faceSupport c).filter fun vp => vp.2 ∈ faceStar label vp.1

omit [Fintype F] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
/-- An active face has at most four incident product vertices, one for each
pair of double-cover side bits. -/
theorem card_activeFaceIncidences_le_four_mul
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (L : Finset (VertexIndex G)) :
    (activeFaceIncidences label c L).card ≤ 4 * (faceSupport c).card := by
  classical
  let T := faceSupport c ×ˢ (Finset.univ : Finset (Fin 2 × Fin 2))
  let project : VertexIndex G × FaceIndex W G →
      FaceIndex W G × (Fin 2 × Fin 2) := fun vp =>
    (vp.2, (vp.1.1, vp.1.2.1))
  have hMap : Set.MapsTo project (activeFaceIncidences label c L) T := by
    intro vp hvp
    have hvpData := Finset.mem_filter.mp hvp
    exact Finset.mem_product.mpr
      ⟨(Finset.mem_product.mp hvpData.1).2, Finset.mem_univ _⟩
  have hInj : (activeFaceIncidences label c L : Set _).InjOn project := by
    rintro ⟨v, p⟩ hvp ⟨v', p'⟩ hvp' heq
    have hp : p = p' := congrArg Prod.fst heq
    have hsides : (v.1, v.2.1) = (v'.1, v'.2.1) :=
      congrArg Prod.snd heq
    subst p'
    have hvFace : p ∈ faceStar label v := (Finset.mem_filter.mp hvp).2
    have hvFace' : p ∈ faceStar label v' := (Finset.mem_filter.mp hvp').2
    have hv := vertexAtFaceSides_eq_of_mem_faceStar label v p hvFace
    have hv' := vertexAtFaceSides_eq_of_mem_faceStar label v' p hvFace'
    have hside : v.1 = v'.1 :=
      congrArg (fun x : Fin 2 × Fin 2 => x.1) hsides
    have hside' : v.2.1 = v'.2.1 :=
      congrArg (fun x : Fin 2 × Fin 2 => x.2) hsides
    have hvEq : v = v' := by
      rw [← hv, ← hv', hside, hside']
    subst v'
    rfl
  calc
    (activeFaceIncidences label c L).card ≤ T.card :=
      Finset.card_le_card_of_injOn project hMap hInj
    _ = 4 * (faceSupport c).card := by
      simp [T, Nat.mul_comm]

/-- Non-active vertices in the canonical labelled closure. -/
noncomputable def nonactiveLabelledVertices (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (m : Nat) : Finset (VertexIndex G) :=
  labelledVertices label c m \ vertexBlockSupport c

/-- Choose one face-active vertical direction incident to each non-active
canonical labelled vertex. -/
noncomputable def selectedFaceActiveDirection (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (m : Nat)
    (v : {v // v ∈ nonactiveLabelledVertices label c m}) : W := by
  classical
  have hvData := Finset.mem_sdiff.mp v.2
  have hvIncident := labelledVertices_nonactive_incident
    label c m v.1 hvData.1 hvData.2
  exact Classical.choose hvIncident

omit [Fintype F] [DecidableEq W] [DecidableEq R] [DecidableEq R'] in
theorem selectedFaceActiveDirection_spec (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (m : Nat)
    (v : {v // v ∈ nonactiveLabelledVertices label c m}) :
    IsFaceActiveVerticalEdgeAt label c v.1
      (selectedFaceActiveDirection label c m v) := by
  classical
  have hvData := Finset.mem_sdiff.mp v.2
  have hvIncident := labelledVertices_nonactive_incident
    label c m v.1 hvData.1 hvData.2
  exact Classical.choose_spec hvIncident

/-- Active face-direction incidences on the selected face-active edge at
each non-active labelled vertex. -/
noncomputable def selectedFaceDirectionIncidences (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (m : Nat) :
    Finset ({v // v ∈ nonactiveLabelledVertices label c m} × W) := by
  classical
  exact Finset.univ.filter fun va =>
    localFaceMatrix label c va.1.1
      (selectedFaceActiveDirection label c m va.1) va.2 ≠ 0

omit [Fintype F] [DecidableEq R] [DecidableEq R'] in
/-- Selected direction incidences inject into the global active-face
incidence set. -/
theorem card_selectedFaceDirectionIncidences_le_activeFaceIncidences
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (m : Nat) :
    (selectedFaceDirectionIncidences label c m).card ≤
      (activeFaceIncidences label c (labelledVertices label c m)).card := by
  classical
  let project :
      {v // v ∈ nonactiveLabelledVertices label c m} × W →
        VertexIndex G × FaceIndex W G := fun va =>
    (va.1.1, faceAtVertex label va.1.1 va.2
      (selectedFaceActiveDirection label c m va.1))
  have hMap : Set.MapsTo project
      (selectedFaceDirectionIncidences label c m)
      (activeFaceIncidences label c (labelledVertices label c m)) := by
    intro va hva
    have hvaNonzero : localFaceMatrix label c va.1.1
        (selectedFaceActiveDirection label c m va.1) va.2 ≠ 0 :=
      (Finset.mem_filter.mp hva).2
    have hvLabelled := (Finset.mem_sdiff.mp va.1.2).1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hvLabelled, ?_⟩, ?_⟩
    · simpa [faceSupport, localFaceMatrix] using hvaNonzero
    · exact (mem_faceStar_iff label va.1.1 _).2
        ⟨va.2, selectedFaceActiveDirection label c m va.1, rfl⟩
  have hInj : (selectedFaceDirectionIncidences label c m : Set _).InjOn
      project := by
    rintro ⟨v, a⟩ hva ⟨v', a'⟩ hva' heq
    have hv : v.1 = v'.1 := congrArg (fun z => z.1) heq
    have hvSubtype : v = v' := Subtype.ext hv
    subst v'
    have hface : faceAtVertex label v.1 a
        (selectedFaceActiveDirection label c m v) =
      faceAtVertex label v.1 a'
        (selectedFaceActiveDirection label c m v) :=
      congrArg (fun z => z.2) heq
    have ha : a = a' := congrArg (fun p : FaceIndex W G => p.1) hface
    subst a'
    rfl
  exact Finset.card_le_card_of_injOn project hMap hInj

omit [Fintype F] [DecidableEq R] [DecidableEq R'] in
/-- Every nonzero face direction at `e` leads to an active opposite vertical
edge, so face-row weight is bounded by degree into the active-edge set. -/
theorem localFaceRow_weight_le_activeVerticalEdge_degree
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (e : VerticalEdgeIndex W G) :
    HammingWeight
        (ProductExpansion.row
          (localFaceMatrix label c (verticalEdgeEndpoint label e 0)) e.2.1) ≤
      ∑ e' ∈ activeVerticalEdges label c, verticalFaceGraph label e e' := by
  classical
  rw [sum_verticalFaceGraph_eq_card_filter]
  rw [HammingWeight_eq_card_hammingSupport]
  apply Finset.card_le_card
  intro a ha
  have haNonzero :
      localFaceMatrix label c (verticalEdgeEndpoint label e 0) e.2.1 a ≠ 0 := by
    simpa [ProductExpansion.row] using (Finset.mem_filter.mp ha).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ a, ?_⟩
  rw [activeVerticalEdges, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  exact Or.inr (Or.inr ⟨a, by
    simpa [localFaceMatrix] using haNonzero⟩)

/-- Active physical vertical edges with neither endpoint in `L`. -/
noncomputable def unlabelledActiveVerticalEdges (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (L : Finset (VertexIndex G)) : Finset (VerticalEdgeIndex W G) := by
  classical
  exact (activeVerticalEdges label c).filter fun e =>
    verticalEdgeEndpoint label e 0 ∉ L ∧
      verticalNeighbor label (verticalEdgeEndpoint label e 0) e.2.1 ∉ L

omit [Fintype F] [DecidableEq W] [DecidableEq R] [DecidableEq R'] in
theorem unlabelledActiveVerticalEdges_subset_activeVerticalEdges
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (L : Finset (VertexIndex G)) :
    unlabelledActiveVerticalEdges label c L ⊆ activeVerticalEdges label c := by
  intro e he
  exact (Finset.mem_filter.mp he).1

omit [Fintype F] [DecidableEq W] [DecidableEq R] [DecidableEq R'] in
/-- If `L` contains every active vertex, an active edge with no labelled
endpoint is face-active. -/
theorem isFaceActive_of_mem_unlabelledActiveVerticalEdges
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (L : Finset (VertexIndex G))
    (hActive : vertexBlockSupport c ⊆ L)
    (e : VerticalEdgeIndex W G)
    (he : e ∈ unlabelledActiveVerticalEdges label c L) :
    IsFaceActiveVerticalEdge label c e := by
  have heData := Finset.mem_filter.mp he
  have heActive : IsActiveVerticalEdge label c e := by
    simpa [activeVerticalEdges] using heData.1
  have heOutside := heData.2
  have hSourceInactive :
      verticalEdgeEndpoint label e 0 ∉ vertexBlockSupport c := fun hv =>
    heOutside.1 (hActive hv)
  have hTargetInactive :
      verticalNeighbor label (verticalEdgeEndpoint label e 0) e.2.1 ∉
        vertexBlockSupport c := fun hv =>
    heOutside.2 (hActive hv)
  have hCarries : CarriesActiveFaceVerticalEdge label c e := by
    rcases heActive with hv | hv | hface
    · exact (hSourceInactive hv).elim
    · exact (hTargetInactive hv).elim
    · exact hface
  exact ⟨hCarries, hSourceInactive, hTargetInactive⟩

omit [Fintype F] [DecidableEq G] [Fintype W] [DecidableEq W]
    [DecidableEq R] [DecidableEq R'] in
/-- A face-active physical edge is the same source predicate at its
canonical endpoint. -/
theorem isFaceActiveVerticalEdge_iff (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (e : VerticalEdgeIndex W G) :
    IsFaceActiveVerticalEdge label c e ↔
      CarriesActiveFaceVerticalEdge label c e ∧
      verticalEdgeEndpoint label e 0 ∉ vertexBlockSupport c ∧
      verticalNeighbor label (verticalEdgeEndpoint label e 0) e.2.1 ∉
        vertexBlockSupport c := by
  rfl

omit [Fintype F] [DecidableEq G] [Fintype W] [DecidableEq W]
    [DecidableEq R] [DecidableEq R'] in
/-- Face-activity is independent of which endpoint represents a physical
vertical edge. -/
theorem isFaceActiveVerticalEdgeAt_verticalNeighbor
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) (b : W)
    (he : IsFaceActiveVerticalEdgeAt label c v b) :
    IsFaceActiveVerticalEdgeAt label c (verticalNeighbor label v b) b := by
  rcases he with ⟨⟨a, ha⟩, hv, hn⟩
  refine ⟨⟨a, ?_⟩, hn, ?_⟩
  · simpa [localFaceMatrix] using ha
  · simpa using hv

omit [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G]
    [Fintype W] [DecidableEq W] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
/-- Carrying an active face is independent of the endpoint used to name the
physical vertical edge. -/
theorem carriesActiveFaceVerticalEdge_verticalEdgeAtVertex_iff
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) (b : W) :
    CarriesActiveFaceVerticalEdge label c
        (verticalEdgeAtVertex label v b) ↔
      CarriesActiveFaceVerticalEdgeAt label c v b := by
  rcases v with ⟨side, side', g⟩
  fin_cases side' <;>
    simp [CarriesActiveFaceVerticalEdge,
      CarriesActiveFaceVerticalEdgeAt, verticalEdgeAtVertex,
      verticalEdgeEndpoint, localFaceMatrix, faceAtVertex,
      doubleCoverVoltage, mul_assoc]

omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W]
    [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R'] in
/-- The canonical endpoints of the physical edge `(v,b)` are exactly `v`
and its vertical neighbour, possibly in the opposite order. -/
theorem verticalEdgeAtVertex_canonicalEndpoints_mem_iff
    (label : W → G) (L : Finset (VertexIndex G))
    (v : VertexIndex G) (b : W) :
    (verticalEdgeEndpoint label (verticalEdgeAtVertex label v b) 0 ∈ L ∨
      verticalNeighbor label
        (verticalEdgeEndpoint label (verticalEdgeAtVertex label v b) 0) b ∈
          L) ↔
      v ∈ L ∨ verticalNeighbor label v b ∈ L := by
  rcases v with ⟨side, side', g⟩
  fin_cases side' <;>
    simp [verticalEdgeAtVertex, verticalEdgeEndpoint, verticalNeighbor,
      doubleCoverVoltage, oppositeSide, or_comm]

omit [Fintype F] [Fintype W] [DecidableEq W]
    [DecidableEq R] [DecidableEq R'] in
/-- The physical-edge face-active predicate agrees with the predicate at any
chosen endpoint representation. -/
theorem isFaceActiveVerticalEdge_verticalEdgeAtVertex_iff
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) (b : W) :
    IsFaceActiveVerticalEdge label c (verticalEdgeAtVertex label v b) ↔
      IsFaceActiveVerticalEdgeAt label c v b := by
  rw [isFaceActiveVerticalEdge_iff,
    carriesActiveFaceVerticalEdge_verticalEdgeAtVertex_iff]
  unfold IsFaceActiveVerticalEdgeAt
  have hEndpoints := verticalEdgeAtVertex_canonicalEndpoints_mem_iff
    label (vertexBlockSupport c) v b
  tauto

/-- On a face-active vertical edge the incident face row lies in the first
local code `ker h`. -/
theorem localFaceMatrix_row_mem_parityCheckCode_of_faceActive
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcCycle : LiftedProduct.boundary1 (data label h g') c = 0)
    (e : VerticalEdgeIndex W G)
    (he : IsFaceActiveVerticalEdge label c e) :
    ProductExpansion.row
        (localFaceMatrix label c (verticalEdgeEndpoint label e 0)) e.2.1 ∈
      (ProductExpansion.parityCheckCode h).carrier := by
  let v := verticalEdgeEndpoint label e 0
  let b := e.2.1
  have he' := (isFaceActiveVerticalEdge_iff label c e).mp he
  have hvZero : localVertexMatrix c v = 0 := by
    by_contra hv
    exact he'.2.1
      ((mem_vertexBlockSupport_iff_localVertexMatrix_ne_zero c v).2 hv)
  have hnZero : localVertexMatrix c (verticalNeighbor label v b) = 0 := by
    by_contra hv
    exact he'.2.2
      ((mem_vertexBlockSupport_iff_localVertexMatrix_ne_zero
        c (verticalNeighbor label v b)).2 hv)
  have hEndpointZero : verticalEndpointSyndrome label g' c v b = 0 := by
    funext r
    rw [verticalEndpointSyndrome_eq_add]
    simp [verticalVertexSyndrome, verticalNeighborSyndrome, hvZero, hnZero]
  change (Matrix.toLin' h)
      (ProductExpansion.row (localFaceMatrix label c v) b) = 0
  rw [Matrix.toLin'_apply]
  funext r
  have hmatrix :=
    localFaceMatrix_mul_transpose_eq_verticalEndpointSyndrome
      label h g' c hcCycle v
  have hentry := congrArg (fun z : Matrix W R F => z b r) hmatrix
  have hzero := congrFun hEndpointZero r
  simpa [Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply,
    dotProduct, ProductExpansion.row, mul_comm, hzero] using hentry

omit [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G]
    [Fintype W] [DecidableEq W] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
/-- A vertical edge that carries an active face has a nonzero local face
row. -/
theorem localFaceMatrix_row_ne_zero_of_carriesActiveFace
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (e : VerticalEdgeIndex W G)
    (he : CarriesActiveFaceVerticalEdge label c e) :
    ProductExpansion.row
      (localFaceMatrix label c (verticalEdgeEndpoint label e 0)) e.2.1 ≠ 0 := by
  rintro hzero
  obtain ⟨a, ha⟩ := he
  have := congrFun hzero a
  exact ha (by simpa [ProductExpansion.row] using this)

/-- PK22 `lemma:face-active-edge`: a face-active vertical edge is incident
to at least the minimum distance of `ker h` active faces. -/
theorem faceActiveVerticalEdge_faceWeight_ge
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcCycle : LiftedProduct.boundary1 (data label h g') c = 0)
    (d : Nat)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (e : VerticalEdgeIndex W G)
    (he : IsFaceActiveVerticalEdge label c e) :
    d ≤ HammingWeight
      (ProductExpansion.row
        (localFaceMatrix label c (verticalEdgeEndpoint label e 0)) e.2.1) := by
  apply hDistance
  · exact localFaceMatrix_row_mem_parityCheckCode_of_faceActive
      label h g' c hcCycle e he
  · exact localFaceMatrix_row_ne_zero_of_carriesActiveFace
      label c e ((isFaceActiveVerticalEdge_iff label c e).mp he).1

/-- Endpoint-indexed form of `lemma:face-active-edge`. -/
theorem faceActiveVerticalEdgeAt_faceWeight_ge
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcCycle : LiftedProduct.boundary1 (data label h g') c = 0)
    (d : Nat)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (v : VertexIndex G) (b : W)
    (he : IsFaceActiveVerticalEdgeAt label c v b) :
    d ≤ HammingWeight
      (ProductExpansion.row (localFaceMatrix label c v) b) := by
  rcases he with ⟨hCarries, hvInactive, hnInactive⟩
  have hvZero : localVertexMatrix c v = 0 := by
    by_contra hv
    exact hvInactive
      ((mem_vertexBlockSupport_iff_localVertexMatrix_ne_zero c v).2 hv)
  have hnZero : localVertexMatrix c (verticalNeighbor label v b) = 0 := by
    by_contra hv
    exact hnInactive
      ((mem_vertexBlockSupport_iff_localVertexMatrix_ne_zero
        c (verticalNeighbor label v b)).2 hv)
  have hEndpointZero : verticalEndpointSyndrome label g' c v b = 0 := by
    funext r
    rw [verticalEndpointSyndrome_eq_add]
    simp [verticalVertexSyndrome, verticalNeighborSyndrome, hvZero, hnZero]
  have hCodeword : ProductExpansion.row (localFaceMatrix label c v) b ∈
      (ProductExpansion.parityCheckCode h).carrier := by
    change (Matrix.toLin' h)
        (ProductExpansion.row (localFaceMatrix label c v) b) = 0
    rw [Matrix.toLin'_apply]
    funext r
    have hmatrix :=
      localFaceMatrix_mul_transpose_eq_verticalEndpointSyndrome
        label h g' c hcCycle v
    have hentry := congrArg (fun z : Matrix W R F => z b r) hmatrix
    have hzero := congrFun hEndpointZero r
    simpa [Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply,
      dotProduct, ProductExpansion.row, mul_comm, hzero] using hentry
  have hNonzero : ProductExpansion.row (localFaceMatrix label c v) b ≠ 0 := by
    rintro hzero
    obtain ⟨a, ha⟩ := hCarries
    exact ha (by simpa [ProductExpansion.row] using congrFun hzero a)
  exact hDistance _ hCodeword hNonzero

/-- Local-code distance gives at least `d` selected active-face incidences
for every non-active labelled vertex. -/
theorem d_mul_card_nonactiveLabelledVertices_le_selectedIncidences
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcCycle : LiftedProduct.boundary1 (data label h g') c = 0)
    (d m : Nat)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x) :
    d * (nonactiveLabelledVertices label c m).card ≤
      (selectedFaceDirectionIncidences label c m).card := by
  classical
  have hEach : ∀ v : {v // v ∈ nonactiveLabelledVertices label c m},
      d ≤ HammingWeight (ProductExpansion.row
        (localFaceMatrix label c v.1)
        (selectedFaceActiveDirection label c m v)) := by
    intro v
    exact faceActiveVerticalEdgeAt_faceWeight_ge
      label h g' c hcCycle d hDistance v.1
      (selectedFaceActiveDirection label c m v)
      (selectedFaceActiveDirection_spec label c m v)
  have hCard : (selectedFaceDirectionIncidences label c m).card =
      ∑ v : {v // v ∈ nonactiveLabelledVertices label c m},
        HammingWeight (ProductExpansion.row
          (localFaceMatrix label c v.1)
          (selectedFaceActiveDirection label c m v)) := by
    unfold selectedFaceDirectionIncidences
    rw [Finset.card_filter, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro v hv
    rw [HammingWeight, hammingSupport, Finset.card_filter]
    rfl
  rw [hCard]
  calc
    d * (nonactiveLabelledVertices label c m).card =
        ∑ _v : {v // v ∈ nonactiveLabelledVertices label c m}, d := by
      simp [Nat.mul_comm]
    _ ≤ ∑ v : {v // v ∈ nonactiveLabelledVertices label c m},
        HammingWeight (ProductExpansion.row
          (localFaceMatrix label c v.1)
          (selectedFaceActiveDirection label c m v)) :=
      Finset.sum_le_sum fun v _hv => hEach v

/-- Double counting active-face incidences bounds the non-active part of the
canonical labelled closure. -/
theorem d_mul_card_nonactiveLabelledVertices_le_four_mul_faceSupport
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcCycle : LiftedProduct.boundary1 (data label h g') c = 0)
    (d m : Nat)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x) :
    d * (nonactiveLabelledVertices label c m).card ≤
      4 * (faceSupport c).card := by
  exact (d_mul_card_nonactiveLabelledVertices_le_selectedIncidences
    label h g' c hcCycle d m hDistance).trans
      ((card_selectedFaceDirectionIncidences_le_activeFaceIncidences
        label c m).trans
        (card_activeFaceIncidences_le_four_mul
          label c (labelledVertices label c m)))

/-- Source bound `|L| ≤ |c|`: when the first local-code distance is at least
four, the canonical labelled set is no larger than the PK22 block support. -/
theorem card_labelledVertices_le_blockWeight
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcCycle : LiftedProduct.boundary1 (data label h g') c = 0)
    (d m : Nat)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hFour : 4 ≤ d) :
    (labelledVertices label c m).card ≤ blockWeight c := by
  have hDouble :=
    d_mul_card_nonactiveLabelledVertices_le_four_mul_faceSupport
      label h g' c hcCycle d m hDistance
  have hFourNonactive :
      4 * (nonactiveLabelledVertices label c m).card ≤
        d * (nonactiveLabelledVertices label c m).card :=
    Nat.mul_le_mul_right (nonactiveLabelledVertices label c m).card hFour
  have hNonactive :
      (nonactiveLabelledVertices label c m).card ≤ (faceSupport c).card := by
    omega
  have hCover : labelledVertices label c m ⊆
      nonactiveLabelledVertices label c m ∪ vertexBlockSupport c := by
    intro v hv
    by_cases hvActive : v ∈ vertexBlockSupport c
    · exact Finset.mem_union_right _ hvActive
    · exact Finset.mem_union_left _
        (Finset.mem_sdiff.mpr ⟨hv, hvActive⟩)
  unfold blockWeight
  calc
    (labelledVertices label c m).card ≤
        (nonactiveLabelledVertices label c m ∪
          vertexBlockSupport c).card := Finset.card_le_card hCover
    _ ≤ (nonactiveLabelledVertices label c m).card +
        (vertexBlockSupport c).card := Finset.card_union_le _ _
    _ ≤ (faceSupport c).card + (vertexBlockSupport c).card :=
      Nat.add_le_add_right hNonactive _

omit [Fintype F] [DecidableEq R] [DecidableEq R'] in
/-- Face-neighbours that are active but not wholly unlabelled are counted by
horizontal labelled-neighbour directions at the two endpoints.  Since the
product adjacency graph also contains those horizontal directions, this is
the incidence bound used in `lemma:lbl-edge`. -/
theorem verticalFaceGraph_external_degree_le_endpoint_adjacency
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (L : Finset (VertexIndex G)) (e : VerticalEdgeIndex W G) :
    (∑ e' ∈ activeVerticalEdges label c \
        unlabelledActiveVerticalEdges label c L,
        verticalFaceGraph label e e') ≤
      (∑ u ∈ L,
        adjacencyGraph label (verticalEdgeEndpoint label e 0) u) +
      ∑ u ∈ L, adjacencyGraph label
        (verticalNeighbor label (verticalEdgeEndpoint label e 0) e.2.1) u := by
  classical
  rw [sum_verticalFaceGraph_eq_card_filter]
  let D := Finset.univ.filter fun a : W =>
    verticalFaceNeighbor label e a ∈
      activeVerticalEdges label c \
        unlabelledActiveVerticalEdges label c L
  let H₀ := horizontalDirectionsInto label L (verticalEdgeEndpoint label e 0)
  let H₁ := horizontalDirectionsInto label L
    (verticalNeighbor label (verticalEdgeEndpoint label e 0) e.2.1)
  have hSubset : D ⊆ H₀ ∪ H₁ := by
    intro a ha
    have haDiff : verticalFaceNeighbor label e a ∈
        activeVerticalEdges label c \
          unlabelledActiveVerticalEdges label c L := by
      simpa [D] using ha
    have haActive := (Finset.mem_sdiff.mp haDiff).1
    have haNotBad := (Finset.mem_sdiff.mp haDiff).2
    have hEndpoint :
        verticalEdgeEndpoint label (verticalFaceNeighbor label e a) 0 ∈ L ∨
        verticalNeighbor label
          (verticalEdgeEndpoint label (verticalFaceNeighbor label e a) 0)
          (verticalFaceNeighbor label e a).2.1 ∈ L := by
      by_cases h₀ :
          verticalEdgeEndpoint label (verticalFaceNeighbor label e a) 0 ∈ L
      · exact Or.inl h₀
      by_cases h₁ :
          verticalNeighbor label
            (verticalEdgeEndpoint label (verticalFaceNeighbor label e a) 0)
            (verticalFaceNeighbor label e a).2.1 ∈ L
      · exact Or.inr h₁
      · exfalso
        apply haNotBad
        exact Finset.mem_filter.mpr ⟨haActive, h₀, h₁⟩
    apply Finset.mem_union.mpr
    rcases hEndpoint with h₀ | h₁
    · left
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ a, by simpa [H₀] using h₀⟩
    · right
      have h₁' : horizontalNeighbor label
          (verticalNeighbor label (verticalEdgeEndpoint label e 0) e.2.1) a ∈
          L := by
        rw [← verticalNeighbor_horizontalNeighbor_commute]
        simpa using h₁
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ a, by simpa [H₁] using h₁'⟩
  have hAdj₀ := sum_adjacencyGraph_eq_card_directionsInto
    label L (verticalEdgeEndpoint label e 0)
  have hAdj₁ := sum_adjacencyGraph_eq_card_directionsInto label L
    (verticalNeighbor label (verticalEdgeEndpoint label e 0) e.2.1)
  calc
    D.card ≤ (H₀ ∪ H₁).card := Finset.card_le_card hSubset
    _ ≤ H₀.card + H₁.card := Finset.card_union_le H₀ H₁
    _ ≤ (∑ u ∈ L,
          adjacencyGraph label (verticalEdgeEndpoint label e 0) u) +
        ∑ u ∈ L, adjacencyGraph label
          (verticalNeighbor label (verticalEdgeEndpoint label e 0) e.2.1) u := by
      dsimp [H₀, H₁]
      omega

/-- The source labelled-edge argument reduced to its remaining incidence
geometry.  The `hNeighborBound` hypothesis is the double-cover fact that
active face-neighbours outside `S` choose distinct labelled vertices adjacent
to one of the two endpoints of `e`. -/
theorem unlabelledActiveVerticalEdges_eq_empty_of_neighborBound
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcCycle : LiftedProduct.boundary1 (data label h g') c = 0)
    (d m radius : Nat) (lambda : ℝ)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (L : Finset (VertexIndex G))
    (hClosed : IsClosedLabelledSet label c m L)
    (hExpand : SmallSetExpansion.IsSmallSetEdgeExpanding
      (verticalFaceGraph label) radius lambda)
    (hActiveRadius : (activeVerticalEdges label c).card ≤ radius)
    (hNeighborBound : ∀ e ∈ unlabelledActiveVerticalEdges label c L,
      (∑ e' ∈ activeVerticalEdges label c \
          unlabelledActiveVerticalEdges label c L,
          verticalFaceGraph label e e') ≤
        (∑ u ∈ L,
          adjacencyGraph label (verticalEdgeEndpoint label e 0) u) +
        ∑ u ∈ L, adjacencyGraph label
          (verticalNeighbor label (verticalEdgeEndpoint label e 0) e.2.1) u)
    (hThreshold : (2 * m : ℝ) + lambda ≤ d) :
    unlabelledActiveVerticalEdges label c L = ∅ := by
  apply SmallSetExpansion.subset_eq_empty_of_internal_expansion_and_external_degree_lt
    (verticalFaceGraph label) radius lambda
    (activeVerticalEdges label c)
    (unlabelledActiveVerticalEdges label c L) d m hExpand
    (unlabelledActiveVerticalEdges_subset_activeVerticalEdges label c L)
    hActiveRadius
  · intro e he
    have hFaceActive := isFaceActive_of_mem_unlabelledActiveVerticalEdges
      label c L hClosed.1 e he
    exact (faceActiveVerticalEdge_faceWeight_ge
      label h g' c hcCycle d hDistance e hFaceActive).trans
        (localFaceRow_weight_le_activeVerticalEdge_degree label c e)
  · intro e he
    have heData := Finset.mem_filter.mp he
    have hFaceActive := isFaceActive_of_mem_unlabelledActiveVerticalEdges
      label c L hClosed.1 e he
    have hSourceIncident : IsIncidentToFaceActiveVerticalEdge label c
        (verticalEdgeEndpoint label e 0) :=
      ⟨e.2.1, hFaceActive⟩
    have hTargetIncident : IsIncidentToFaceActiveVerticalEdge label c
        (verticalNeighbor label (verticalEdgeEndpoint label e 0) e.2.1) :=
      ⟨e.2.1,
        isFaceActiveVerticalEdgeAt_verticalNeighbor label c
          (verticalEdgeEndpoint label e 0) e.2.1 hFaceActive⟩
    have hSourceDegree :
        (∑ u ∈ L,
          adjacencyGraph label (verticalEdgeEndpoint label e 0) u) < m := by
      apply Nat.lt_of_not_ge
      intro hDegree
      exact heData.2.1
        (hClosed.2 (verticalEdgeEndpoint label e 0)
          hSourceIncident hDegree)
    have hTargetDegree :
        (∑ u ∈ L, adjacencyGraph label
          (verticalNeighbor label (verticalEdgeEndpoint label e 0) e.2.1) u) <
            m := by
      apply Nat.lt_of_not_ge
      intro hDegree
      exact heData.2.2
        (hClosed.2
          (verticalNeighbor label (verticalEdgeEndpoint label e 0) e.2.1)
          hTargetIncident hDegree)
    exact (hNeighborBound e he).trans_lt (by omega)
  · exact hThreshold

/-- PK22 `lemma:lbl-edge` for the physical vertical-edge graph: every active
vertical edge has a labelled endpoint once the first local-code distance and
small-set expansion beat the `2m` closure threshold. -/
theorem unlabelledActiveVerticalEdges_eq_empty
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcCycle : LiftedProduct.boundary1 (data label h g') c = 0)
    (d m radius : Nat) (lambda : ℝ)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (L : Finset (VertexIndex G))
    (hClosed : IsClosedLabelledSet label c m L)
    (hExpand : SmallSetExpansion.IsSmallSetEdgeExpanding
      (verticalFaceGraph label) radius lambda)
    (hActiveRadius : (activeVerticalEdges label c).card ≤ radius)
    (hThreshold : (2 * m : ℝ) + lambda ≤ d) :
    unlabelledActiveVerticalEdges label c L = ∅ := by
  apply unlabelledActiveVerticalEdges_eq_empty_of_neighborBound
    label h g' c hcCycle d m radius lambda hDistance L hClosed
    hExpand hActiveRadius
  · intro e _he
    exact verticalFaceGraph_external_degree_le_endpoint_adjacency label c L e
  · exact hThreshold

/-- Endpoint form of `lemma:lbl-edge`, ready for the canonical labelled-set
global expansion theorem. -/
theorem faceActiveVerticalEdge_has_labelledEndpoint
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcCycle : LiftedProduct.boundary1 (data label h g') c = 0)
    (d m radius : Nat) (lambda : ℝ)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (L : Finset (VertexIndex G))
    (hClosed : IsClosedLabelledSet label c m L)
    (hExpand : SmallSetExpansion.IsSmallSetEdgeExpanding
      (verticalFaceGraph label) radius lambda)
    (hActiveRadius : (activeVerticalEdges label c).card ≤ radius)
    (hThreshold : (2 * m : ℝ) + lambda ≤ d)
    (v : VertexIndex G) (b : W)
    (he : IsFaceActiveVerticalEdgeAt label c v b) :
    v ∈ L ∨ verticalNeighbor label v b ∈ L := by
  classical
  let e := verticalEdgeAtVertex label v b
  have hFace : IsFaceActiveVerticalEdge label c e :=
    (isFaceActiveVerticalEdge_verticalEdgeAtVertex_iff label c v b).2 he
  have hCarries : CarriesActiveFaceVerticalEdge label c e :=
    ((isFaceActiveVerticalEdge_iff label c e).mp hFace).1
  have heActive : e ∈ activeVerticalEdges label c := by
    rw [activeVerticalEdges, Finset.mem_filter]
    exact ⟨Finset.mem_univ e, Or.inr (Or.inr hCarries)⟩
  have hEmpty := unlabelledActiveVerticalEdges_eq_empty
    label h g' c hcCycle d m radius lambda hDistance L hClosed
    hExpand hActiveRadius hThreshold
  have hCanonical :
      verticalEdgeEndpoint label e 0 ∈ L ∨
        verticalNeighbor label (verticalEdgeEndpoint label e 0) e.2.1 ∈ L := by
    by_cases hSource : verticalEdgeEndpoint label e 0 ∈ L
    · exact Or.inl hSource
    by_cases hTarget :
        verticalNeighbor label (verticalEdgeEndpoint label e 0) e.2.1 ∈ L
    · exact Or.inr hTarget
    · have hBad : e ∈ unlabelledActiveVerticalEdges label c L := by
        rw [unlabelledActiveVerticalEdges, Finset.mem_filter]
        exact ⟨heActive, hSource, hTarget⟩
      rw [hEmpty] at hBad
      simp at hBad
  exact (verticalEdgeAtVertex_canonicalEndpoints_mem_iff label L v b).mp
    (by simpa [e] using hCanonical)

/-- PK22's one-orientation global zero theorem with the labelled-edge
hypothesis discharged from local-code distance and expansion of the physical
vertical-edge face graph. -/
theorem cycle_eq_zero_of_globalExpansion_of_expandingVerticalEdges
    (label : W → G) (h : Matrix R W F)
    (hRank : h.rank = Fintype.card R) (g' : Matrix R' W F)
    (gInjective : Function.Injective
      (fun u : Word F R' => g'.transpose.mulVec u))
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcCycle : LiftedProduct.boundary1 (data label h g') c = 0)
    (hcLocal : LocallyMinimalDistance.IsLocallyMinimal blockWeight
      (horizontalFiberBoundaryMoves label h g') c)
    (d m s : Nat) (beta : ℝ)
    (hProductExpand : ProductExpansion.ProductExpanding h
      (ProductExpansion.generatorImageParityCheck g') s (2 * m) beta)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hLength : d ≤ Fintype.card W)
    (hDistanceScale : 4 * m ≤ d)
    (hRectangleScale : 4 * s ≤ m * d)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W)
    (radiusVertical : Nat) (lambdaVertical : ℝ)
    (hExpandVertical : SmallSetExpansion.IsSmallSetEdgeExpanding
      (verticalFaceGraph label) radiusVertical lambdaVertical)
    (hActiveRadius : (activeVerticalEdges label c).card ≤ radiusVertical)
    (hVerticalThreshold : (2 * m : ℝ) + lambdaVertical ≤ d)
    (radiusEdge radiusFace : Nat) (lambdaEdge lambdaFace : ℝ)
    (hLambdaEdge : 0 < lambdaEdge) (hLambdaFace : 0 < lambdaFace)
    (hExpandEdge : SmallSetExpansion.IsSmallSetEdgeExpanding
      (adjacencyGraph label) radiusEdge lambdaEdge)
    (hExpandFace : SmallSetExpansion.IsSmallSetEdgeExpanding
      (faceSquareGraph label) radiusFace lambdaFace)
    (hLRadiusEdge : (labelledVertices label c m).card ≤ radiusEdge)
    (hLRadiusFace : (labelledVertices label c m).card ≤ radiusFace)
    (hThresholdEdge : 2 * lambdaEdge ≤ m)
    (hThresholdFace : 2 * lambdaFace ≤ s) :
    c = 0 := by
  apply cycle_eq_zero_of_globalExpansion_of_labelledVertices
    label h hRank g' gInjective c hcCycle hcLocal d m s beta
  · intro v b he
    exact faceActiveVerticalEdge_has_labelledEndpoint
      label h g' c hcCycle d m radiusVertical lambdaVertical hDistance
      (labelledVertices label c m) (labelledVertices_isClosed label c m)
      hExpandVertical hActiveRadius hVerticalThreshold v b he
  · exact hProductExpand
  · exact hDistance
  · exact hLength
  · exact hDistanceScale
  · exact hRectangleScale
  · exact hBudget
  · exact hLambdaEdge
  · exact hLambdaFace
  · exact hExpandEdge
  · exact hExpandFace
  · exact hLRadiusEdge
  · exact hLRadiusFace
  · exact hThresholdEdge
  · exact hThresholdFace

/-- Block-weight form of the one-orientation PK22 zero lemma.  All three
small-set radius obligations are reduced to the source block weight: active
vertical edges cost at most `w` per block, while canonical labelled vertices
cost at most one per block. -/
theorem cycle_eq_zero_of_globalExpansion_of_blockWeight
    (label : W → G) (h : Matrix R W F)
    (hRank : h.rank = Fintype.card R) (g' : Matrix R' W F)
    (gInjective : Function.Injective
      (fun u : Word F R' => g'.transpose.mulVec u))
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcCycle : LiftedProduct.boundary1 (data label h g') c = 0)
    (hcLocal : LocallyMinimalDistance.IsLocallyMinimal blockWeight
      (horizontalFiberBoundaryMoves label h g') c)
    (d m s : Nat) (beta : ℝ)
    (hProductExpand : ProductExpansion.ProductExpanding h
      (ProductExpansion.generatorImageParityCheck g') s (2 * m) beta)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hLength : d ≤ Fintype.card W)
    (hTwo : 2 ≤ Fintype.card W) (hFour : 4 ≤ d)
    (hDistanceScale : 4 * m ≤ d)
    (hRectangleScale : 4 * s ≤ m * d)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W)
    (radiusVertical : Nat) (lambdaVertical : ℝ)
    (hExpandVertical : SmallSetExpansion.IsSmallSetEdgeExpanding
      (verticalFaceGraph label) radiusVertical lambdaVertical)
    (hBlockRadiusVertical :
      Fintype.card W * blockWeight c ≤ radiusVertical)
    (hVerticalThreshold : (2 * m : ℝ) + lambdaVertical ≤ d)
    (radiusEdge radiusFace : Nat) (lambdaEdge lambdaFace : ℝ)
    (hLambdaEdge : 0 < lambdaEdge) (hLambdaFace : 0 < lambdaFace)
    (hExpandEdge : SmallSetExpansion.IsSmallSetEdgeExpanding
      (adjacencyGraph label) radiusEdge lambdaEdge)
    (hExpandFace : SmallSetExpansion.IsSmallSetEdgeExpanding
      (faceSquareGraph label) radiusFace lambdaFace)
    (hBlockRadiusEdge : blockWeight c ≤ radiusEdge)
    (hBlockRadiusFace : blockWeight c ≤ radiusFace)
    (hThresholdEdge : 2 * lambdaEdge ≤ m)
    (hThresholdFace : 2 * lambdaFace ≤ s) :
    c = 0 := by
  apply cycle_eq_zero_of_globalExpansion_of_expandingVerticalEdges
    label h hRank g' gInjective c hcCycle hcLocal d m s beta
    hProductExpand hDistance hLength hDistanceScale hRectangleScale hBudget
    radiusVertical lambdaVertical hExpandVertical
  · exact (card_activeVerticalEdges_le_card_mul_blockWeight
      label c hTwo).trans hBlockRadiusVertical
  · exact hVerticalThreshold
  · exact hLambdaEdge
  · exact hLambdaFace
  · exact hExpandEdge
  · exact hExpandFace
  · exact (card_labelledVertices_le_blockWeight
      label h g' c hcCycle d m hDistance hFour).trans hBlockRadiusEdge
  · exact (card_labelledVertices_le_blockWeight
      label h g' c hcCycle d m hDistance hFour).trans hBlockRadiusFace
  · exact hThresholdEdge
  · exact hThresholdFace

end QEC.Coding.TannerLiftedProduct
