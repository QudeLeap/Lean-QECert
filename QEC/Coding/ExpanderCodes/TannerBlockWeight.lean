import QEC.Coding.ExpanderCodes.TannerLiftedProduct
import QEC.Coding.ExpanderCodes.LocallyMinimalDistance
import QEC.Coding.ExpanderCodes.LocalStarExpansion

/-!
# PK22 block weight for the Tanner lifted product

The degree-one space has a face block indexed by `W × W × G` and a
vertex block indexed by `(Fin 2 × R) × (Fin 2 × R') × G`. PK22 counts
each nonzero face coefficient once, but counts an entire `R × R'` fiber over
one underlying double-cover product vertex only once. This module defines that
source weight and proves that it is bounded by scalar Hamming weight.
-/

namespace QEC.Coding.TannerLiftedProduct

universe u v

variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']

/-- Scalar face coordinates of the Tanner lifted product. -/
abbrev FaceIndex (W G : Type v) := W × W × G

/-- Underlying vertices whose coefficient fibers have shape `R × R'`. -/
abbrev VertexIndex (G : Type v) := Fin 2 × Fin 2 × G

/-- The other endpoint side in the bipartite double cover. -/
def oppositeSide (side : Fin 2) : Fin 2 :=
  Fin.rev side

/-- The face in local directions `(a,b)` incident to an underlying product
vertex. The group coordinate is forced by the two double-cover voltages. -/
def faceAtVertex (label : W → G) (v : VertexIndex G) (a b : W) :
    FaceIndex W G :=
  match v with
  | (side, side', g) =>
      (a, b, (doubleCoverVoltage label side' b)⁻¹ * g *
        (doubleCoverVoltage label side a)⁻¹)

/-- Local matrix coordinates embed injectively into the global face set around
one fixed vertex. The matrix row is the vertical direction and its column is
the horizontal direction. -/
def faceAtVertexEmbedding (label : W → G) (v : VertexIndex G) :
    W × W ↪ FaceIndex W G where
  toFun p := faceAtVertex label v p.2 p.1
  inj' := by
    rintro ⟨b, a⟩ ⟨b', a'⟩ h
    have ha : a = a' := congrArg (fun z : FaceIndex W G => z.1) h
    have hb : b = b' := congrArg (fun z : FaceIndex W G => z.2.1) h
    cases hb
    cases ha
    rfl

/-- The `w²` faces in the complete-square star of one vertex. -/
noncomputable def faceStar (label : W → G) (v : VertexIndex G) :
    Finset (FaceIndex W G) :=
  Finset.univ.map (faceAtVertexEmbedding label v)

omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] [DecidableEq W] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
/-- A vertex star has exactly `|W|²` distinct faces. -/
@[simp] theorem card_faceStar (label : W → G) (v : VertexIndex G) :
    (faceStar label v).card = Fintype.card W * Fintype.card W := by
  simp [faceStar]

omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] [DecidableEq W] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
/-- Membership in a vertex face star has explicit local coordinates. -/
theorem mem_faceStar_iff (label : W → G) (v : VertexIndex G)
    (p : FaceIndex W G) :
    p ∈ faceStar label v ↔ ∃ a b, faceAtVertex label v a b = p := by
  classical
  constructor
  · intro hp
    obtain ⟨q, _hq, hq⟩ := Finset.mem_map.mp hp
    exact ⟨q.2, q.1, hq⟩
  · rintro ⟨a, b, rfl⟩
    exact Finset.mem_map.mpr ⟨(b, a), Finset.mem_univ _, rfl⟩

/-- Embed a face coordinate in the first middle-chain block. -/
def faceCoordinate (p : FaceIndex W G) :
    LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G :=
  Sum.inl p

/-- Embed one scalar in the coefficient fiber over an underlying vertex. -/
def vertexCoordinate (v : VertexIndex G) (r : R) (r' : R') :
    LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G :=
  match v with
  | (side, side', g) => Sum.inr ((side, r), (side', r'), g)

/-- Recover the underlying vertex of a degree-one coordinate, when present. -/
def coordinateVertex :
    LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G →
      Option (VertexIndex G)
  | Sum.inl _ => none
  | Sum.inr ((side, _r), (side', _r'), g) => some (side, side', g)

/-- A degree-zero coordinate on the vertical edge in direction b incident
to v, with local first-code check coordinate r. -/
def verticalEdgeCoordinate (label : W → G) (v : VertexIndex G)
    (r : R) (b : W) :
    LiftedProduct.C0Index (Fin 2 × R) W G :=
  match v with
  | (side, side', g) =>
      ((side, r), b, (doubleCoverVoltage label side' b)⁻¹ * g)

/-- A degree-two coordinate on the horizontal edge in direction a incident
to v, with local second-code check coordinate r'. -/
def horizontalEdgeCoordinate (label : W → G) (v : VertexIndex G)
    (a : W) (r' : R') :
    LiftedProduct.C2Index W (Fin 2 × R') G :=
  match v with
  | (side, side', g) =>
      (a, (side', r'), g * (doubleCoverVoltage label side a)⁻¹)

/-- The other endpoint of the vertical edge in direction b at v. -/
def verticalNeighbor (label : W → G) (v : VertexIndex G) (b : W) :
    VertexIndex G :=
  match v with
  | (side, side', g) =>
      (side, oppositeSide side',
        doubleCoverVoltage label (oppositeSide side') b *
          (doubleCoverVoltage label side' b)⁻¹ * g)

/-- The other endpoint of the horizontal edge in direction a at v. -/
def horizontalNeighbor (label : W → G) (v : VertexIndex G) (a : W) :
    VertexIndex G :=
  match v with
  | (side, side', g) =>
      (oppositeSide side, side',
        g * (doubleCoverVoltage label side a)⁻¹ *
          doubleCoverVoltage label (oppositeSide side) a)

/-- The scalar vertex coordinate at the endpoint with selected second side of
the vertical edge in direction b at v. -/
def verticalEndpointCoordinate (label : W → G) (v : VertexIndex G)
    (r : R) (b : W) (endpointSide : Fin 2) (r' : R') :
    LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G :=
  match v with
  | (side, side', g) =>
      vertexCoordinate (W := W)
        (side, endpointSide,
          doubleCoverVoltage label endpointSide b *
            (doubleCoverVoltage label side' b)⁻¹ * g)
        r r'

/-- The scalar vertex coordinate at the endpoint with selected first side of
the horizontal edge in direction a at v. -/
def horizontalEndpointCoordinate (label : W → G) (v : VertexIndex G)
    (a : W) (endpointSide : Fin 2) (r : R) (r' : R') :
    LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G :=
  match v with
  | (side, side', g) =>
      vertexCoordinate (W := W)
        (endpointSide, side',
          g * (doubleCoverVoltage label side a)⁻¹ *
            doubleCoverVoltage label endpointSide a)
        r r'

omit [Field F] [Fintype F] [DecidableEq F] [Group G] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W] [Fintype R]
    [DecidableEq R] [Fintype R'] [DecidableEq R'] in
@[simp] theorem oppositeSide_oppositeSide (side : Fin 2) :
    oppositeSide (oppositeSide side) = side := by
  fin_cases side <;> rfl

omit [Field F] [Fintype F] [DecidableEq F] [Group G] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W] [Fintype R]
    [DecidableEq R] [Fintype R'] [DecidableEq R'] in
@[simp] theorem oppositeSide_ne (side : Fin 2) :
    oppositeSide side ≠ side := by
  fin_cases side <;> decide

omit [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G]
    [Fintype W] [DecidableEq W] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
/-- Moving to the other vertical endpoint preserves the underlying edge
coordinate. -/
@[simp] theorem verticalEdgeCoordinate_verticalNeighbor
    (label : W → G) (v : VertexIndex G) (r : R) (b : W) :
    verticalEdgeCoordinate label (verticalNeighbor label v b) r b =
      verticalEdgeCoordinate label v r b := by
  rcases v with ⟨side, side', g⟩
  simp [verticalEdgeCoordinate, verticalNeighbor, mul_assoc]

omit [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G]
    [Fintype W] [DecidableEq W] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
/-- Moving to the other horizontal endpoint preserves the underlying edge
coordinate. -/
@[simp] theorem horizontalEdgeCoordinate_horizontalNeighbor
    (label : W → G) (v : VertexIndex G) (a : W) (r' : R') :
    horizontalEdgeCoordinate label (horizontalNeighbor label v a) a r' =
      horizontalEdgeCoordinate label v a r' := by
  rcases v with ⟨side, side', g⟩
  simp [horizontalEdgeCoordinate, horizontalNeighbor, mul_assoc]

omit [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G]
    [Fintype W] [DecidableEq W] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
/-- A face through v and direction b is also through the other endpoint of
that vertical edge. -/
@[simp] theorem faceAtVertex_verticalNeighbor
    (label : W → G) (v : VertexIndex G) (a b : W) :
    faceAtVertex label (verticalNeighbor label v b) a b =
      faceAtVertex label v a b := by
  rcases v with ⟨side, side', g⟩
  simp [faceAtVertex, verticalNeighbor, mul_assoc]

omit [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G]
    [Fintype W] [DecidableEq W] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
/-- A face through v and direction a is also through the other endpoint of
that horizontal edge. -/
@[simp] theorem faceAtVertex_horizontalNeighbor
    (label : W → G) (v : VertexIndex G) (a b : W) :
    faceAtVertex label (horizontalNeighbor label v a) a b =
      faceAtVertex label v a b := by
  rcases v with ⟨side, side', g⟩
  simp [faceAtVertex, horizontalNeighbor, mul_assoc]

/-
The coefficient identities below are independent of the ambient decidable
equality choices used by the finite support representations.
-/
omit [DecidableEq F] [DecidableEq G] in
/-- The face in local directions (a,b) meets the vertical edge at v with
the first local-check coefficient. -/
@[simp] theorem boundary1Matrix_vertical_face_apply
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (v : VertexIndex G) (r : R) (b a : W) :
    LiftedProduct.boundary1Matrix (data label h h')
        (verticalEdgeCoordinate label v r b)
        (faceCoordinate (R := R) (R' := R') (faceAtVertex label v a b)) =
      h r a := by
  rcases v with ⟨side, side', g⟩
  simp [verticalEdgeCoordinate, faceCoordinate, faceAtVertex, data,
    doubleCoverTannerMatrix, LiftedProduct.rightRegularMatrix, mul_assoc]

omit [DecidableEq F] [DecidableEq G] in
/-- The coefficient at v in its incident vertical-edge equation is the
negative second local-check coefficient. -/
@[simp] theorem boundary1Matrix_vertical_vertex_apply
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (v : VertexIndex G) (r : R) (r' : R') (b : W) :
    LiftedProduct.boundary1Matrix (data label h h')
        (verticalEdgeCoordinate label v r b)
        (vertexCoordinate (W := W) v r r') =
      -h' r' b := by
  rcases v with ⟨side, side', g⟩
  simp [verticalEdgeCoordinate, vertexCoordinate, data,
    doubleCoverTannerMatrix, LiftedProduct.starTranspose,
    LiftedProduct.groupConj, LiftedProduct.leftRegularMatrix]

omit [DecidableEq F] [DecidableEq G] in
/-- The same local face meets the horizontal edge at v with the second
local-check coefficient. -/
@[simp] theorem boundary2Matrix_face_horizontal_apply
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (v : VertexIndex G) (r' : R') (b a : W) :
    LiftedProduct.boundary2Matrix (data label h h')
        (faceCoordinate (R := R) (R' := R') (faceAtVertex label v a b))
        (horizontalEdgeCoordinate label v a r') =
      h' r' b := by
  rcases v with ⟨side, side', g⟩
  simp [horizontalEdgeCoordinate, faceCoordinate, faceAtVertex, data,
    doubleCoverTannerMatrix, LiftedProduct.starTranspose,
    LiftedProduct.groupConj, LiftedProduct.leftRegularMatrix]

omit [DecidableEq F] [DecidableEq G] in
/-- The coefficient at v in its incident horizontal-edge equation is the
first local-check coefficient. -/
@[simp] theorem boundary2Matrix_vertex_horizontal_apply
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (v : VertexIndex G) (r : R) (r' : R') (a : W) :
    LiftedProduct.boundary2Matrix (data label h h')
        (vertexCoordinate (W := W) v r r')
        (horizontalEdgeCoordinate label v a r') =
      h r a := by
  rcases v with ⟨side, side', g⟩
  simp [horizontalEdgeCoordinate, vertexCoordinate, data,
    doubleCoverTannerMatrix, LiftedProduct.rightRegularMatrix]

/-- Outside the explicit Tanner support cover, a first-boundary matrix row
vanishes. -/
theorem boundary1Matrix_eq_zero_of_not_mem_supportCover
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (c0 : LiftedProduct.C0Index (Fin 2 × R) W G)
    (q : LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)
    (hq : q ∉ boundary1SupportCover label h h' c0) :
    LiftedProduct.boundary1Matrix (data label h h') c0 q = 0 := by
  classical
  by_contra hcoeff
  apply hq
  apply boundary1RowSupport_subset_cover label h h' c0
  rcases c0 with ⟨ar, br, go⟩
  cases q with
  | inl q =>
      rcases q with ⟨ac, br', gi⟩
      rw [LiftedProduct.mem_boundary1RowSupport_inl]
      simpa [LiftedProduct.boundary1Matrix_inl_apply,
        LiftedProduct.rightRegularMatrix] using hcoeff
  | inr q =>
      rcases q with ⟨ar', bc, gi⟩
      rw [LiftedProduct.mem_boundary1RowSupport_inr]
      simpa [LiftedProduct.boundary1Matrix_inr_apply,
        LiftedProduct.leftRegularMatrix] using hcoeff

/-- Outside the explicit Tanner support cover, a second-boundary matrix row
vanishes. -/
theorem boundary2Matrix_eq_zero_of_not_mem_supportCover
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (q : LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)
    (c2 : LiftedProduct.C2Index W (Fin 2 × R') G)
    (hq : q ∉ boundary2SupportCover label h h' c2) :
    LiftedProduct.boundary2Matrix (data label h h') q c2 = 0 := by
  classical
  by_contra hcoeff
  apply hq
  apply boundary2RowSupport_subset_cover label h h' c2
  rcases c2 with ⟨ac, bc, gi⟩
  cases q with
  | inl q =>
      rcases q with ⟨ac', br, go⟩
      rw [LiftedProduct.mem_boundary2RowSupport_inl]
      simpa [LiftedProduct.boundary2Matrix_inl_apply,
        LiftedProduct.leftRegularMatrix] using hcoeff
  | inr q =>
      rcases q with ⟨ar, bc', go⟩
      rw [LiftedProduct.mem_boundary2RowSupport_inr]
      simpa [LiftedProduct.boundary2Matrix_inr_apply,
        LiftedProduct.rightRegularMatrix] using hcoeff

/-- Evaluation of the first boundary may be restricted exactly to its
group-size-independent Tanner support cover. -/
theorem boundary1_apply_eq_sum_supportCover
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (c0 : LiftedProduct.C0Index (Fin 2 × R) W G) :
    LiftedProduct.boundary1 (data label h h') c c0 =
      ∑ q ∈ boundary1SupportCover label h h' c0,
        LiftedProduct.boundary1Matrix (data label h h') c0 q * c q := by
  classical
  change (∑ q, LiftedProduct.boundary1Matrix (data label h h') c0 q * c q) = _
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro q _hqUniv hqCover
  rw [boundary1Matrix_eq_zero_of_not_mem_supportCover
    label h h' c0 q hqCover, zero_mul]

/-- The full vertical-edge boundary equation is the local face syndrome plus
the two endpoint vertex contributions. -/
theorem boundary1_verticalEdge_apply
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) (r : R) (b : W) :
    LiftedProduct.boundary1 (data label h h') c
        (verticalEdgeCoordinate label v r b) =
      (∑ a, h r a *
        c (faceCoordinate (R := R) (R' := R')
          (faceAtVertex label v a b))) +
      ∑ endpoint : Fin 2 × R',
        (-h' endpoint.2 b) *
          c (verticalEndpointCoordinate label v r b endpoint.1 endpoint.2) := by
  classical
  rw [boundary1_apply_eq_sum_supportCover]
  rcases v with ⟨side, side', g⟩
  unfold boundary1SupportCover
  dsimp only
  rw [Finset.sum_union]
  · rw [Finset.sum_map, Finset.sum_map]
    simp [verticalEdgeCoordinate, verticalEndpointCoordinate, faceCoordinate,
      faceAtVertex, vertexCoordinate, data, doubleCoverTannerMatrix,
      LiftedProduct.starTranspose, LiftedProduct.groupConj,
      LiftedProduct.leftRegularMatrix, LiftedProduct.rightRegularMatrix,
      mul_assoc]
  · simp [Finset.disjoint_left]

/-- Restrict a middle chain's face block to the complete-square star of one
underlying vertex. Rows are vertical directions and columns are horizontal
directions, matching the source convention in the local-star argument. -/
def localFaceMatrix (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) : Matrix W W F :=
  fun b a => c (faceCoordinate (R := R) (R' := R')
    (faceAtVertex label v a b))

/-- The `R×R'` coefficient matrix carried by one underlying vertex. -/
def localVertexMatrix
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) : Matrix R R' F :=
  fun r r' => c (vertexCoordinate (W := W) v r r')

/-- Syndrome on the vertical edges at v contributed by the two endpoint
vertex blocks. -/
def verticalEndpointSyndrome (label : W → G) (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) : Matrix W R F :=
  fun b r =>
    ∑ endpoint : Fin 2 × R',
      h' endpoint.2 b *
        c (verticalEndpointCoordinate label v r b endpoint.1 endpoint.2)

/-- The part of the vertical-edge syndrome contributed by the coefficient
block at the distinguished vertex itself. -/
def verticalVertexSyndrome (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) : Matrix W R F :=
  fun b r => ∑ r', h' r' b * localVertexMatrix c v r r'

/-- The part of the vertical-edge syndrome contributed by the opposite
endpoint of each vertical edge at the distinguished vertex. -/
def verticalNeighborSyndrome (label : W → G) (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) : Matrix W R F :=
  fun b r => ∑ r', h' r' b *
    localVertexMatrix c (verticalNeighbor label v b) r r'

omit [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G]
    [Fintype W] [DecidableEq W] [Fintype R] [DecidableEq R]
    [DecidableEq R'] in
/-- The two endpoint contributions split into the distinguished vertex and
its vertical neighbor, with the exact Tanner coordinate conventions. -/
theorem verticalEndpointSyndrome_eq_add
    (label : W → G) (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) :
    verticalEndpointSyndrome label h' c v =
      verticalVertexSyndrome h' c v +
        verticalNeighborSyndrome label h' c v := by
  ext b r
  rcases v with ⟨side, side', g⟩
  fin_cases side'
  · simp [verticalEndpointSyndrome, verticalVertexSyndrome,
      verticalNeighborSyndrome, localVertexMatrix,
      verticalEndpointCoordinate, verticalNeighbor, vertexCoordinate,
      oppositeSide, Fintype.sum_prod_type, Fin.sum_univ_two, mul_assoc]
  · simp [verticalEndpointSyndrome, verticalVertexSyndrome,
      verticalNeighborSyndrome, localVertexMatrix,
      verticalEndpointCoordinate, verticalNeighbor, vertexCoordinate,
      oppositeSide, Fintype.sum_prod_type, Fin.sum_univ_two, mul_assoc,
      add_comm]

omit [Fintype F] [DecidableEq F] [Group G] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W] [Fintype R]
    [DecidableEq R] [DecidableEq R'] in
/-- Every column of the distinguished-vertex syndrome belongs to the row
image generated by the second local matrix. -/
theorem verticalVertexSyndrome_column_mem_generatorImage
    (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) (r : R) :
    (fun b => verticalVertexSyndrome h' c v b r) ∈
      ProductExpansion.generatorImage h' := by
  rw [ProductExpansion.mem_generatorImage_iff]
  refine ⟨fun r' => localVertexMatrix c v r r', ?_⟩
  funext b
  simp [verticalVertexSyndrome, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply]

omit [DecidableEq F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype R] [DecidableEq R] [DecidableEq R'] in
/-- The parity check presenting the second generator image kills the entire
distinguished-vertex syndrome. -/
theorem generatorImageParityCheck_mul_verticalVertexSyndrome_eq_zero
    (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) :
    ProductExpansion.generatorImageParityCheck h' *
        verticalVertexSyndrome h' c v = 0 := by
  ext i r
  have hmem := verticalVertexSyndrome_column_mem_generatorImage h' c v r
  rw [← ProductExpansion.parityCheckCode_generatorImageParityCheck_carrier]
    at hmem
  change (Matrix.toLin' (ProductExpansion.generatorImageParityCheck h'))
      (fun b => verticalVertexSyndrome h' c v b r) = 0 at hmem
  rw [Matrix.toLin'_apply] at hmem
  have hir := congrFun hmem i
  simpa [Matrix.mulVec, Matrix.mul_apply, dotProduct] using hir

omit [Fintype F] [DecidableEq F] [Group G] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W] [Fintype R]
    [DecidableEq R] [DecidableEq R'] in
/-- Injectivity of the second generator map makes the vertex syndrome detect
every nonzero local coefficient block. -/
theorem verticalVertexSyndrome_ne_zero_of_localVertexMatrix_ne_zero
    (h' : Matrix R' W F)
    (hinjective : Function.Injective
      (fun u : Word F R' => h'.transpose.mulVec u))
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) (hv : localVertexMatrix c v ≠ 0) :
    verticalVertexSyndrome h' c v ≠ 0 := by
  intro hzero
  apply hv
  funext r r'
  have hrow : h'.transpose.mulVec (localVertexMatrix c v r) = 0 := by
    funext b
    have hentry := congrArg (fun z : Matrix W R F => z b r) hzero
    simpa [verticalVertexSyndrome, Matrix.mulVec, dotProduct,
      Matrix.transpose_apply] using hentry
  have hlocal : localVertexMatrix c v r = 0 := by
    apply hinjective
    simpa using hrow
  exact congrFun hlocal r'

/-- The source's rowwise coset-leader matrix at one vertex. The first local
check must have maximal row rank so that every vertex syndrome is realized. -/
noncomputable def localVertexCosetLeaderMatrix
    (h : Matrix R W F) (hRank : h.rank = Fintype.card R)
    (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) : Matrix W W F :=
  ProductExpansion.fullRowRankCosetLeaderMatrix h hRank
    (verticalVertexSyndrome h' c v)

omit [Group G] [Fintype G] [DecidableEq G]
    [DecidableEq R] [DecidableEq R'] in
/-- The local coset-leader matrix is an actual word of the product kernel
used by the PK22 expansion hypothesis. -/
theorem localVertexCosetLeaderMatrix_productKernel
    (h : Matrix R W F) (hRank : h.rank = Fintype.card R)
    (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) :
    ProductExpansion.ProductKernel h
      (ProductExpansion.generatorImageParityCheck h')
      (localVertexCosetLeaderMatrix h hRank h' c v) := by
  exact ProductExpansion.fullRowRankCosetLeaderMatrix_productKernel
    h (ProductExpansion.generatorImageParityCheck h') hRank
    (verticalVertexSyndrome h' c v)
    (generatorImageParityCheck_mul_verticalVertexSyndrome_eq_zero h' c v)

omit [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [DecidableEq W] [DecidableEq R] [DecidableEq R'] in
/-- At an active vertex, injectivity of the second generator map makes the
local product-kernel witness nonzero. -/
theorem localVertexCosetLeaderMatrix_ne_zero
    (h : Matrix R W F) (hRank : h.rank = Fintype.card R)
    (h' : Matrix R' W F)
    (hinjective : Function.Injective
      (fun u : Word F R' => h'.transpose.mulVec u))
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) (hv : localVertexMatrix c v ≠ 0) :
    localVertexCosetLeaderMatrix h hRank h' c v ≠ 0 := by
  intro hzero
  have hsyndrome := ProductExpansion.fullRowRankCosetLeaderMatrix_mul_transpose
    h hRank (verticalVertexSyndrome h' c v)
  have hzero' : ProductExpansion.fullRowRankCosetLeaderMatrix h hRank
      (verticalVertexSyndrome h' c v) = 0 := by
    simpa [localVertexCosetLeaderMatrix] using hzero
  rw [hzero', Matrix.zero_mul] at hsyndrome
  exact verticalVertexSyndrome_ne_zero_of_localVertexMatrix_ne_zero
    h' hinjective c v hv hsyndrome.symm

/-- Matrix form of the vertical-edge boundary equation. -/
theorem boundary1_verticalEdge_matrix_apply
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) (r : R) (b : W) :
    LiftedProduct.boundary1 (data label h h') c
        (verticalEdgeCoordinate label v r b) =
      (localFaceMatrix label c v * h.transpose) b r -
        verticalEndpointSyndrome label h' c v b r := by
  rw [boundary1_verticalEdge_apply]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, localFaceMatrix,
    verticalEndpointSyndrome, Finset.sum_neg_distrib, neg_mul]
  simp [mul_comm, sub_eq_add_neg]

/-- A global one-cycle restricts at every vertex to the exact row-syndrome
equation used to choose the PK22 coset-leader matrix. -/
theorem localFaceMatrix_mul_transpose_eq_verticalEndpointSyndrome
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hc : LiftedProduct.boundary1 (data label h h') c = 0)
    (v : VertexIndex G) :
    localFaceMatrix label c v * h.transpose =
      verticalEndpointSyndrome label h' c v := by
  ext b r
  have hedge := congrFun hc (verticalEdgeCoordinate label v r b)
  rw [boundary1_verticalEdge_matrix_apply] at hedge
  exact sub_eq_zero.mp hedge

/-- Difference between the face matrix and the rowwise coset-leader witness
attached to the distinguished vertex syndrome. -/
noncomputable def localFaceDifference
    (label : W → G) (h : Matrix R W F)
    (hRank : h.rank = Fintype.card R) (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) : Matrix W W F :=
  localFaceMatrix label c v - localVertexCosetLeaderMatrix h hRank h' c v

/-- Vertical directions whose opposite endpoint carries no active vertex
coefficient block. -/
noncomputable def verticalInactiveDirections (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) : Finset W := by
  classical
  exact Finset.univ.filter fun b =>
    localVertexMatrix c (verticalNeighbor label v b) = 0

/-- Horizontal directions whose opposite endpoint carries no active vertex
coefficient block. -/
noncomputable def horizontalInactiveDirections (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) : Finset W := by
  classical
  exact Finset.univ.filter fun a =>
    localVertexMatrix c (horizontalNeighbor label v a) = 0

/-- Inactive vertical directions on which the face row differs from its
chosen syndrome coset leader. -/
noncomputable def localHeavyDifferenceDirections
    (label : W → G) (h : Matrix R W F)
    (hRank : h.rank = Fintype.card R) (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) : Finset W := by
  classical
  exact (verticalInactiveDirections label c v).filter fun b =>
    ProductExpansion.row (localFaceDifference label h hRank h' c v) b ≠ 0

/-- Inactive vertical directions on which the face row agrees with its
chosen syndrome coset leader. -/
noncomputable def localAgreementDirections
    (label : W → G) (h : Matrix R W F)
    (hRank : h.rank = Fintype.card R) (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) : Finset W := by
  classical
  exact (verticalInactiveDirections label c v).filter fun b =>
    ProductExpansion.row (localFaceDifference label h hRank h' c v) b = 0

/-- A cycle's face/coset-leader difference has exactly the syndrome supplied
by the opposite vertical endpoints. -/
theorem localFaceDifference_mul_transpose_eq_verticalNeighborSyndrome
    (label : W → G) (h : Matrix R W F)
    (hRank : h.rank = Fintype.card R) (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hc : LiftedProduct.boundary1 (data label h h') c = 0)
    (v : VertexIndex G) :
    localFaceDifference label h hRank h' c v * h.transpose =
      verticalNeighborSyndrome label h' c v := by
  rw [localFaceDifference, Matrix.sub_mul,
    localFaceMatrix_mul_transpose_eq_verticalEndpointSyndrome
      label h h' c hc v,
    localVertexCosetLeaderMatrix,
    ProductExpansion.fullRowRankCosetLeaderMatrix_mul_transpose,
    verticalEndpointSyndrome_eq_add]
  simp

omit [Fintype F] [Fintype G] [DecidableEq G] [DecidableEq W]
    [DecidableEq R] [DecidableEq R'] in
/-- On an inactive vertical direction, the opposite-endpoint syndrome
vanishes. -/
theorem verticalNeighborSyndrome_row_eq_zero_of_mem_inactive
    (label : W → G) (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) (b : W)
    (hb : b ∈ verticalInactiveDirections label c v) :
    verticalNeighborSyndrome label h' c v b = 0 := by
  have hbzero : localVertexMatrix c (verticalNeighbor label v b) = 0 := by
    simpa [verticalInactiveDirections] using hb
  funext r
  simp [verticalNeighborSyndrome, hbzero]

/-- On every inactive direction, the face/coset-leader difference is a word
of the first local code. -/
theorem localFaceDifference_row_mem_parityCheckCode_of_mem_inactive
    (label : W → G) (h : Matrix R W F)
    (hRank : h.rank = Fintype.card R) (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hc : LiftedProduct.boundary1 (data label h h') c = 0)
    (v : VertexIndex G) (b : W)
    (hb : b ∈ verticalInactiveDirections label c v) :
    ProductExpansion.row (localFaceDifference label h hRank h' c v) b ∈
      (ProductExpansion.parityCheckCode h).carrier := by
  change (Matrix.toLin' h)
      (ProductExpansion.row (localFaceDifference label h hRank h' c v) b) = 0
  rw [Matrix.toLin'_apply]
  funext r
  have hmatrix :=
    localFaceDifference_mul_transpose_eq_verticalNeighborSyndrome
      label h hRank h' c hc v
  have hentry := congrArg (fun z : Matrix W R F => z b r) hmatrix
  have hneighbor := congrFun
    (verticalNeighborSyndrome_row_eq_zero_of_mem_inactive
      label h' c v b hb) r
  simpa [Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply,
    dotProduct, ProductExpansion.row, mul_comm, hneighbor] using hentry

omit [Fintype F] [Fintype G] [DecidableEq G]
    [DecidableEq R] [DecidableEq R'] in
/-- The heavy and agreement directions partition all inactive vertical
directions. -/
theorem verticalInactiveDirections_eq_heavy_union_agreement
    (label : W → G) (h : Matrix R W F)
    (hRank : h.rank = Fintype.card R) (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) :
    verticalInactiveDirections label c v =
      localHeavyDifferenceDirections label h hRank h' c v ∪
        localAgreementDirections label h hRank h' c v := by
  classical
  ext b
  by_cases hb : ProductExpansion.row
      (localFaceDifference label h hRank h' c v) b = 0 <;>
    simp [localHeavyDifferenceDirections, localAgreementDirections, hb]

omit [Fintype F] [Fintype G] [DecidableEq G] [DecidableEq W]
    [DecidableEq R] [DecidableEq R'] in
/-- Agreement directions are literally rows where the face matrix equals the
local product-kernel witness. -/
theorem localFaceMatrix_eq_localVertexCosetLeaderMatrix_of_mem_agreement
    (label : W → G) (h : Matrix R W F)
    (hRank : h.rank = Fintype.card R) (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) (b : W)
    (hb : b ∈ localAgreementDirections label h hRank h' c v) :
    ∀ a, localFaceMatrix label c v b a =
      localVertexCosetLeaderMatrix h hRank h' c v b a := by
  have hzero : ProductExpansion.row
      (localFaceDifference label h hRank h' c v) b = 0 := by
    exact (Finset.mem_filter.mp hb).2
  intro a
  have hentry := congrFun hzero a
  exact sub_eq_zero.mp (by
    simpa [ProductExpansion.row, localFaceDifference] using hentry)

omit [Fintype F] [Fintype G] [DecidableEq G]
    [DecidableEq W] [DecidableEq R] [DecidableEq R'] in
theorem localHeavyDifferenceDirections_subset_verticalInactiveDirections
    (label : W → G) (h : Matrix R W F)
    (hRank : h.rank = Fintype.card R) (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) :
    localHeavyDifferenceDirections label h hRank h' c v ⊆
      verticalInactiveDirections label c v :=
  Finset.filter_subset _ _

omit [Fintype F] [Fintype G] [DecidableEq G]
    [DecidableEq W] [DecidableEq R] [DecidableEq R'] in
theorem localAgreementDirections_subset_verticalInactiveDirections
    (label : W → G) (h : Matrix R W F)
    (hRank : h.rank = Fintype.card R) (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) :
    localAgreementDirections label h hRank h' c v ⊆
      verticalInactiveDirections label c v :=
  Finset.filter_subset _ _

/-- Every nonzero inactive difference row is heavy: its local-code distance
and the coset-leader inequality force the corresponding face row to carry at
least half that distance. -/
theorem localFaceMatrix_row_heavy_of_mem_heavyDifference
    (label : W → G) (h : Matrix R W F)
    (hRank : h.rank = Fintype.card R) (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hc : LiftedProduct.boundary1 (data label h h') c = 0)
    (d : Nat)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (v : VertexIndex G) (b : W)
    (hb : b ∈ localHeavyDifferenceDirections label h hRank h' c v) :
    d ≤ 2 * HammingWeight
      (ProductExpansion.row (localFaceMatrix label c v) b) := by
  have hbInactive : b ∈ verticalInactiveDirections label c v :=
    (Finset.mem_filter.mp hb).1
  have hdiffNonzero : ProductExpansion.row
      (localFaceDifference label h hRank h' c v) b ≠ 0 :=
    (Finset.mem_filter.mp hb).2
  have hdiffCode :=
    localFaceDifference_row_mem_parityCheckCode_of_mem_inactive
      label h hRank h' c hc v b hbInactive
  have hdiffHeavy := hDistance _ hdiffCode hdiffNonzero
  have hleader := ProductExpansion.fullRowRankCosetLeaderMatrix_isCosetLeader
    h hRank (verticalVertexSyndrome h' c v) b
  have hleaderBound := hleader.weight_le_add_codeword
    (ProductExpansion.row (localFaceDifference label h hRank h' c v) b)
    hdiffCode
  have hsum :
      ProductExpansion.row (localVertexCosetLeaderMatrix h hRank h' c v) b +
          ProductExpansion.row (localFaceDifference label h hRank h' c v) b =
        ProductExpansion.row (localFaceMatrix label c v) b := by
    funext a
    simp [ProductExpansion.row, localFaceDifference]
  rw [← localVertexCosetLeaderMatrix, hsum] at hleaderBound
  have htriangle := ProductExpansion.HammingWeight_sub_le
    (ProductExpansion.row (localFaceMatrix label c v) b)
    (ProductExpansion.row (localVertexCosetLeaderMatrix h hRank h' c v) b)
  have hdiffEq : ProductExpansion.row
      (localFaceDifference label h hRank h' c v) b =
        ProductExpansion.row (localFaceMatrix label c v) b -
          ProductExpansion.row
            (localVertexCosetLeaderMatrix h hRank h' c v) b := by
    rfl
  rw [hdiffEq] at hdiffHeavy
  omega

/-- Active local direction pairs in one face star. -/
noncomputable def localFaceSupport (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) : Finset (W × W) := by
  classical
  exact Finset.univ.filter (fun p => localFaceMatrix label c v p.1 p.2 ≠ 0)

omit [Field F] [Fintype F] [DecidableEq F] [Group G] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W] [Fintype R]
    [DecidableEq R] [Fintype R'] [DecidableEq R'] in
@[simp] theorem coordinateVertex_faceCoordinate (p : FaceIndex W G) :
    coordinateVertex (R := R) (R' := R') (faceCoordinate (R := R) (R' := R') p) = none :=
  rfl

omit [Field F] [Fintype F] [DecidableEq F] [Group G] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W] [Fintype R]
    [DecidableEq R] [Fintype R'] [DecidableEq R'] in
@[simp] theorem coordinateVertex_vertexCoordinate
    (v : VertexIndex G) (r : R) (r' : R') :
    coordinateVertex (W := W) (vertexCoordinate (W := W) v r r') = some v := by
  rcases v with ⟨⟨side, side'⟩, g⟩
  rfl

/-- Nonzero scalar face coefficients. -/
noncomputable def faceSupport
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) :
    Finset (FaceIndex W G) := by
  classical
  exact Finset.univ.filter (fun p => c (faceCoordinate (R := R) (R' := R') p) ≠ 0)

/-- Underlying vertices carrying at least one nonzero scalar coefficient. -/
noncomputable def vertexBlockSupport
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) :
    Finset (VertexIndex G) := by
  classical
  exact Finset.univ.filter (fun v =>
    ∃ r : R, ∃ r' : R', c (vertexCoordinate (W := W) v r r') ≠ 0)

omit [Fintype F] [Group G] [DecidableEq G]
    [Fintype W] [DecidableEq W] [DecidableEq R] [DecidableEq R'] in
/-- A vertex is active exactly when its local coefficient matrix is nonzero. -/
theorem mem_vertexBlockSupport_iff_localVertexMatrix_ne_zero
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) :
    v ∈ vertexBlockSupport c ↔ localVertexMatrix c v ≠ 0 := by
  classical
  simp only [vertexBlockSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨r, r', hnonzero⟩ hzero
    have hentry := congrFun (congrFun hzero r) r'
    exact hnonzero hentry
  · intro hmatrix
    by_contra hnone
    push Not at hnone
    apply hmatrix
    ext r r'
    exact hnone r r'

omit [Fintype F] [DecidableEq G] [DecidableEq W] [Fintype R]
    [DecidableEq R] [Fintype R'] [DecidableEq R'] in
/-- Local face support maps into the global active-face support. -/
theorem localFaceSupport_map_subset_faceSupport
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) :
    (localFaceSupport label c v).map (faceAtVertexEmbedding label v) ⊆
      faceSupport c := by
  intro p hp
  rw [Finset.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  change faceAtVertex label v q.2 q.1 ∈ faceSupport c
  simpa [localFaceSupport, localFaceMatrix, faceSupport]
    using (Finset.mem_filter.mp hq).2

omit [Fintype F] [Fintype G] [DecidableEq G] [DecidableEq W]
    [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R'] in
/-- The number of active faces in a star is the full-rectangle weight of its
local face matrix. -/
theorem card_localFaceSupport_eq_restrictedWeight
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) :
    (localFaceSupport label c v).card =
      ProductExpansion.restrictedWeight (localFaceMatrix label c v)
        Finset.univ Finset.univ := by
  classical
  unfold localFaceSupport ProductExpansion.restrictedWeight
  rw [Finset.card_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hzero : localFaceMatrix label c v a b = 0 <;> simp [hzero]

/-- PK22 block weight: scalar face weight plus nonzero vertex-fiber count. -/
noncomputable def blockWeight
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) : Nat :=
  (faceSupport c).card + (vertexBlockSupport c).card

/-- A selected nonzero scalar coordinate in every active vertex block. -/
noncomputable def vertexWitness
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : {v // v ∈ vertexBlockSupport c}) : R × R' := by
  classical
  have hv : ∃ r : R, ∃ r' : R',
      c (vertexCoordinate (W := W) v.1 r r') ≠ 0 := by
    simpa [vertexBlockSupport] using v.2
  exact ⟨Classical.choose hv, Classical.choose (Classical.choose_spec hv)⟩

omit [Fintype F] [Group G] [DecidableEq G] [Fintype W] [DecidableEq W]
    [DecidableEq R] [DecidableEq R'] in
/-- The chosen vertex-block witness is genuinely nonzero. -/
theorem vertexWitness_nonzero
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : {v // v ∈ vertexBlockSupport c}) :
    c (vertexCoordinate (W := W) v.1 (vertexWitness c v).1
      (vertexWitness c v).2) ≠ 0 := by
  classical
  have hv : ∃ r : R, ∃ r' : R',
      c (vertexCoordinate (W := W) v.1 r r') ≠ 0 := by
    simpa [vertexBlockSupport] using v.2
  exact Classical.choose_spec (Classical.choose_spec hv)

/-- Every active source block chooses a scalar coordinate in Hamming support. -/
noncomputable def blockSupportToHammingSupport
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) :
    Sum {p // p ∈ faceSupport c} {v // v ∈ vertexBlockSupport c} →
      {q // q ∈ hammingSupport c}
  | Sum.inl p => ⟨faceCoordinate (R := R) (R' := R') p.1, by
      simpa [faceSupport, hammingSupport] using p.2⟩
  | Sum.inr v =>
      ⟨vertexCoordinate (W := W) v.1 (vertexWitness c v).1
          (vertexWitness c v).2, by
        simpa [hammingSupport] using vertexWitness_nonzero c v⟩

omit [Fintype F] [Group G] [DecidableEq G] [DecidableEq W]
    [DecidableEq R] [DecidableEq R'] in
/-- Distinct source blocks choose distinct scalar coordinates. -/
theorem blockSupportToHammingSupport_injective
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) :
    Function.Injective (blockSupportToHammingSupport c) := by
  classical
  intro x y hxy
  cases x with
  | inl p =>
      cases y with
      | inl q =>
          apply congrArg Sum.inl
          apply Subtype.ext
          have hcoord := congrArg Subtype.val hxy
          exact Sum.inl.inj hcoord
      | inr q =>
          have hcoord := congrArg Subtype.val hxy
          cases hcoord
  | inr p =>
      cases y with
      | inl q =>
          have hcoord := congrArg Subtype.val hxy
          cases hcoord
      | inr q =>
          apply congrArg Sum.inr
          apply Subtype.ext
          have hcoord := congrArg Subtype.val hxy
          have hVertex := congrArg
            (coordinateVertex (R := R) (R' := R')) hcoord
          exact Option.some.inj hVertex

omit [Fintype F] [Group G] [DecidableEq G] [DecidableEq W]
    [DecidableEq R] [DecidableEq R'] in
/-- The source block weight never exceeds scalar Hamming weight. -/
theorem blockWeight_le_hammingWeight
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) :
    blockWeight c ≤ HammingWeight c := by
  classical
  have hCard := Fintype.card_le_of_injective
    (blockSupportToHammingSupport c)
    (blockSupportToHammingSupport_injective c)
  simpa [blockWeight, HammingWeight] using hCard

omit [Fintype F] [Group G] [DecidableEq G] [DecidableEq W]
    [DecidableEq R] [DecidableEq R'] in
/-- Zero block weight detects exactly the zero middle chain. -/
theorem blockWeight_eq_zero_iff
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) :
    blockWeight c = 0 ↔ c = 0 := by
  constructor
  · intro hWeight
    have hFaceCard : (faceSupport c).card = 0 := by
      unfold blockWeight at hWeight
      omega
    have hVertexCard : (vertexBlockSupport c).card = 0 := by
      unfold blockWeight at hWeight
      omega
    have hFace : faceSupport c = ∅ := Finset.card_eq_zero.mp hFaceCard
    have hVertex : vertexBlockSupport c = ∅ := Finset.card_eq_zero.mp hVertexCard
    funext q
    cases q with
    | inl p =>
        have hp : p ∉ faceSupport c := by simp [hFace]
        have hp' : ¬ c (faceCoordinate (R := R) (R' := R') p) ≠ 0 := by
          simpa [faceSupport] using hp
        exact not_ne_iff.mp hp'
    | inr p =>
        rcases p with ⟨⟨side, r⟩, ⟨side', r'⟩, g⟩
        let v : VertexIndex G := (side, side', g)
        have hv : v ∉ vertexBlockSupport c := by simp [hVertex]
        have hv' : ¬ ∃ a : R, ∃ b : R',
            c (vertexCoordinate (W := W) v a b) ≠ 0 := by
          simpa [vertexBlockSupport] using hv
        simpa [v, vertexCoordinate] using not_ne_iff.mp
          (not_exists.mp (not_exists.mp hv' r) r')
  · rintro rfl
    simp [blockWeight, faceSupport, vertexBlockSupport]

omit [Fintype F] [Group G] [DecidableEq G] [DecidableEq W]
    [DecidableEq R] [DecidableEq R'] in
/-- A nonzero middle chain has positive source block weight. -/
theorem blockWeight_pos_iff
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) :
    0 < blockWeight c ↔ c ≠ 0 := by
  rw [Nat.pos_iff_ne_zero, ne_eq, blockWeight_eq_zero_iff]

omit [Fintype F] [Group G] [DecidableEq R] [DecidableEq R'] in
/-- If two chains agree away from selected face and vertex blocks, a global
block-weight comparison bounds the old affected-face count by the new one
plus the number of affected vertex blocks. -/
theorem card_faceSupport_inter_le_of_blockWeight_le
    (c c' : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (S : Finset (FaceIndex W G)) (T : Finset (VertexIndex G))
    (hface : ∀ p, p ∉ S →
      c' (faceCoordinate (R := R) (R' := R') p) =
        c (faceCoordinate (R := R) (R' := R') p))
    (hvertex : ∀ v, v ∉ T → ∀ r r',
      c' (vertexCoordinate (W := W) v r r') =
        c (vertexCoordinate (W := W) v r r'))
    (hweight : blockWeight c ≤ blockWeight c') :
    (faceSupport c ∩ S).card ≤ (faceSupport c' ∩ S).card + T.card := by
  classical
  have hFaceOutside : faceSupport c \ S = faceSupport c' \ S := by
    ext p
    by_cases hp : p ∈ S
    · simp [hp]
    · simp [faceSupport, hp, hface p hp]
  have hVertexOutside :
      vertexBlockSupport c \ T = vertexBlockSupport c' \ T := by
    ext v
    by_cases hv : v ∈ T
    · simp [hv]
    · have heq : ∀ r r',
          c' (vertexCoordinate (W := W) v r r') =
            c (vertexCoordinate (W := W) v r r') :=
        hvertex v hv
      simp [vertexBlockSupport, hv, heq]
  have hVertexOld :
      (vertexBlockSupport c ∩ T).card ≤ T.card :=
    Finset.card_le_card (Finset.inter_subset_right)
  have hVertexNew :
      (vertexBlockSupport c' ∩ T).card ≤ T.card :=
    Finset.card_le_card (Finset.inter_subset_right)
  have hFaceSplitOld :=
    Finset.card_sdiff_add_card_inter (faceSupport c) S
  have hFaceSplitNew :=
    Finset.card_sdiff_add_card_inter (faceSupport c') S
  have hVertexSplitOld :=
    Finset.card_sdiff_add_card_inter (vertexBlockSupport c) T
  have hVertexSplitNew :=
    Finset.card_sdiff_add_card_inter (vertexBlockSupport c') T
  have hFaceOutsideCard := congrArg Finset.card hFaceOutside
  have hVertexOutsideCard := congrArg Finset.card hVertexOutside
  unfold blockWeight at hweight
  omega

/-- The Tanner lifted-product chain complex, named for the block-weight API. -/
noncomputable def chainComplex
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F) :=
  LiftedProduct.chainComplex (data label h g')

/-- Horizontal edge cells before expanding their R'-dimensional coefficient
fiber into scalar degree-two coordinates. -/
abbrev HorizontalEdgeIndex (W G : Type v) := W × Fin 2 × G

/-- Vertical edge cells before expanding their R-dimensional coefficient
fiber into scalar degree-zero coordinates. -/
abbrev VerticalEdgeIndex (W G : Type v) := Fin 2 × W × G

/-- The source-level horizontal edge in direction a incident to v. -/
def horizontalEdgeAtVertex (label : W → G) (v : VertexIndex G) (a : W) :
    HorizontalEdgeIndex W G :=
  match v with
  | (side, side', g) =>
      (a, side', g * (doubleCoverVoltage label side a)⁻¹)

/-- The source-level vertical edge in direction b incident to v. -/
def verticalEdgeAtVertex (label : W → G) (v : VertexIndex G) (b : W) :
    VerticalEdgeIndex W G :=
  match v with
  | (side, side', g) =>
      (side, b, (doubleCoverVoltage label side' b)⁻¹ * g)

/-- Vertical directions embed into the global faces in one horizontal column
of the star at v. -/
def horizontalFaceColumnEmbedding (label : W → G)
    (v : VertexIndex G) (a : W) : W ↪ FaceIndex W G where
  toFun b := faceAtVertex label v a b
  inj' := by
    intro b b' hbb
    exact congrArg (fun p : FaceIndex W G => p.2.1) hbb

/-- The global faces changed by a move on the horizontal edge (v,a). -/
noncomputable def horizontalFaceColumn (label : W → G)
    (v : VertexIndex G) (a : W) : Finset (FaceIndex W G) :=
  Finset.univ.map (horizontalFaceColumnEmbedding label v a)

/-- The two vertex blocks changed by a move on the horizontal edge (v,a). -/
noncomputable def horizontalVertexEndpoints (label : W → G)
    (v : VertexIndex G) (a : W) : Finset (VertexIndex G) :=
  {v, horizontalNeighbor label v a}

omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] [DecidableEq W] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
theorem mem_horizontalFaceColumn_iff
    (label : W → G) (v : VertexIndex G) (a : W) (p : FaceIndex W G) :
    p ∈ horizontalFaceColumn label v a ↔
      ∃ b, faceAtVertex label v a b = p := by
  classical
  constructor
  · intro hp
    obtain ⟨b, _hb, hbp⟩ := Finset.mem_map.mp hp
    exact ⟨b, hbp⟩
  · rintro ⟨b, rfl⟩
    exact Finset.mem_map.mpr ⟨b, Finset.mem_univ _, rfl⟩

omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [Fintype W] [DecidableEq W] [Fintype R]
    [DecidableEq R] [Fintype R'] [DecidableEq R'] in
theorem card_horizontalVertexEndpoints_le_two
    (label : W → G) (v : VertexIndex G) (a : W) :
    (horizontalVertexEndpoints label v a).card ≤ 2 := by
  unfold horizontalVertexEndpoints
  exact (Finset.card_insert_le v {horizontalNeighbor label v a}).trans_eq
    (by simp)

omit [Fintype F]
    [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R'] in
/-- Active global faces in one horizontal star column are counted by the
Hamming weight of the corresponding local matrix column. -/
theorem card_faceSupport_inter_horizontalFaceColumn
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) (a : W) :
    (faceSupport c ∩ horizontalFaceColumn label v a).card =
      HammingWeight
        (ProductExpansion.column (localFaceMatrix label c v) a) := by
  classical
  let S := hammingSupport
    (ProductExpansion.column (localFaceMatrix label c v) a)
  have hMap :
      S.map (horizontalFaceColumnEmbedding label v a) =
        faceSupport c ∩ horizontalFaceColumn label v a := by
    ext p
    constructor
    · intro hp
      obtain ⟨b, hbS, rfl⟩ := Finset.mem_map.mp hp
      have hbNonzero :
          c (faceCoordinate (R := R) (R' := R')
            (faceAtVertex label v a b)) ≠ 0 := by
        change b ∈ hammingSupport
          (ProductExpansion.column (localFaceMatrix label c v) a) at hbS
        exact (Finset.mem_filter.mp hbS).2
      apply Finset.mem_inter.mpr
      constructor
      · change faceAtVertex label v a b ∈ faceSupport c
        simpa [faceSupport] using hbNonzero
      · apply (mem_horizontalFaceColumn_iff label v a _).2
        exact ⟨b, rfl⟩
    · intro hp
      obtain ⟨hpFace, hpColumn⟩ := Finset.mem_inter.mp hp
      obtain ⟨b, rfl⟩ :=
        (mem_horizontalFaceColumn_iff label v a p).1 hpColumn
      apply Finset.mem_map.mpr
      refine ⟨b, ?_, rfl⟩
      change b ∈ hammingSupport
        (ProductExpansion.column (localFaceMatrix label c v) a)
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by
        simpa [faceSupport, ProductExpansion.column, localFaceMatrix] using hpFace⟩
  calc
    (faceSupport c ∩ horizontalFaceColumn label v a).card =
        (S.map (horizontalFaceColumnEmbedding label v a)).card := by
          rw [hMap]
    _ = S.card := by simp
    _ = HammingWeight
        (ProductExpansion.column (localFaceMatrix label c v) a) := rfl

/-- Put an arbitrary R'-vector on one horizontal edge fiber. -/
noncomputable def horizontalFiberChain
    (edge : HorizontalEdgeIndex W G) (u : Word F R') :
    Word F (LiftedProduct.C2Index W (Fin 2 × R') G) := by
  classical
  exact ∑ r', u r' • canonicalBasisWord
    (edge.1, (edge.2.1, r'), edge.2.2)

/-- Put an arbitrary R-vector on one vertical edge fiber. -/
noncomputable def verticalFiberCochain
    (edge : VerticalEdgeIndex W G) (u : Word F R) :
    Word F (LiftedProduct.C0Index (Fin 2 × R) W G) := by
  classical
  exact ∑ r, u r • canonicalBasisWord
    ((edge.1, r), edge.2.1, edge.2.2)

/-- Boundary moves supported on one complete horizontal coefficient fiber.
These are the source-level local moves, rather than only scalar basis moves. -/
noncomputable def horizontalFiberBoundaryMoves
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F) :
    Finset (Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) := by
  classical
  exact Finset.univ.image (fun p : HorizontalEdgeIndex W G × Word F R' =>
    (chainComplex label h g').boundary2 (horizontalFiberChain p.1 p.2))

/-- Coboundary moves supported on one complete vertical coefficient fiber. -/
noncomputable def verticalFiberCoboundaryMoves
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F) :
    Finset (Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) := by
  classical
  exact Finset.univ.image (fun p : VerticalEdgeIndex W G × Word F R =>
    wordLinearMapTranspose (chainComplex label h g').boundary1
      (verticalFiberCochain p.1 p.2))

/-- The boundary move obtained from a vector on the horizontal edge in
direction a at v. -/
noncomputable def horizontalFiberBoundaryMoveAtVertex
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (v : VertexIndex G) (a : W) (u : Word F R') :
    Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G) :=
  (chainComplex label h g').boundary2
    (horizontalFiberChain (horizontalEdgeAtVertex label v a) u)

omit [DecidableEq F] in
/-- A horizontal fiber move changes its incident face column by the codeword
generated by g'. -/
theorem horizontalFiberBoundaryMoveAtVertex_face_apply
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (v : VertexIndex G) (a a' b : W) (u : Word F R') :
    horizontalFiberBoundaryMoveAtVertex label h g' v a u
        (faceCoordinate (R := R) (R' := R')
          (faceAtVertex label v a' b)) =
      if a' = a then g'.transpose.mulVec u b else 0 := by
  classical
  unfold horizontalFiberBoundaryMoveAtVertex horizontalFiberChain chainComplex
  rw [LiftedProduct.chainComplex_boundary2]
  rw [map_sum]
  simp only [LinearMapClass.map_smul, Finset.sum_apply, Pi.smul_apply,
    LiftedProduct.boundary2_canonicalBasisWord_apply]
  rcases v with ⟨side, side', g⟩
  by_cases haa : a' = a
  · subst a'
    simp [horizontalEdgeAtVertex, faceCoordinate, faceAtVertex, data,
      doubleCoverTannerMatrix, LiftedProduct.starTranspose,
      LiftedProduct.groupConj, LiftedProduct.leftRegularMatrix,
      Matrix.mulVec, dotProduct, mul_comm, mul_assoc]
  · simp [horizontalEdgeAtVertex, faceCoordinate, faceAtVertex, data,
      haa]

omit [DecidableEq F] in
/-- At v itself, the same fiber move changes the vertex matrix by the outer
product of the local h-column and u. -/
theorem horizontalFiberBoundaryMoveAtVertex_vertex_apply
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (v : VertexIndex G) (a : W) (u : Word F R') (r : R) (r' : R') :
    horizontalFiberBoundaryMoveAtVertex label h g' v a u
        (vertexCoordinate (W := W) v r r') =
      h r a * u r' := by
  classical
  unfold horizontalFiberBoundaryMoveAtVertex horizontalFiberChain chainComplex
  rw [LiftedProduct.chainComplex_boundary2]
  rw [map_sum]
  simp only [LinearMapClass.map_smul, Finset.sum_apply, Pi.smul_apply,
    LiftedProduct.boundary2_canonicalBasisWord_apply]
  rcases v with ⟨side, side', g⟩
  simp [horizontalEdgeAtVertex, vertexCoordinate, data,
    doubleCoverTannerMatrix, LiftedProduct.rightRegularMatrix, mul_comm]

omit [DecidableEq F] in
/-- The other endpoint receives the same local outer-product update. -/
theorem horizontalFiberBoundaryMoveAtVertex_neighbor_apply
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (v : VertexIndex G) (a : W) (u : Word F R') (r : R) (r' : R') :
    horizontalFiberBoundaryMoveAtVertex label h g' v a u
        (vertexCoordinate (W := W) (horizontalNeighbor label v a) r r') =
      h r a * u r' := by
  classical
  unfold horizontalFiberBoundaryMoveAtVertex horizontalFiberChain chainComplex
  rw [LiftedProduct.chainComplex_boundary2]
  rw [map_sum]
  simp only [LinearMapClass.map_smul, Finset.sum_apply, Pi.smul_apply,
    LiftedProduct.boundary2_canonicalBasisWord_apply]
  rcases v with ⟨side, side', g⟩
  simp [horizontalEdgeAtVertex, horizontalNeighbor, vertexCoordinate, data,
    doubleCoverTannerMatrix, LiftedProduct.rightRegularMatrix, mul_comm,
    mul_assoc]

omit [DecidableEq F] in
/-- A horizontal fiber move vanishes on every face outside its one incident
column. -/
theorem horizontalFiberBoundaryMoveAtVertex_face_eq_zero_of_not_mem
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (v : VertexIndex G) (a : W) (u : Word F R') (p : FaceIndex W G)
    (hp : p ∉ horizontalFaceColumn label v a) :
    horizontalFiberBoundaryMoveAtVertex label h g' v a u
        (faceCoordinate (R := R) (R' := R') p) = 0 := by
  classical
  unfold horizontalFiberBoundaryMoveAtVertex horizontalFiberChain chainComplex
  rw [LiftedProduct.chainComplex_boundary2, map_sum]
  simp only [LinearMapClass.map_smul, Finset.sum_apply, Pi.smul_apply,
    LiftedProduct.boundary2_canonicalBasisWord_apply]
  apply Finset.sum_eq_zero
  intro r' _hr'
  rw [boundary2Matrix_eq_zero_of_not_mem_supportCover]
  simp
  intro hcover
  apply hp
  rcases v with ⟨side, side', g⟩
  rcases p with ⟨a', b, gp⟩
  simp [boundary2SupportCover, horizontalEdgeAtVertex, faceCoordinate] at hcover
  rcases hcover with ⟨rfl, rfl⟩
  apply (mem_horizontalFaceColumn_iff label
    (side, side', g) a (a, b,
      (doubleCoverVoltage label side' b)⁻¹ *
        (g * (doubleCoverVoltage label side a)⁻¹))).2
  exact ⟨b, by simp [faceAtVertex, mul_assoc]⟩

omit [DecidableEq F] in
/-- A horizontal fiber move vanishes on every vertex block except the two
endpoints of its edge. -/
theorem horizontalFiberBoundaryMoveAtVertex_vertex_eq_zero_of_not_mem
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (v x : VertexIndex G) (a : W) (u : Word F R') (r : R) (r' : R')
    (hx : x ∉ horizontalVertexEndpoints label v a) :
    horizontalFiberBoundaryMoveAtVertex label h g' v a u
        (vertexCoordinate (W := W) x r r') = 0 := by
  classical
  unfold horizontalFiberBoundaryMoveAtVertex horizontalFiberChain chainComplex
  rw [LiftedProduct.chainComplex_boundary2, map_sum]
  simp only [LinearMapClass.map_smul, Finset.sum_apply, Pi.smul_apply,
    LiftedProduct.boundary2_canonicalBasisWord_apply]
  apply Finset.sum_eq_zero
  intro s' _hs'
  rw [boundary2Matrix_eq_zero_of_not_mem_supportCover]
  simp
  intro hcover
  apply hx
  rcases v with ⟨side, side', g⟩
  rcases x with ⟨xside, xside', xg⟩
  simp [boundary2SupportCover, horizontalEdgeAtVertex, vertexCoordinate] at hcover
  rcases hcover with ⟨⟨hside', hs'⟩, hg⟩
  subst xside'
  subst s'
  subst xg
  by_cases hs : xside = side
  · subst xside
    simp [horizontalVertexEndpoints]
  · have hsOpp : xside = oppositeSide side := by
      fin_cases xside <;> fin_cases side <;> simp_all [oppositeSide]
    subst xside
    simp [horizontalVertexEndpoints, horizontalNeighbor, mul_assoc]

/-- Every explicit fiber move occurs in the finite source-local move set. -/
theorem horizontalFiberBoundaryMoveAtVertex_mem
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (v : VertexIndex G) (a : W) (u : Word F R') :
    horizontalFiberBoundaryMoveAtVertex label h g' v a u ∈
      horizontalFiberBoundaryMoves label h g' := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨(horizontalEdgeAtVertex label v a, u), Finset.mem_univ _, rfl⟩

/-- Source-level local minimality says that correcting any one face column by
a generated second-code word can decrease its face weight by at most the two
vertex blocks at the edge endpoints. -/
theorem faceColumn_weight_le_add_generator_of_fiberLocallyMinimal
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcLocal : LocallyMinimalDistance.IsLocallyMinimal blockWeight
      (horizontalFiberBoundaryMoves label h g') c)
    (v : VertexIndex G) (a : W) (u : Word F R') :
    HammingWeight
        (ProductExpansion.column (localFaceMatrix label c v) a) ≤
      HammingWeight
        (ProductExpansion.column (localFaceMatrix label c v) a +
          g'.transpose.mulVec u) + 2 := by
  let move := horizontalFiberBoundaryMoveAtVertex label h g' v a u
  have hWeight : blockWeight c ≤ blockWeight (c + move) :=
    hcLocal move (horizontalFiberBoundaryMoveAtVertex_mem
      label h g' v a u)
  have hAffected := card_faceSupport_inter_le_of_blockWeight_le
    c (c + move) (horizontalFaceColumn label v a)
      (horizontalVertexEndpoints label v a)
    (by
      intro p hp
      simp [move,
        horizontalFiberBoundaryMoveAtVertex_face_eq_zero_of_not_mem
          label h g' v a u p hp])
    (by
      intro x hx r r'
      simp [move,
        horizontalFiberBoundaryMoveAtVertex_vertex_eq_zero_of_not_mem
          label h g' v x a u r r' hx])
    hWeight
  rw [card_faceSupport_inter_horizontalFaceColumn,
    card_faceSupport_inter_horizontalFaceColumn] at hAffected
  have hColumn :
      ProductExpansion.column (localFaceMatrix label (c + move) v) a =
        ProductExpansion.column (localFaceMatrix label c v) a +
          g'.transpose.mulVec u := by
    funext b
    simp [ProductExpansion.column, localFaceMatrix, move,
      horizontalFiberBoundaryMoveAtVertex_face_apply]
  rw [hColumn] at hAffected
  have hEndpoints :=
    card_horizontalVertexEndpoints_le_two label v a
  omega

/-- The preceding column correction bound in the exact parity-check-code
interface consumed by the PK22 local-star minimality theorem. -/
theorem faceColumn_weight_le_add_codeword_of_fiberLocallyMinimal
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcLocal : LocallyMinimalDistance.IsLocallyMinimal blockWeight
      (horizontalFiberBoundaryMoves label h g') c)
    (v : VertexIndex G) (a : W) (delta : Word F W)
    (hdelta : delta ∈
      (ProductExpansion.parityCheckCode
        (ProductExpansion.generatorImageParityCheck g')).carrier) :
    HammingWeight
        (ProductExpansion.column (localFaceMatrix label c v) a) ≤
      HammingWeight
        (ProductExpansion.column (localFaceMatrix label c v) a + delta) + 2 := by
  rw [ProductExpansion.parityCheckCode_generatorImageParityCheck_carrier] at hdelta
  rw [ProductExpansion.mem_generatorImage_iff] at hdelta
  obtain ⟨u, hu⟩ := hdelta
  rw [← hu]
  exact faceColumn_weight_le_add_generator_of_fiberLocallyMinimal
    label h g' c hcLocal v a u

/-- The concrete Tanner geometry supplies the column-minimality hypothesis of
the PK22 local-star argument. Together with rowwise coset leaders, it makes
the selected product-kernel representative beta*w-minimal. -/
theorem cosetLeaderMatrix_isDeltaMinimal_of_fiberLocallyMinimal
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcLocal : LocallyMinimalDistance.IsLocallyMinimal blockWeight
      (horizontalFiberBoundaryMoves label h g') c)
    (v : VertexIndex G) (z : Matrix W R F) (x₀ : Matrix W W F)
    (hx₀ : ∀ i, h.mulVec (ProductExpansion.row x₀ i) = z i)
    (J₃ : Finset W) (m : Nat) (beta : ℝ)
    (hJ₃ : Fintype.card W - 2 * m ≤ J₃.card)
    (hAgree : ∀ i ∈ J₃, ∀ j,
      localFaceMatrix label c v i j =
        ProductExpansion.cosetLeaderMatrix h z x₀ hx₀ i j)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W) :
    ProductExpansion.IsDeltaMinimal h
      (ProductExpansion.generatorImageParityCheck g')
      (beta * Fintype.card W)
      (ProductExpansion.cosetLeaderMatrix h z x₀ hx₀) := by
  apply ProductExpansion.isDeltaMinimal_of_rowLeaders_and_faceColumnMinimal
    h (ProductExpansion.generatorImageParityCheck g')
    (localFaceMatrix label c v)
    (ProductExpansion.cosetLeaderMatrix h z x₀ hx₀)
    J₃ m beta hJ₃ hAgree
  · intro i codeword hcodeword
    exact (ProductExpansion.cosetLeaderMatrix_isCosetLeader
      h z x₀ hx₀ i).weight_le_add_codeword codeword hcodeword
  · intro j codeword hcodeword
    exact_mod_cast
      faceColumn_weight_le_add_codeword_of_fiberLocallyMinimal
        label h g' c hcLocal v j codeword hcodeword
  · exact hBudget

/-- The concrete active-vertex coset-leader witness is beta*w-minimal on the
large-agreement branch of the Tanner-star argument. -/
theorem localVertexCosetLeaderMatrix_isDeltaMinimal_of_fiberLocallyMinimal
    (label : W → G) (h : Matrix R W F)
    (hRank : h.rank = Fintype.card R) (g' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcLocal : LocallyMinimalDistance.IsLocallyMinimal blockWeight
      (horizontalFiberBoundaryMoves label h g') c)
    (v : VertexIndex G) (m : Nat) (beta : ℝ)
    (hJ₃ : Fintype.card W - 2 * m ≤
      (localAgreementDirections label h hRank g' c v).card)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W) :
    ProductExpansion.IsDeltaMinimal h
      (ProductExpansion.generatorImageParityCheck g')
      (beta * Fintype.card W)
      (localVertexCosetLeaderMatrix h hRank g' c v) := by
  apply ProductExpansion.isDeltaMinimal_of_rowLeaders_and_faceColumnMinimal
    h (ProductExpansion.generatorImageParityCheck g')
    (localFaceMatrix label c v)
    (localVertexCosetLeaderMatrix h hRank g' c v)
    (localAgreementDirections label h hRank g' c v)
    m beta hJ₃
  · intro i hi j
    exact localFaceMatrix_eq_localVertexCosetLeaderMatrix_of_mem_agreement
      label h hRank g' c v i hi j
  · intro i codeword hcodeword
    exact (ProductExpansion.fullRowRankCosetLeaderMatrix_isCosetLeader
      h hRank (verticalVertexSyndrome g' c v) i).weight_le_add_codeword
        codeword hcodeword
  · intro j codeword hcodeword
    exact_mod_cast
      faceColumn_weight_le_add_codeword_of_fiberLocallyMinimal
        label h g' c hcLocal v j codeword hcodeword
  · exact hBudget

/-- Concrete PK22 active-vertex star bound. Once both inactive-direction sets
are large, an active vertex supplies a nonzero product-kernel witness; the
J2/J3 dichotomy then forces at least s active faces in their rectangle. -/
theorem localStar_restrictedWeight_ge_of_fiberLocallyMinimal
    (label : W → G) (h : Matrix R W F)
    (hRank : h.rank = Fintype.card R) (g' : Matrix R' W F)
    (gInjective : Function.Injective
      (fun u : Word F R' => g'.transpose.mulVec u))
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcCycle : LiftedProduct.boundary1 (data label h g') c = 0)
    (hcLocal : LocallyMinimalDistance.IsLocallyMinimal blockWeight
      (horizontalFiberBoundaryMoves label h g') c)
    (v : VertexIndex G) (hv : localVertexMatrix c v ≠ 0)
    (d m s : Nat) (beta : ℝ)
    (hExpand : ProductExpansion.ProductExpanding h
      (ProductExpansion.generatorImageParityCheck g') s (2 * m) beta)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hHorizontalLarge : Fintype.card W - m <
      (horizontalInactiveDirections label c v).card)
    (hVerticalLarge : Fintype.card W - m <
      (verticalInactiveDirections label c v).card)
    (hDistanceScale : 4 * m ≤ d)
    (hRectangleScale : 4 * s ≤ m * d)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W) :
    s ≤ ProductExpansion.restrictedWeight (localFaceMatrix label c v)
      (verticalInactiveDirections label c v)
      (horizontalInactiveDirections label c v) := by
  apply ProductExpansion.localStar_restrictedWeight_ge
    h (ProductExpansion.generatorImageParityCheck g')
    (localFaceMatrix label c v)
    (localVertexCosetLeaderMatrix h hRank g' c v)
    (horizontalInactiveDirections label c v)
    (verticalInactiveDirections label c v)
    (localHeavyDifferenceDirections label h hRank g' c v)
    (localAgreementDirections label h hRank g' c v)
    d m s beta hExpand
  · exact localVertexCosetLeaderMatrix_productKernel h hRank g' c v
  · exact localVertexCosetLeaderMatrix_ne_zero
      h hRank g' gInjective c v hv
  · intro hJ₃
    exact localVertexCosetLeaderMatrix_isDeltaMinimal_of_fiberLocallyMinimal
      label h hRank g' c hcLocal v m beta hJ₃ hBudget
  · exact hHorizontalLarge
  · exact hVerticalLarge
  · intro b hb
    rw [← verticalInactiveDirections_eq_heavy_union_agreement
      label h hRank g' c v]
    exact hb
  · exact localHeavyDifferenceDirections_subset_verticalInactiveDirections
      label h hRank g' c v
  · exact localAgreementDirections_subset_verticalInactiveDirections
      label h hRank g' c v
  · intro b hb
    exact localFaceMatrix_row_heavy_of_mem_heavyDifference
      label h hRank g' c hcCycle d hDistance v b hb
  · exact hDistanceScale
  · exact hRectangleScale
  · intro b hb a _ha
    exact localFaceMatrix_eq_localVertexCosetLeaderMatrix_of_mem_agreement
      label h hRank g' c v b hb a

/-- Every horizontal fiber move is a genuine middle boundary. -/
theorem horizontalFiberBoundaryMoves_subset_middleBoundaryCode
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (m : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hm : m ∈ horizontalFiberBoundaryMoves label h g') :
    m ∈ (chainComplex label h g').middleBoundaryCode.carrier := by
  classical
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hm
  exact ((chainComplex label h g').mem_middleBoundaryCode_iff _).2
    ⟨horizontalFiberChain p.1 p.2, rfl⟩

/-- Every vertical fiber move is a genuine first coboundary. -/
theorem verticalFiberCoboundaryMoves_subset_firstCoboundaryCheckCode
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (m : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hm : m ∈ verticalFiberCoboundaryMoves label h g') :
    m ∈ (chainComplex label h g').firstCoboundaryCheckCode.carrier := by
  classical
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hm
  exact ((chainComplex label h g').mem_firstCoboundaryCheckCode_iff _).2
    ⟨verticalFiberCochain p.1 p.2, rfl⟩

/-- Bounds proved using scalar-coordinate local moves imply the same lower
bound on the attained algebraic CSS minimum distance. -/
theorem algebraicCSSMinimumDistance_ge_of_blockLocallyMinimal_bounds
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (lowerBound d : Nat)
    (hcycles : ∀ c,
      c ∈ (chainComplex label h g').middleCycleCode.carrier → c ≠ 0 →
      LocallyMinimalDistance.IsLocallyMinimal blockWeight
        (LocallyMinimalDistance.elementaryBoundaryMoves
          (chainComplex label h g')) c →
      lowerBound ≤ blockWeight c)
    (hcocycles : ∀ c,
      c ∈ (chainComplex label h g').middleCocycleCode.carrier → c ≠ 0 →
      LocallyMinimalDistance.IsLocallyMinimal blockWeight
        (LocallyMinimalDistance.elementaryCoboundaryMoves
          (chainComplex label h g')) c →
      lowerBound ≤ blockWeight c)
    (hminimum : AlgebraicCSSMinimumDistance
      (chainComplex label h g').firstCoboundaryCheckCode
      (chainComplex label h g').middleBoundaryCode d) :
    lowerBound ≤ d := by
  exact LocallyMinimalDistance.chainComplex_algebraicCSSMinimumDistance_ge_of_locallyMinimal_bounds
      (chainComplex label h g') blockWeight lowerBound d
      blockWeight_le_hammingWeight hcycles hcocycles hminimum

/-- Primal and dual local-minimal bounds for the source-level coefficient
fibers imply the same lower bound on the attained algebraic CSS minimum
distance. This is the local-minimality interface used by the PK22 proof. -/
theorem algebraicCSSMinimumDistance_ge_of_fiberLocallyMinimal_bounds
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (lowerBound d : Nat)
    (hcycles : ∀ c,
      c ∈ (chainComplex label h g').middleCycleCode.carrier → c ≠ 0 →
      LocallyMinimalDistance.IsLocallyMinimal blockWeight
        (horizontalFiberBoundaryMoves label h g') c →
      lowerBound ≤ blockWeight c)
    (hcocycles : ∀ c,
      c ∈ (chainComplex label h g').middleCocycleCode.carrier → c ≠ 0 →
      LocallyMinimalDistance.IsLocallyMinimal blockWeight
        (verticalFiberCoboundaryMoves label h g') c →
      lowerBound ≤ blockWeight c)
    (hminimum : AlgebraicCSSMinimumDistance
      (chainComplex label h g').firstCoboundaryCheckCode
      (chainComplex label h g').middleBoundaryCode d) :
    lowerBound ≤ d := by
  let K := chainComplex label h g'
  rcases hminimum with ⟨c, hc, hdistance, _⟩
  rw [← hdistance]
  rcases hc with hcX | hcZ
  · have hcCocycle : c ∈ K.middleCocycleCode.carrier := by
      rw [← K.middleBoundaryCode_dual_carrier_eq_middleCocycleCode]
      exact hcX.1
    have hBlock := LocallyMinimalDistance.weight_ge_of_locallyMinimal_cycle_bound
      blockWeight K.middleCocycleCode.carrier.toAddSubgroup
      K.firstCoboundaryCheckCode.carrier.toAddSubgroup
      (verticalFiberCoboundaryMoves label h g')
      K.firstCoboundaryCheckCode_le_middleCocycleCode
      (verticalFiberCoboundaryMoves_subset_firstCoboundaryCheckCode
        label h g') lowerBound hcocycles c hcCocycle hcX.2
    exact hBlock.trans (blockWeight_le_hammingWeight c)
  · have hcCycle : c ∈ K.middleCycleCode.carrier := by
      rw [← K.firstCoboundaryCheckCode_dual_carrier_eq_middleCycleCode]
      exact hcZ.1
    have hBlock := LocallyMinimalDistance.weight_ge_of_locallyMinimal_cycle_bound
      blockWeight K.middleCycleCode.carrier.toAddSubgroup
      K.middleBoundaryCode.carrier.toAddSubgroup
      (horizontalFiberBoundaryMoves label h g')
      K.middleBoundaryCode_le_middleCycleCode
      (horizontalFiberBoundaryMoves_subset_middleBoundaryCode
        label h g') lowerBound hcycles c hcCycle hcZ.2
    exact hBlock.trans (blockWeight_le_hammingWeight c)

end QEC.Coding.TannerLiftedProduct
