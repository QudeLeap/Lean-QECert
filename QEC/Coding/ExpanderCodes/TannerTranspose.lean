import QEC.Coding.ExpanderCodes.LiftedProductDuality
import QEC.Coding.ExpanderCodes.TannerGraphExpansion

/-!
# Transpose symmetry of the PK22 Tanner product

The dual-distance argument exchanges the horizontal and vertical Tanner
factors.  For a generator labelling closed under inversion, this exchange is
implemented on product vertices by swapping the two bipartite sides and
inverting the group coordinate.  Face directions are exchanged and relabelled
by the inverse-generator permutation.
-/

namespace QEC.Coding.TannerLiftedProduct

universe u v

variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']

/-- Swap the horizontal and vertical sides of a product vertex and invert its
group coordinate. -/
def transposeVertexEquiv : VertexIndex G ≃ VertexIndex G where
  toFun v := (v.2.1, v.1, v.2.2⁻¹)
  invFun v := (v.2.1, v.1, v.2.2⁻¹)
  left_inv v := by rcases v with ⟨i, j, g⟩; simp
  right_inv v := by rcases v with ⟨i, j, g⟩; simp

omit [Field F] [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G]
    [Fintype W] [DecidableEq W] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
@[simp] theorem transposeVertexEquiv_apply (v : VertexIndex G) :
    transposeVertexEquiv v = (v.2.1, v.1, v.2.2⁻¹) := rfl

/-- Exchange the two local directions of a face, relabel both by inverse
generators, and invert the group coordinate. -/
def transposeFaceEquiv (inverseDirection : W ≃ W) :
    FaceIndex W G ≃ FaceIndex W G where
  toFun p := (inverseDirection p.2.1, inverseDirection p.1, p.2.2⁻¹)
  invFun p :=
    (inverseDirection.symm p.2.1, inverseDirection.symm p.1, p.2.2⁻¹)
  left_inv p := by rcases p with ⟨a, b, g⟩; simp
  right_inv p := by rcases p with ⟨a, b, g⟩; simp

omit [Field F] [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G]
    [Fintype W] [DecidableEq W] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
@[simp] theorem transposeFaceEquiv_apply
    (inverseDirection : W ≃ W) (p : FaceIndex W G) :
    transposeFaceEquiv inverseDirection p =
      (inverseDirection p.2.1, inverseDirection p.1, p.2.2⁻¹) := rfl

/-- The middle-coordinate equivalence between a Tanner product and the
product with its two local matrices exchanged. -/
def transposeQubitEquiv (inverseDirection : W ≃ W) :
    LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G ≃
      LiftedProduct.QubitIndex (Fin 2 × R') W W (Fin 2 × R) G where
  toFun q :=
    match q with
    | Sum.inl p => Sum.inl (transposeFaceEquiv inverseDirection p)
    | Sum.inr ((side, r), (side', r'), g) =>
        Sum.inr ((side', r'), (side, r), g⁻¹)
  invFun q :=
    match q with
    | Sum.inl p => Sum.inl ((transposeFaceEquiv inverseDirection).symm p)
    | Sum.inr ((side', r'), (side, r), g) =>
        Sum.inr ((side, r), (side', r'), g⁻¹)
  left_inv q := by
    cases q with
    | inl p =>
        exact congrArg Sum.inl
          ((transposeFaceEquiv inverseDirection).symm_apply_apply p)
    | inr p => rcases p with ⟨⟨side, r⟩, ⟨side', r'⟩, g⟩; simp
  right_inv q := by
    cases q with
    | inl p => simp
    | inr p => rcases p with ⟨⟨side', r'⟩, ⟨side, r⟩, g⟩; simp

/-- Degree-two horizontal-edge coordinates become degree-zero vertical-edge
coordinates after transposition. -/
def transposeEdgeEquiv (inverseDirection : W ≃ W) :
    LiftedProduct.C2Index W (Fin 2 × R') G ≃
      LiftedProduct.C0Index (Fin 2 × R') W G where
  toFun e := (e.2.1, inverseDirection e.1, e.2.2⁻¹)
  invFun e := (inverseDirection.symm e.2.1, e.1, e.2.2⁻¹)
  left_inv e := by rcases e with ⟨a, sr', g⟩; simp
  right_inv e := by rcases e with ⟨sr', a, g⟩; simp

/-- Reindex matrix columns by a direction equivalence. -/
def reindexColumns (e : W ≃ W) (M : Matrix R W F) : Matrix R W F :=
  fun r j => M r (e.symm j)

omit [Fintype F] [Fintype G] [DecidableEq G] [Fintype W] [DecidableEq W]
    [Field F] [DecidableEq F] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
@[simp] theorem reindexColumns_apply (e : W ≃ W)
    (M : Matrix R W F) (r : R) (j : W) :
    reindexColumns e M r j = M r (e.symm j) := rfl

omit [Fintype F] [Fintype G] [DecidableEq G] [Fintype W] [DecidableEq W]
    [Field F] [DecidableEq F] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
@[simp] theorem reindexColumns_refl (M : Matrix R W F) :
    reindexColumns (Equiv.refl W) M = M := by
  rfl

omit [Fintype F] [Fintype G] [DecidableEq G] [Fintype W] [DecidableEq W]
    [Field F] [DecidableEq F] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
@[simp] theorem reindexColumns_symm_reindexColumns
    (e : W ≃ W) (M : Matrix R W F) :
    reindexColumns e.symm (reindexColumns e M) = M := by
  funext r j
  simp [reindexColumns]

/-- Face scalars are transported without a sign, while vertex-fiber scalars
pick up the Koszul sign from exchanging the two factors. -/
def transposeTannerWord (inverseDirection : W ≃ W)
    (z : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) :
    Word F
      (LiftedProduct.QubitIndex (Fin 2 × R') W W (Fin 2 × R) G) :=
  fun q =>
    match q with
    | Sum.inl _ => z ((transposeQubitEquiv inverseDirection).symm q)
    | Sum.inr _ => -z ((transposeQubitEquiv inverseDirection).symm q)

omit [Fintype F] [Fintype G] [DecidableEq G] [Fintype W] [DecidableEq W]
    [DecidableEq F] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
@[simp] theorem transposeTannerWord_face_apply
    (inverseDirection : W ≃ W)
    (z : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (p : FaceIndex W G) :
    transposeTannerWord inverseDirection z
      (faceCoordinate (R := R') (R' := R)
        (transposeFaceEquiv inverseDirection p)) =
      z (faceCoordinate (R := R) (R' := R') p) := by
  change z (Sum.inl ((transposeFaceEquiv inverseDirection).symm
    (transposeFaceEquiv inverseDirection p))) = z (Sum.inl p)
  rw [(transposeFaceEquiv inverseDirection).symm_apply_apply]

omit [Fintype F] [Fintype G] [DecidableEq G] [Fintype W] [DecidableEq W]
    [DecidableEq F] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
@[simp] theorem transposeTannerWord_vertex_apply
    (inverseDirection : W ≃ W)
    (z : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) (r : R) (r' : R') :
    transposeTannerWord inverseDirection z
      (vertexCoordinate (W := W) (transposeVertexEquiv v) r' r) =
      -z (vertexCoordinate (W := W) v r r') := by
  rcases v with ⟨side, side', g⟩
  simp [transposeTannerWord, transposeQubitEquiv, transposeVertexEquiv,
    vertexCoordinate]

/- Transposition carries the active-face support bijectively. -/
omit [Fintype F] [DecidableEq G] [DecidableEq W] [Fintype R]
    [DecidableEq R] [Fintype R'] [DecidableEq R'] in
theorem faceSupport_transposeTannerWord
    (inverseDirection : W ≃ W)
    (z : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) :
    faceSupport (transposeTannerWord inverseDirection z) =
      (faceSupport z).map (transposeFaceEquiv inverseDirection).toEmbedding := by
  classical
  ext p
  constructor
  · intro hp
    have hpNonzero :
        transposeTannerWord inverseDirection z
          (faceCoordinate (R := R') (R' := R) p) ≠ 0 := by
      simpa [faceSupport] using hp
    let q := (transposeFaceEquiv inverseDirection).symm p
    have hqNonzero :
        z (faceCoordinate (R := R) (R' := R') q) ≠ 0 := by
      have hpEq : p = transposeFaceEquiv inverseDirection q := by
        exact ((transposeFaceEquiv inverseDirection).apply_symm_apply p).symm
      rw [hpEq] at hpNonzero
      rw [transposeTannerWord_face_apply] at hpNonzero
      exact hpNonzero
    apply Finset.mem_map.mpr
    exact ⟨q, by simpa [faceSupport] using hqNonzero,
      (transposeFaceEquiv inverseDirection).apply_symm_apply p⟩
  · intro hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hp
    have hqNonzero :
        z (faceCoordinate (R := R) (R' := R') q) ≠ 0 := by
      simpa [faceSupport] using hq
    have htrans := transposeTannerWord_face_apply
      (F := F) (R := R) (R' := R') inverseDirection z q
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change transposeTannerWord inverseDirection z
      (faceCoordinate (R := R') (R' := R)
        (transposeFaceEquiv inverseDirection q)) ≠ 0
    rw [htrans]
    exact hqNonzero

/- Transposition carries the active vertex fibers bijectively. -/
omit [Fintype F] [DecidableEq G] [Fintype W] [DecidableEq W]
    [DecidableEq R] [DecidableEq R'] in
theorem vertexBlockSupport_transposeTannerWord
    (inverseDirection : W ≃ W)
    (z : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) :
    vertexBlockSupport (transposeTannerWord inverseDirection z) =
      (vertexBlockSupport z).map transposeVertexEquiv.toEmbedding := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨r', r, hnonzero⟩ := (Finset.mem_filter.mp hv).2
    let u := transposeVertexEquiv.symm v
    have huv : transposeVertexEquiv u = v :=
      transposeVertexEquiv.apply_symm_apply v
    have huNonzero :
        z (vertexCoordinate (W := W) u r r') ≠ 0 := by
      have htrans := transposeTannerWord_vertex_apply
        (F := F) (W := W) inverseDirection z u r r'
      rw [huv] at htrans
      rw [htrans] at hnonzero
      exact fun hzero => hnonzero (by simp [hzero])
    apply Finset.mem_map.mpr
    exact ⟨u, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ⟨r, r', huNonzero⟩⟩, huv⟩
  · intro hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hv
    obtain ⟨r, r', hnonzero⟩ := (Finset.mem_filter.mp hu).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ⟨r', r, ?_⟩⟩
    change transposeTannerWord inverseDirection z
      (vertexCoordinate (W := W) (transposeVertexEquiv u) r' r) ≠ 0
    rw [transposeTannerWord_vertex_apply]
    exact fun hzero => hnonzero (neg_eq_zero.mp hzero)

/- The source block weight is invariant under Tanner-factor transposition. -/
omit [Fintype F] [DecidableEq G] [DecidableEq W] [DecidableEq R]
    [DecidableEq R'] in
theorem blockWeight_transposeTannerWord
    (inverseDirection : W ≃ W)
    (z : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) :
    blockWeight (transposeTannerWord inverseDirection z) = blockWeight z := by
  rw [blockWeight, blockWeight, faceSupport_transposeTannerWord,
    vertexBlockSupport_transposeTannerWord]
  simp

omit [Fintype F] [DecidableEq G] [DecidableEq W]
    [DecidableEq R] [DecidableEq R'] in
/-- Signed Tanner-factor transposition preserves the full Hamming weight. -/
theorem HammingWeight_transposeTannerWord
    (inverseDirection : W ≃ W)
    (z : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) :
    HammingWeight (transposeTannerWord inverseDirection z) = HammingWeight z := by
  classical
  have hSupport :
      hammingSupport (transposeTannerWord inverseDirection z) =
        hammingSupport
          (fun q => z ((transposeQubitEquiv inverseDirection).symm q)) := by
    ext q
    simp only [hammingSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    cases q <;> simp [transposeTannerWord]
  rw [HammingWeight_eq_card_hammingSupport, hSupport]
  let e := transposeQubitEquiv (G := G) (R := R) (R' := R') inverseDirection
  have hMap :
      (hammingSupport (fun q => z (e.symm q))).map e.symm.toEmbedding =
        hammingSupport z := by
    ext q
    simp [hammingSupport]
  rw [HammingWeight_eq_card_hammingSupport, ← hMap, Finset.card_map]

omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W] [Fintype R]
    [DecidableEq R] [Fintype R'] [DecidableEq R'] in
/-- Horizontal neighbours become vertical neighbours under transposition. -/
theorem transposeVertexEquiv_horizontalNeighbor
    (label targetLabel : W → G) (inverseDirection : W ≃ W)
    (hInverse : ∀ a, targetLabel (inverseDirection a) = (label a)⁻¹)
    (v : VertexIndex G) (a : W) :
    transposeVertexEquiv (horizontalNeighbor label v a) =
      verticalNeighbor targetLabel
        (transposeVertexEquiv v) (inverseDirection a) := by
  rcases v with ⟨side, side', g⟩
  fin_cases side <;>
    simp [transposeVertexEquiv, horizontalNeighbor, verticalNeighbor,
      doubleCoverVoltage, oppositeSide, hInverse]

omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W] [Fintype R]
    [DecidableEq R] [Fintype R'] [DecidableEq R'] in
/-- Vertical neighbours become horizontal neighbours under transposition. -/
theorem transposeVertexEquiv_verticalNeighbor
    (label targetLabel : W → G) (inverseDirection : W ≃ W)
    (hInverse : ∀ a, targetLabel (inverseDirection a) = (label a)⁻¹)
    (v : VertexIndex G) (b : W) :
    transposeVertexEquiv (verticalNeighbor label v b) =
      horizontalNeighbor targetLabel
        (transposeVertexEquiv v) (inverseDirection b) := by
  rcases v with ⟨side, side', g⟩
  fin_cases side' <;>
    simp [transposeVertexEquiv, horizontalNeighbor, verticalNeighbor,
      doubleCoverVoltage, oppositeSide, hInverse]

omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W] [Fintype R]
    [DecidableEq R] [Fintype R'] [DecidableEq R'] in
/-- The face incident to a vertex is carried to the face with exchanged local
directions at the transposed vertex. -/
theorem transposeFaceEquiv_faceAtVertex
    (label targetLabel : W → G) (inverseDirection : W ≃ W)
    (hInverse : ∀ a, targetLabel (inverseDirection a) = (label a)⁻¹)
    (v : VertexIndex G) (a b : W) :
    transposeFaceEquiv inverseDirection (faceAtVertex label v a b) =
      faceAtVertex targetLabel (transposeVertexEquiv v)
        (inverseDirection b) (inverseDirection a) := by
  rcases v with ⟨side, side', g⟩
  fin_cases side <;> fin_cases side' <;>
    simp [transposeFaceEquiv, transposeVertexEquiv, faceAtVertex,
      doubleCoverVoltage, hInverse, mul_assoc]

omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W] [Fintype R]
    [DecidableEq R] [Fintype R'] [DecidableEq R'] in
/-- Every horizontal endpoint vertex is carried to the corresponding vertical
endpoint vertex in the exchanged product. -/
theorem transposeVertexEquiv_horizontalEndpoint
    (label targetLabel : W → G) (inverseDirection : W ≃ W)
    (hInverse : ∀ a, targetLabel (inverseDirection a) = (label a)⁻¹)
    (v : VertexIndex G) (a : W) (endpointSide : Fin 2) :
    transposeVertexEquiv
        (match v with
        | (side, side', g) =>
            (endpointSide, side',
              g * (doubleCoverVoltage label side a)⁻¹ *
                doubleCoverVoltage label endpointSide a)) =
      (match transposeVertexEquiv v with
      | (side', side, g) =>
          (side', endpointSide,
            doubleCoverVoltage targetLabel endpointSide (inverseDirection a) *
              (doubleCoverVoltage targetLabel side (inverseDirection a))⁻¹ * g)) := by
  rcases v with ⟨side, side', g⟩
  fin_cases side <;> fin_cases endpointSide <;>
    simp [transposeVertexEquiv, doubleCoverVoltage, hInverse, mul_assoc]

/-- The transpose of the second boundary is the horizontal-edge equation:
one complete face row plus the two endpoint vertex fibers. -/
theorem transpose_boundary2_horizontalEdge_apply
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (z : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) (a : W) (r' : R') :
    wordLinearMapTranspose (LiftedProduct.boundary2 (data label h h')) z
        (horizontalEdgeCoordinate label v a r') =
      (∑ b, h' r' b *
        z (faceCoordinate (R := R) (R' := R')
          (faceAtVertex label v a b))) +
      ∑ endpoint : Fin 2 × R,
        h endpoint.2 a *
          z (horizontalEndpointCoordinate label v a
            endpoint.1 endpoint.2 r') := by
  classical
  rw [LiftedProduct.boundary2,
    QEC.Coding.wordLinearMapTranspose_toLin'_apply]
  let c2 := horizontalEdgeCoordinate label v a r'
  have hRestrict :
      (∑ q,
          z q * LiftedProduct.boundary2Matrix (data label h h') q c2) =
        ∑ q ∈ boundary2SupportCover label h h' c2,
          z q * LiftedProduct.boundary2Matrix (data label h h') q c2 := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro q _hqUniv hqCover
    rw [boundary2Matrix_eq_zero_of_not_mem_supportCover
      label h h' q c2 hqCover, mul_zero]
  rw [hRestrict]
  rcases v with ⟨side, side', g⟩
  unfold boundary2SupportCover
  dsimp only
  rw [Finset.sum_union]
  · rw [Finset.sum_map, Finset.sum_map]
    simp [c2, horizontalEdgeCoordinate, horizontalEndpointCoordinate,
      faceCoordinate, faceAtVertex, vertexCoordinate, data,
      doubleCoverTannerMatrix, LiftedProduct.starTranspose,
      LiftedProduct.groupConj, LiftedProduct.leftRegularMatrix,
      LiftedProduct.rightRegularMatrix, mul_comm, mul_assoc]
  · simp [Finset.disjoint_left]

/-- Exchanging the Tanner factors intertwines the original second coboundary
with the first boundary of the exchanged product. -/
theorem boundary1_transposeTannerWord_apply
    (label targetLabel : W → G) (inverseDirection : W ≃ W)
    (hInverse : ∀ a, targetLabel (inverseDirection a) = (label a)⁻¹)
    (h : Matrix R W F) (h' : Matrix R' W F)
    (z : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (c2 : LiftedProduct.C2Index W (Fin 2 × R') G) :
    LiftedProduct.boundary1
        (data targetLabel (reindexColumns inverseDirection h')
          (reindexColumns inverseDirection h))
        (transposeTannerWord inverseDirection z)
        (transposeEdgeEquiv inverseDirection c2) =
      wordLinearMapTranspose (LiftedProduct.boundary2 (data label h h')) z c2 := by
  classical
  rcases c2 with ⟨a, ⟨side', r'⟩, g⟩
  let v : VertexIndex G := (0, side', g)
  have hHorizontal :
      horizontalEdgeCoordinate label v a r' = (a, (side', r'), g) := by
    simp [v, horizontalEdgeCoordinate, doubleCoverVoltage]
  have hVertical :
      verticalEdgeCoordinate targetLabel (transposeVertexEquiv v) r'
          (inverseDirection a) =
        ((side', r'), inverseDirection a, g⁻¹) := by
    simp [v, transposeVertexEquiv, verticalEdgeCoordinate,
      doubleCoverVoltage]
  change LiftedProduct.boundary1
      (data targetLabel (reindexColumns inverseDirection h')
        (reindexColumns inverseDirection h))
      (transposeTannerWord inverseDirection z)
      ((side', r'), inverseDirection a, g⁻¹) =
    wordLinearMapTranspose (LiftedProduct.boundary2 (data label h h')) z
      (a, (side', r'), g)
  rw [← hVertical, ← hHorizontal,
    boundary1_verticalEdge_apply,
    transpose_boundary2_horizontalEdge_apply]
  congr 1
  · apply Fintype.sum_equiv inverseDirection.symm
    intro b
    rw [reindexColumns_apply]
    have hFace :
        transposeFaceEquiv inverseDirection
            (faceAtVertex label v a (inverseDirection.symm b)) =
          faceAtVertex targetLabel (transposeVertexEquiv v) b
            (inverseDirection a) := by
      simpa using transposeFaceEquiv_faceAtVertex
        label targetLabel inverseDirection hInverse
        v a (inverseDirection.symm b)
    rw [← hFace, transposeTannerWord_face_apply]
  · apply Fintype.sum_congr
    intro endpoint
    have hEndpoint :
        verticalEndpointCoordinate targetLabel (transposeVertexEquiv v) r'
            (inverseDirection a) endpoint.1 endpoint.2 =
          vertexCoordinate (W := W)
            (transposeVertexEquiv
              (match v with
              | (side, side', g) =>
                  (endpoint.1, side',
                    g * (doubleCoverVoltage label side a)⁻¹ *
                      doubleCoverVoltage label endpoint.1 a)))
            r' endpoint.2 := by
      rw [transposeVertexEquiv_horizontalEndpoint
        label targetLabel inverseDirection hInverse v a endpoint.1]
      rcases v with ⟨side, side'', gv⟩
      simp [verticalEndpointCoordinate, vertexCoordinate,
        transposeVertexEquiv]
    rw [reindexColumns_apply]
    simp only [Equiv.symm_apply_apply, hEndpoint]
    rw [transposeTannerWord_vertex_apply]
    rcases v with ⟨side, side'', gv⟩
    simp [horizontalEndpointCoordinate, vertexCoordinate]

/-- An original Tanner cocycle becomes a cycle for the product with exchanged
and inverse-direction-reindexed local matrices. -/
theorem transposeTannerWord_mem_middleCycleCode_of_mem_middleCocycleCode
    (label targetLabel : W → G) (inverseDirection : W ≃ W)
    (hInverse : ∀ a, targetLabel (inverseDirection a) = (label a)⁻¹)
    (h : Matrix R W F) (h' : Matrix R' W F)
    (z : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hz : z ∈ (chainComplex label h h').middleCocycleCode.carrier) :
    transposeTannerWord inverseDirection z ∈
      (chainComplex targetLabel (reindexColumns inverseDirection h')
        (reindexColumns inverseDirection h)).middleCycleCode.carrier := by
  rw [(chainComplex targetLabel (reindexColumns inverseDirection h')
    (reindexColumns inverseDirection h)).mem_middleCycleCode_iff]
  funext c0
  obtain ⟨c2, rfl⟩ := (transposeEdgeEquiv inverseDirection).surjective c0
  rw [chainComplex, LiftedProduct.chainComplex_boundary1,
    boundary1_transposeTannerWord_apply
      label targetLabel inverseDirection hInverse h h']
  exact congrFun
    (((chainComplex label h h').mem_middleCocycleCode_iff z).1 hz) c2

omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W] [Fintype R]
    [DecidableEq R] [Fintype R'] [DecidableEq R'] in
theorem inverseLabels_symm
    (label targetLabel : W → G) (inverseDirection : W ≃ W)
    (hInverse : ∀ a, targetLabel (inverseDirection a) = (label a)⁻¹) :
    ∀ b, label (inverseDirection.symm b) = (targetLabel b)⁻¹ := by
  intro b
  have h := congrArg (fun g : G => g⁻¹)
    (hInverse (inverseDirection.symm b))
  simpa using h.symm

/- Applying the inverse-direction transpose returns the original word. -/
omit [Fintype F] [Fintype G] [DecidableEq G] [Fintype W] [DecidableEq W]
    [DecidableEq F] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
theorem transposeTannerWord_symm_transposeTannerWord
    (inverseDirection : W ≃ W)
    (z : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) :
    transposeTannerWord inverseDirection.symm
        (transposeTannerWord inverseDirection z) = z := by
  funext q
  cases q with
  | inl p =>
      rcases p with ⟨a, b, g⟩
      simp [transposeTannerWord, transposeQubitEquiv, transposeFaceEquiv]
  | inr p =>
      rcases p with ⟨⟨side, r⟩, ⟨side', r'⟩, g⟩
      simp [transposeTannerWord, transposeQubitEquiv]

/- Transposition respects addition. -/
omit [Fintype F] [Fintype G] [DecidableEq G] [Fintype W] [DecidableEq W]
    [DecidableEq F] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
theorem transposeTannerWord_add
    (inverseDirection : W ≃ W)
    (z z' : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) :
    transposeTannerWord inverseDirection (z + z') =
      transposeTannerWord inverseDirection z +
        transposeTannerWord inverseDirection z' := by
  funext q
  cases q with
  | inl _ => simp [transposeTannerWord]
  | inr _ => simp [transposeTannerWord]; abel

/- The signed coordinate transpose is self-adjoint after replacing the
direction equivalence by its inverse. -/
omit [Fintype F] [DecidableEq F] [DecidableEq G] [DecidableEq W]
    [DecidableEq R] [DecidableEq R'] in
theorem wordPairing_transposeTannerWord
    (inverseDirection : W ≃ W)
    (z : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (y : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R') W W (Fin 2 × R) G)) :
    wordPairing (transposeTannerWord inverseDirection z) y =
      wordPairing z (transposeTannerWord inverseDirection.symm y) := by
  classical
  unfold wordPairing dotProduct
  apply Fintype.sum_equiv (transposeQubitEquiv inverseDirection).symm
  intro q
  cases q with
  | inl p =>
      rcases p with ⟨a, b, g⟩
      simp [transposeTannerWord, transposeQubitEquiv, transposeFaceEquiv]
  | inr p =>
      rcases p with ⟨⟨side', r'⟩, ⟨side, r⟩, g⟩
      simp [transposeTannerWord, transposeQubitEquiv]

/- Transport a degree-zero word to the degree-two coordinates of the
exchanged Tanner product. -/
def transposeC0Word (inverseDirection : W ≃ W)
    (x : Word F (LiftedProduct.C0Index (Fin 2 × R) W G)) :
    Word F (LiftedProduct.C2Index W (Fin 2 × R) G) :=
  fun c2 => x (transposeEdgeEquiv inverseDirection.symm c2)

/- A vertical edge becomes a horizontal edge of the exchanged product. -/
def transposeVerticalEdge (inverseDirection : W ≃ W)
    (edge : VerticalEdgeIndex W G) : HorizontalEdgeIndex W G :=
  (inverseDirection edge.2.1, edge.1, edge.2.2⁻¹)

/- The inverse transport from exchanged horizontal edges to original
vertical edges. -/
def untransposeHorizontalEdge (inverseDirection : W ≃ W)
    (edge : HorizontalEdgeIndex W G) : VerticalEdgeIndex W G :=
  (edge.2.1, inverseDirection.symm edge.1, edge.2.2⁻¹)

omit [Field F] [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G]
    [Fintype W] [DecidableEq W] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
@[simp] theorem transposeVerticalEdge_untransposeHorizontalEdge
    (inverseDirection : W ≃ W) (edge : HorizontalEdgeIndex W G) :
    transposeVerticalEdge inverseDirection
      (untransposeHorizontalEdge inverseDirection edge) = edge := by
  rcases edge with ⟨a, side, g⟩
  simp [transposeVerticalEdge, untransposeHorizontalEdge]

omit [Fintype F] [DecidableEq F] [Fintype G] [Fintype W]
    [DecidableEq W] [DecidableEq R] [Fintype R'] [DecidableEq R'] in
theorem transposeC0Word_verticalFiberCochain
    (inverseDirection : W ≃ W) (edge : VerticalEdgeIndex W G)
    (u : Word F R) :
    transposeC0Word inverseDirection (verticalFiberCochain edge u) =
      horizontalFiberChain (transposeVerticalEdge inverseDirection edge) u := by
  classical
  funext c2
  rcases edge with ⟨side, b, g⟩
  rcases c2 with ⟨a, ⟨side', r⟩, g'⟩
  by_cases hside : side = side'
  · by_cases hdirection : inverseDirection b = a
    · by_cases hgroup : g⁻¹ = g'
      · subst side'
        subst a
        subst g'
        simp [transposeC0Word, transposeEdgeEquiv, transposeVerticalEdge,
          verticalFiberCochain, horizontalFiberChain, canonicalBasisWord,
          Finset.sum_apply, Pi.smul_apply]
        rw [Fintype.sum_eq_single r (by
          intro x hx
          have hcoord : ((side, r), b, g) ≠ ((side, x), b, g) := by
            intro h
            apply hx
            exact (congrArg (fun t => t.1.2) h).symm
          simp [hcoord])]
        rw [Fintype.sum_eq_single r (by
          intro x hx
          have hcoord :
              (inverseDirection b, (side, r), g⁻¹) ≠
                (inverseDirection b, (side, x), g⁻¹) := by
            intro h
            apply hx
            exact (congrArg (fun t => t.2.1.2) h).symm
          simp [hcoord])]
        simp
      · have hg : g ≠ g'⁻¹ := by
          intro heq
          apply hgroup
          have hinv := congrArg (fun x : G => x⁻¹) heq
          simpa using hinv
        simp [transposeC0Word, transposeEdgeEquiv, transposeVerticalEdge,
          verticalFiberCochain, horizontalFiberChain, canonicalBasisWord,
          hside, hdirection, hgroup, hg]
    · have hb : b ≠ inverseDirection.symm a := by
        intro heq
        apply hdirection
        rw [heq]
        simp
      simp [transposeC0Word, transposeEdgeEquiv, transposeVerticalEdge,
        verticalFiberCochain, horizontalFiberChain, canonicalBasisWord,
        hside, hdirection, hb]
  · simp [transposeC0Word, transposeEdgeEquiv, transposeVerticalEdge,
      verticalFiberCochain, horizontalFiberChain, canonicalBasisWord, hside]

omit [Fintype F] [DecidableEq F] [DecidableEq G] [DecidableEq W]
    [DecidableEq R] [Fintype R'] [DecidableEq R'] in
theorem wordPairing_transposeC0Word
    (inverseDirection : W ≃ W)
    (x : Word F (LiftedProduct.C0Index (Fin 2 × R) W G))
    (y : Word F (LiftedProduct.C2Index W (Fin 2 × R) G)) :
    wordPairing (transposeC0Word inverseDirection x) y =
      wordPairing x
        (fun c0 => y ((transposeEdgeEquiv inverseDirection.symm).symm c0)) := by
  classical
  unfold wordPairing dotProduct transposeC0Word
  apply Fintype.sum_equiv (transposeEdgeEquiv inverseDirection.symm)
  intro c2
  simp

/- Transposed degree-zero words generate exactly the degree-two boundaries
of the exchanged Tanner product. -/
theorem boundary2_transposeC0Word
    (label targetLabel : W → G) (inverseDirection : W ≃ W)
    (hInverse : ∀ a, targetLabel (inverseDirection a) = (label a)⁻¹)
    (h : Matrix R W F) (h' : Matrix R' W F)
    (x : Word F (LiftedProduct.C0Index (Fin 2 × R) W G)) :
    LiftedProduct.boundary2
        (data targetLabel (reindexColumns inverseDirection h')
          (reindexColumns inverseDirection h))
        (transposeC0Word inverseDirection x) =
      transposeTannerWord inverseDirection
        (wordLinearMapTranspose (LiftedProduct.boundary1 (data label h h')) x) := by
  classical
  rw [← sub_eq_zero]
  apply (wordPairing_nondegenerate (F := F)).right
  intro y
  have hInverseSymm := inverseLabels_symm
    label targetLabel inverseDirection hInverse
  have hCoordinate :
      (fun c0 =>
        wordLinearMapTranspose
          (LiftedProduct.boundary2
            (data targetLabel (reindexColumns inverseDirection h')
              (reindexColumns inverseDirection h))) y
          ((transposeEdgeEquiv inverseDirection.symm).symm c0)) =
        LiftedProduct.boundary1 (data label h h')
          (transposeTannerWord inverseDirection.symm y) := by
    funext c0
    obtain ⟨c2, rfl⟩ :=
      (transposeEdgeEquiv inverseDirection.symm).surjective c0
    simp only [Equiv.symm_apply_apply]
    symm
    simpa using boundary1_transposeTannerWord_apply
      targetLabel label inverseDirection.symm
      hInverseSymm (reindexColumns inverseDirection h')
      (reindexColumns inverseDirection h) y c2
  have hPair :
      wordPairing y
          (LiftedProduct.boundary2
            (data targetLabel (reindexColumns inverseDirection h')
              (reindexColumns inverseDirection h))
            (transposeC0Word inverseDirection x)) =
        wordPairing y
          (transposeTannerWord inverseDirection
            (wordLinearMapTranspose
              (LiftedProduct.boundary1 (data label h h')) x)) := by
    calc
      wordPairing y
          (LiftedProduct.boundary2
            (data targetLabel (reindexColumns inverseDirection h')
              (reindexColumns inverseDirection h))
            (transposeC0Word inverseDirection x)) =
          wordPairing
            (wordLinearMapTranspose
              (LiftedProduct.boundary2
                (data targetLabel (reindexColumns inverseDirection h')
                  (reindexColumns inverseDirection h))) y)
            (transposeC0Word inverseDirection x) := by
              exact (wordPairing_wordLinearMapTranspose
                (LiftedProduct.boundary2
                  (data targetLabel (reindexColumns inverseDirection h')
                    (reindexColumns inverseDirection h))) y
                (transposeC0Word inverseDirection x)).symm
      _ = wordPairing (transposeC0Word inverseDirection x)
            (wordLinearMapTranspose
              (LiftedProduct.boundary2
                (data targetLabel (reindexColumns inverseDirection h')
                  (reindexColumns inverseDirection h))) y) := by
              simp [wordPairing_apply, dotProduct_comm]
      _ = wordPairing x
            (fun c0 =>
              wordLinearMapTranspose
                (LiftedProduct.boundary2
                  (data targetLabel (reindexColumns inverseDirection h')
                    (reindexColumns inverseDirection h))) y
                ((transposeEdgeEquiv inverseDirection.symm).symm c0)) :=
              wordPairing_transposeC0Word inverseDirection x _
      _ = wordPairing x
            (LiftedProduct.boundary1 (data label h h')
              (transposeTannerWord inverseDirection.symm y)) := by
              rw [hCoordinate]
      _ = wordPairing
            (wordLinearMapTranspose
              (LiftedProduct.boundary1 (data label h h')) x)
            (transposeTannerWord inverseDirection.symm y) := by
              exact (wordPairing_wordLinearMapTranspose
                (LiftedProduct.boundary1 (data label h h')) x
                (transposeTannerWord inverseDirection.symm y)).symm
      _ = wordPairing
            (transposeTannerWord inverseDirection
              (wordLinearMapTranspose
                (LiftedProduct.boundary1 (data label h h')) x)) y := by
              exact (wordPairing_transposeTannerWord inverseDirection _ y).symm
      _ = wordPairing y
            (transposeTannerWord inverseDirection
              (wordLinearMapTranspose
                (LiftedProduct.boundary1 (data label h h')) x)) := by
              simp [wordPairing_apply, dotProduct_comm]
  simpa [wordPairing_apply, dotProduct_sub] using sub_eq_zero.mpr hPair

/- A vertical coboundary fiber move becomes a horizontal boundary fiber move
for the exchanged Tanner product. -/
theorem transposeTannerWord_verticalFiberCoboundaryMove
    (label targetLabel : W → G) (inverseDirection : W ≃ W)
    (hInverse : ∀ a, targetLabel (inverseDirection a) = (label a)⁻¹)
    (h : Matrix R W F) (h' : Matrix R' W F)
    (edge : VerticalEdgeIndex W G) (u : Word F R) :
    transposeTannerWord inverseDirection
        (wordLinearMapTranspose (chainComplex label h h').boundary1
          (verticalFiberCochain edge u)) =
      (chainComplex targetLabel (reindexColumns inverseDirection h')
        (reindexColumns inverseDirection h)).boundary2
        (horizontalFiberChain
          (transposeVerticalEdge inverseDirection edge) u) := by
  rw [chainComplex, LiftedProduct.chainComplex_boundary1,
    chainComplex, LiftedProduct.chainComplex_boundary2,
    ← transposeC0Word_verticalFiberCochain inverseDirection edge u]
  exact (boundary2_transposeC0Word
    label targetLabel inverseDirection hInverse h h'
      (verticalFiberCochain edge u)).symm

/- Transposition maps every allowed vertical coboundary move into an allowed
horizontal boundary move of the exchanged product. -/
theorem transposeTannerWord_mem_horizontalFiberBoundaryMoves
    (label targetLabel : W → G) (inverseDirection : W ≃ W)
    (hInverse : ∀ a, targetLabel (inverseDirection a) = (label a)⁻¹)
    (h : Matrix R W F) (h' : Matrix R' W F)
    (m : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hm : m ∈ verticalFiberCoboundaryMoves label h h') :
    transposeTannerWord inverseDirection m ∈
      horizontalFiberBoundaryMoves targetLabel
        (reindexColumns inverseDirection h')
        (reindexColumns inverseDirection h) := by
  classical
  obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hm
  apply Finset.mem_image.mpr
  refine ⟨(transposeVerticalEdge inverseDirection p.1, p.2),
    Finset.mem_univ _, ?_⟩
  exact (transposeTannerWord_verticalFiberCoboundaryMove
    label targetLabel inverseDirection hInverse h h' p.1 p.2).symm

/- Every exchanged horizontal fiber move has an original vertical-fiber
preimage under Tanner transposition. -/
theorem exists_verticalFiberCoboundaryMove_of_mem_horizontal
    (label targetLabel : W → G) (inverseDirection : W ≃ W)
    (hInverse : ∀ a, targetLabel (inverseDirection a) = (label a)⁻¹)
    (h : Matrix R W F) (h' : Matrix R' W F)
    (m' : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R') W W (Fin 2 × R) G))
    (hm' : m' ∈ horizontalFiberBoundaryMoves targetLabel
      (reindexColumns inverseDirection h')
      (reindexColumns inverseDirection h)) :
    ∃ m ∈ verticalFiberCoboundaryMoves label h h',
      transposeTannerWord inverseDirection m = m' := by
  classical
  obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hm'
  let edge := untransposeHorizontalEdge inverseDirection p.1
  let m := wordLinearMapTranspose (chainComplex label h h').boundary1
    (verticalFiberCochain edge p.2)
  refine ⟨m, ?_, ?_⟩
  · apply Finset.mem_image.mpr
    exact ⟨(edge, p.2), Finset.mem_univ _, rfl⟩
  · rw [transposeTannerWord_verticalFiberCoboundaryMove
      label targetLabel inverseDirection hInverse h h' edge p.2]
    simp [edge]

/- Fiber-local minimality is invariant under exchanging the two Tanner
factors. -/
theorem isLocallyMinimal_transposeTannerWord
    (label targetLabel : W → G) (inverseDirection : W ≃ W)
    (hInverse : ∀ a, targetLabel (inverseDirection a) = (label a)⁻¹)
    (h : Matrix R W F) (h' : Matrix R' W F)
    (z : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hzLocal : LocallyMinimalDistance.IsLocallyMinimal blockWeight
      (verticalFiberCoboundaryMoves label h h') z) :
    LocallyMinimalDistance.IsLocallyMinimal blockWeight
      (horizontalFiberBoundaryMoves targetLabel
        (reindexColumns inverseDirection h')
        (reindexColumns inverseDirection h))
      (transposeTannerWord inverseDirection z) := by
  intro m' hm'
  obtain ⟨m, hm, rfl⟩ :=
    exists_verticalFiberCoboundaryMove_of_mem_horizontal
      label targetLabel inverseDirection hInverse h h' m' hm'
  rw [← transposeTannerWord_add, blockWeight_transposeTannerWord,
    blockWeight_transposeTannerWord]
  exact hzLocal m hm

/- The one-orientation graph-expansion zero lemma also annihilates locally
minimal cocycles after exchanging and reindexing the Tanner factors. -/
theorem cocycle_eq_zero_of_doubleCoverExpansion_reindexed
    (label targetLabel : W → G) (inverseDirection : W ≃ W)
    (hInverse : ∀ a, targetLabel (inverseDirection a) = (label a)⁻¹)
    (h : Matrix R W F) (h' : Matrix R' W F)
    (hRank : (reindexColumns inverseDirection h').rank = Fintype.card R')
    (hInjective : Function.Injective
      (fun u : Word F R =>
        (reindexColumns inverseDirection h).transpose.mulVec u))
    (z : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hzCocycle : z ∈ (chainComplex label h h').middleCocycleCode.carrier)
    (hzLocal : LocallyMinimalDistance.IsLocallyMinimal blockWeight
      (verticalFiberCoboundaryMoves label h h') z)
    (d m s : Nat) (beta : ℝ)
    (hProductExpand : ProductExpansion.ProductExpanding
      (reindexColumns inverseDirection h')
      (ProductExpansion.generatorImageParityCheck
        (reindexColumns inverseDirection h)) s (2 * m) beta)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode
        (reindexColumns inverseDirection h')).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hLength : d ≤ Fintype.card W)
    (hTwo : 2 ≤ Fintype.card W) (hFour : 4 ≤ d)
    (hDistanceScale : 4 * m ≤ d)
    (hRectangleScale : 4 * s ≤ m * d)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W)
    (radius : Nat) (lambda : ℝ) (hLambda : 0 < lambda)
    (hBase : SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph targetLabel) radius lambda)
    (hBlockRadiusVertical :
      Fintype.card W * blockWeight z ≤ radius)
    (hBlockRadiusEdge : blockWeight z ≤ radius)
    (hBlockRadiusFace :
      blockWeight z ≤ radius / (2 * Fintype.card W))
    (hVerticalThreshold : (2 * m : ℝ) + lambda ≤ d)
    (hEdgeThreshold : 2 * (2 * lambda) ≤ m)
    (hFaceThreshold :
      2 * (((Nat.log 2 (2 * Fintype.card W) + 1 : Nat) : ℝ) *
        (8 * lambda ^ 2)) ≤ s) :
    z = 0 := by
  let zT := transposeTannerWord inverseDirection z
  have hzTCycleMem : zT ∈
      (chainComplex targetLabel (reindexColumns inverseDirection h')
        (reindexColumns inverseDirection h)).middleCycleCode.carrier :=
    transposeTannerWord_mem_middleCycleCode_of_mem_middleCocycleCode
      label targetLabel inverseDirection hInverse h h' z hzCocycle
  have hzTCycle : LiftedProduct.boundary1
      (data targetLabel (reindexColumns inverseDirection h')
        (reindexColumns inverseDirection h)) zT = 0 := by
    simpa [chainComplex] using
      ((chainComplex targetLabel (reindexColumns inverseDirection h')
        (reindexColumns inverseDirection h)).mem_middleCycleCode_iff zT).1
        hzTCycleMem
  have hzTLocal := isLocallyMinimal_transposeTannerWord
    label targetLabel inverseDirection hInverse h h' z hzLocal
  have hzTZero : zT = 0 := cycle_eq_zero_of_doubleCoverExpansion
    targetLabel (reindexColumns inverseDirection h') hRank
    (reindexColumns inverseDirection h) hInjective zT hzTCycle hzTLocal
    d m s beta hProductExpand hDistance hLength hTwo hFour
    hDistanceScale hRectangleScale hBudget radius lambda hLambda hBase
    (by simpa [zT, blockWeight_transposeTannerWord] using hBlockRadiusVertical)
    (by simpa [zT, blockWeight_transposeTannerWord] using hBlockRadiusEdge)
    (by simpa [zT, blockWeight_transposeTannerWord] using hBlockRadiusFace)
    hVerticalThreshold hEdgeThreshold hFaceThreshold
  have hBack := congrArg (transposeTannerWord inverseDirection.symm) hzTZero
  have hZero : transposeTannerWord inverseDirection.symm
      (0 : Word F
        (LiftedProduct.QubitIndex (Fin 2 × R') W W (Fin 2 × R) G)) = 0 := by
    funext q
    cases q <;> simp [transposeTannerWord]
  rw [hZero] at hBack
  dsimp [zT] at hBack
  rw [transposeTannerWord_symm_transposeTannerWord] at hBack
  exact hBack

/- Invert every generator label without changing its direction index. -/
def inverseGeneratorLabel (label : W → G) : W → G :=
  fun a => (label a)⁻¹

/- Switching the two double-cover sides identifies a labelling with its
pointwise inverse. -/
def doubleCoverSideSwapEquiv : (Fin 2 × G) ≃ (Fin 2 × G) where
  toFun x := (oppositeSide x.1, x.2)
  invFun x := (oppositeSide x.1, x.2)
  left_inv x := by rcases x with ⟨side, g⟩; simp
  right_inv x := by rcases x with ⟨side, g⟩; simp

omit [Field F] [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G]
    [Fintype W] [DecidableEq W] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
theorem doubleCoverSideSwapEquiv_rightDoubleCoverNeighbor
    (label : W → G) (x : Fin 2 × G) (a : W) :
    doubleCoverSideSwapEquiv (rightDoubleCoverNeighbor label x a) =
      rightDoubleCoverNeighbor (inverseGeneratorLabel label)
        (doubleCoverSideSwapEquiv x) a := by
  rcases x with ⟨side, g⟩
  fin_cases side <;>
    simp [doubleCoverSideSwapEquiv, rightDoubleCoverNeighbor,
      inverseGeneratorLabel, doubleCoverVoltage, oppositeSide]

omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq W] [Fintype R] [DecidableEq R] [Fintype R']
    [DecidableEq R'] in
theorem rightDoubleCoverGraph_inverseGeneratorLabel_eq_relabel
    (label : W → G) :
    rightDoubleCoverGraph (inverseGeneratorLabel label) =
      SmallSetExpansion.relabel doubleCoverSideSwapEquiv
        (rightDoubleCoverGraph label) := by
  funext x y
  unfold rightDoubleCoverGraph SmallSetExpansion.relabel
  congr 1
  apply Finset.filter_congr
  intro a _ha
  constructor
  · intro hxy
    apply doubleCoverSideSwapEquiv.injective
    rw [doubleCoverSideSwapEquiv_rightDoubleCoverNeighbor]
    simpa using hxy
  · intro hxy
    have h := congrArg doubleCoverSideSwapEquiv hxy
    rw [doubleCoverSideSwapEquiv_rightDoubleCoverNeighbor] at h
    simpa using h

omit [Field F] [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq W]
    [Fintype R]
    [DecidableEq R] [Fintype R'] [DecidableEq R'] in
theorem inverseGeneratorLabel_expanding_of_doubleCover
    (label : W → G) (radius : Nat) (lambda : ℝ)
    (hBase : SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius lambda) :
    SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph (inverseGeneratorLabel label)) radius lambda := by
  rw [rightDoubleCoverGraph_inverseGeneratorLabel_eq_relabel]
  exact hBase.relabel doubleCoverSideSwapEquiv

/- Source-shaped dual-orientation zero lemma.  No reindexed local-code
hypotheses remain: the target product uses the pointwise inverse labelling and
the original local matrices in reverse order. -/
theorem cocycle_eq_zero_of_doubleCoverExpansion
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (hRank : h'.rank = Fintype.card R')
    (hInjective : Function.Injective
      (fun u : Word F R => h.transpose.mulVec u))
    (z : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hzCocycle : z ∈ (chainComplex label h h').middleCocycleCode.carrier)
    (hzLocal : LocallyMinimalDistance.IsLocallyMinimal blockWeight
      (verticalFiberCoboundaryMoves label h h') z)
    (d m s : Nat) (beta : ℝ)
    (hProductExpand : ProductExpansion.ProductExpanding h'
      (ProductExpansion.generatorImageParityCheck h) s (2 * m) beta)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h').carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hLength : d ≤ Fintype.card W)
    (hTwo : 2 ≤ Fintype.card W) (hFour : 4 ≤ d)
    (hDistanceScale : 4 * m ≤ d)
    (hRectangleScale : 4 * s ≤ m * d)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W)
    (radius : Nat) (lambda : ℝ) (hLambda : 0 < lambda)
    (hBase : SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius lambda)
    (hBlockRadiusVertical :
      Fintype.card W * blockWeight z ≤ radius)
    (hBlockRadiusEdge : blockWeight z ≤ radius)
    (hBlockRadiusFace :
      blockWeight z ≤ radius / (2 * Fintype.card W))
    (hVerticalThreshold : (2 * m : ℝ) + lambda ≤ d)
    (hEdgeThreshold : 2 * (2 * lambda) ≤ m)
    (hFaceThreshold :
      2 * (((Nat.log 2 (2 * Fintype.card W) + 1 : Nat) : ℝ) *
        (8 * lambda ^ 2)) ≤ s) :
    z = 0 := by
  apply cocycle_eq_zero_of_doubleCoverExpansion_reindexed
    label (inverseGeneratorLabel label) (Equiv.refl W) (by intro a; rfl)
    h h'
  · simpa [reindexColumns] using hRank
  · simpa [reindexColumns] using hInjective
  · exact hzCocycle
  · exact hzLocal
  · simpa [reindexColumns] using hProductExpand
  · intro x hx hx0
    apply hDistance x
    · simpa [reindexColumns] using hx
    · exact hx0
  · exact hLength
  · exact hTwo
  · exact hFour
  · exact hDistanceScale
  · exact hRectangleScale
  · exact hBudget
  · exact hLambda
  · exact inverseGeneratorLabel_expanding_of_doubleCover
      label radius lambda hBase
  · exact hBlockRadiusVertical
  · exact hBlockRadiusEdge
  · exact hBlockRadiusFace
  · exact hVerticalThreshold
  · exact hEdgeThreshold
  · exact hFaceThreshold

private theorem blockWeight_radius_bounds
    (weight radius degree : Nat)
    (hSmall : weight < radius / (2 * degree) + 1) :
    degree * weight ≤ radius ∧
      weight ≤ radius ∧
      weight ≤ radius / (2 * degree) := by
  have hFace : weight ≤ radius / (2 * degree) := by omega
  refine ⟨?_, hFace.trans (Nat.div_le_self radius _), hFace⟩
  calc
    degree * weight ≤ degree * (radius / (2 * degree)) :=
      Nat.mul_le_mul_left degree hFace
    _ ≤ (2 * degree) * (radius / (2 * degree)) := by
      exact Nat.mul_le_mul_right (radius / (2 * degree)) (by omega)
    _ ≤ radius := Nat.mul_div_le radius (2 * degree)

/-- A nonzero horizontally fiber-minimal cycle has block weight at least the
small-set expansion radius divided by twice the local degree. -/
theorem blockWeight_ge_of_nonzero_locallyMinimal_cycle_of_doubleCoverExpansion
    (label : W → G) (h : Matrix R W F)
    (hRank : h.rank = Fintype.card R) (g' : Matrix R' W F)
    (gInjective : Function.Injective
      (fun u : Word F R' => g'.transpose.mulVec u))
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcCycle : c ∈ (chainComplex label h g').middleCycleCode.carrier)
    (hcNonzero : c ≠ 0)
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
    (radius : Nat) (lambda : ℝ) (hLambda : 0 < lambda)
    (hBase : SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius lambda)
    (hVerticalThreshold : (2 * m : ℝ) + lambda ≤ d)
    (hEdgeThreshold : 2 * (2 * lambda) ≤ m)
    (hFaceThreshold :
      2 * (((Nat.log 2 (2 * Fintype.card W) + 1 : Nat) : ℝ) *
        (8 * lambda ^ 2)) ≤ s) :
    radius / (2 * Fintype.card W) + 1 ≤ blockWeight c := by
  by_contra hBound
  have hSmall : blockWeight c < radius / (2 * Fintype.card W) + 1 :=
    Nat.lt_of_not_ge hBound
  obtain ⟨hVertical, hEdge, hFace⟩ :=
    blockWeight_radius_bounds (blockWeight c) radius (Fintype.card W) hSmall
  apply hcNonzero
  apply cycle_eq_zero_of_doubleCoverExpansion label h hRank g' gInjective c
  · exact ((chainComplex label h g').mem_middleCycleCode_iff c).1 hcCycle
  · exact hcLocal
  · exact hProductExpand
  · exact hDistance
  · exact hLength
  · exact hTwo
  · exact hFour
  · exact hDistanceScale
  · exact hRectangleScale
  · exact hBudget
  · exact hLambda
  · exact hBase
  · exact hVertical
  · exact hEdge
  · exact hFace
  · exact hVerticalThreshold
  · exact hEdgeThreshold
  · exact hFaceThreshold

/-- A nonzero vertically fiber-minimal cocycle has the same block-weight
lower bound, using the reverse product-expansion orientation. -/
theorem blockWeight_ge_of_nonzero_locallyMinimal_cocycle_of_doubleCoverExpansion
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (hRank : h'.rank = Fintype.card R')
    (hInjective : Function.Injective
      (fun u : Word F R => h.transpose.mulVec u))
    (z : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hzCocycle : z ∈ (chainComplex label h h').middleCocycleCode.carrier)
    (hzNonzero : z ≠ 0)
    (hzLocal : LocallyMinimalDistance.IsLocallyMinimal blockWeight
      (verticalFiberCoboundaryMoves label h h') z)
    (d m s : Nat) (beta : ℝ)
    (hProductExpand : ProductExpansion.ProductExpanding h'
      (ProductExpansion.generatorImageParityCheck h) s (2 * m) beta)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h').carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hLength : d ≤ Fintype.card W)
    (hTwo : 2 ≤ Fintype.card W) (hFour : 4 ≤ d)
    (hDistanceScale : 4 * m ≤ d)
    (hRectangleScale : 4 * s ≤ m * d)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W)
    (radius : Nat) (lambda : ℝ) (hLambda : 0 < lambda)
    (hBase : SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius lambda)
    (hVerticalThreshold : (2 * m : ℝ) + lambda ≤ d)
    (hEdgeThreshold : 2 * (2 * lambda) ≤ m)
    (hFaceThreshold :
      2 * (((Nat.log 2 (2 * Fintype.card W) + 1 : Nat) : ℝ) *
        (8 * lambda ^ 2)) ≤ s) :
    radius / (2 * Fintype.card W) + 1 ≤ blockWeight z := by
  by_contra hBound
  have hSmall : blockWeight z < radius / (2 * Fintype.card W) + 1 :=
    Nat.lt_of_not_ge hBound
  obtain ⟨hVertical, hEdge, hFace⟩ :=
    blockWeight_radius_bounds (blockWeight z) radius (Fintype.card W) hSmall
  apply hzNonzero
  apply cocycle_eq_zero_of_doubleCoverExpansion label h h' hRank hInjective z
  · exact hzCocycle
  · exact hzLocal
  · exact hProductExpand
  · exact hDistance
  · exact hLength
  · exact hTwo
  · exact hFour
  · exact hDistanceScale
  · exact hRectangleScale
  · exact hBudget
  · exact hLambda
  · exact hBase
  · exact hVertical
  · exact hEdge
  · exact hFace
  · exact hVerticalThreshold
  · exact hEdgeThreshold
  · exact hFaceThreshold

/-- The two product-expansion orientations and one labelled double-cover
expansion bound give the attained algebraic CSS distance of the Tanner lifted
product.  This is the distance-level PK22 interface: the remaining family
theorem only has to instantiate its finite-field and graph hypotheses. -/
theorem algebraicCSSMinimumDistance_ge_of_doubleCoverExpansion
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (hRank : h.rank = Fintype.card R)
    (h'Injective : Function.Injective
      (fun u : Word F R' => h'.transpose.mulVec u))
    (h'Rank : h'.rank = Fintype.card R')
    (hInjective : Function.Injective
      (fun u : Word F R => h.transpose.mulVec u))
    (d m s : Nat) (beta : ℝ)
    (hProductExpand : ProductExpansion.ProductExpanding h
      (ProductExpansion.generatorImageParityCheck h') s (2 * m) beta)
    (hProductExpandReverse : ProductExpansion.ProductExpanding h'
      (ProductExpansion.generatorImageParityCheck h) s (2 * m) beta)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hDistanceReverse : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h').carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hLength : d ≤ Fintype.card W)
    (hTwo : 2 ≤ Fintype.card W) (hFour : 4 ≤ d)
    (hDistanceScale : 4 * m ≤ d)
    (hRectangleScale : 4 * s ≤ m * d)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W)
    (radius : Nat) (lambda : ℝ) (hLambda : 0 < lambda)
    (hBase : SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius lambda)
    (hVerticalThreshold : (2 * m : ℝ) + lambda ≤ d)
    (hEdgeThreshold : 2 * (2 * lambda) ≤ m)
    (hFaceThreshold :
      2 * (((Nat.log 2 (2 * Fintype.card W) + 1 : Nat) : ℝ) *
        (8 * lambda ^ 2)) ≤ s)
    (dCSS : Nat)
    (hMinimum : AlgebraicCSSMinimumDistance
      (chainComplex label h h').firstCoboundaryCheckCode
      (chainComplex label h h').middleBoundaryCode dCSS) :
    radius / (2 * Fintype.card W) + 1 ≤ dCSS := by
  apply algebraicCSSMinimumDistance_ge_of_fiberLocallyMinimal_bounds
    label h h' (radius / (2 * Fintype.card W) + 1) dCSS
  · intro c hcCycle hcNonzero hcLocal
    exact blockWeight_ge_of_nonzero_locallyMinimal_cycle_of_doubleCoverExpansion
      label h hRank h' h'Injective c hcCycle hcNonzero hcLocal
      d m s beta hProductExpand hDistance hLength hTwo hFour
      hDistanceScale hRectangleScale hBudget radius lambda hLambda hBase
      hVerticalThreshold hEdgeThreshold hFaceThreshold
  · intro z hzCocycle hzNonzero hzLocal
    exact blockWeight_ge_of_nonzero_locallyMinimal_cocycle_of_doubleCoverExpansion
      label h h' h'Rank hInjective z hzCocycle hzNonzero hzLocal
      d m s beta hProductExpandReverse hDistanceReverse hLength hTwo hFour
      hDistanceScale hRectangleScale hBudget radius lambda hLambda hBase
      hVerticalThreshold hEdgeThreshold hFaceThreshold
  · exact hMinimum

end QEC.Coding.TannerLiftedProduct
