import QEC.Coding.FiniteAlternatingConstruction.RXLocalReplacement
import QEC.Coding.FiniteAlternatingConstruction.RZCoordinateBridge

/-!
# Cochains of the materialized RX Tanner presentation

The raw cellular matrices agree entrywise with the Boolean incidences produced
by actual RX face corners. This identifies the two concrete cochain models.
-/

namespace QEC.Coding.BDL26RXLocalReplacement

open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RZMap1CoordinateBridge (tannerCoboundary0 tannerCoboundary1)
open scoped BigOperators

private noncomputable def rxVertexIndicator {V : Type} (a b : V) : Field := by
  classical
  exact if a = b then 1 else 0

private def rxFinTwoElim {motive : Fin 2 → Sort _}
    (zero : motive 0) (one : motive 1) (endpoint : Fin 2) : motive endpoint := by
  rcases endpoint with ⟨n, hn⟩
  rcases n with _ | n
  · exact zero
  · rcases n with _ | n
    · exact one
    · omega

private theorem qDoubleCylinderVertexXIncidence_atRoot
    (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (q : P.Q) (hxq : P.xq x q = true)
    (root : QStarEdge P q) (qVertex : QDoubleCylinderVertex P q S)
    (xVertex : DoubleCylinderVertex P x S) :
    qDoubleCylinderVertexXIncidence P q x S xVertex qVertex =
      rxVertexIndicator xVertex
        (qToXDoubleCylinderVertexAtRoot P q x hxq S root qVertex) := by
  classical
  rcases xVertex with ⟨xCopy, xVertex⟩
  rcases qVertex with ⟨qCopy, qVertex⟩
  fin_cases xCopy <;> fin_cases qCopy
  all_goals
    rcases xVertex with oldVertex | edgeInterior | faceInterior
  all_goals
    rcases qVertex with oldVertex' | edgeInterior'
  all_goals
    first
    | (rcases oldVertex' with cone | endpoint <;>
        simp [qDoubleCylinderVertexXIncidence, qSubdivisionVertexXIncidence,
          qToXDoubleCylinderVertexAtRoot, qToXSubdivisionVertexAtRoot,
          qToXBoundaryVertexAtRoot, xStarBoundaryVertexToStar,
          xBoundaryEdgeStart, xBoundaryEdgeEnd, qToXBoundaryEdge,
          rxVertexIndicator, Subtype.ext_iff, Prod.ext_iff, hxq])
    | simp [qDoubleCylinderVertexXIncidence, qSubdivisionVertexXIncidence,
        qToXDoubleCylinderVertexAtRoot, qToXSubdivisionVertexAtRoot,
        qToXBoundaryVertexAtRoot, xStarBoundaryVertexToStar,
        xBoundaryEdgeStart, xBoundaryEdgeEnd, qToXBoundaryEdge,
        rxVertexIndicator, Subtype.ext_iff, Prod.ext_iff, hxq]
  all_goals
    rcases edgeInterior with ⟨⟨edge, hmem⟩, index⟩
    rcases edge with xqEdge | qzEdge
    · simp [xStarBoundaryEdgeToStar, rxVertexIndicator,
        Subtype.ext_iff] at hmem ⊢
    · simp [xStarBoundaryEdgeToStar, qToXBoundaryEdge,
        rxVertexIndicator, Subtype.ext_iff, Prod.ext_iff, and_assoc]

private theorem qDoubleCylinderVertexXIncidence_endpoint
    (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (q : P.Q) (hxq : P.xq x q = true)
    (qEdge : QDoubleCylinderEdge P q S) (endpoint : Two)
    (xVertex : DoubleCylinderVertex P x S) :
    qDoubleCylinderVertexXIncidence P q x S xVertex
        (edgeEndpoint (qDoubleCylinderEdgeStart P q S)
          (qDoubleCylinderEdgeEnd P q S) qEdge endpoint) =
      rxVertexIndicator xVertex
        (edgeEndpoint (tannerDoubleCylinderEdgeStart P x S)
          (tannerDoubleCylinderEdgeEnd P x S)
          (qToXDoubleCylinderEdgeRaw P q x hxq S qEdge) endpoint) := by
  let root := qDoubleCylinderUnderlyingStarEdge P q S qEdge
  refine rxFinTwoElim (motive := fun endpoint =>
    qDoubleCylinderVertexXIncidence P q x S xVertex
        (edgeEndpoint (qDoubleCylinderEdgeStart P q S)
          (qDoubleCylinderEdgeEnd P q S) qEdge endpoint) =
      rxVertexIndicator xVertex
        (edgeEndpoint (tannerDoubleCylinderEdgeStart P x S)
          (tannerDoubleCylinderEdgeEnd P x S)
          (qToXDoubleCylinderEdgeRaw P q x hxq S qEdge) endpoint)) ?_ ?_ endpoint
  · simp only [edgeEndpoint, twoSelect_zero]
    rw [qDoubleCylinderVertexXIncidence_atRoot P S x q hxq root]
    rw [qToXDoubleCylinderEdgeRaw_start P q x hxq S root qEdge]
  · simp only [edgeEndpoint, twoSelect_one]
    rw [qDoubleCylinderVertexXIncidence_atRoot P S x q hxq root]
    rw [qToXDoubleCylinderEdgeRaw_end P q x hxq S root qEdge]

private theorem doubleCylinderEdgeVertexMatrix_eq_endpointIndicators
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (vertex : DoubleCylinderVertex P x S)
    (edge : DoubleCylinderEdge P x S) :
    doubleCylinderEdgeVertexMatrix P x S vertex edge =
      rxVertexIndicator vertex (tannerDoubleCylinderEdgeStart P x S edge) +
        rxVertexIndicator vertex (tannerDoubleCylinderEdgeEnd P x S edge) := by
  classical
  rcases edge with ⟨copy, subdivisionEdge⟩ | boundaryVertex
  · rcases vertex with ⟨vertexCopy, vertexValue⟩
    fin_cases vertexCopy <;> fin_cases copy <;>
      simp [doubleCylinderEdgeVertexMatrix, subdivisionEdgeVertexMatrix,
        tannerDoubleCylinderEdgeStart, tannerDoubleCylinderEdgeEnd,
        rxVertexIndicator]
  · rcases vertex with ⟨vertexCopy, vertexValue⟩
    fin_cases vertexCopy <;>
      simp [doubleCylinderEdgeVertexMatrix, tannerDoubleCylinderEdgeStart,
        tannerDoubleCylinderEdgeEnd, rxVertexIndicator]

private theorem rxMatrix_localEdge_eq_one_iff
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (v : DoubleCylinderVertex P x S) (e : DoubleCylinderEdge P x S) :
    doubleCylinderEdgeVertexMatrix P x S v e = 1 ↔
      v = tannerDoubleCylinderEdgeStart P x S e ∨
      v = tannerDoubleCylinderEdgeEnd P x S e := by
  classical
  rw [doubleCylinderEdgeVertexMatrix_eq_endpointIndicators]
  have hne := tannerDoubleCylinderEdgeStart_ne_end P x S e
  by_cases ha : v = tannerDoubleCylinderEdgeStart P x S e
  · have hb : v ≠ tannerDoubleCylinderEdgeEnd P x S e := by
      intro hb
      exact hne (ha.symm.trans hb)
    simp [rxVertexIndicator, ha, hb, hne, Ne.symm hne]
  · by_cases hb : v = tannerDoubleCylinderEdgeEnd P x S e <;>
      simp [rxVertexIndicator, ha, hb, hne, Ne.symm hne]

/-- Every endpoint of an X-local edge occurs in a materialized RX face. -/
theorem rxPresentation_xEdge_endpoint_incidence
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (x : P.X) (edge : DoubleCylinderEdge P x S)
    (endpoint : Two) :
    rxXQIncidence P S
      ⟨x, edgeEndpoint (tannerDoubleCylinderEdgeStart P x S)
        (tannerDoubleCylinderEdgeEnd P x S) edge endpoint⟩
      (Sum.inl ⟨x, edge⟩) = true := by
  obtain ⟨⟨⟨ownerX, cell, material⟩, corner⟩, hq⟩ :=
    rxLocalEdgeCornerOwner P A3 S x edge
  have hsigma : (⟨ownerX,
      if corner = 0 then localFaceQ0EdgeAt P ownerX S cell material
      else localFaceQ1EdgeAt P ownerX S cell material⟩ :
        Σ x : P.X, DoubleCylinderEdge P x S) = ⟨x, edge⟩ := by
    fin_cases corner
    · simpa [localFaceQAt, localFaceQ0, localFaceQ0Edge] using hq
    · simpa [localFaceQAt, localFaceQ1, localFaceQ1Edge] using hq
  have hx : ownerX = x := congrArg Sigma.fst hsigma
  subst ownerX
  have hedge := eq_of_heq (Sigma.mk.inj_iff.mp hsigma).2
  let m := localMaterialCornerAtEndpoint P x S cell material corner endpoint
  apply (rxXQIncidence_eq_true_iff P S _ _).2
  refine ⟨Sum.inl ⟨x, cell, m⟩, corner, ?_, ?_⟩
  · change localFaceX P S ⟨x, cell, m⟩ = _
    have h := localFaceX_atEndpoint P x S cell material corner endpoint
    rw [hedge] at h
    exact h
  · change localFaceQAt P S ⟨x, cell, m⟩ corner = _
    calc
      _ = localFaceQAt P S ⟨x, cell, material⟩ corner := by
        exact localFaceQ_atEndpoint P x S cell material corner endpoint
      _ = _ := hq

/-- The X-local branch has exactly its two explicit endpoint incidences. -/
theorem rxPresentation_boundary1_local_eq_one_iff
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (v : RX0 P S)
    (edge : Σ x : P.X, DoubleCylinderEdge P x S) :
    rxBoundary1Matrix P S v (Sum.inl edge) = 1 ↔
      rxXQIncidence P S v (Sum.inl edge) = true := by
  classical
  constructor
  · rcases v with ⟨x, v⟩
    rcases edge with ⟨y, edge⟩
    by_cases hxy : x = y
    · subst y
      simp only [rxBoundary1Matrix, dite_true] at *
      intro h
      rcases (rxMatrix_localEdge_eq_one_iff P S x v edge).1 h with h | h
      · subst v
        exact rxPresentation_xEdge_endpoint_incidence P A3 S x edge 0
      · subst v
        exact rxPresentation_xEdge_endpoint_incidence P A3 S x edge 1
    · simp [rxBoundary1Matrix, hxy]
  · intro h
    obtain ⟨face, corner, hx, hq⟩ :=
      (rxXQIncidence_eq_true_iff P S _ _).1 h
    obtain ⟨endpoint, he⟩ := rxFaceX_eq_endpoint_of_faceQ_eq_xEdge
      P S face corner edge.1 edge.2 hq
    rw [← hx, he]
    simp only [rxBoundary1Matrix, dite_true]
    apply (rxMatrix_localEdge_eq_one_iff P S edge.1 _ edge.2).2
    fin_cases endpoint
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- Each materialized RX face corner has raw degree-one incidence one. -/
theorem rxPresentation_boundary1_face_corner
    (P : TannerSquarePresentation) (S : OddScale)
    (face : RXFace P S) (corner : Two) :
    rxBoundary1Matrix P S (rxFaceX P S face)
      (rxFaceQ P S face corner) = 1 := by
  rcases face with localFace | glue | old
  · rcases localFace with ⟨x, cell, material⟩
    fin_cases corner
    · obtain ⟨endpoint, he⟩ := localFaceX_eq_q0_endpoint P x S cell material
      change rxBoundary1Matrix P S (localFaceX P S ⟨x, cell, material⟩)
        (Sum.inl ⟨x, localFaceQ0EdgeAt P x S cell material⟩) = 1
      rw [he]
      simp only [rxBoundary1Matrix, dite_true]
      apply (rxMatrix_localEdge_eq_one_iff P S x _ _).2
      fin_cases endpoint
      · exact Or.inl rfl
      · exact Or.inr rfl
    · obtain ⟨endpoint, he⟩ := localFaceX_eq_q1_endpoint P x S cell material
      change rxBoundary1Matrix P S (localFaceX P S ⟨x, cell, material⟩)
        (Sum.inl ⟨x, localFaceQ1EdgeAt P x S cell material⟩) = 1
      rw [he]
      simp only [rxBoundary1Matrix, dite_true]
      apply (rxMatrix_localEdge_eq_one_iff P S x _ _).2
      fin_cases endpoint
      · exact Or.inl rfl
      · exact Or.inr rfl
  · rcases glue with ⟨a, edge, endpoint⟩
    fin_cases corner
    · change rxBoundary1Matrix P S
        ⟨a.1.1, edgeEndpoint (tannerDoubleCylinderEdgeStart P a.1.1 S)
          (tannerDoubleCylinderEdgeEnd P a.1.1 S)
          (qToXDoubleCylinderEdgeRaw P a.1.2 a.1.1 a.2 S edge) endpoint⟩
        (Sum.inl ⟨a.1.1, qToXDoubleCylinderEdgeRaw P a.1.2 a.1.1 a.2 S edge⟩) = 1
      simp only [rxBoundary1Matrix, dite_true]
      apply (rxMatrix_localEdge_eq_one_iff P S _ _ _).2
      fin_cases endpoint
      · exact Or.inl rfl
      · exact Or.inr rfl
    · change qDoubleCylinderVertexXIncidence P a.1.2 a.1.1 S
        (edgeEndpoint (tannerDoubleCylinderEdgeStart P a.1.1 S)
          (tannerDoubleCylinderEdgeEnd P a.1.1 S)
          (qToXDoubleCylinderEdgeRaw P a.1.2 a.1.1 a.2 S edge) endpoint)
        (edgeEndpoint (qDoubleCylinderEdgeStart P a.1.2 S)
          (qDoubleCylinderEdgeEnd P a.1.2 S) edge endpoint) = 1
      rw [qDoubleCylinderVertexXIncidence_endpoint P S _ _ a.2]
      simp [rxVertexIndicator]
  · rcases old with ⟨face, copy⟩
    change qDoubleCylinderVertexXIncidence P (P.faceQ face corner)
      (P.faceX face) S
      (copy, Sum.inl (xStarFaceZVertex P (P.faceX face) (oldFaceInXStar P face)))
      (copy, Sum.inl (Sum.inr
        (⟨P.faceZ face, P.data.faceQ_qz face corner⟩ :
          QStarEdge P (P.faceQ face corner)))) = 1
    rw [qDoubleCylinderVertexXIncidence_atRoot P S _ _
      (P.data.faceQ_xq face corner)
      (⟨P.faceZ face, P.data.faceQ_qz face corner⟩ :
        QStarEdge P (P.faceQ face corner))]
    rw [qToXDoubleCylinderVertexAtRoot_oldZFace]
    simp [rxVertexIndicator]

/-- The shifted Q-local branch has exactly its materialized face incidences. -/
theorem rxPresentation_boundary1_qVertex_eq_one_iff
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (v : RX0 P S)
    (qv : Σ q : P.Q, QDoubleCylinderVertex P q S) :
    rxBoundary1Matrix P S v (Sum.inr qv) = 1 ↔
      rxXQIncidence P S v (Sum.inr qv) = true := by
  classical
  constructor
  · rcases v with ⟨x, xv⟩
    rcases qv with ⟨q, qv⟩
    intro h
    change qDoubleCylinderVertexXIncidence P q x S xv qv = 1 at h
    have hxq : P.xq x q = true := by
      by_contra hn
      simp [qDoubleCylinderVertexXIncidence, qSubdivisionVertexXIncidence, hn] at h
    obtain ⟨⟨edge, endpoint⟩, he⟩ :=
      rxQDoubleCylinderVertexIncidentEdge P A q S qv
    have he' : edgeEndpoint (qDoubleCylinderEdgeStart P q S)
        (qDoubleCylinderEdgeEnd P q S) edge endpoint = qv := by
      fin_cases endpoint <;> exact he
    rw [← he', qDoubleCylinderVertexXIncidence_endpoint P S x q hxq] at h
    have hxv : xv = edgeEndpoint (tannerDoubleCylinderEdgeStart P x S)
        (tannerDoubleCylinderEdgeEnd P x S)
        (qToXDoubleCylinderEdgeRaw P q x hxq S edge) endpoint := by
      simpa [rxVertexIndicator] using h
    apply (rxXQIncidence_eq_true_iff P S _ _).2
    refine ⟨Sum.inr (Sum.inl
      ⟨(⟨(x, q), hxq⟩ : XQEdge P), edge, endpoint⟩), 1, ?_, ?_⟩
    · change (⟨x, _⟩ : RX0 P S) = ⟨x, xv⟩
      exact congrArg (fun v => (⟨x, v⟩ : RX0 P S)) hxv.symm
    · change Sum.inr (⟨q, _⟩ : Σ q : P.Q, QDoubleCylinderVertex P q S) =
        Sum.inr ⟨q, qv⟩
      exact congrArg (fun v => Sum.inr (⟨q, v⟩ :
        Σ q : P.Q, QDoubleCylinderVertex P q S)) he'
  · intro h
    obtain ⟨face, corner, hx, hq⟩ :=
      (rxXQIncidence_eq_true_iff P S _ _).1 h
    rw [← hx, ← hq]
    exact rxPresentation_boundary1_face_corner P S face corner

/-- The degree-one raw matrix is the indicator of the actual successor X-Q relation. -/
theorem rxPresentation_boundary1Matrix_eq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : RX0 P S) (q : RX1 P S) :
    rxBoundary1Matrix P S x q =
      if (rxReplacementPresentation P S).xq x q = true then 1 else 0 := by
  classical
  have hiff : rxBoundary1Matrix P S x q = 1 ↔
      (rxReplacementPresentation P S).xq x q = true := by
    rcases q with edge | vertex
    · exact rxPresentation_boundary1_local_eq_one_iff
        P A4.toTannerSquareAdmissibleV3 S x edge
    · exact rxPresentation_boundary1_qVertex_eq_one_iff
        P A4.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S x vertex
  generalize hv : rxBoundary1Matrix P S x q = value at *
  fin_cases value
  · have hn := fun hp => zero_ne_one (hiff.mpr hp)
    rw [if_neg hn]
    rfl
  · have hp := hiff.mp rfl
    rw [if_pos hp]
    rfl

private theorem rxGeneric_coboundary0_eq (P : TannerSquarePresentation) :
    tannerCoboundary0 P = wordLinearMapTranspose
      (Matrix.toLin' (fun x : P.X => fun q : P.Q =>
        if P.xq x q = true then (1 : Field) else 0)) := by
  classical
  apply LinearMap.ext
  intro f
  apply funext
  intro q
  exact (wordLinearMapTranspose_toLin'_apply
    (fun x q => if P.xq x q = true then (1 : Field) else 0) f q).symm

/-- The materialized Tanner degree-zero coboundary is the transpose raw boundary. -/
theorem rxPresentation_coboundary0_eq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (_R : TannerSquareCellularRegular P) (S : OddScale) :
    tannerCoboundary0 (rxReplacementPresentation P S) =
      wordLinearMapTranspose (rxBoundary1 P S) := by
  classical
  have hm : (fun x : RX0 P S => fun q : RX1 P S =>
      if (rxReplacementPresentation P S).xq x q = true then (1 : Field) else 0) =
      rxBoundary1Matrix P S := by
    funext x q
    exact (rxPresentation_boundary1Matrix_eq P A4 S x q).symm
  exact (rxGeneric_coboundary0_eq (rxReplacementPresentation P S)).trans
    (congrArg (fun M : Matrix (RX0 P S) (RX1 P S) Field =>
      wordLinearMapTranspose (Matrix.toLin' M)) hm)

private noncomputable def rxLocalBoundarySlot
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (cell : DoubleCylinderFace P x S) (slot : Two × Two) :
    DoubleCylinderEdge P x S :=
  match cell with
  | Sum.inl cf => Sum.inl (cf.1, subdivisionFaceBoundaryEdge P x S cf.2 slot)
  | Sum.inr r => doubleCylinderRectangleBoundaryEdge P x S r slot

private theorem rxLocalMatrix_eq_one_iff_slot
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : DoubleCylinderEdge P x S) (cell : DoubleCylinderFace P x S) :
    doubleCylinderFaceEdgeMatrix P x S edge cell = 1 ↔
      ∃ slot : Two × Two, rxLocalBoundarySlot P x S cell slot = edge := by
  classical
  rcases cell with ⟨copy, cell⟩ | rectangle
  · rcases edge with ⟨copy', edge⟩ | vertex
    · by_cases hc : copy' = copy
      · subst copy'
        simpa [doubleCylinderFaceEdgeMatrix, rxLocalBoundarySlot] using
          subdivisionFaceEdgeMatrix_eq_one_iff P x S edge cell
      · simp [doubleCylinderFaceEdgeMatrix, rxLocalBoundarySlot, hc, Ne.symm hc]
    · simp [doubleCylinderFaceEdgeMatrix, rxLocalBoundarySlot]
  · exact doubleCylinderFaceEdgeMatrix_rectangle_eq_one_iff P x S edge rectangle

private theorem rxLocalBoundarySlot_materialize
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (cell : DoubleCylinderFace P x S) (slot : Two × Two) :
    localFaceQAt P S ⟨x, cell, (slot.2, slot.2)⟩ slot.1 =
      Sum.inl ⟨x, rxLocalBoundarySlot P x S cell slot⟩ := by
  rcases slot with ⟨kind, tag⟩
  rcases cell with cf | rectangle
  all_goals fin_cases kind <;>
    simp [localFaceQAt, localFaceQ0, localFaceQ1, localFaceQ0Edge,
      localFaceQ1Edge, localFaceQ0EdgeAt, localFaceQ1EdgeAt, rxLocalBoundarySlot]

private theorem rxLocalMatrix_corner
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (cell : DoubleCylinderFace P x S) (material : Two × Two) (corner : Two) :
    doubleCylinderFaceEdgeMatrix P x S
      (if corner = 0 then localFaceQ0EdgeAt P x S cell material
        else localFaceQ1EdgeAt P x S cell material) cell = 1 := by
  apply (rxLocalMatrix_eq_one_iff_slot P x S _ cell).2
  rcases cell with cf | rectangle
  · fin_cases corner
    · exact ⟨(0, material.2), rfl⟩
    · exact ⟨(1, material.1), rfl⟩
  · fin_cases corner
    · exact ⟨(0, material.1), rfl⟩
    · exact ⟨(1, material.2), rfl⟩

private theorem rxQEdgeStart_ne_end
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (S : OddScale) (edge : QDoubleCylinderEdge P q S) :
    qDoubleCylinderEdgeStart P q S edge ≠ qDoubleCylinderEdgeEnd P q S edge := by
  intro h
  let x := (A.xqRoot q).1
  let hxq := (A.xqRoot q).2
  let root := qDoubleCylinderUnderlyingStarEdge P q S edge
  have hm := congrArg (qToXDoubleCylinderVertexAtRoot P q x hxq S root) h
  rw [qToXDoubleCylinderEdgeRaw_start, qToXDoubleCylinderEdgeRaw_end] at hm
  exact tannerDoubleCylinderEdgeStart_ne_end P x S _ hm

private theorem rxQEdgeVertex_eq_one_iff
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (S : OddScale) (vertex : QDoubleCylinderVertex P q S)
    (edge : QDoubleCylinderEdge P q S) :
    qDoubleCylinderEdgeVertexIncidence P q S vertex edge = 1 ↔
      vertex = qDoubleCylinderEdgeStart P q S edge ∨
      vertex = qDoubleCylinderEdgeEnd P q S edge := by
  classical
  have hn := rxQEdgeStart_ne_end P A q S edge
  by_cases hs : vertex = qDoubleCylinderEdgeStart P q S edge
  · have he : vertex ≠ qDoubleCylinderEdgeEnd P q S edge := by
      intro he
      exact hn (hs.symm.trans he)
    simp [qDoubleCylinderEdgeVertexIncidence, hs, he, hn, Ne.symm hn]
  · by_cases he : vertex = qDoubleCylinderEdgeEnd P q S edge <;>
      simp [qDoubleCylinderEdgeVertexIncidence, hs, he, hn, Ne.symm hn]

/-- Each materialized RX face corner has raw degree-two incidence one. -/
theorem rxPresentation_boundary2_face_corner
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (face : RXFace P S) (corner : Two) :
    rxBoundary2Matrix P S (rxFaceQ P S face corner)
      (rxFaceZ P S face) = 1 := by
  classical
  rcases face with localFace | glue | old
  · rcases localFace with ⟨x, cell, material⟩
    have h := rxLocalMatrix_corner P x S cell material corner
    fin_cases corner <;>
      simpa [rxFaceQ, rxFaceZ, localFaceZ, localFaceQAt, localFaceQ0,
        localFaceQ1, localFaceQ0Edge, localFaceQ1Edge, rxBoundary2Matrix] using h
  · rcases glue with ⟨a, edge, endpoint⟩
    fin_cases corner
    · simp [rxFaceQ, rxFaceZ, glueFaceZ, glueFaceQ0,
        rxBoundary2Matrix, qDoubleCylinderEdgeXIncidence, a.2]
    · change rxBoundary2Matrix P S
        (Sum.inr ⟨a.1.2, edgeEndpoint (qDoubleCylinderEdgeStart P a.1.2 S)
          (qDoubleCylinderEdgeEnd P a.1.2 S) edge endpoint⟩)
        (Sum.inl (Sum.inr ⟨a.1.2, edge⟩)) = 1
      simp only [rxBoundary2Matrix, dite_true]
      apply (rxQEdgeVertex_eq_one_iff P A a.1.2 S _ edge).2
      fin_cases endpoint
      · exact Or.inl rfl
      · exact Or.inr rfl
  · rcases old with ⟨face, copy⟩
    simp [rxFaceQ, rxFaceZ, oldZFaceQ, oldZFaceZ, rxBoundary2Matrix,
      qDoubleCylinderVertexZIncidence, P.data.faceQ_qz]

/-- Nonzero local two-cell incidence supplies its actual materialized corner. -/
theorem rxPresentation_boundary2_local_mem
    (P : TannerSquarePresentation) (S : OddScale)
    (q : RX1 P S) (cell : Σ x : P.X, DoubleCylinderFace P x S)
    (h : rxBoundary2Matrix P S q (Sum.inl (Sum.inl cell)) = 1) :
    rxQZIncidence P S q (Sum.inl (Sum.inl cell)) = true := by
  classical
  rcases q with ⟨x, edge⟩ | qv
  · rcases cell with ⟨y, cell⟩
    by_cases hxy : x = y
    · subst y
      simp only [rxBoundary2Matrix, dite_true] at h
      obtain ⟨slot, hs⟩ := (rxLocalMatrix_eq_one_iff_slot P x S edge cell).1 h
      apply (rxQZIncidence_eq_true_iff P S _ _).2
      refine ⟨Sum.inl ⟨x, cell, (slot.2, slot.2)⟩, slot.1, ?_, rfl⟩
      change localFaceQAt P S _ _ = _
      rw [rxLocalBoundarySlot_materialize, hs]
    · simp [rxBoundary2Matrix, hxy] at h
  · simp [rxBoundary2Matrix] at h

/-- Nonzero Q-cylinder-edge incidence supplies an actual glue face corner. -/
theorem rxPresentation_boundary2_qEdge_mem
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (q : RX1 P S)
    (cell : Σ q : P.Q, QDoubleCylinderEdge P q S)
    (h : rxBoundary2Matrix P S q (Sum.inl (Sum.inr cell)) = 1) :
    rxQZIncidence P S q (Sum.inl (Sum.inr cell)) = true := by
  classical
  rcases cell with ⟨oldQ, edge⟩
  rcases q with ⟨x, xe⟩ | ⟨oldQ', vertex⟩
  · change qDoubleCylinderEdgeXIncidence P oldQ x S xe edge = 1 at h
    by_cases hxq : P.xq x oldQ = true
    · have he : xe = qToXDoubleCylinderEdgeRaw P oldQ x hxq S edge := by
        simpa [qDoubleCylinderEdgeXIncidence, hxq] using h
      apply (rxQZIncidence_eq_true_iff P S _ _).2
      refine ⟨Sum.inr (Sum.inl
        ⟨(⟨(x, oldQ), hxq⟩ : XQEdge P), edge, 0⟩), 0, ?_, rfl⟩
      change Sum.inl (⟨x, _⟩ : Σ x : P.X, DoubleCylinderEdge P x S) =
        Sum.inl ⟨x, xe⟩
      rw [he]
    · simp [qDoubleCylinderEdgeXIncidence, hxq] at h
  · by_cases hq : oldQ' = oldQ
    · subst oldQ'
      simp only [rxBoundary2Matrix, dite_true] at h
      obtain ⟨endpoint, he⟩ : ∃ endpoint : Two,
          edgeEndpoint (qDoubleCylinderEdgeStart P oldQ S)
            (qDoubleCylinderEdgeEnd P oldQ S) edge endpoint = vertex := by
        rcases (rxQEdgeVertex_eq_one_iff P A oldQ S vertex edge).1 h with hs | he
        · exact ⟨0, hs.symm⟩
        · exact ⟨1, he.symm⟩
      let a : XQEdge P := ⟨((A.xqRoot oldQ).1, oldQ), (A.xqRoot oldQ).2⟩
      apply (rxQZIncidence_eq_true_iff P S _ _).2
      refine ⟨Sum.inr (Sum.inl ⟨a, edge, endpoint⟩), 1, ?_, rfl⟩
      change Sum.inr (⟨oldQ, _⟩ : Σ q : P.Q, QDoubleCylinderVertex P q S) =
        Sum.inr ⟨oldQ, vertex⟩
      rw [he]
    · simp [rxBoundary2Matrix, hq] at h

private theorem qDoubleCylinderVertexZIncidence_eq_indicator
    (P : TannerSquarePresentation) (S : OddScale)
    (q : P.Q) (z : P.Z) (zCopy : Two) (hqz : P.qz q z = true)
    (vertex : QDoubleCylinderVertex P q S) :
    qDoubleCylinderVertexZIncidence P q S vertex (z, zCopy) =
      rxVertexIndicator vertex
        (zCopy, Sum.inl (Sum.inr (⟨z, hqz⟩ : QStarEdge P q))) := by
  classical
  rcases vertex with ⟨copy, vertex⟩
  fin_cases copy <;> fin_cases zCopy
  all_goals rcases vertex with (cone | endpoint) | interior
  all_goals
    simp [qDoubleCylinderVertexZIncidence, rxVertexIndicator, hqz,
      Subtype.ext_iff]

private theorem rxTerminalCoordinate_congr
    (P : TannerSquarePresentation) (S : OddScale)
    (q₁ q₂ : P.Q) (z₁ z₂ : P.Z)
    (h₁ : P.qz q₁ z₁ = true) (h₂ : P.qz q₂ z₂ = true)
    (copy : Two) (hq : q₁ = q₂) (hz : z₁ = z₂) :
    (⟨q₁, (copy, Sum.inl (Sum.inr (⟨z₁, h₁⟩ : QStarEdge P q₁)))⟩ :
      Σ q : P.Q, QDoubleCylinderVertex P q S) =
    ⟨q₂, (copy, Sum.inl (Sum.inr (⟨z₂, h₂⟩ : QStarEdge P q₂)))⟩ := by
  cases hq
  cases hz
  rfl

/-- Nonzero old-Z restriction supplies an actual original face corner. -/
theorem rxPresentation_boundary2_oldZ_mem
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (q : RX1 P S) (z : P.Z × Two)
    (h : rxBoundary2Matrix P S q (Sum.inr z) = 1) :
    rxQZIncidence P S q (Sum.inr z) = true := by
  classical
  rcases q with edge | ⟨q, vertex⟩
  · simp [rxBoundary2Matrix] at h
  · rcases z with ⟨z, copy⟩
    change qDoubleCylinderVertexZIncidence P q S vertex (z, copy) = 1 at h
    have hqz : P.qz q z = true := by
      by_contra hn
      simp [qDoubleCylinderVertexZIncidence, hn] at h
    rw [qDoubleCylinderVertexZIncidence_eq_indicator P S q z copy hqz] at h
    have hv : vertex =
        (copy, Sum.inl (Sum.inr (⟨z, hqz⟩ : QStarEdge P q))) := by
      simpa [rxVertexIndicator] using h
    let x := (A.xqRoot q).1
    let shared : SharedQ P.data x z := ⟨q, by
      simpa using And.intro (A.xqRoot q).2 hqz⟩
    obtain ⟨⟨face, corner⟩, hc⟩ := (P.perfectPairing x z).2 shared
    have hfaceQ : P.faceQ face.val corner = q := congrArg Subtype.val hc
    have hfaceZ : P.faceZ face.val = z := face.property.2
    apply (rxQZIncidence_eq_true_iff P S _ _).2
    refine ⟨Sum.inr (Sum.inr (face.val, copy)), corner, ?_, ?_⟩
    · change Sum.inr (⟨P.faceQ face.val corner,
          (copy, Sum.inl (Sum.inr
            (⟨P.faceZ face.val, P.data.faceQ_qz face.val corner⟩ :
              QStarEdge P (P.faceQ face.val corner))))⟩ :
            Σ q : P.Q, QDoubleCylinderVertex P q S) = Sum.inr ⟨q, vertex⟩
      rw [hv]
      apply congrArg Sum.inr
      exact rxTerminalCoordinate_congr P S _ _ _ _ _ _ copy hfaceQ hfaceZ
    · change Sum.inr (P.faceZ face.val, copy) = Sum.inr (z, copy)
      rw [hfaceZ]

/-- The degree-two raw matrix is the indicator of the actual successor Q-Z relation. -/
theorem rxPresentation_boundary2Matrix_eq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q : RX1 P S) (z : RX2 P S) :
    rxBoundary2Matrix P S q z =
      if (rxReplacementPresentation P S).qz q z = true then 1 else 0 := by
  classical
  let A := A4.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  have hiff : rxBoundary2Matrix P S q z = 1 ↔
      (rxReplacementPresentation P S).qz q z = true := by
    constructor
    · intro h
      rcases z with (cell | edge) | old
      · exact rxPresentation_boundary2_local_mem P S q cell h
      · exact rxPresentation_boundary2_qEdge_mem P A S q edge h
      · exact rxPresentation_boundary2_oldZ_mem P A S q old h
    · intro h
      obtain ⟨face, corner, hq, hz⟩ :=
        (rxQZIncidence_eq_true_iff P S _ _).1 h
      rw [← hq, ← hz]
      exact rxPresentation_boundary2_face_corner P A S face corner
  generalize hv : rxBoundary2Matrix P S q z = value at *
  fin_cases value
  · have hn := fun hp => zero_ne_one (hiff.mpr hp)
    rw [if_neg hn]
    rfl
  · have hp := hiff.mp rfl
    rw [if_pos hp]
    rfl

private theorem rxGeneric_coboundary1_eq (P : TannerSquarePresentation) :
    tannerCoboundary1 P = wordLinearMapTranspose
      (Matrix.toLin' (fun x : P.Q => fun q : P.Z =>
        if P.qz x q = true then (1 : Field) else 0)) := by
  classical
  apply LinearMap.ext
  intro f
  apply funext
  intro q
  exact (wordLinearMapTranspose_toLin'_apply
    (fun x q => if P.qz x q = true then (1 : Field) else 0) f q).symm

/-- The materialized Tanner degree-one coboundary is the transpose raw boundary. -/
theorem rxPresentation_coboundary1_eq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (_R : TannerSquareCellularRegular P) (S : OddScale) :
    tannerCoboundary1 (rxReplacementPresentation P S) =
      wordLinearMapTranspose (rxBoundary2 P S) := by
  classical
  have hm : (fun x : RX1 P S => fun q : RX2 P S =>
      if (rxReplacementPresentation P S).qz x q = true then (1 : Field) else 0) =
      rxBoundary2Matrix P S := by
    funext x q
    exact (rxPresentation_boundary2Matrix_eq P A4 S x q).symm
  exact (rxGeneric_coboundary1_eq (rxReplacementPresentation P S)).trans
    (congrArg (fun M : Matrix (RX1 P S) (RX2 P S) Field =>
      wordLinearMapTranspose (Matrix.toLin' M)) hm)

end QEC.Coding.BDL26RXLocalReplacement
