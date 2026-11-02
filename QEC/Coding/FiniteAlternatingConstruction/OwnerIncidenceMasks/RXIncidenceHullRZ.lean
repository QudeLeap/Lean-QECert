import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.RXIncidenceHullGrowth

/-!
# Retained Q-root shared-Z paths through an actual RZ successor

The path between two old neighbors uses their two subdivided radial edges
inside the same Z-local cylinder. No global connectivity premise is supplied.
-/
noncomputable section
namespace QEC.Coding.BDL26RXIncidenceHullRZ
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RXIncidenceHullGrowth
open scoped Classical

/-- The actual two retained roots of each original Q coordinate. -/
def rzRoot (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (q : P.Q) (copy : BDL26FiniteTannerSquare.Two) : (rzReplacementPresentation P A S).Q :=
  Sum.inr ⟨q,(copy,Sum.inl (Sum.inl ()))⟩

private theorem matrix_start (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : DoubleCylinderEdge P x S) :
    doubleCylinderEdgeVertexMatrix P x S (tannerDoubleCylinderEdgeStart P x S edge) edge=1 := by
  rcases edge with ⟨copy,edge⟩ | vertex
  · simpa [tannerDoubleCylinderEdgeStart,doubleCylinderEdgeVertexMatrix]
      using subdivisionEdgeVertexMatrix_start_eq_one P x S edge
  · simp [tannerDoubleCylinderEdgeStart,doubleCylinderEdgeVertexMatrix]

private theorem matrix_end (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : DoubleCylinderEdge P x S) :
    doubleCylinderEdgeVertexMatrix P x S (tannerDoubleCylinderEdgeEnd P x S edge) edge=1 := by
  rcases edge with ⟨copy,edge⟩ | vertex
  · simpa [tannerDoubleCylinderEdgeEnd,doubleCylinderEdgeVertexMatrix]
      using subdivisionEdgeVertexMatrix_end_eq_one P x S edge
  · simp [tannerDoubleCylinderEdgeEnd,doubleCylinderEdgeVertexMatrix]

private theorem local_start (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (z : P.Z) (edge : ZDoubleCylinderEdge P z S) :
    (rzReplacementPresentation P A S).qz (Sum.inl ⟨z,edge⟩)
      ⟨z,tannerDoubleCylinderEdgeStart (transposePresentation P) z S edge⟩=true := by
  change decide (∃ h : z=z, doubleCylinderEdgeVertexMatrix (transposePresentation P) z S
    (h ▸ tannerDoubleCylinderEdgeStart (transposePresentation P) z S edge) edge=1)=true
  rw [decide_eq_true_eq]
  exact ⟨rfl,matrix_start _ _ _ _⟩

private theorem local_end (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (z : P.Z) (edge : ZDoubleCylinderEdge P z S) :
    (rzReplacementPresentation P A S).qz (Sum.inl ⟨z,edge⟩)
      ⟨z,tannerDoubleCylinderEdgeEnd (transposePresentation P) z S edge⟩=true := by
  change decide (∃ h : z=z, doubleCylinderEdgeVertexMatrix (transposePresentation P) z S
    (h ▸ tannerDoubleCylinderEdgeEnd (transposePresentation P) z S edge) edge=1)=true
  rw [decide_eq_true_eq]
  exact ⟨rfl,matrix_end _ _ _ _⟩

/-- Traverse actual local edges as intermediate successor Q coordinates. -/
private theorem lift_local_path (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (z : P.Z) {u v : ZDoubleCylinderVertex P z S}
    (path : UndirectedPath (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S) u v)
    (a b : (rzReplacementPresentation P A S).Q)
    (ha : (rzReplacementPresentation P A S).qz a ⟨z,u⟩=true)
    (hb : (rzReplacementPresentation P A S).qz b ⟨z,v⟩=true) :
    SharedZPath (rzReplacementPresentation P A S) a b := by
  induction path generalizing b with
  | nil => exact .snoc (.refl a) ⟨z,u⟩ ha hb
  | @step previous target path edge connects ih =>
      have first : (rzReplacementPresentation P A S).qz (Sum.inl ⟨z,edge⟩) ⟨z,previous⟩=true := by
        rcases connects with h | h
        · simpa [h.1] using local_start P A S z edge
        · simpa [h.2] using local_end P A S z edge
      have last : (rzReplacementPresentation P A S).qz (Sum.inl ⟨z,edge⟩) ⟨z,target⟩=true := by
        rcases connects with h | h
        · simpa [h.2] using local_end P A S z edge
        · simpa [h.1] using local_start P A S z edge
      exact .snoc (ih _ first) ⟨z,target⟩ last hb

private theorem q_incident (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (q : P.Q) (z : P.Z) (hz : P.qz q z=true)
    (v : QDoubleCylinderVertex (transposePresentation P) q S) :
    (rzReplacementPresentation P A S).qz (Sum.inr ⟨q,v⟩)
      ⟨z,qToZDoubleCylinderVertex P A q z hz S v⟩=true := by
  change decide (∃ h : P.qz q z=true,
    qToZDoubleCylinderVertex P A q z h S v=qToZDoubleCylinderVertex P A q z hz S v)=true
  rw [decide_eq_true_eq]
  exact ⟨hz,rfl⟩

/-- Original q-cylinder connectivity survives through the genuine Z-local edges. -/
theorem rz_same_q (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (q : P.Q) (a b : BDL26FiniteTannerSquare.Two) :
    SharedZPath (rzReplacementPresentation P A S) (rzRoot P A S q a) (rzRoot P A S q b) := by
  let root := A.qzRoot q
  let vertex (c : BDL26FiniteTannerSquare.Two) : QDoubleCylinderVertex (transposePresentation P) q S := (c,Sum.inl (Sum.inl ()))
  let toA := qDoubleCylinderPath (transposePresentation P) (transposeTannerSquareAdmissible P A) q S (vertex a)
  let toB := qDoubleCylinderPath (transposePresentation P) (transposeTannerSquareAdmissible P A) q S (vertex b)
  let path := toA.reverse.append toB
  let mapped := UndirectedPath.map
    (qToZDoubleCylinderVertex P A q root.val root.property S)
    (qToZDoubleCylinderEdge P A q root.val root.property S)
    (fun d => (qToZDoubleCylinderEdge_start P A q root.val root.property S d).symm)
    (fun d => (qToZDoubleCylinderEdge_end P A q root.val root.property S d).symm) path
  exact lift_local_path P A S root.val mapped _ _
    (q_incident P A S q root.val root.property (vertex a))
    (q_incident P A S q root.val root.property (vertex b))

private def segmentVertex (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : XStarEdge P x) (step : Nat) (hstep : step ≤ S.half) : SubdivisionVertex P x S :=
  if hzero : step=0 then Sum.inl (xStarEdgeStart P x edge)
  else if hlast : step=S.half then Sum.inl (xStarEdgeEnd P x edge)
  else Sum.inr (Sum.inl (edge,⟨step-1,by omega⟩))

private theorem segment_path (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : XStarEdge P x) (step : Nat) (hstep : step ≤ S.half) :
    Nonempty (UndirectedPath (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S)
      (Sum.inl (xStarEdgeStart P x edge)) (segmentVertex P x S edge step hstep)) := by
  induction step with
  | zero => exact ⟨.nil⟩
  | succ previous ih =>
      have hprevious : previous ≤ S.half := by omega
      have hindex : previous < S.half := by omega
      obtain ⟨path⟩ := ih hprevious
      let index : Fin S.half := ⟨previous,hindex⟩
      refine ⟨.step (by simpa [segmentVertex,index] using path) (Sum.inl (edge,index)) ?_⟩
      apply Or.inl
      constructor
      · have hnotlast : previous ≠ S.half := by omega
        simp [subdivisionEdgeStart,subdivisionSegmentStart,index,hnotlast]
      · simp [subdivisionEdgeEnd,subdivisionSegmentEnd,segmentVertex,index]

private def central (P : TannerSquarePresentation) (x : P.X) : XStarVertex P x :=
  ⟨Vertex.x x,by simp [xStarVertexMember]⟩

private theorem radial_path (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (q : P.Q) (member : xStarBoundaryVertexMember P x (Vertex.q q)=true) (copy : BDL26FiniteTannerSquare.Two) :
    Nonempty (UndirectedPath (tannerDoubleCylinderEdgeStart P x S)
      (tannerDoubleCylinderEdgeEnd P x S) (copy,Sum.inl (central P x))
      (copy,Sum.inl (xStarBoundaryVertexToStar P x ⟨Vertex.q q,member⟩))) := by
  let edge := rxOriginalXBoundaryRadialEdge P x q member
  obtain ⟨path⟩ := segment_path P x S edge S.half (le_refl _)
  have start : xStarEdgeStart P x edge=central P x := by apply Subtype.ext; rfl
  have finish : xStarEdgeEnd P x edge=xStarBoundaryVertexToStar P x ⟨Vertex.q q,member⟩ := by
    apply Subtype.ext
    rfl
  have plain : UndirectedPath (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S)
      (Sum.inl (central P x)) (Sum.inl (xStarBoundaryVertexToStar P x ⟨Vertex.q q,member⟩)) := by
    simpa [segmentVertex,S.half_pos.ne',start,finish] using path
  exact ⟨UndirectedPath.map
    (edgeStart := subdivisionEdgeStart P x S)
    (edgeEnd := subdivisionEdgeEnd P x S)
    (edgeStart' := tannerDoubleCylinderEdgeStart P x S)
    (edgeEnd' := tannerDoubleCylinderEdgeEnd P x S)
    (fun v => (copy,v)) (fun e => Sum.inl (copy,e))
    (fun _ => rfl) (fun _ => rfl) plain⟩

private theorem center_radial_path (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (q : P.Q) (z : P.Z) (hz : P.qz q z=true) (copy : BDL26FiniteTannerSquare.Two) :
    Nonempty (UndirectedPath (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
      (copy,Sum.inl (central (transposePresentation P) z))
      (qToZDoubleCylinderVertex P A q z hz S (copy,Sum.inl (Sum.inl ())))) := by
  let boundary := (transposeXStarBoundaryVertexEquiv P z).symm
    (qToZBoundaryVertex P A q z hz (Sum.inl ()))
  have value : boundary.val=(Vertex.q q : Vertex (transposePresentation P)) := by rfl
  have member : xStarBoundaryVertexMember (transposePresentation P) z (Vertex.q q : Vertex (transposePresentation P))=true := by
    simpa only [value] using boundary.property
  obtain ⟨path⟩ := radial_path (transposePresentation P) z S q member copy
  have endpoint : qToZDoubleCylinderVertex P A q z hz S (copy,Sum.inl (Sum.inl ())) =
      (copy,Sum.inl (xStarBoundaryVertexToStar (transposePresentation P) z ⟨(Vertex.q q : Vertex (transposePresentation P)),member⟩)) := by
    apply Prod.ext
    · rfl
    · change Sum.inl (xStarBoundaryVertexToStar (transposePresentation P) z boundary) = _
      congr 1
  exact ⟨by simpa only [endpoint] using path⟩

/-- Old neighbors lift at a fixed copy using only their common Z-star radial paths. -/
theorem rz_shared_roots (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (q r : P.Q) (z : P.Z) (hq : P.qz q z=true) (hr : P.qz r z=true) (copy : BDL26FiniteTannerSquare.Two) :
    SharedZPath (rzReplacementPresentation P A S) (rzRoot P A S q copy) (rzRoot P A S r copy) := by
  obtain ⟨toQ⟩ := center_radial_path P A S q z hq copy
  obtain ⟨toR⟩ := center_radial_path P A S r z hr copy
  exact lift_local_path P A S z (toQ.reverse.append toR) _ _
    (q_incident P A S q z hq _) (q_incident P A S r z hr _)

/-- Any actual original shared-Z path lifts, including independently chosen copies. -/
theorem rz_path_roots (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) {q r : P.Q} (path : SharedZPath P q r) (a b : BDL26FiniteTannerSquare.Two) :
    SharedZPath (rzReplacementPresentation P A S) (rzRoot P A S q a) (rzRoot P A S r b) := by
  have same : SharedZPath (rzReplacementPresentation P A S) (rzRoot P A S q a) (rzRoot P A S r a) := by
    induction path with
    | refl => exact .refl _
    | snoc path z left right ih => exact ih.trans (rz_shared_roots P A S _ _ z left right a)
  exact same.trans (rz_same_q P A S r a b)

end QEC.Coding.BDL26RXIncidenceHullRZ
end
