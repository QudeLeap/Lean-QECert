import QEC.Coding.FiniteAlternatingConstruction.QuantitativeBounds
import QEC.Coding.FiniteAlternatingConstruction.BoundedValenceSuccessors
import QEC.Coding.FiniteAlternatingConstruction.ReplacementSupport

namespace QEC.Coding.BDL26GraphQuantitativeBounds

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26FiniteAlternatingCore BDL26RXLocalReplacement
open scoped BigOperators Classical

/-- Measured undirected Tanner degree. -/
def tannerDegree (P : TannerSquarePresentation) (v : Vertex P) : Nat :=
  Fintype.card {w : Vertex P // tannerAdjacent P v w}

/-- Neighbors of an X vertex are exactly its actual Q incidences. -/
def xNeighborEquiv (P : TannerSquarePresentation) (x : P.X) :
    {v : Vertex P // tannerAdjacent P (.x x) v} ≃ {q : P.Q // P.xq x q = true} where
  toFun v := by
    rcases v with ⟨v,h⟩
    cases v with
    | x _ => cases h
    | q q => exact ⟨q,h⟩
    | z _ => cases h
  invFun q := ⟨.q q.1,q.2⟩
  left_inv := by
    rintro ⟨v,h⟩
    cases v with
    | x _ => cases h
    | q q => rfl
    | z _ => cases h
  right_inv := fun _ => rfl

/-- Neighbors of a Z vertex are exactly its actual Q incidences. -/
def zNeighborEquiv (P : TannerSquarePresentation) (z : P.Z) :
    {v : Vertex P // tannerAdjacent P (.z z) v} ≃ {q : P.Q // P.qz q z = true} where
  toFun v := by
    rcases v with ⟨v,h⟩
    cases v with
    | x _ => cases h
    | q q => exact ⟨q,h⟩
    | z _ => cases h
  invFun q := ⟨.q q.1,q.2⟩
  left_inv := by
    rintro ⟨v,h⟩
    cases v with
    | x _ => cases h
    | q q => rfl
    | z _ => cases h
  right_inv := fun _ => rfl

/-- Q neighbors split into the disjoint X and Z incidence classes. -/
def qNeighborEquiv (P : TannerSquarePresentation) (q : P.Q) :
    {v : Vertex P // tannerAdjacent P (.q q) v} ≃
      ({x : P.X // P.xq x q = true} ⊕ {z : P.Z // P.qz q z = true}) where
  toFun v := by
    rcases v with ⟨v,h⟩
    cases v with
    | x x => exact Sum.inl ⟨x,h⟩
    | q _ => cases h
    | z z => exact Sum.inr ⟨z,h⟩
  invFun v := match v with
    | Sum.inl x => ⟨.x x.1,x.2⟩
    | Sum.inr z => ⟨.z z.1,z.2⟩
  left_inv := by
    rintro ⟨v,h⟩
    cases v with
    | x x => rfl
    | q _ => cases h
    | z z => rfl
  right_inv := by intro v; cases v <;> rfl

/-- The proved valence invariant bounds the actual undirected degree. -/
theorem tannerDegree_le (P : TannerSquarePresentation) (h : BoundedValence P)
    (v : Vertex P) : tannerDegree P v ≤ 7 := by
  unfold tannerDegree
  cases v with
  | x x => rw [Fintype.card_congr (xNeighborEquiv P x)]; exact h.1 x
  | z z => rw [Fintype.card_congr (zNeighborEquiv P z)]; exact h.2.1 z
  | q q =>
      rw [Fintype.card_congr (qNeighborEquiv P q),Fintype.card_sum]
      exact (h.2.2 q).2.2

/-- The actual recursive Tanner graph has a scale- and depth-independent bound. -/
theorem state_tannerDegree_le (S : OddScale) (n : Nat)
    (v : Vertex (state S n).presentation) : tannerDegree (state S n).presentation v ≤ 7 :=
  tannerDegree_le _ (state_boundedValence S n) v

/-- Conservative explicit envelope for local coordinate counts, not their exact maximum. -/
def localCoordinateBound (S : OddScale) : Nat := 14 * S.ell ^ 2

/-- Conservative full-graph degree envelope, including one parent and seven level edges. -/
def fullGraphDegreeBound (S : OddScale) : Nat := localCoordinateBound S + 8

/-- At most one lower neighbor can be incident to any upper graph vertex. -/
theorem parentNeighbors_subsingleton (S : OddScale) (n : Nat)
    (v : GraphVertex S (n+1)) :
    Subsingleton {u : GraphVertex S n // v ∈ localRegion S n u} where
  allEq := by
    intro u w
    apply Subtype.ext
    exact Option.some.inj
      (((parent_mem_iff S n u.1 v).mpr u.2).symm.trans
        ((parent_mem_iff S n w.1 v).mpr w.2))

/-- The incoming inter-level degree is at most one, including unowned connectors. -/
theorem parentNeighbors_card_le (S : OddScale) (n : Nat) (v : GraphVertex S (n+1)) :
    Fintype.card {u : GraphVertex S n // v ∈ localRegion S n u} ≤ 1 := by
  classical
  letI := parentNeighbors_subsingleton S n v
  exact Fintype.card_le_one_iff_subsingleton.mpr inferInstance


/-- Face corners at fixed X inject into its actual Q-Z wedges. -/
def xStarCornerWedge (P : TannerSquarePresentation) (x : P.X) :
    XStarFace P x × BDL26FiniteTannerSquare.Two →
      Σ q : {q : P.Q // P.xq x q = true}, QStarEdge P q.1 := fun fi =>
  ⟨⟨P.faceQ fi.1.1 fi.2, by
    have hx : P.faceX fi.1.1 = x := by simpa [xStarFaceMember] using fi.1.2
    simpa only [hx] using P.data.faceQ_xq fi.1.1 fi.2⟩,
    P.faceZ fi.1.1, P.data.faceQ_qz fi.1.1 fi.2⟩

theorem xStarCornerWedge_injective (P : TannerSquarePresentation) (x : P.X) :
    Function.Injective (xStarCornerWedge P x) := by
  rintro ⟨f,i⟩ ⟨g,j⟩ h
  have hq : P.faceQ f.1 i = P.faceQ g.1 j :=
    congrArg (fun w : Σ q : {q : P.Q // P.xq x q = true}, QStarEdge P q.1 => w.1.1) h
  have hz : P.faceZ f.1 = P.faceZ g.1 :=
    congrArg (fun w : Σ q : {q : P.Q // P.xq x q = true}, QStarEdge P q.1 => w.2.1) h
  have hx : P.faceX f.1 = P.faceX g.1 := by
    have hf : P.faceX f.1 = x := by simpa [xStarFaceMember] using f.2
    have hg : P.faceX g.1 = x := by simpa [xStarFaceMember] using g.2
    exact hf.trans hg.symm
  have hw : faceCornerWedge P (f.1,i) = faceCornerWedge P (g.1,j) :=
    Subtype.ext (Prod.ext hx (Prod.ext hq hz))
  have hfg := (faceCornerWedge_bijective P).1 hw
  have hfirst : f.1 = g.1 := congrArg (fun v : P.Face × BDL26FiniteTannerSquare.Two => v.1) hfg
  have hsecond : i = j := congrArg (fun v : P.Face × BDL26FiniteTannerSquare.Two => v.2) hfg
  exact Prod.ext (Subtype.ext hfirst) hsecond

/-- At most fourteen actual faces occur in any X-star. -/
theorem xStarFace_card_le (P : TannerSquarePresentation) (h : BoundedValence P) (x : P.X) :
    Fintype.card (XStarFace P x) ≤ 14 := by
  have hi := Fintype.card_le_of_injective _ (xStarCornerWedge_injective P x)
  have hb : (∑ q : {q : P.Q // P.xq x q = true}, Fintype.card (QStarEdge P q.1)) ≤
      4 * xDegree P x := by
    calc
      _ ≤ ∑ _q : {q : P.Q // P.xq x q = true}, 4 :=
        Finset.sum_le_sum (fun q _ => (h.2.2 q.1).2.1)
      _ = _ := by simp [xDegree,Nat.mul_comm]
  have hd := h.1 x
  simp only [Fintype.card_prod, BDL26FiniteTannerSquare.Two, Fintype.card_fin,
    Fintype.card_sigma] at hi
  omega

/-- An admissible star has a face: its stored boundary root belongs to a face. -/
theorem xStarFace_nonempty (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) : Nonempty (XStarFace P x) := by
  rcases A.xBoundaryRoot x with ⟨v,hv⟩
  cases v with
  | x _ => simp [xStarBoundaryVertexMember] at hv
  | q q =>
      obtain ⟨f,hf,_⟩ := of_decide_eq_true hv
      exact ⟨⟨f,hf⟩⟩
  | z z =>
      obtain ⟨f,hf,_⟩ := of_decide_eq_true hv
      exact ⟨⟨f,hf⟩⟩

/-- Actual face corners cover the constructed local-star vertex carrier. -/
theorem xStarFaceCorner_surjective (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (x : P.X) :
    Function.Surjective (fun fc : XStarFace P x ×
      (BDL26FiniteTannerSquare.Two × BDL26FiniteTannerSquare.Two) =>
        xStarFaceCorner P x fc.1 fc.2) := by
  rintro ⟨v,hv⟩
  cases v with
  | x x' =>
      obtain ⟨f⟩ := xStarFace_nonempty P A x
      have hx' : x' = x := of_decide_eq_true hv
      have hfx : P.faceX f.1 = x := by simpa [xStarFaceMember] using f.2
      refine ⟨(f,(0,0)),Subtype.ext ?_⟩
      simp only [xStarFaceCorner_zero_zero,xStarFaceXVertex]
      rw [hfx,hx']
  | q q =>
      obtain ⟨f,hf,hq⟩ := of_decide_eq_true hv
      rcases hq with hq | hq
      · refine ⟨(⟨f,hf⟩,(1,0)),Subtype.ext ?_⟩
        simp only [xStarFaceCorner_one_zero,xStarFaceQVertex]
        rw [hq]
      · refine ⟨(⟨f,hf⟩,(0,1)),Subtype.ext ?_⟩
        simp only [xStarFaceCorner_zero_one,xStarFaceQVertex]
        rw [hq]
  | z z =>
      obtain ⟨f,hf,hz⟩ := of_decide_eq_true hv
      refine ⟨(⟨f,hf⟩,(1,1)),Subtype.ext ?_⟩
      simp only [xStarFaceCorner_one_one,xStarFaceZVertex]
      rw [hz]

/-- A finite bound on all local-star vertices, derived from actual face cover. -/
theorem xStarVertex_card_le (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (h : BoundedValence P) (x : P.X) : Fintype.card (XStarVertex P x) ≤ 56 := by
  have hc := Fintype.card_le_of_surjective _ (xStarFaceCorner_surjective P A x)
  have hf := xStarFace_card_le P h x
  simp only [Fintype.card_prod, BDL26FiniteTannerSquare.Two,Fintype.card_fin] at hc
  omega

/-- A face supplies two radial and two boundary edges in the exact carrier. -/
def xStarFaceEdge (P : TannerSquarePresentation) (x : P.X)
    (fe : XStarFace P x × (BDL26FiniteTannerSquare.Two × BDL26FiniteTannerSquare.Two)) :
    XStarEdge P x :=
  if fe.2.1 = 0 then xStarFaceXQEdge P x fe.1 fe.2.2
  else xStarFaceQZEdge P x fe.1 fe.2.2

theorem xStarFaceEdge_surjective (P : TannerSquarePresentation) (x : P.X) :
    Function.Surjective (xStarFaceEdge P x) := by
  rintro ⟨e,he⟩
  cases e with
  | inl e =>
      obtain ⟨f,hf,he⟩ := of_decide_eq_true he
      change decide (e = faceXQEdge P f 0 ∨ e = faceXQEdge P f 1) = true at he
      rcases of_decide_eq_true he with he | he
      · exact ⟨(⟨f,hf⟩,(0,0)),Subtype.ext (by simp [xStarFaceEdge,xStarFaceXQEdge,he])⟩
      · exact ⟨(⟨f,hf⟩,(0,1)),Subtype.ext (by simp [xStarFaceEdge,xStarFaceXQEdge,he])⟩
  | inr e =>
      obtain ⟨f,hf,he⟩ := of_decide_eq_true he
      change decide (e = faceQZEdge P f 0 ∨ e = faceQZEdge P f 1) = true at he
      rcases of_decide_eq_true he with he | he
      · exact ⟨(⟨f,hf⟩,(1,0)),Subtype.ext (by simp [xStarFaceEdge,xStarFaceQZEdge,he])⟩
      · exact ⟨(⟨f,hf⟩,(1,1)),Subtype.ext (by simp [xStarFaceEdge,xStarFaceQZEdge,he])⟩

theorem xStarEdge_card_le (P : TannerSquarePresentation) (h : BoundedValence P) (x : P.X) :
    Fintype.card (XStarEdge P x) ≤ 56 := by
  have hc := Fintype.card_le_of_surjective _ (xStarFaceEdge_surjective P x)
  have hf := xStarFace_card_le P h x
  simp only [Fintype.card_prod,BDL26FiniteTannerSquare.Two,Fintype.card_fin] at hc
  omega

/-- Forgetting only the boundary label embeds into the actual star-edge carrier. -/
def boundaryEdgeEmbedding (P : TannerSquarePresentation) (x : P.X) :
    XStarBoundaryEdge P x ↪ XStarEdge P x where
  toFun e := ⟨e.1,xStarBoundaryEdgeMember_to_star P x e.1 e.2⟩
  inj' := by
    intro e f h
    exact Subtype.ext (congrArg (fun a : XStarEdge P x => a.1) h)

theorem xStarBoundaryEdge_card_le (P : TannerSquarePresentation) (h : BoundedValence P)
    (x : P.X) : Fintype.card (XStarBoundaryEdge P x) ≤ 56 :=
  (Fintype.card_le_of_injective _ (boundaryEdgeEmbedding P x).injective).trans
    (xStarEdge_card_le P h x)

/-- Intrinsic local zero-cells fit the explicit quadratic envelope. -/
theorem doubleCylinderVertex_card_le (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (h : BoundedValence P) (x : P.X) (S : OddScale) :
    Fintype.card (DoubleCylinderVertex P x S) ≤ localCoordinateBound S := by
  have hv := xStarVertex_card_le P A h x
  have he := Nat.mul_le_mul_right (S.half-1) (xStarEdge_card_le P h x)
  have hf := Nat.mul_le_mul_right ((S.half-1)*(S.half-1)) (xStarFace_card_le P h x)
  have hm : S.half-1+1=S.half := by have hp:=S.half_pos; omega
  rw [doubleCylinderVertex_card]
  unfold localCoordinateBound
  rw [←S.two_half_add_one]
  nlinarith

/-- Degree-two X-local syndrome coordinates obey the same envelope. -/
theorem doubleCylinderFace_card_le (P : TannerSquarePresentation)
    (h : BoundedValence P) (x : P.X) (S : OddScale) :
    Fintype.card (DoubleCylinderFace P x S) ≤ localCoordinateBound S := by
  have hf := Nat.mul_le_mul_right (S.half^2) (xStarFace_card_le P h x)
  have hb := Nat.mul_le_mul_right S.half (xStarBoundaryEdge_card_le P h x)
  rw [doubleCylinderFace_card]
  unfold localCoordinateBound
  rw [←S.two_half_add_one]
  nlinarith

theorem qDoubleCylinderVertex_card_le (P : TannerSquarePresentation)
    (h : BoundedValence P) (q : P.Q) (S : OddScale) :
    Fintype.card (QDoubleCylinderVertex P q S) ≤ localCoordinateBound S := by
  have hd : Fintype.card (QStarEdge P q) ≤4 := (h.2.2 q).2.1
  have hm := Nat.mul_le_mul_right S.half hd
  rw [qDoubleCylinderVertex_card]
  unfold localCoordinateBound
  rw [←S.two_half_add_one]
  nlinarith

theorem qDoubleCylinderEdge_card_le (P : TannerSquarePresentation)
    (h : BoundedValence P) (q : P.Q) (S : OddScale) :
    Fintype.card (QDoubleCylinderEdge P q S) ≤ localCoordinateBound S := by
  have hd : Fintype.card (QStarEdge P q) ≤4 := (h.2.2 q).2.1
  have hm := Nat.mul_le_mul_right S.ell hd
  have hs := S.three_le
  rw [qDoubleCylinderEdge_card]
  unfold localCoordinateBound
  nlinarith

/-- Enumerate intrinsic zero-cells without imposing an external size assumption. -/
noncomputable instance rxZeroCellFintype (P : TannerSquarePresentation)
    (S : OddScale) (u : Vertex P) : Fintype (RXZeroCell P S u) := by
  classical
  cases u <;> dsimp [RXZeroCell] <;> infer_instance

noncomputable instance rzZeroCellFintype (P : TannerSquarePresentation)
    (S : OddScale) (u : Vertex P) : Fintype (RZZeroCell P S u) := by
  classical
  cases u <;> dsimp [RZZeroCell,ZDoubleCylinderVertex,DoubleCylinderVertex,
    transposePresentation,transposeTannerSquareData] <;> infer_instance

/-- The unchanged RX inclusion covers exactly the actual parent fiber. -/
theorem rxParentFiber_card_le (P : TannerSquarePresentation) (S : OddScale)
    (u : Vertex P) :
    Fintype.card {v : Vertex (rxReplacementPresentation P S) //
      rxParent P S v = some u} ≤ Fintype.card (RXZeroCell P S u) := by
  classical
  let f : RXZeroCell P S u → {v : Vertex (rxReplacementPresentation P S) //
      rxParent P S v = some u} :=
    fun a => ⟨rxZeroInclude P S u a,(rxParent_iff P S u _).mpr ⟨a,rfl⟩⟩
  apply Fintype.card_le_of_surjective f
  rintro ⟨v,hv⟩
  obtain ⟨a,ha⟩ := (rxParent_iff P S u v).mp hv
  exact ⟨a,Subtype.ext ha⟩

/-- The unchanged RZ inclusion likewise covers its materialized parent fiber. -/
theorem rzParentFiber_card_le (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (u : Vertex P) :
    Fintype.card {v : Vertex (BDL26RZLocalReplacement.rzReplacementPresentation P A S) //
      rzParent P A S v = some u} ≤ Fintype.card (RZZeroCell P S u) := by
  classical
  let f : RZZeroCell P S u →
      {v : Vertex (BDL26RZLocalReplacement.rzReplacementPresentation P A S) //
        rzParent P A S v = some u} :=
    fun a => ⟨rzZeroInclude P A S u a,(rzParent_iff P A S u _).mpr ⟨a,rfl⟩⟩
  apply Fintype.card_le_of_surjective f
  rintro ⟨v,hv⟩
  obtain ⟨a,ha⟩ := (rzParent_iff P A S u v).mp hv
  exact ⟨a,Subtype.ext ha⟩

/-- The RX local zero-cell envelope is independent of the depth. -/
theorem rxZeroCell_card_le (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (h : BoundedValence P) (S : OddScale) (u : Vertex P) :
    Fintype.card (RXZeroCell P S u) ≤ localCoordinateBound S := by
  cases u with
  | x x => exact doubleCylinderVertex_card_le P A h x S
  | q q => exact qDoubleCylinderVertex_card_le P h q S
  | z z =>
      have hs := S.three_le
      change Fintype.card (Fin 2) ≤ _
      simp only [Fintype.card_fin]
      unfold localCoordinateBound
      nlinarith

/-- Materialized RZ zero-cells satisfy the same quadratic envelope. -/
theorem rzZeroCell_card_le (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (h : BoundedValence P) (S : OddScale) (u : Vertex P) :
    Fintype.card (RZZeroCell P S u) ≤ localCoordinateBound S := by
  have ht := boundedValence_transpose P h
  cases u with
  | x x =>
      have hs := S.three_le
      change Fintype.card (Fin 2) ≤ _
      simp only [Fintype.card_fin]
      unfold localCoordinateBound
      nlinarith
  | q q => exact qDoubleCylinderVertex_card_le (transposePresentation P) ht q S
  | z z =>
      exact doubleCylinderVertex_card_le (transposePresentation P)
        (transposeTannerSquareAdmissible P A) ht z S

/-- Parent fibers of actual RX replacements have the explicit finite envelope. -/
theorem rxParentFiber_bound (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (h : BoundedValence P) (S : OddScale) (u : Vertex P) :
    Fintype.card {v : Vertex (rxReplacementPresentation P S) //
      rxParent P S v = some u} ≤ localCoordinateBound S :=
  (rxParentFiber_card_le P S u).trans (rxZeroCell_card_le P A h S u)

/-- Parent fibers of actual RZ replacements have the explicit finite envelope. -/
theorem rzParentFiber_bound (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (h : BoundedValence P) (S : OddScale) (u : Vertex P) :
    Fintype.card {v : Vertex (BDL26RZLocalReplacement.rzReplacementPresentation P A S) //
      rzParent P A S v = some u} ≤ localCoordinateBound S :=
  (rzParentFiber_card_le P A S u).trans (rzZeroCell_card_le P A h S u)

/-- Parity selection preserves the actual parent-fiber bound. -/
theorem nextParentFiber_bound (S : OddScale) (n : Nat) (C : ConstructionState)
    (hC : BoundedValence C.presentation) (u : Vertex C.presentation) :
    Fintype.card {v : Vertex (nextState S n C).presentation //
      nextParent S n C v = some u} ≤ localCoordinateBound S := by
  classical
  by_cases hn : n % 2 = 0
  · let f : {v : Vertex (nextState S n C).presentation // nextParent S n C v = some u} →
        {v : Vertex (rxReplacementPresentation C.presentation S) //
          rxParent C.presentation S v = some u} := fun v =>
      ⟨nextRXVertex S n C hn v.1, by
        simpa only [nextParent,dif_pos hn] using v.2⟩
    have hi : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      have hv := congrArg (fun v : {v : Vertex (rxReplacementPresentation C.presentation S) //
        rxParent C.presentation S v = some u} => v.1) hab
      exact (Equiv.cast (congrArg (fun D : ConstructionState => Vertex D.presentation)
        (show nextState S n C = rxState S C from if_pos hn))).injective hv
    exact (Fintype.card_le_of_injective f hi).trans
      (rxParentFiber_bound C.presentation C.admissible.toTannerSquareAdmissible hC S u)
  · let f : {v : Vertex (nextState S n C).presentation // nextParent S n C v = some u} →
        {v : Vertex (BDL26RZLocalReplacement.rzReplacementPresentation
          C.presentation C.admissible.toTannerSquareAdmissible S) //
          rzParent C.presentation C.admissible.toTannerSquareAdmissible S v = some u} := fun v =>
      ⟨nextRZVertex S n C hn v.1, by
        simpa only [nextParent,dif_neg hn] using v.2⟩
    have hi : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      have hv := congrArg (fun v : {v : Vertex (BDL26RZLocalReplacement.rzReplacementPresentation
        C.presentation C.admissible.toTannerSquareAdmissible S) //
        rzParent C.presentation C.admissible.toTannerSquareAdmissible S v = some u} => v.1) hab
      exact (Equiv.cast (congrArg (fun D : ConstructionState => Vertex D.presentation)
        (show nextState S n C = rzState S C from if_neg hn))).injective hv
    exact (Fintype.card_le_of_injective f hi).trans
      (rzParentFiber_bound C.presentation C.admissible.toTannerSquareAdmissible hC S u)

/-- The actual finite local region obeys one bound at every level. -/
theorem localRegion_card_le (S : OddScale) (n : Nat) (u : GraphVertex S n) :
    (localRegion S n u).card ≤ localCoordinateBound S := by
  classical
  have he : Fintype.card {v : GraphVertex S (n+1) // parent S n v = some u} =
      (localRegion S n u).card := by
    simp only [Fintype.card_subtype, parent_mem_iff]
    simp
  rw [←he]
  cases n with
  | zero =>
      cases u
      have hs := S.three_le
      simp only [parent,eq_self,Fintype.card_subtype_true]
      change 9 ≤ localCoordinateBound S
      unfold localCoordinateBound
      nlinarith
  | succ n =>
      exact nextParentFiber_bound S n (state S n) (state_boundedValence S n) u

namespace DegreeCover
open MultiscaleDecoder
variable {depth : Nat} {V : LevelIndex depth → Type}
variable [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]

abbrev Same (G : DecodingGraphFamily depth V) (u : G.Node) :=
  {y : V u.1 // (G.level u.1).skeleton.adjacent u.2 y}
abbrev Up (G : DecodingGraphFamily depth V) (u : G.Node) :=
  Σ s : {s : StepIndex depth // u.1 = s.castSucc},
    {y : V s.1.succ // G.interLevel s.1 (s.2 ▸ u.2) y = true}
abbrev Down (G : DecodingGraphFamily depth V) (u : G.Node) :=
  Σ s : {s : StepIndex depth // u.1 = s.succ},
    {y : V s.1.castSucc // G.interLevel s.1 y (s.2 ▸ u.2) = true}

/-- Each witness is an actual graph neighbor; truncation removes impossible steps. -/
def cover (G : DecodingGraphFamily depth V) (u : G.Node) :
    Same G u ⊕ (Up G u ⊕ Down G u) → {v : G.Node // G.adjacent u v}
  | .inl y => ⟨⟨u.1,y.1⟩, by
      left
      simpa only [dif_pos rfl,dite_true] using y.2⟩
  | .inr (.inl sy) => ⟨⟨sy.1.1.succ,sy.2.1⟩, by
      right; left
      exact ⟨sy.1.1,by simpa only [dif_pos sy.1.2,dif_pos rfl,dite_true] using sy.2.2⟩⟩
  | .inr (.inr sy) => ⟨⟨sy.1.1.castSucc,sy.2.1⟩, by
      right; right
      exact ⟨sy.1.1,by simpa only [dif_pos rfl,dif_pos sy.1.2,dite_true] using sy.2.2⟩⟩

theorem cover_surjective (G : DecodingGraphFamily depth V) (u : G.Node) :
    Function.Surjective (cover G u) := by
  rcases u with ⟨i,x⟩
  rintro ⟨⟨j,y⟩,h⟩
  rcases h with h | h | h
  · by_cases hij : i = j
    · subst j
      exact ⟨.inl ⟨y,by simpa only [dif_pos rfl,dite_true] using h⟩,rfl⟩
    · simp only [dif_neg hij] at h
  · obtain ⟨s,hs⟩ := h
    by_cases hi : i = s.castSucc
    · by_cases hj : j = s.succ
      · subst j
        exact ⟨.inr (.inl ⟨⟨s,hi⟩,y,
          by simpa only [dif_pos hi,dif_pos rfl,dite_true] using hs⟩),rfl⟩
      · simp only [dif_pos hi,dif_neg hj] at hs
    · simp only [dif_neg hi] at hs
  · obtain ⟨s,hs⟩ := h
    by_cases hj : j = s.castSucc
    · by_cases hi : i = s.succ
      · subst j
        exact ⟨.inr (.inr ⟨⟨s,hi⟩,y,
          by simpa only [dif_pos hi,dif_pos rfl,dite_true] using hs⟩),rfl⟩
      · simp only [dif_pos hj,dif_neg hi] at hs
    · simp only [dif_neg hj] at hs

/-- There is at most one successor step and at most one predecessor step. -/
instance upStepSubsingleton (i : LevelIndex depth) :
    Subsingleton {s : StepIndex depth // i = s.castSucc} where
  allEq a b := Subtype.ext (Fin.ext (by
    have h := congrArg Fin.val (a.2.symm.trans b.2)
    exact h))
instance downStepSubsingleton (i : LevelIndex depth) :
    Subsingleton {s : StepIndex depth // i = s.succ} where
  allEq a b := Subtype.ext (Fin.ext (by
    have h := congrArg Fin.val (a.2.symm.trans b.2)
    exact Nat.succ.inj h))

/-- Degree is bounded by measured same-level, outgoing and incoming neighborhoods. -/
theorem degree_bound (G : DecodingGraphFamily depth V) (u : G.Node) (M : Nat)
    (hlevel : ∀ (i : LevelIndex depth) (x : V i), Nat.card {y : V i // (G.level i).skeleton.adjacent x y} ≤ 7)
    (hup : ∀ (s : StepIndex depth) (x : V s.castSucc), Nat.card {y : V s.succ // G.interLevel s x y = true} ≤ M)
    (hdown : ∀ (s : StepIndex depth) (y : V s.succ), Nat.card {x : V s.castSucc // G.interLevel s x y = true} ≤ 1) :
    Nat.card {v : G.Node // G.adjacent u v} ≤ M + 8 := by
  classical
  have hc := Fintype.card_le_of_surjective _ (cover_surjective G u)
  have hl : Fintype.card (Same G u) ≤ 7 := by
    simpa only [Nat.card_eq_fintype_card] using hlevel u.1 u.2
  have hu : Fintype.card (Up G u) ≤ M := by
    calc
      _ = ∑ s : {s : StepIndex depth // u.1 = s.castSucc},
          Fintype.card {y : V s.1.succ // G.interLevel s.1 (s.2 ▸ u.2) y = true} :=
        Fintype.card_sigma
      _ ≤ ∑ _s : {s : StepIndex depth // u.1 = s.castSucc}, M := by
        apply Finset.sum_le_sum
        intro s _
        simpa only [Nat.card_eq_fintype_card] using hup s.1 (s.2 ▸ u.2)
      _ ≤ M := by
        simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
        exact (Nat.mul_le_mul_right M (Fintype.card_le_one_iff_subsingleton.mpr inferInstance)).trans_eq (one_mul M)
  have hd : Fintype.card (Down G u) ≤ 1 := by
    calc
      _ = ∑ s : {s : StepIndex depth // u.1 = s.succ},
          Fintype.card {y : V s.1.castSucc // G.interLevel s.1 y (s.2 ▸ u.2) = true} :=
        Fintype.card_sigma
      _ ≤ ∑ _s : {s : StepIndex depth // u.1 = s.succ}, 1 := by
        apply Finset.sum_le_sum
        intro s _
        simpa only [Nat.card_eq_fintype_card] using hdown s.1 (s.2 ▸ u.2)
      _ ≤ 1 := by simpa using (Fintype.card_le_one_iff_subsingleton.mpr (inferInstance : Subsingleton {s : StepIndex depth // u.1 = s.succ}))
  simp only [Fintype.card_sum] at hc
  rw [Nat.card_eq_fintype_card]
  omega
end DegreeCover

/-- Every actual truncation satisfies the same finite degree envelope.
The singleton root and top truncation are included in the finite witness cover. -/
theorem decodingGraph_degree_bound (S : OddScale) (depth : Nat)
    (u : (decodingGraph S depth).Node) :
    Nat.card {v : (decodingGraph S depth).Node //
      (decodingGraph S depth).adjacent u v} ≤ fullGraphDegreeBound S := by
  classical
  apply DegreeCover.degree_bound (decodingGraph S depth) u (localCoordinateBound S)
  · intro i x
    change Nat.card {y : GraphVertex S i.val //
      (level S i.val).skeleton.adjacent x y} ≤ 7
    rcases i with ⟨n,hn⟩
    cases n with
    | zero => simp [level,rootLevel]
    | succ n =>
        change Nat.card {y : Vertex (state S n).presentation //
          tannerAdjacent (state S n).presentation x y} ≤ 7
        letI : DecidablePred (tannerAdjacent (state S n).presentation x) :=
          tannerAdjacentDecidable (state S n).presentation x
        rw [Nat.card_eq_fintype_card]
        exact state_tannerDegree_le S n x
  · intro s x
    change Nat.card {y : GraphVertex S (s.val+1) //
      decide (y ∈ localRegion S s.val x) = true} ≤ localCoordinateBound S
    simpa only [decide_eq_true_eq,Nat.card_eq_fintype_card,Fintype.card_coe] using
      localRegion_card_le S s.val x
  · intro s y
    change Nat.card {x : GraphVertex S s.val //
      decide (y ∈ localRegion S s.val x) = true} ≤ 1
    simpa only [decide_eq_true_eq,Nat.card_eq_fintype_card] using
      parentNeighbors_card_le S s.val y

open BDL26ReplacementSupport

/-- The degree-two coordinates of each actual RX local block. -/
def RXSyndromeCell (P : TannerSquarePresentation) (S : OddScale) : Vertex P → Type
  | .x x => DoubleCylinderFace P x S
  | .q q => QDoubleCylinderEdge P q S
  | .z _ => BDL26FiniteTannerSquare.Two

noncomputable instance rxSyndromeCellFintype (P : TannerSquarePresentation)
    (S : OddScale) (u : Vertex P) : Fintype (RXSyndromeCell P S u) := by
  classical
  cases u <;> dsimp [RXSyndromeCell] <;> infer_instance

/-- The cardinality counts syndrome coordinates rather than the union of all cells. -/
theorem rxSyndromeCell_card_le (P : TannerSquarePresentation) (h : BoundedValence P)
    (S : OddScale) (u : Vertex P) :
    Fintype.card (RXSyndromeCell P S u) ≤ localCoordinateBound S := by
  cases u with
  | x x => exact doubleCylinderFace_card_le P h x S
  | q q => exact qDoubleCylinderEdge_card_le P h q S
  | z z =>
      have hs := S.three_le
      change Fintype.card (Fin 2) ≤ _
      simp only [Fintype.card_fin]
      unfold localCoordinateBound
      nlinarith

/-- Include the actual degree-two RX carrier in its unchanged owner fiber. -/
def rxSyndromeCellToFiber (P : TannerSquarePresentation) (S : OddScale) :
    (u : Vertex P) → RXSyndromeCell P S u →
      {c : RX2 P S // rxSyndromeOwner P S c = u}
  | .x x, a => ⟨.inl (.inl ⟨x,a⟩),rfl⟩
  | .q q, a => ⟨.inl (.inr ⟨q,a⟩),rfl⟩
  | .z z, a => ⟨.inr (z,a),rfl⟩

theorem rxSyndromeCellToFiber_surjective (P : TannerSquarePresentation) (S : OddScale)
    (u : Vertex P) : Function.Surjective (rxSyndromeCellToFiber P S u) := by
  rintro ⟨c,hc⟩
  rcases c with (⟨x,a⟩ | ⟨q,a⟩) | ⟨z,a⟩
  · change Vertex.x x = u at hc
    subst u
    exact ⟨a,rfl⟩
  · change Vertex.q q = u at hc
    subst u
    exact ⟨a,rfl⟩
  · change Vertex.z z = u at hc
    subst u
    exact ⟨a,rfl⟩

/-- The measured actual RX syndrome-owner fiber has the finite quadratic bound. -/
theorem rxSyndromeFiber_card_le (P : TannerSquarePresentation) (h : BoundedValence P)
    (S : OddScale) (u : Vertex P) :
    Fintype.card {c : RX2 P S // rxSyndromeOwner P S c = u} ≤ localCoordinateBound S :=
  (Fintype.card_le_of_surjective _ (rxSyndromeCellToFiber_surjective P S u)).trans
    (rxSyndromeCell_card_le P h S u)

/-- RZ syndrome coordinates are intrinsic vertices of the transposed Z cylinder. -/
theorem rzSyndromeFiber_card_le (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (h : BoundedValence P) (S : OddScale) (z : P.Z) :
    Fintype.card {c : BDL26RZLocalReplacement.RZZ P S //
      rzSyndromeOwner P S c = z} ≤ localCoordinateBound S := by
  classical
  let f : ZDoubleCylinderVertex P z S →
      {c : BDL26RZLocalReplacement.RZZ P S // rzSyndromeOwner P S c = z} :=
    fun a => ⟨⟨z,a⟩,rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨⟨z',a⟩,hz⟩
    change z' = z at hz
    subst z'
    exact ⟨a,rfl⟩
  exact (Fintype.card_le_of_surjective f hf).trans
    (doubleCylinderVertex_card_le (transposePresentation P)
      (transposeTannerSquareAdmissible P A) (boundedValence_transpose P h) z S)

/-- Actual maximum syndrome-fiber size over both replacement orientations. -/
noncomputable def maxLocalSyndromeSize (P : TannerSquarePresentation) (S : OddScale) : Nat :=
  max (Finset.univ.sup (fun u : Vertex P =>
      Nat.card {c : RX2 P S // rxSyndromeOwner P S c = u}))
    (Finset.univ.sup (fun z : P.Z =>
      Nat.card {c : BDL26RZLocalReplacement.RZZ P S // rzSyndromeOwner P S c = z}))

/-- The measured maximum is bounded by the exported budget, not equated to it. -/
theorem maxLocalSyndromeSize_le (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (h : BoundedValence P) (S : OddScale) :
    maxLocalSyndromeSize P S ≤ localCoordinateBound S := by
  classical
  apply max_le
  · apply Finset.sup_le
    intro u _
    simpa only [Nat.card_eq_fintype_card] using rxSyndromeFiber_card_le P h S u
  · apply Finset.sup_le
    intro z _
    simpa only [Nat.card_eq_fintype_card] using rzSyndromeFiber_card_le P A h S z

/-- Actual maximum degree of a finite decoding-graph truncation. -/
noncomputable def maxDecodingGraphDegree (S : OddScale) (depth : Nat) : Nat :=
  Finset.univ.sup (fun u : (decodingGraph S depth).Node =>
    Nat.card {v : (decodingGraph S depth).Node // (decodingGraph S depth).adjacent u v})

theorem maxDecodingGraphDegree_le (S : OddScale) (depth : Nat) :
    maxDecodingGraphDegree S depth ≤ fullGraphDegreeBound S := by
  classical
  apply Finset.sup_le
  intro u _
  exact decodingGraph_degree_bound S depth u

/-- The F16 size envelope holds for every actual recursive presentation. -/
theorem state_maxLocalSyndromeSize_le (S : OddScale) (n : Nat) :
    maxLocalSyndromeSize (state S n).presentation S ≤ localCoordinateBound S :=
  maxLocalSyndromeSize_le _ (state S n).admissible.toTannerSquareAdmissible
    (state_boundedValence S n) S

end QEC.Coding.BDL26GraphQuantitativeBounds
