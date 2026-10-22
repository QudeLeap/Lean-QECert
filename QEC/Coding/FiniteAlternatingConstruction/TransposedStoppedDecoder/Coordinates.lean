import QEC.Coding.FiniteAlternatingConstruction.RXDecoderAdapter.Reindex
import QEC.Coding.FiniteAlternatingConstruction.RXPresentationCochain
import QEC.Coding.FiniteAlternatingConstruction.RZDecoderAdapter

/-!
# Literal transpose coordinates for the stopped dual decoder

BDL26 v1, paper.tex:2296-2319, defines Z decoding on the dual complex.
The physical Q carrier is retained literally; replacement tags, ordered
face corners and all labels are retained. No decoder or stability result
is supplied by a caller.
-/

noncomputable section
namespace QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement hiding Two
open BDL26RZLocalReplacement hiding Two
open BDL26RZMap1CoordinateBridge hiding Two
open BDL26RXDecoderAdapter
open MultiscaleDecoder (BDL26Field)
open scoped Classical BigOperators

private theorem bool_eq_of_true_iff {a b : Bool} (h : (a = true) ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

@[simp] theorem transpose_transpose (P : TannerSquarePresentation) :
    transposePresentation (transposePresentation P) = P := by
  cases P
  rfl

/-- Actual X-Q incidence is recovered from an ordered face corner. -/
theorem xq_iff_face_corner (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (x : P.X) (q : P.Q) :
    P.xq x q = true ↔
      ∃ f : P.Face, ∃ b : Two, P.faceX f = x ∧ P.faceQ f b = q := by
  constructor
  · intro h
    let z := (A.qzRoot q).val
    let shared : SharedQ P.data x z := ⟨q, by
      change (P.xq x q && P.qz q z) = true
      simp [h,z,(A.qzRoot q).property]⟩
    obtain ⟨c, hc⟩ := (P.perfectPairing x z).surjective shared
    exact ⟨c.1.val, c.2, c.1.property.1, congrArg Subtype.val hc⟩
  · rintro ⟨f,b,hx,hq⟩
    simpa only [hx,hq] using P.data.faceQ_xq f b

/-- Actual Q-Z incidence is recovered from an ordered face corner. -/
theorem qz_iff_face_corner (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q) (z : P.Z) :
    P.qz q z = true ↔
      ∃ f : P.Face, ∃ b : Two, P.faceZ f = z ∧ P.faceQ f b = q := by
  constructor
  · intro h
    let x := (A.xqRoot q).val
    let shared : SharedQ P.data x z := ⟨q, by
      change (P.xq x q && P.qz q z) = true
      simp [h,x,(A.xqRoot q).property]⟩
    obtain ⟨c, hc⟩ := (P.perfectPairing x z).surjective shared
    exact ⟨c.1.val, c.2, c.1.property.2, congrArg Subtype.val hc⟩
  · rintro ⟨f,b,hz,hq⟩
    simpa only [hz,hq] using P.data.faceQ_qz f b

/-- Primitive face equations derive X-Q incidence conjugacy. -/
theorem xq_of_face_equiv (P R : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (B : TannerSquareAdmissible R)
    (eX : P.X ≃ R.X) (eQ : P.Q ≃ R.Q) (eF : P.Face ≃ R.Face)
    (hX : ∀ f, R.faceX (eF f) = eX (P.faceX f))
    (hQ : ∀ f b, R.faceQ (eF f) b = eQ (P.faceQ f b))
    (x : P.X) (q : P.Q) : R.xq (eX x) (eQ q) = P.xq x q := by
  apply bool_eq_of_true_iff
  rw [xq_iff_face_corner R B, xq_iff_face_corner P A]
  constructor
  · rintro ⟨f,b,hx,hq⟩
    refine ⟨eF.symm f,b,?_,?_⟩
    · apply eX.injective
      simpa only [← hX, Equiv.apply_symm_apply] using hx
    · apply eQ.injective
      simpa only [← hQ, Equiv.apply_symm_apply] using hq
  · rintro ⟨f,b,hx,hq⟩
    exact ⟨eF f,b,by rw [hX,hx],by rw [hQ,hq]⟩

/-- Primitive face equations derive Q-Z incidence conjugacy. -/
theorem qz_of_face_equiv (P R : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (B : TannerSquareAdmissible R)
    (eQ : P.Q ≃ R.Q) (eZ : P.Z ≃ R.Z) (eF : P.Face ≃ R.Face)
    (hZ : ∀ f, R.faceZ (eF f) = eZ (P.faceZ f))
    (hQ : ∀ f b, R.faceQ (eF f) b = eQ (P.faceQ f b))
    (q : P.Q) (z : P.Z) : R.qz (eQ q) (eZ z) = P.qz q z := by
  apply bool_eq_of_true_iff
  rw [qz_iff_face_corner R B, qz_iff_face_corner P A]
  constructor
  · rintro ⟨f,b,hz,hq⟩
    refine ⟨eF.symm f,b,?_,?_⟩
    · apply eZ.injective
      simpa only [← hZ, Equiv.apply_symm_apply] using hz
    · apply eQ.injective
      simpa only [← hQ, Equiv.apply_symm_apply] using hq
  · rintro ⟨f,b,hz,hq⟩
    exact ⟨eF f,b,by rw [hZ,hz],by rw [hQ,hq]⟩

/-- Finite coordinate transport of the actual degree-zero Tanner map. -/
theorem coboundary0_transport (P R : TannerSquarePresentation)
    (eX : P.X ≃ R.X) (eQ : P.Q ≃ R.Q)
    (h : ∀ x q, R.xq (eX x) (eQ q) = P.xq x q)
    (w : Word BDL26Field P.X) (q : P.Q) :
    tannerCoboundary0 R (wordEquiv eX w) (eQ q) =
      tannerCoboundary0 P w q := by
  change (∑ x : R.X, wordEquiv eX w x *
      if R.xq x (eQ q) = true then 1 else 0) = _
  rw [← Equiv.sum_comp eX]
  apply Finset.sum_congr rfl
  intro x _
  rw [h]
  simp only [wordEquiv_apply,Equiv.symm_apply_apply]

/-- Finite coordinate transport of the actual degree-one Tanner map. -/
theorem coboundary1_transport (P R : TannerSquarePresentation)
    (eQ : P.Q ≃ R.Q) (eZ : P.Z ≃ R.Z)
    (h : ∀ q z, R.qz (eQ q) (eZ z) = P.qz q z)
    (w : Word BDL26Field P.Q) (z : P.Z) :
    tannerCoboundary1 R (wordEquiv eQ w) (eZ z) =
      tannerCoboundary1 P w z := by
  change (∑ q : R.Q, wordEquiv eQ w q *
      if R.qz q (eZ z) = true then 1 else 0) = _
  rw [← Equiv.sum_comp eQ]
  apply Finset.sum_congr rfl
  intro q _
  rw [h]
  simp only [wordEquiv_apply,Equiv.symm_apply_apply]

/-- Degree-zero coordinates of T(RX(P)) are the materialized dual RZ tags. -/
def rxDualX (P : TannerSquarePresentation) (S : OddScale) :
    RX2 P S ≃ RZX (transposePresentation P) S := Equiv.refl _

/-- The same physical coordinate, including the full cylinder/vertex tag. -/
def rxDualQ (P : TannerSquarePresentation) (S : OddScale) :
    RX1 P S ≃ RZQ (transposePresentation P) S := Equiv.refl _

/-- Degree-two coordinates of T(RX(P)) retain every local vertex tag. -/
def rxDualZ (P : TannerSquarePresentation) (S : OddScale) :
    RX0 P S ≃ RZZ (transposePresentation P) S := Equiv.refl _

/-- Every face family and its ordered copy/corner tags are retained. -/
def rxDualFace (P : TannerSquarePresentation) (S : OddScale) :
    RXFace P S ≃ RZFace (transposePresentation P) S where
  toFun
    | .inl ⟨x,f,b⟩ => .inl ⟨x,f,b⟩
    | .inr (.inl ⟨a,e,b⟩) =>
        .inr (.inl ⟨(transposeQZEdgeEquiv P).symm a,e,b⟩)
    | .inr (.inr ⟨f,b⟩) => .inr (.inr ⟨f,b⟩)
  invFun
    | .inl ⟨x,f,b⟩ => .inl ⟨x,f,b⟩
    | .inr (.inl ⟨a,e,b⟩) =>
        .inr (.inl ⟨transposeQZEdgeEquiv P a,e,b⟩)
    | .inr (.inr ⟨f,b⟩) => .inr (.inr ⟨f,b⟩)
  left_inv := by
    rintro (⟨x,f,b⟩ | (⟨a,e,b⟩ | ⟨f,b⟩)) <;> rfl
  right_inv := by
    rintro (⟨x,f,b⟩ | (⟨a,e,b⟩ | ⟨f,b⟩)) <;> rfl

def rzDualX (P : TannerSquarePresentation) (S : OddScale) :
    RZZ P S ≃ RX0 (transposePresentation P) S := Equiv.refl _

def rzDualQ (P : TannerSquarePresentation) (S : OddScale) :
    RZQ P S ≃ RX1 (transposePresentation P) S := Equiv.refl _

def rzDualZ (P : TannerSquarePresentation) (S : OddScale) :
    RZX P S ≃ RX2 (transposePresentation P) S := Equiv.refl _

/-- Opposite replacement direction, using the actual Q-Z incidence tags. -/
def rzDualFace (P : TannerSquarePresentation) (S : OddScale) :
    RZFace P S ≃ RXFace (transposePresentation P) S where
  toFun
    | .inl ⟨z,f,b⟩ => .inl ⟨z,f,b⟩
    | .inr (.inl ⟨a,e,b⟩) =>
        .inr (.inl ⟨(transposeXQEdgeEquiv P).symm a,e,b⟩)
    | .inr (.inr ⟨f,b⟩) => .inr (.inr ⟨f,b⟩)
  invFun
    | .inl ⟨z,f,b⟩ => .inl ⟨z,f,b⟩
    | .inr (.inl ⟨a,e,b⟩) =>
        .inr (.inl ⟨transposeXQEdgeEquiv P a,e,b⟩)
    | .inr (.inr ⟨f,b⟩) => .inr (.inr ⟨f,b⟩)
  left_inv := by
    rintro (⟨z,f,b⟩ | (⟨a,e,b⟩ | ⟨f,b⟩)) <;> rfl
  right_inv := by
    rintro (⟨z,f,b⟩ | (⟨a,e,b⟩ | ⟨f,b⟩)) <;> rfl

@[simp] theorem rxDualFace_left_inverse (P : TannerSquarePresentation) (S : OddScale)
    (f : RXFace P S) : (rxDualFace P S).symm (rxDualFace P S f) = f :=
  (rxDualFace P S).symm_apply_apply f

@[simp] theorem rxDualFace_right_inverse (P : TannerSquarePresentation) (S : OddScale)
    (f : RZFace (transposePresentation P) S) :
    rxDualFace P S ((rxDualFace P S).symm f) = f :=
  (rxDualFace P S).apply_symm_apply f

@[simp] theorem rzDualFace_left_inverse (P : TannerSquarePresentation) (S : OddScale)
    (f : RZFace P S) : (rzDualFace P S).symm (rzDualFace P S f) = f :=
  (rzDualFace P S).symm_apply_apply f

@[simp] theorem rzDualFace_right_inverse (P : TannerSquarePresentation) (S : OddScale)
    (f : RXFace (transposePresentation P) S) :
    rzDualFace P S ((rzDualFace P S).symm f) = f :=
  (rzDualFace P S).apply_symm_apply f


/-- The actual transpose-derived edge is the root-free raw RX edge.
This is an explicit coordinate equality, not proof irrelevance of A. -/
theorem qToZ_edge_raw (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (z : P.Z) (hz : P.qz q z = true) (S : OddScale)
    (e : QDoubleCylinderEdge (transposePresentation P) q S) :
    qToZDoubleCylinderEdge P A q z hz S e =
      qToXDoubleCylinderEdgeRaw (transposePresentation P) q z hz S e := by
  rcases e with ⟨copy,e⟩ | v <;> rfl

/-- All raw center/neighbor/interior tags coincide. The chosen root edge
does not alter the fixed Q center; no path/owner record is identified. -/
theorem qToZ_vertex_raw (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (z : P.Z) (hz : P.qz q z = true) (S : OddScale)
    (root : QStarEdge (transposePresentation P) q)
    (v : QDoubleCylinderVertex (transposePresentation P) q S) :
    qToZDoubleCylinderVertex P A q z hz S v =
      qToXDoubleCylinderVertexAtRoot (transposePresentation P) q z hz S root v := by
  rcases v with ⟨copy, old | interior⟩
  · rcases old with center | neighbor <;> rfl
  · rfl

/-- Transposing RX retains the exact ordered face's first check endpoint. -/
theorem rxDualFace_X (P : TannerSquarePresentation) (S : OddScale)
    (f : RXFace P S) :
    rzFaceX (transposePresentation P) S (rxDualFace P S f) =
      rxDualX P S (rxFaceZ P S f) := by
  rcases f with ⟨x,f,b⟩ | (⟨a,e,b⟩ | ⟨f,b⟩) <;> rfl

/-- The other check endpoint retains the actual raw glue endpoint. -/
theorem rxDualFace_Z (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible (transposePresentation P)) (S : OddScale)
    (f : RXFace P S) :
    rzFaceZ (transposePresentation P) A S (rxDualFace P S f) =
      rxDualZ P S (rxFaceX P S f) := by
  rcases f with ⟨x,f,b⟩ | (⟨a,e,b⟩ | ⟨f,b⟩)
  · rcases f with copy | boundary
    · rfl
    · rcases b with ⟨copy,corner⟩
      fin_cases corner <;> rfl
  · let root := qDoubleCylinderUnderlyingStarEdge P a.1.2 S e
    refine (congrArg (fun v : DoubleCylinderVertex P a.1.1 S =>
      (⟨a.1.1,v⟩ : RX0 P S))
      (qToZ_vertex_raw (transposePresentation P) A a.1.2 a.1.1 a.2 S root
        (BDL26RZLocalReplacement.edgeEndpoint (qDoubleCylinderEdgeStart P a.1.2 S)
          (qDoubleCylinderEdgeEnd P a.1.2 S) e b))).trans ?_
    fin_cases b
    · exact congrArg (fun v => (⟨a.1.1,v⟩ : RX0 P S))
        (qToXDoubleCylinderEdgeRaw_start P a.1.2 a.1.1 a.2 S root e)
    · exact congrArg (fun v => (⟨a.1.1,v⟩ : RX0 P S))
        (qToXDoubleCylinderEdgeRaw_end P a.1.2 a.1.1 a.2 S root e)
  · rfl

/-- Both ordered Q corners commute; neither corner order nor pieces are changed. -/
theorem rxDualFace_Q (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible (transposePresentation P)) (S : OddScale)
    (f : RXFace P S) (b : Two) :
    rzFaceQ (transposePresentation P) A S (rxDualFace P S f) b =
      rxDualQ P S (rxFaceQ P S f b) := by
  rcases f with ⟨x,f,c⟩ | (⟨a,e,c⟩ | ⟨f,c⟩)
  · rcases f with copy | boundary
    · rcases c with ⟨horizontal,vertical⟩
      fin_cases horizontal <;> fin_cases vertical <;> fin_cases b <;> rfl
    · rcases c with ⟨copy,corner⟩
      fin_cases corner <;> fin_cases b <;> rfl
  · fin_cases b
    · exact congrArg (fun w : DoubleCylinderEdge P a.1.1 S =>
        (Sum.inl (⟨a.1.1,w⟩ : Sigma fun x : P.X => DoubleCylinderEdge P x S) : RX1 P S))
        (qToZ_edge_raw (transposePresentation P) A a.1.2 a.1.1 a.2 S e)
    · rfl
  · rfl

/-- The opposite direction uses the original actual RZ admissibility data. -/
theorem rzDualFace_X (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (f : RZFace P S) :
    rxFaceX (transposePresentation P) S (rzDualFace P S f) =
      rzDualX P S (rzFaceZ P A S f) := by
  rcases f with ⟨z,f,b⟩ | (⟨a,e,b⟩ | ⟨f,b⟩)
  · rcases f with copy | boundary
    · rfl
    · rcases b with ⟨copy,corner⟩
      fin_cases corner <;> rfl
  · let root := qDoubleCylinderUnderlyingStarEdge (transposePresentation P) a.1.1 S e
    let v := BDL26RZLocalReplacement.edgeEndpoint
      (qDoubleCylinderEdgeStart (transposePresentation P) a.1.1 S)
      (qDoubleCylinderEdgeEnd (transposePresentation P) a.1.1 S) e b
    have hedge : BDL26RXLocalReplacement.edgeEndpoint
        (tannerDoubleCylinderEdgeStart (transposePresentation P) a.1.2 S)
        (tannerDoubleCylinderEdgeEnd (transposePresentation P) a.1.2 S)
        (qToXDoubleCylinderEdgeRaw (transposePresentation P) a.1.1 a.1.2 a.2 S e) b =
        qToXDoubleCylinderVertexAtRoot (transposePresentation P) a.1.1 a.1.2 a.2 S root v := by
      fin_cases b
      · exact (qToXDoubleCylinderEdgeRaw_start (transposePresentation P) a.1.1 a.1.2 a.2 S root e).symm
      · exact (qToXDoubleCylinderEdgeRaw_end (transposePresentation P) a.1.1 a.1.2 a.2 S root e).symm
    exact congrArg (fun w : DoubleCylinderVertex (transposePresentation P) a.1.2 S =>
      (⟨a.1.2,w⟩ : RX0 (transposePresentation P) S))
      (hedge.trans (qToZ_vertex_raw P A a.1.1 a.1.2 a.2 S root v).symm)
  · rfl

theorem rzDualFace_Z (P : TannerSquarePresentation) (S : OddScale)
    (f : RZFace P S) :
    rxFaceZ (transposePresentation P) S (rzDualFace P S f) =
      rzDualZ P S (rzFaceX P S f) := by
  rcases f with ⟨z,f,b⟩ | (⟨a,e,b⟩ | ⟨f,b⟩) <;> rfl

theorem rzDualFace_Q (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (f : RZFace P S) (b : Two) :
    rxFaceQ (transposePresentation P) S (rzDualFace P S f) b =
      rzDualQ P S (rzFaceQ P A S f b) := by
  rcases f with ⟨z,f,c⟩ | (⟨a,e,c⟩ | ⟨f,c⟩)
  · rcases f with copy | boundary
    · rcases c with ⟨horizontal,vertical⟩
      fin_cases horizontal <;> fin_cases vertical <;> fin_cases b <;> rfl
    · rcases c with ⟨copy,corner⟩
      fin_cases corner <;> fin_cases b <;> rfl
  · fin_cases b
    · exact (congrArg (fun w : DoubleCylinderEdge (transposePresentation P) a.1.2 S =>
        (Sum.inl (⟨a.1.2,w⟩ : Sigma fun z : P.Z =>
          DoubleCylinderEdge (transposePresentation P) z S) : RX1 (transposePresentation P) S))
        (qToZ_edge_raw P A a.1.1 a.1.2 a.2 S e)).symm
    · rfl
  · rfl


/-- Actual RX successor incidence, with both admissibilities derived. -/
theorem rxDual_xq (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (x : (transposePresentation (rxReplacementPresentation P S)).X) (q : (transposePresentation (rxReplacementPresentation P S)).Q) :
    (rzReplacementPresentation (transposePresentation P)
      (transposeTannerSquareAdmissibleV4 P A).toTannerSquareAdmissible S).xq (rxDualX P S x) (rxDualQ P S q) = (transposePresentation (rxReplacementPresentation P S)).xq x q := by
  apply xq_of_face_equiv (transposePresentation (rxReplacementPresentation P S)) (rzReplacementPresentation (transposePresentation P)
      (transposeTannerSquareAdmissibleV4 P A).toTannerSquareAdmissible S)
    (transposeTannerSquareAdmissibleV4 (rxReplacementPresentation P S)
      (rxReplacementAdmissibleV4 P A R S)).toTannerSquareAdmissible
    (rzReplacementAdmissibleV4 (transposePresentation P)
      (transposeTannerSquareAdmissibleV4 P A) (transposeTannerSquareCellularRegular P R) S).toTannerSquareAdmissible (rxDualX P S) (rxDualQ P S) (rxDualFace P S)
  · exact rxDualFace_X P S
  · exact rxDualFace_Q P (transposeTannerSquareAdmissibleV4 P A).toTannerSquareAdmissible S

/-- Actual RX successor incidence, with both admissibilities derived. -/
theorem rxDual_qz (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (q : (transposePresentation (rxReplacementPresentation P S)).Q) (z : (transposePresentation (rxReplacementPresentation P S)).Z) :
    (rzReplacementPresentation (transposePresentation P)
      (transposeTannerSquareAdmissibleV4 P A).toTannerSquareAdmissible S).qz (rxDualQ P S q) (rxDualZ P S z) = (transposePresentation (rxReplacementPresentation P S)).qz q z := by
  apply qz_of_face_equiv (transposePresentation (rxReplacementPresentation P S)) (rzReplacementPresentation (transposePresentation P)
      (transposeTannerSquareAdmissibleV4 P A).toTannerSquareAdmissible S)
    (transposeTannerSquareAdmissibleV4 (rxReplacementPresentation P S)
      (rxReplacementAdmissibleV4 P A R S)).toTannerSquareAdmissible
    (rzReplacementAdmissibleV4 (transposePresentation P)
      (transposeTannerSquareAdmissibleV4 P A) (transposeTannerSquareCellularRegular P R) S).toTannerSquareAdmissible (rxDualQ P S) (rxDualZ P S) (rxDualFace P S)
  · exact rxDualFace_Z P (transposeTannerSquareAdmissibleV4 P A).toTannerSquareAdmissible S
  · exact rxDualFace_Q P (transposeTannerSquareAdmissibleV4 P A).toTannerSquareAdmissible S

/-- The literal successor coordinate equivalence intertwines degree 0. -/
theorem rxDual_coboundary0 (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale)
    (w : Word BDL26Field (transposePresentation (rxReplacementPresentation P S)).X) :
    tannerCoboundary0 (rzReplacementPresentation (transposePresentation P)
      (transposeTannerSquareAdmissibleV4 P A).toTannerSquareAdmissible S) (wordEquiv (rxDualX P S) w) =
      wordEquiv (rxDualQ P S) (tannerCoboundary0 (transposePresentation (rxReplacementPresentation P S)) w) := by
  funext z
  obtain ⟨z,rfl⟩ := (rxDualQ P S).surjective z
  change _ = tannerCoboundary0 (transposePresentation (rxReplacementPresentation P S)) w z
  exact
    coboundary0_transport (transposePresentation (rxReplacementPresentation P S)) (rzReplacementPresentation (transposePresentation P)
      (transposeTannerSquareAdmissibleV4 P A).toTannerSquareAdmissible S)
      (rxDualX P S) (rxDualQ P S) (rxDual_xq P A R S) w z

/-- The literal successor coordinate equivalence intertwines degree 1. -/
theorem rxDual_coboundary1 (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale)
    (w : Word BDL26Field (transposePresentation (rxReplacementPresentation P S)).Q) :
    tannerCoboundary1 (rzReplacementPresentation (transposePresentation P)
      (transposeTannerSquareAdmissibleV4 P A).toTannerSquareAdmissible S) (wordEquiv (rxDualQ P S) w) =
      wordEquiv (rxDualZ P S) (tannerCoboundary1 (transposePresentation (rxReplacementPresentation P S)) w) := by
  funext z
  obtain ⟨z,rfl⟩ := (rxDualZ P S).surjective z
  change _ = tannerCoboundary1 (transposePresentation (rxReplacementPresentation P S)) w z
  exact
    coboundary1_transport (transposePresentation (rxReplacementPresentation P S)) (rzReplacementPresentation (transposePresentation P)
      (transposeTannerSquareAdmissibleV4 P A).toTannerSquareAdmissible S)
      (rxDualQ P S) (rxDualZ P S) (rxDual_qz P A R S) w z

/-- Actual RZ successor incidence, with both admissibilities derived. -/
theorem rzDual_xq (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (x : (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)).X) (q : (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)).Q) :
    (rxReplacementPresentation (transposePresentation P) S).xq (rzDualX P S x) (rzDualQ P S q) = (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)).xq x q := by
  apply xq_of_face_equiv (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)) (rxReplacementPresentation (transposePresentation P) S)
    (transposeTannerSquareAdmissibleV4
      (rzReplacementPresentation P A.toTannerSquareAdmissible S)
      (rzReplacementAdmissibleV4 P A R S)).toTannerSquareAdmissible
    (rxReplacementAdmissibleV4 (transposePresentation P)
      (transposeTannerSquareAdmissibleV4 P A) (transposeTannerSquareCellularRegular P R) S).toTannerSquareAdmissible (rzDualX P S) (rzDualQ P S) (rzDualFace P S)
  · exact rzDualFace_X P A.toTannerSquareAdmissible S
  · exact rzDualFace_Q P A.toTannerSquareAdmissible S

/-- Actual RZ successor incidence, with both admissibilities derived. -/
theorem rzDual_qz (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (q : (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)).Q) (z : (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)).Z) :
    (rxReplacementPresentation (transposePresentation P) S).qz (rzDualQ P S q) (rzDualZ P S z) = (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)).qz q z := by
  apply qz_of_face_equiv (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)) (rxReplacementPresentation (transposePresentation P) S)
    (transposeTannerSquareAdmissibleV4
      (rzReplacementPresentation P A.toTannerSquareAdmissible S)
      (rzReplacementAdmissibleV4 P A R S)).toTannerSquareAdmissible
    (rxReplacementAdmissibleV4 (transposePresentation P)
      (transposeTannerSquareAdmissibleV4 P A) (transposeTannerSquareCellularRegular P R) S).toTannerSquareAdmissible (rzDualQ P S) (rzDualZ P S) (rzDualFace P S)
  · exact rzDualFace_Z P S
  · exact rzDualFace_Q P A.toTannerSquareAdmissible S

/-- The literal successor coordinate equivalence intertwines degree 0. -/
theorem rzDual_coboundary0 (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale)
    (w : Word BDL26Field (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)).X) :
    tannerCoboundary0 (rxReplacementPresentation (transposePresentation P) S) (wordEquiv (rzDualX P S) w) =
      wordEquiv (rzDualQ P S) (tannerCoboundary0 (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)) w) := by
  funext z
  obtain ⟨z,rfl⟩ := (rzDualQ P S).surjective z
  change _ = tannerCoboundary0 (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)) w z
  exact
    coboundary0_transport (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)) (rxReplacementPresentation (transposePresentation P) S)
      (rzDualX P S) (rzDualQ P S) (rzDual_xq P A R S) w z

/-- The literal successor coordinate equivalence intertwines degree 1. -/
theorem rzDual_coboundary1 (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale)
    (w : Word BDL26Field (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)).Q) :
    tannerCoboundary1 (rxReplacementPresentation (transposePresentation P) S) (wordEquiv (rzDualQ P S) w) =
      wordEquiv (rzDualZ P S) (tannerCoboundary1 (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)) w) := by
  funext z
  obtain ⟨z,rfl⟩ := (rzDualZ P S).surjective z
  change _ = tannerCoboundary1 (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)) w z
  exact
    coboundary1_transport (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)) (rxReplacementPresentation (transposePresentation P) S)
      (rzDualQ P S) (rzDualZ P S) (rzDual_qz P A R S) w z

end QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates
