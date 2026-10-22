import QEC.Coding.FiniteAlternatingConstruction.TannerSquare

/-!
# Measured valence in the concrete Tanner construction

The counts below enumerate actual incidence fibers.  The edge-face calculation
uses the presentation's perfect pairing, without assuming a face-degree bound.
-/

namespace QEC.Coding.BDL26BoundedValence

open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare

/-- Number of Q neighbours of an X vertex. -/
def xDegree (P : TannerSquarePresentation) (x : P.X) : Nat :=
  Fintype.card {q : P.Q // P.xq x q = true}

/-- Number of Q neighbours of a Z vertex. -/
def zDegree (P : TannerSquarePresentation) (z : P.Z) : Nat :=
  Fintype.card {q : P.Q // P.qz q z = true}

/-- X-direction valence of a Q vertex. -/
def qXDegree (P : TannerSquarePresentation) (q : P.Q) : Nat :=
  Fintype.card {x : P.X // P.xq x q = true}

/-- Z-direction valence of a Q vertex. -/
def qZDegree (P : TannerSquarePresentation) (q : P.Q) : Nat :=
  Fintype.card {z : P.Z // P.qz q z = true}

/-- The fixed numerical induction invariant; every clause is a measured count. -/
def BoundedValence (P : TannerSquarePresentation) : Prop :=
  (∀ x, xDegree P x ≤ 7) ∧ (∀ z, zDegree P z ≤ 7) ∧
    ∀ q, qXDegree P q ≤ 4 ∧ qZDegree P q ≤ 4 ∧
      qXDegree P q + qZDegree P q ≤ 7

/-- Actual faces incident to an X-Q edge. -/
abbrev XQIncidentFace (P : TannerSquarePresentation) (e : XQEdge P) :=
  {f : P.Face // P.faceX f = e.1.1 ∧ ∃ i, P.faceQ f i = e.1.2}

/-- Actual faces incident to a Q-Z edge. -/
abbrev QZIncidentFace (P : TannerSquarePresentation) (e : QZEdge P) :=
  {f : P.Face // P.faceZ f = e.1.2 ∧ ∃ i, P.faceQ f i = e.1.1}

/-- Face-to-Z routing at a fixed X-Q edge is bijective by perfect pairing. -/
theorem xqIncidentFace_to_z_bijective
    (P : TannerSquarePresentation) (e : XQEdge P) :
    Function.Bijective (fun f : XQIncidentFace P e =>
      (⟨P.faceZ f.1, by
        obtain ⟨i, hi⟩ := f.2.2
        simpa [hi] using P.data.faceQ_qz f.1 i⟩ :
        {z : P.Z // P.qz e.1.2 z = true})) := by
  constructor
  · intro f g h
    obtain ⟨i, hi⟩ := f.2.2
    obtain ⟨j, hj⟩ := g.2.2
    have hz : P.faceZ g.1 = P.faceZ f.1 := (congrArg Subtype.val h).symm
    let a : FaceOver P.data e.1.1 (P.faceZ f.1) × Fin 2 :=
      (⟨f.1, f.2.1, rfl⟩, i)
    let b : FaceOver P.data e.1.1 (P.faceZ f.1) × Fin 2 :=
      (⟨g.1, g.2.1, hz⟩, j)
    have hab : faceCornerToShared P.data e.1.1 (P.faceZ f.1) a =
        faceCornerToShared P.data e.1.1 (P.faceZ f.1) b := by
      apply Subtype.ext
      exact hi.trans hj.symm
    apply Subtype.ext
    exact congrArg (fun v => v.1.1) ((P.perfectPairing _ _).1 hab)
  · intro z
    let q : SharedQ P.data e.1.1 z.1 := ⟨e.1.2, by simp [e.2, z.2]⟩
    obtain ⟨⟨f, i⟩, h⟩ := (P.perfectPairing e.1.1 z.1).2 q
    have hi : P.faceQ f.1 i = e.1.2 := congrArg Subtype.val h
    refine ⟨⟨f.1, f.2.1, i, hi⟩, ?_⟩
    apply Subtype.ext
    exact f.2.2

/-- Face-to-X routing at a fixed Q-Z edge is bijective by perfect pairing. -/
theorem qzIncidentFace_to_x_bijective
    (P : TannerSquarePresentation) (e : QZEdge P) :
    Function.Bijective (fun f : QZIncidentFace P e =>
      (⟨P.faceX f.1, by
        obtain ⟨i, hi⟩ := f.2.2
        simpa [hi] using P.data.faceQ_xq f.1 i⟩ :
        {x : P.X // P.xq x e.1.1 = true})) := by
  constructor
  · intro f g h
    obtain ⟨i, hi⟩ := f.2.2
    obtain ⟨j, hj⟩ := g.2.2
    have hx : P.faceX g.1 = P.faceX f.1 := (congrArg Subtype.val h).symm
    let a : FaceOver P.data (P.faceX f.1) e.1.2 × Fin 2 :=
      (⟨f.1, rfl, f.2.1⟩, i)
    let b : FaceOver P.data (P.faceX f.1) e.1.2 × Fin 2 :=
      (⟨g.1, hx, g.2.1⟩, j)
    have hab : faceCornerToShared P.data (P.faceX f.1) e.1.2 a =
        faceCornerToShared P.data (P.faceX f.1) e.1.2 b := by
      apply Subtype.ext
      exact hi.trans hj.symm
    apply Subtype.ext
    exact congrArg (fun v => v.1.1) ((P.perfectPairing _ _).1 hab)
  · intro x
    let q : SharedQ P.data x.1 e.1.2 := ⟨e.1.1, by simp [e.2, x.2]⟩
    obtain ⟨⟨f, i⟩, h⟩ := (P.perfectPairing x.1 e.1.2).2 q
    have hi : P.faceQ f.1 i = e.1.1 := congrArg Subtype.val h
    refine ⟨⟨f.1, f.2.2, i, hi⟩, ?_⟩
    apply Subtype.ext
    exact f.2.1

/-- The exact X-Q edge face count is the Q vertex's Z-direction valence. -/
theorem xqIncidentFace_card (P : TannerSquarePresentation) (e : XQEdge P) :
    Fintype.card (XQIncidentFace P e) = qZDegree P e.1.2 := by
  classical
  exact Fintype.card_of_bijective (xqIncidentFace_to_z_bijective P e)

/-- The exact Q-Z edge face count is the Q vertex's X-direction valence. -/
theorem qzIncidentFace_card (P : TannerSquarePresentation) (e : QZEdge P) :
    Fintype.card (QZIncidentFace P e) = qXDegree P e.1.1 := by
  classical
  exact Fintype.card_of_bijective (qzIncidentFace_to_x_bijective P e)

theorem xqIncidentFace_card_le_four (P : TannerSquarePresentation)
    (h : BoundedValence P) (e : XQEdge P) :
    Fintype.card (XQIncidentFace P e) ≤ 4 := by
  rw [xqIncidentFace_card]
  exact (h.2.2 e.1.2).2.1

theorem qzIncidentFace_card_le_four (P : TannerSquarePresentation)
    (h : BoundedValence P) (e : QZEdge P) :
    Fintype.card (QZIncidentFace P e) ≤ 4 := by
  rw [qzIncidentFace_card]
  exact (h.2.2 e.1.1).1

/-- The actual five-qubit seed satisfies the numerical invariant. -/
theorem base_boundedValence : BoundedValence baseTannerSquarePresentation := by
  unfold BoundedValence
  decide


theorem boundedValence_transpose (P : TannerSquarePresentation)
    (h : BoundedValence P) : BoundedValence (transposePresentation P) := by
  refine ⟨h.2.1, h.1, ?_⟩
  intro q
  obtain ⟨hx, hz, hsum⟩ := h.2.2 q
  refine ⟨hz, hx, ?_⟩
  change qZDegree P q + qXDegree P q ≤ 7
  omega

/-- Cellular regularity turns perfect pairing into a fixed shared-Q bound. -/
theorem sharedQ_card_le_two (P : TannerSquarePresentation)
    (R : TannerSquareCellularRegular P) (x : P.X) (z : P.Z) :
    Fintype.card (SharedQ P.data x z) ≤ 2 := by
  classical
  letI : Subsingleton (FaceOver P.data x z) := R.faceOver_subsingleton x z
  have hface : Fintype.card (FaceOver P.data x z) ≤ 1 :=
    Fintype.card_le_one_iff_subsingleton.mpr inferInstance
  calc
    Fintype.card (SharedQ P.data x z) =
        Fintype.card (FaceOver P.data x z × Fin 2) :=
      (Fintype.card_congr (P.faceCornerEquiv x z)).symm
    _ = Fintype.card (FaceOver P.data x z) * 2 := by simp
    _ ≤ 1 * 2 := Nat.mul_le_mul_right 2 hface
    _ = 2 := by decide


end QEC.Coding.BDL26BoundedValence
