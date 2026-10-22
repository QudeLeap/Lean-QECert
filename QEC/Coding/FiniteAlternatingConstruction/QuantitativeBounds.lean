import QEC.Coding.FiniteAlternatingConstruction.DecodingGraph
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Finite counts for the concrete alternating construction

The counts below concern the actual tagged carriers, before any asymptotic
estimate. They are internal prerequisites of the F15/F16/F18 quantitative
construction bounds in [BDL26, construction and decoding graph].
-/

namespace QEC.Coding.BDL26QuantitativeBounds

open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26DecodingGraph

/-- Exact subdivision vertex count, including boundary and interior tags. -/
theorem subdivisionVertex_card (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Fintype.card (SubdivisionVertex P x S) =
      Fintype.card (XStarVertex P x) +
      Fintype.card (XStarEdge P x) * (S.half - 1) +
      Fintype.card (XStarFace P x) * (S.half - 1) * (S.half - 1) := by
  simp only [SubdivisionVertex, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

/-- Exact count of subdivided old edges and both square-interior directions. -/
theorem subdivisionEdge_card (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Fintype.card (SubdivisionEdge P x S) =
      Fintype.card (XStarEdge P x) * S.half +
      2 * Fintype.card (XStarFace P x) * S.half * (S.half - 1) := by
  simp only [SubdivisionEdge, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

/-- Every old face contributes precisely an m by m grid. -/
theorem subdivisionFace_card (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Fintype.card (SubdivisionFace P x S) =
      Fintype.card (XStarFace P x) * S.half ^ 2 := by
  simp only [SubdivisionFace, Fintype.card_prod, Fintype.card_fin]
  ring

/-- The intrinsic local zero-cells consist of two disjoint copies. -/
theorem doubleCylinderVertex_card (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) :
    Fintype.card (DoubleCylinderVertex P x S) =
      2 * (Fintype.card (XStarVertex P x) +
        Fintype.card (XStarEdge P x) * (S.half - 1) +
        Fintype.card (XStarFace P x) * (S.half - 1) * (S.half - 1)) := by
  simp only [DoubleCylinderVertex, Fintype.card_prod, BDL26FiniteTannerSquare.Two, Fintype.card_fin,
    subdivisionVertex_card]

/-- Q-side path subdivision count, retaining every original endpoint. -/
theorem qSubdivisionVertex_card (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) :
    Fintype.card (QSubdivisionVertex P q S) =
      1 + Fintype.card (QStarEdge P q) * S.half := by
  have hm := S.half_pos
  simp only [QSubdivisionVertex, QStarVertex, QStarEdge, Fintype.card_sum,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_unit]
  rw [Nat.mul_sub_left_distrib]
  have h := Nat.le_mul_of_pos_right (Fintype.card {z : P.Z // P.qz q z = true}) hm
  omega

/-- Exact Q-local intrinsic zero-cell count. -/
theorem qDoubleCylinderVertex_card (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) :
    Fintype.card (QDoubleCylinderVertex P q S) =
      2 * (1 + Fintype.card (QStarEdge P q) * S.half) := by
  simp only [QDoubleCylinderVertex, Fintype.card_prod, BDL26FiniteTannerSquare.Two, Fintype.card_fin,
    qSubdivisionVertex_card]

/-- Exact Q-local syndrome-coordinate count: two end paths and vertical edges. -/
theorem qDoubleCylinderEdge_card (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) :
    Fintype.card (QDoubleCylinderEdge P q S) =
      Fintype.card (QStarEdge P q) * S.ell := by
  simp only [QDoubleCylinderEdge, QSubdivisionEdge, Fintype.card_sum,
    Fintype.card_prod, BDL26FiniteTannerSquare.Two, Fintype.card_fin]
  rw [← S.two_half_add_one]
  ring

/-- Finite enumeration of the materialized RZ carrier, exposing its transpose aliases. -/
noncomputable instance rzQFintype (P : TannerSquarePresentation) (S : OddScale) :
    Fintype (BDL26RZLocalReplacement.RZQ P S) := by
  classical
  dsimp [BDL26RZLocalReplacement.RZQ, ZDoubleCylinderEdge, QDoubleCylinderVertex,
    DoubleCylinderEdge, transposePresentation, transposeTannerSquareData]
  infer_instance

/-- Both original Q roots survive the actual RX carrier, independently of incidence. -/
def rxQubitRoots (P : TannerSquarePresentation) (S : OddScale) :
    P.Q × BDL26FiniteTannerSquare.Two ↪ RX1 P S where
  toFun qt := Sum.inr ⟨qt.1, qt.2, Sum.inl (Sum.inl ())⟩
  inj' := by
    rintro ⟨q, t⟩ ⟨q', t'⟩ h
    have hs := Sum.inr.inj h
    have hq := congrArg Sigma.fst hs
    cases hq
    have hv := eq_of_heq (Sigma.mk.inj_iff.mp hs).2
    have ht := congrArg Prod.fst hv
    cases ht
    rfl

/-- Actual RX replacement at least doubles the qubit count. -/
theorem rxQubit_card_lower (P : TannerSquarePresentation) (S : OddScale) :
    2 * Fintype.card P.Q ≤ Fintype.card (RX1 P S) := by
  have h := Fintype.card_le_of_injective (rxQubitRoots P S) (rxQubitRoots P S).injective
  simpa only [Fintype.card_prod, BDL26FiniteTannerSquare.Two, Fintype.card_fin, Nat.mul_comm] using h

/-- Both Q roots also survive the materialized RZ carrier. -/
def rzQubitRoots (P : TannerSquarePresentation) (S : OddScale) :
    P.Q × BDL26FiniteTannerSquare.Two ↪ BDL26RZLocalReplacement.RZQ P S where
  toFun qt := Sum.inr ⟨qt.1, qt.2, Sum.inl (Sum.inl ())⟩
  inj' := by
    rintro ⟨q, t⟩ ⟨q', t'⟩ h
    have hs := Sum.inr.inj h
    have hq := congrArg Sigma.fst hs
    cases hq
    have hv := eq_of_heq (Sigma.mk.inj_iff.mp hs).2
    have ht := congrArg Prod.fst hv
    cases ht
    rfl

/-- Actual RZ replacement at least doubles the qubit count. -/
theorem rzQubit_card_lower (P : TannerSquarePresentation) (S : OddScale) :
    2 * Fintype.card P.Q ≤ Fintype.card (BDL26RZLocalReplacement.RZQ P S) := by
  have h := Fintype.card_le_of_injective (rzQubitRoots P S) (rzQubitRoots P S).injective
  simpa only [Fintype.card_prod, BDL26FiniteTannerSquare.Two, Fintype.card_fin, Nat.mul_comm] using h

/-- The lower recurrence follows from the selected RX/RZ constructors. -/
theorem nextState_qubit_card_lower (S : OddScale) (n : Nat) (C : ConstructionState) :
    2 * Fintype.card C.presentation.Q ≤
      Fintype.card (nextState S n C).presentation.Q := by
  unfold nextState
  split
  · exact rxQubit_card_lower C.presentation S
  · calc
      2 * Fintype.card C.presentation.Q ≤
          Fintype.card (BDL26RZLocalReplacement.RZQ C.presentation S) :=
        rzQubit_card_lower C.presentation S
      _ = Fintype.card (rzState S C).presentation.Q :=
        Fintype.card_congr (Equiv.refl _)

/-- A finite exponential lower bound with the actual five-qubit seed. -/
theorem state_qubit_card_lower (S : OddScale) (n : Nat) :
    5 * 2 ^ n ≤ Fintype.card (state S n).presentation.Q := by
  induction n with
  | zero => change 5 * 2 ^ 0 ≤ Fintype.card BaseQubit; simp
  | succ n ih =>
      have h := nextState_qubit_card_lower S n (state S n)
      change 5 * 2 ^ (n + 1) ≤ Fintype.card (nextState S n (state S n)).presentation.Q
      calc
        5 * 2 ^ (n + 1) = 2 * (5 * 2 ^ n) := by ring
        _ ≤ 2 * Fintype.card (state S n).presentation.Q := Nat.mul_le_mul_left 2 ih
        _ ≤ _ := h

/-- Admissibility ensures every Q coordinate occurs as a face corner. -/
theorem faceQ_surjective (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) :
    Function.Surjective (fun fi : P.Face × BDL26FiniteTannerSquare.Two => P.faceQ fi.1 fi.2) := by
  intro q
  let x := A.xqRoot q
  let z := A.qzRoot q
  let shared : SharedQ P.data x.1 z.1 := ⟨q, by simp [x.2, z.2]⟩
  obtain ⟨⟨f, i⟩, h⟩ := (P.perfectPairing x.1 z.1).2 shared
  exact ⟨(f.1, i), congrArg Subtype.val h⟩

/-- Every actual qubit is covered by one of two corners of a face. -/
theorem qubit_card_le_twice_face (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) :
    Fintype.card P.Q ≤ 2 * Fintype.card P.Face := by
  have h := Fintype.card_le_of_surjective _ (faceQ_surjective P A)
  simpa only [Fintype.card_prod, BDL26FiniteTannerSquare.Two, Fintype.card_fin, Nat.mul_comm] using h

/-- The degree-two incidence corners form a wedge, with no chosen face inverse. -/
abbrev TannerWedge (P : TannerSquarePresentation) :=
  {t : P.X × P.Q × P.Z // P.xq t.1 t.2.1 = true ∧ P.qz t.2.1 t.2.2 = true}

def faceCornerWedge (P : TannerSquarePresentation) :
    P.Face × BDL26FiniteTannerSquare.Two → TannerWedge P :=
  fun fi => ⟨(P.faceX fi.1, P.faceQ fi.1 fi.2, P.faceZ fi.1),
    P.data.faceQ_xq fi.1 fi.2, P.data.faceQ_qz fi.1 fi.2⟩

theorem faceCornerWedge_bijective (P : TannerSquarePresentation) :
    Function.Bijective (faceCornerWedge P) := by
  constructor
  · rintro ⟨f, i⟩ ⟨g, j⟩ h
    have hx : P.faceX f = P.faceX g := congrArg (fun w : TannerWedge P => w.1.1) h
    have hq : P.faceQ f i = P.faceQ g j := congrArg (fun w : TannerWedge P => w.1.2.1) h
    have hz : P.faceZ f = P.faceZ g := congrArg (fun w : TannerWedge P => w.1.2.2) h
    let ff : FaceOver P.data (P.faceX f) (P.faceZ f) := ⟨f, rfl, rfl⟩
    let gg : FaceOver P.data (P.faceX f) (P.faceZ f) := ⟨g, hx.symm, hz.symm⟩
    have heq : faceCornerToShared P.data (P.faceX f) (P.faceZ f) (ff,i) =
        faceCornerToShared P.data (P.faceX f) (P.faceZ f) (gg,j) := Subtype.ext hq
    have hc := (P.perfectPairing (P.faceX f) (P.faceZ f)).1 heq
    exact congrArg (fun pair : FaceOver P.data (P.faceX f) (P.faceZ f) ×
      BDL26FiniteTannerSquare.Two => (pair.1.1, pair.2)) hc
  · rintro ⟨⟨x,q,z⟩,hx,hz⟩
    let shared : SharedQ P.data x z := ⟨q, by simp [hx,hz]⟩
    obtain ⟨⟨f,i⟩,h⟩ := (P.perfectPairing x z).2 shared
    refine ⟨(f.1,i), Subtype.ext ?_⟩
    exact Prod.ext f.2.1 (Prod.ext (congrArg Subtype.val h) f.2.2)

theorem tannerWedge_card (P : TannerSquarePresentation) :
    Fintype.card (TannerWedge P) = 2 * Fintype.card P.Face := by
  have h := Fintype.card_congr (Equiv.ofBijective _ (faceCornerWedge_bijective P))
  simpa only [Fintype.card_prod, BDL26FiniteTannerSquare.Two, Fintype.card_fin, Nat.mul_comm] using h.symm

/-- Forgetting the unique owner tag covers every old face exactly once. -/
def xStarFaceEquiv (P : TannerSquarePresentation) :
    (Σ x : P.X, XStarFace P x) ≃ P.Face where
  toFun f := f.2.1
  invFun f := ⟨P.faceX f, f, by simp [xStarFaceMember]⟩
  left_inv := by
    rintro ⟨x, f, hf⟩
    have hx : P.faceX f = x := by simpa [xStarFaceMember] using hf
    subst x
    rfl
  right_inv := fun _ => rfl

/-- The two Q-Z sides of each face cover the entire family of star boundaries. -/
def faceCornerBoundaryEdge (P : TannerSquarePresentation) :
    P.Face × BDL26FiniteTannerSquare.Two → Σ x : P.X, XStarBoundaryEdge P x :=
  fun fi => ⟨P.faceX fi.1, Sum.inr (faceQZEdge P fi.1 fi.2), by
    simp only [xStarBoundaryEdgeMember, decide_eq_true_eq]
    refine ⟨fi.1, by simp [xStarFaceMember], ?_⟩
    change decide (faceQZEdge P fi.1 fi.2 = faceQZEdge P fi.1 0 ∨
      faceQZEdge P fi.1 fi.2 = faceQZEdge P fi.1 1) = true
    have hi : fi.2 = 0 ∨ fi.2 = 1 := by
      have hlt : fi.2.val < 2 := fi.2.isLt
      apply or_iff_not_imp_left.mpr
      intro hzero
      apply Fin.ext
      have hne : fi.2.val ≠ 0 := fun h => hzero (Fin.ext h)
      omega
    rcases hi with hi | hi <;> simp [hi]⟩

theorem faceCornerBoundaryEdge_surjective (P : TannerSquarePresentation) :
    Function.Surjective (faceCornerBoundaryEdge P) := by
  rintro ⟨x, e, he⟩
  cases e with
  | inl e => simp [xStarBoundaryEdgeMember] at he
  | inr e =>
    obtain ⟨f, hx, he⟩ := (of_decide_eq_true he)
    have hfx : P.faceX f = x := by simpa [xStarFaceMember] using hx
    have hc : e = faceQZEdge P f 0 ∨ e = faceQZEdge P f 1 := by
      change decide (e = faceQZEdge P f 0 ∨ e = faceQZEdge P f 1) = true at he
      simpa using he
    rcases hc with hc | hc
    · refine ⟨(f,0), ?_⟩
      subst x
      subst e
      rfl
    · refine ⟨(f,1), ?_⟩
      subst x
      subst e
      rfl

/-- Boundary edge count uses actual face sides, not an assumed local-size bound. -/
theorem xStarBoundaryEdge_total_le (P : TannerSquarePresentation) :
    (∑ x : P.X, Fintype.card (XStarBoundaryEdge P x)) ≤ 2 * Fintype.card P.Face := by
  have h := Fintype.card_le_of_surjective _ (faceCornerBoundaryEdge_surjective P)
  simpa only [Fintype.card_sigma, Fintype.card_prod, BDL26FiniteTannerSquare.Two, Fintype.card_fin,
    Nat.mul_comm] using h

/-- Subdivision boundary edges are exactly segments of old boundary edges. -/
def subdivisionBoundaryEdgeEquiv (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) :
    SubdivisionBoundaryEdge P x S ≃ XStarBoundaryEdge P x × Fin S.half where
  toFun e := by
    rcases e with ⟨e, he⟩
    cases e with
    | inl ei => exact (⟨ei.1.1, he⟩, ei.2)
    | inr fi => simp [subdivisionBoundaryEdgeMember] at he
  invFun ei := subdivisionOriginalBoundaryEdge P x S ei.1 ei.2
  left_inv := by
    rintro ⟨e, he⟩
    cases e with
    | inl ei => rfl
    | inr fi => simp [subdivisionBoundaryEdgeMember] at he
  right_inv := by rintro ⟨⟨e, he⟩, i⟩; rfl

theorem subdivisionBoundaryEdge_card (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) :
    Fintype.card (SubdivisionBoundaryEdge P x S) =
      Fintype.card (XStarBoundaryEdge P x) * S.half := by
  simpa only [Fintype.card_prod, Fintype.card_fin] using
    Fintype.card_congr (subdivisionBoundaryEdgeEquiv P x S)

theorem doubleCylinderFace_card (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) :
    Fintype.card (DoubleCylinderFace P x S) =
      2 * Fintype.card (XStarFace P x) * S.half ^ 2 +
      Fintype.card (XStarBoundaryEdge P x) * S.half := by
  simp only [DoubleCylinderFace, Fintype.card_sum, Fintype.card_prod, BDL26FiniteTannerSquare.Two,
    Fintype.card_fin, subdivisionFace_card, subdivisionBoundaryEdge_card]
  ring

/-- A Q-side edge over an X-Q incidence is exactly one Tanner wedge. -/
def xqQStarEdgeEquiv (P : TannerSquarePresentation) :
    (Σ a : XQEdge P, QStarEdge P a.1.2) ≃ TannerWedge P where
  toFun az := ⟨(az.1.1.1, az.1.1.2, az.2.1), az.1.2, az.2.2⟩
  invFun w := ⟨⟨(w.1.1,w.1.2.1),w.2.1⟩,w.1.2.2,w.2.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The glue-face count is linear in actual old face count by perfect pairing. -/
theorem rxGlueFace_card (P : TannerSquarePresentation) (S : OddScale) :
    Fintype.card (RXXQGlueFace P S) = 4 * S.ell * Fintype.card P.Face := by
  have hw : (∑ a : XQEdge P, Fintype.card (QStarEdge P a.1.2)) =
      2 * Fintype.card P.Face := by
    calc
      _ = Fintype.card (TannerWedge P) := by
        simpa only [Fintype.card_sigma] using Fintype.card_congr (xqQStarEdgeEquiv P)
      _ = _ := tannerWedge_card P
  simp only [RXXQGlueFace, Fintype.card_sigma, Fintype.card_prod,
    BDL26FiniteTannerSquare.Two, Fintype.card_fin, qDoubleCylinderEdge_card, ← Finset.sum_mul, hw]
  ring

/-- The two end-copy face families and boundary rectangles have a uniform
finite total bound, before applying the four local corner labels. -/
theorem doubleCylinderFace_total_le (P : TannerSquarePresentation) (S : OddScale) :
    (∑ x : P.X, Fintype.card (DoubleCylinderFace P x S)) ≤
      (2 * S.half ^ 2 + 2 * S.half) * Fintype.card P.Face := by
  have hf : (∑ x : P.X, Fintype.card (XStarFace P x)) = Fintype.card P.Face := by
    simpa only [Fintype.card_sigma] using Fintype.card_congr (xStarFaceEquiv P)
  have hb := Nat.mul_le_mul_right S.half (xStarBoundaryEdge_total_le P)
  simp only [doubleCylinderFace_card, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, hf]
  nlinarith

/-- Explicit finite face-growth factor, depending only on the fixed odd scale. -/
def faceGrowthFactor (S : OddScale) : Nat := 2 * S.ell * (S.ell + 2)

/-- Actual RX face counts have a depth-independent multiplicative envelope. -/
theorem rxFace_card_upper (P : TannerSquarePresentation) (S : OddScale) :
    Fintype.card (RXFace P S) ≤ faceGrowthFactor S * Fintype.card P.Face := by
  have hf := Nat.mul_le_mul_right 4 (doubleCylinderFace_total_le P S)
  have hlocal : Fintype.card (RXLocalFace P S) =
      (∑ x : P.X, Fintype.card (DoubleCylinderFace P x S)) * 4 := by
    simp only [RXLocalFace, Fintype.card_sigma, Fintype.card_prod,
      BDL26FiniteTannerSquare.Two, Fintype.card_fin, ← Finset.sum_mul]
  have hold : Fintype.card (RXOldZFace P) = 2 * Fintype.card P.Face := by
    simp only [RXOldZFace, Fintype.card_prod, BDL26FiniteTannerSquare.Two,
      Fintype.card_fin, Nat.mul_comm]
  have hsplit : Fintype.card (RXFace P S) =
      Fintype.card (RXLocalFace P S) +
        (Fintype.card (RXXQGlueFace P S) + Fintype.card (RXOldZFace P)) := by
    change Fintype.card (RXLocalFace P S ⊕ (RXXQGlueFace P S ⊕ RXOldZFace P)) = _
    rw [Fintype.card_sum, Fintype.card_sum]
  rw [hsplit, hlocal, rxGlueFace_card, hold]
  unfold faceGrowthFactor
  rw [← S.two_half_add_one]
  nlinarith

/-- Finite enumeration of the materialized RZ face tags. -/
noncomputable instance rzFaceFintype (P : TannerSquarePresentation) (S : OddScale) :
    Fintype (BDL26RZLocalReplacement.RZFace P S) := by
  classical
  dsimp [BDL26RZLocalReplacement.RZFace, BDL26RZLocalReplacement.RZLocalFace,
    BDL26RZLocalReplacement.RZQZGlueFace, BDL26RZLocalReplacement.RZOldXFace,
    ZDoubleCylinderFace, QDoubleCylinderEdge, DoubleCylinderFace,
    transposePresentation, transposeTannerSquareData]
  infer_instance

/-- Materialized RZ face tags have the same finite count as RX on the transpose. -/
noncomputable def rzFaceEquiv (P : TannerSquarePresentation) (S : OddScale) :
    BDL26RZLocalReplacement.RZFace P S ≃ RXFace (transposePresentation P) S :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr
    (Equiv.sigmaCongr (transposeXQEdgeEquiv P).symm (fun _ => Equiv.refl _))
    (Equiv.refl _))

theorem rzFace_card_upper (P : TannerSquarePresentation) (S : OddScale) :
    Fintype.card (BDL26RZLocalReplacement.RZFace P S) ≤
      faceGrowthFactor S * Fintype.card P.Face := by
  rw [Fintype.card_congr (rzFaceEquiv P S)]
  exact rxFace_card_upper (transposePresentation P) S

theorem nextState_face_card_upper (S : OddScale) (n : Nat) (C : ConstructionState) :
    Fintype.card (nextState S n C).presentation.Face ≤
      faceGrowthFactor S * Fintype.card C.presentation.Face := by
  unfold nextState
  split
  · exact rxFace_card_upper C.presentation S
  · calc
      Fintype.card (rzState S C).presentation.Face =
          Fintype.card (BDL26RZLocalReplacement.RZFace C.presentation S) :=
        Fintype.card_congr (Equiv.refl _)
      _ ≤ faceGrowthFactor S * Fintype.card C.presentation.Face :=
        rzFace_card_upper C.presentation S

/-- Finite face growth from the actual four-face seed. -/
theorem state_face_card_upper (S : OddScale) (n : Nat) :
    Fintype.card (state S n).presentation.Face ≤ 4 * faceGrowthFactor S ^ n := by
  induction n with
  | zero => change Fintype.card BaseFace ≤ 4 * faceGrowthFactor S ^ 0; simp
  | succ n ih =>
      change Fintype.card (nextState S n (state S n)).presentation.Face ≤ _
      calc
        _ ≤ faceGrowthFactor S * Fintype.card (state S n).presentation.Face :=
          nextState_face_card_upper S n (state S n)
        _ ≤ faceGrowthFactor S * (4 * faceGrowthFactor S ^ n) :=
          Nat.mul_le_mul_left _ ih
        _ = 4 * faceGrowthFactor S ^ (n + 1) := by ring

/-- Explicit finite upper bound, with no asymptotic or degree-bound premise. -/
theorem state_qubit_card_upper (S : OddScale) (n : Nat) :
    Fintype.card (state S n).presentation.Q ≤ 8 * faceGrowthFactor S ^ n := by
  calc
    _ ≤ 2 * Fintype.card (state S n).presentation.Face :=
      qubit_card_le_twice_face _ (state S n).admissible.toTannerSquareAdmissible
    _ ≤ 2 * (4 * faceGrowthFactor S ^ n) :=
      Nat.mul_le_mul_left _ (state_face_card_upper S n)
    _ = 8 * faceGrowthFactor S ^ n := by ring

/-- Both finite qubit inequalities at the even levels used by the source. -/
theorem evenState_qubit_card_bounds (S : OddScale) (k : Nat) :
    5 * 2 ^ (2 * k) ≤ Fintype.card (state S (2 * k)).presentation.Q ∧
    Fintype.card (state S (2 * k)).presentation.Q ≤
      8 * (2 * S.ell * (S.ell + 2)) ^ (2 * k) :=
  ⟨state_qubit_card_lower S (2 * k), state_qubit_card_upper S (2 * k)⟩

/-- Least odd integer strictly above a natural threshold. -/
def leastOddAbove (threshold : Nat) : Nat := 2 * ((threshold + 1) / 2) + 1

theorem leastOddAbove_odd (threshold : Nat) : leastOddAbove threshold % 2 = 1 := by
  unfold leastOddAbove
  omega

theorem leastOddAbove_gt (threshold : Nat) : threshold < leastOddAbove threshold := by
  unfold leastOddAbove
  omega

theorem leastOddAbove_le (threshold n : Nat) (hodd : n % 2 = 1) (hgt : threshold < n) :
    leastOddAbove threshold ≤ n := by
  unfold leastOddAbove
  omega

/-- The source scale selection, at a real threshold at least one. Geometric
embedding claims are not part of this purely arithmetic construction. -/
noncomputable def leastOddScaleAbove (threshold : ℝ) (hone : 1 ≤ threshold) : OddScale where
  ell := leastOddAbove ⌊threshold⌋₊
  odd := leastOddAbove_odd _
  three_le := by
    have hf : 1 ≤ ⌊threshold⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by simpa using hone)
    have hg := leastOddAbove_gt ⌊threshold⌋₊
    have ho := leastOddAbove_odd ⌊threshold⌋₊
    omega

theorem leastOddScaleAbove_gt (threshold : ℝ) (hone : 1 ≤ threshold) :
    threshold < (leastOddScaleAbove threshold hone).ell :=
  (Nat.floor_lt (by linarith)).mp (leastOddAbove_gt _)

/-- Exact minimality among odd integers, including the strict threshold boundary. -/
theorem leastOddScaleAbove_minimal (threshold : ℝ) (hone : 1 ≤ threshold)
    (n : Nat) (hodd : n % 2 = 1) (hgt : threshold < n) :
    (leastOddScaleAbove threshold hone).ell ≤ n :=
  leastOddAbove_le _ n hodd ((Nat.floor_lt (by linarith)).mpr hgt)

/-- The canonical half-scale remains exactly the source's subdivision parameter. -/
theorem leastOddScaleAbove_half (threshold : ℝ) (hone : 1 ≤ threshold) :
    (leastOddScaleAbove threshold hone).half = (⌊threshold⌋₊ + 1) / 2 := by
  have h := (leastOddScaleAbove threshold hone).two_half_add_one
  change 2 * (leastOddScaleAbove threshold hone).half + 1 =
    2 * ((⌊threshold⌋₊ + 1) / 2) + 1 at h
  omega

end QEC.Coding.BDL26QuantitativeBounds
