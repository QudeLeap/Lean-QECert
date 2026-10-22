import QEC.Coding.FiniteAlternatingConstruction.Core
import QEC.Coding.ChainComplex.Duality

/-!
# Finite Tanner-square and cellular primitives for BDL26

This module constructs the finite shared topology used before the branch-specific
RX and RZ replacement blocks.  A presentation stores finite incidence data and
one explicit perfect pairing of the two face corners over every `(x,z)` fiber.
All matrix and chain laws below are proved from that pairing and the resulting
cell boundaries.  No cohomology result, replacement map, transport map, decoder,
embedding, or lifetime statement is included.
-/

namespace QEC
namespace Coding
namespace BDL26FiniteTannerSquare

open BDL26FiniteAlternatingCore
open Module

abbrev Field := BDL26FiniteAlternatingCore.Field
abbrev Two := Fin 2

/-! ## Finite Tanner-square presentations -/

/-- Raw finite incidence and ordered face-corner data. -/
structure TannerSquareData where
  X : Type
  Q : Type
  Z : Type
  Face : Type
  xFintype : Fintype X
  qFintype : Fintype Q
  zFintype : Fintype Z
  faceFintype : Fintype Face
  xDecidableEq : DecidableEq X
  qDecidableEq : DecidableEq Q
  zDecidableEq : DecidableEq Z
  faceDecidableEq : DecidableEq Face
  xq : X → Q → Bool
  qz : Q → Z → Bool
  faceX : Face → X
  faceZ : Face → Z
  faceQ : Face → Two → Q
  faceQ_xq : ∀ f i, xq (faceX f) (faceQ f i) = true
  faceQ_qz : ∀ f i, qz (faceQ f i) (faceZ f) = true

attribute [instance] TannerSquareData.xFintype TannerSquareData.qFintype
  TannerSquareData.zFintype TannerSquareData.faceFintype
  TannerSquareData.xDecidableEq TannerSquareData.qDecidableEq
  TannerSquareData.zDecidableEq TannerSquareData.faceDecidableEq

/-- Faces with fixed X and Z endpoints. -/
abbrev FaceOver (D : TannerSquareData) (x : D.X) (z : D.Z) :=
  {f : D.Face // D.faceX f = x ∧ D.faceZ f = z}

/-- Q vertices simultaneously incident to fixed X and Z endpoints. -/
abbrev SharedQ (D : TannerSquareData) (x : D.X) (z : D.Z) :=
  {q : D.Q // D.xq x q && D.qz q z}

/-- Send an ordered face corner to its shared Q vertex. -/
def faceCornerToShared (D : TannerSquareData) (x : D.X) (z : D.Z) :
    FaceOver D x z × Two → SharedQ D x z := fun fi =>
  ⟨D.faceQ fi.1.1 fi.2, by
    simpa [fi.1.2.1, fi.1.2.2] using
      And.intro (D.faceQ_xq fi.1.1 fi.2) (D.faceQ_qz fi.1.1 fi.2)⟩

/-- A finite Tanner-square presentation.

The only validity field is the explicit perfect pairing: for each `(x,z)`,
ordered corners of the faces over `(x,z)` are in bijection with the shared Q
vertices.  In particular the presentation does not accept a chain law.
-/
structure TannerSquarePresentation where
  data : TannerSquareData
  perfectPairing : ∀ x z, Function.Bijective (faceCornerToShared data x z)

namespace TannerSquarePresentation

abbrev X (P : TannerSquarePresentation) := P.data.X
abbrev Q (P : TannerSquarePresentation) := P.data.Q
abbrev Z (P : TannerSquarePresentation) := P.data.Z
abbrev Face (P : TannerSquarePresentation) := P.data.Face

abbrev xq (P : TannerSquarePresentation) := P.data.xq
abbrev qz (P : TannerSquarePresentation) := P.data.qz
abbrev faceX (P : TannerSquarePresentation) := P.data.faceX
abbrev faceZ (P : TannerSquarePresentation) := P.data.faceZ
abbrev faceQ (P : TannerSquarePresentation) := P.data.faceQ

/-- The project-selected perfect pairing as an actual equivalence. -/
noncomputable def faceCornerEquiv (P : TannerSquarePresentation) (x : P.X) (z : P.Z) :
    FaceOver P.data x z × Two ≃ SharedQ P.data x z :=
  Equiv.ofBijective (faceCornerToShared P.data x z) (P.perfectPairing x z)

/-- The two ordered Q corners of every presented face are distinct.  This is a
consequence of the sole validity field, not an additional presentation axiom. -/
theorem faceQ_injective (P : TannerSquarePresentation) (f : P.Face) :
    Function.Injective (P.faceQ f) := by
  intro first second hq
  let firstCorner : FaceOver P.data (P.faceX f) (P.faceZ f) × Two :=
    (⟨f, rfl, rfl⟩, first)
  let secondCorner : FaceOver P.data (P.faceX f) (P.faceZ f) × Two :=
    (⟨f, rfl, rfl⟩, second)
  have hshared :
      faceCornerToShared P.data (P.faceX f) (P.faceZ f) firstCorner =
        faceCornerToShared P.data (P.faceX f) (P.faceZ f) secondCorner := by
    apply Subtype.ext
    exact hq
  have hcorner := (P.perfectPairing (P.faceX f) (P.faceZ f)).1 hshared
  exact congrArg Prod.snd hcorner

end TannerSquarePresentation

/-! ## Cellular regularity -/

/-- The raw cellular-regularity domain frozen by #917.

There is exactly one field: a face is determined by its opposite X/Z pair.
No admissibility, cohomology, contraction, filling, path, or selected inverse is
stored here.
-/
structure TannerSquareCellularRegular (P : TannerSquarePresentation) where
  faceXZ_injective :
    Function.Injective (fun face : P.Face => (P.faceX face, P.faceZ face))

/-- Every fixed X/Z face fiber is subsingleton.  This is theorem-derived from
the raw injectivity field rather than stored as a second regularity field. -/
theorem TannerSquareCellularRegular.faceOver_subsingleton
    {P : TannerSquarePresentation} (R : TannerSquareCellularRegular P)
    (x : P.X) (z : P.Z) : Subsingleton (FaceOver P.data x z) where
  allEq := by
    intro first second
    apply Subtype.ext
    apply R.faceXZ_injective
    apply Prod.ext
    · exact first.2.1.trans second.2.1.symm
    · exact first.2.2.trans second.2.2.symm

/-! ## The theorem-derived X/Z transpose -/

/-- Swap X and Z while retaining the same faces and ordered Q corners. -/
def transposeTannerSquareData (P : TannerSquarePresentation) : TannerSquareData where
  X := P.Z
  Q := P.Q
  Z := P.X
  Face := P.Face
  xFintype := P.data.zFintype
  qFintype := P.data.qFintype
  zFintype := P.data.xFintype
  faceFintype := P.data.faceFintype
  xDecidableEq := P.data.zDecidableEq
  qDecidableEq := P.data.qDecidableEq
  zDecidableEq := P.data.xDecidableEq
  faceDecidableEq := P.data.faceDecidableEq
  xq := fun z q => P.qz q z
  qz := fun q x => P.xq x q
  faceX := P.faceZ
  faceZ := P.faceX
  faceQ := P.faceQ
  faceQ_xq := P.data.faceQ_qz
  faceQ_qz := P.data.faceQ_xq

/-- Face fibers of the transpose are the original fibers with endpoints swapped. -/
def transposeFaceOverEquiv (P : TannerSquarePresentation) (z : P.Z) (x : P.X) :
    FaceOver (transposeTannerSquareData P) z x ≃ FaceOver P.data x z where
  toFun := fun f => ⟨f.1, f.2.2, f.2.1⟩
  invFun := fun f => ⟨f.1, f.2.2, f.2.1⟩
  left_inv := fun _ => Subtype.ext rfl
  right_inv := fun _ => Subtype.ext rfl

/-- Shared-Q fibers of the transpose are the original fibers with the Boolean
conjunction reordered. -/
def transposeSharedQEquiv (P : TannerSquarePresentation) (z : P.Z) (x : P.X) :
    SharedQ (transposeTannerSquareData P) z x ≃ SharedQ P.data x z where
  toFun := fun q => ⟨q.1, by simpa [transposeTannerSquareData, Bool.and_comm] using q.2⟩
  invFun := fun q => ⟨q.1, by simpa [transposeTannerSquareData, Bool.and_comm] using q.2⟩
  left_inv := fun q => Subtype.ext rfl
  right_inv := fun q => Subtype.ext rfl

/-- Ordered face corners transport along the swapped face fiber. -/
def transposeFaceCornerDomainEquiv (P : TannerSquarePresentation)
    (z : P.Z) (x : P.X) :
    FaceOver (transposeTannerSquareData P) z x × Two ≃
      FaceOver P.data x z × Two :=
  Equiv.prodCongr (transposeFaceOverEquiv P z x) (Equiv.refl Two)

theorem transpose_faceCorner_commutes (P : TannerSquarePresentation)
    (z : P.Z) (x : P.X)
    (fi : FaceOver (transposeTannerSquareData P) z x × Two) :
    transposeSharedQEquiv P z x
        (faceCornerToShared (transposeTannerSquareData P) z x fi) =
      faceCornerToShared P.data x z (transposeFaceCornerDomainEquiv P z x fi) := by
  apply Subtype.ext
  rfl

/-- The transpose has no additional validity input: its perfect pairing is
transported from the original presentation's pairing theorem. -/
noncomputable def transposePresentation (P : TannerSquarePresentation) :
    TannerSquarePresentation where
  data := transposeTannerSquareData P
  perfectPairing := by
    intro z x
    let A := transposeFaceCornerDomainEquiv P z x
    let B := transposeSharedQEquiv P z x
    constructor
    · intro a b hab
      apply A.injective
      apply (P.perfectPairing x z).1
      have h := congrArg B hab
      change transposeSharedQEquiv P z x _ = transposeSharedQEquiv P z x _ at h
      erw [transpose_faceCorner_commutes, transpose_faceCorner_commutes] at h
      exact h
    · intro y
      obtain ⟨a, ha⟩ := (P.perfectPairing x z).2 (B y)
      refine ⟨A.symm a, ?_⟩
      apply B.injective
      change transposeSharedQEquiv P z x _ = transposeSharedQEquiv P z x _
      erw [transpose_faceCorner_commutes]
      change faceCornerToShared P.data x z (A (A.symm a)) = B y
      erw [A.apply_symm_apply]
      exact ha

/-- Cellular regularity is preserved by transposition because the face pair
coordinates are only swapped. -/
def transposeTannerSquareCellularRegular (P : TannerSquarePresentation)
    (R : TannerSquareCellularRegular P) :
    TannerSquareCellularRegular (transposePresentation P) where
  faceXZ_injective := by
    intro first second hpairs
    apply R.faceXZ_injective
    apply Prod.ext
    · exact congrArg Prod.snd hpairs
    · exact congrArg Prod.fst hpairs

/-! ## Derived cells and incidence matrices -/

/-- Typed cellular vertices. -/
inductive Vertex (P : TannerSquarePresentation) where
  | x : P.X → Vertex P
  | q : P.Q → Vertex P
  | z : P.Z → Vertex P
  deriving DecidableEq, Fintype

/-- X-Q edges are exactly true X-Q incidences. -/
abbrev XQEdge (P : TannerSquarePresentation) :=
  {e : P.X × P.Q // P.xq e.1 e.2 = true}

/-- Q-Z edges are exactly true Q-Z incidences. -/
abbrev QZEdge (P : TannerSquarePresentation) :=
  {e : P.Q × P.Z // P.qz e.1 e.2 = true}

/-- The disjoint union of the two typed edge classes. -/
abbrev Edge (P : TannerSquarePresentation) := XQEdge P ⊕ QZEdge P

/-- The X-Q edge selected by one ordered face corner. -/
def faceXQEdge (P : TannerSquarePresentation) (f : P.Face) (i : Two) : XQEdge P :=
  ⟨(P.faceX f, P.faceQ f i), P.data.faceQ_xq f i⟩

/-- The Q-Z edge selected by one ordered face corner. -/
def faceQZEdge (P : TannerSquarePresentation) (f : P.Face) (i : Two) : QZEdge P :=
  ⟨(P.faceQ f i, P.faceZ f), P.data.faceQ_qz f i⟩

/-- Cellular vertices of the transpose are the original vertices with X and Z
tags exchanged. -/
noncomputable def transposeVertexEquiv (P : TannerSquarePresentation) :
    Vertex (transposePresentation P) ≃ Vertex P where
  toFun
    | .x z => .z z
    | .q q => .q q
    | .z x => .x x
  invFun
    | .x x => .z x
    | .q q => .q q
    | .z z => .x z
  left_inv := by intro v; cases v <;> rfl
  right_inv := by intro v; cases v <;> rfl

/-- Transposed X-Q edges are original Q-Z edges. -/
noncomputable def transposeXQEdgeEquiv (P : TannerSquarePresentation) :
    XQEdge (transposePresentation P) ≃ QZEdge P where
  toFun := fun e => ⟨(e.1.2, e.1.1), e.2⟩
  invFun := fun e => ⟨(e.1.2, e.1.1), e.2⟩
  left_inv := fun e => Subtype.ext (by simp)
  right_inv := fun e => Subtype.ext (by simp)

/-- Transposed Q-Z edges are original X-Q edges. -/
noncomputable def transposeQZEdgeEquiv (P : TannerSquarePresentation) :
    QZEdge (transposePresentation P) ≃ XQEdge P where
  toFun := fun e => ⟨(e.1.2, e.1.1), e.2⟩
  invFun := fun e => ⟨(e.1.2, e.1.1), e.2⟩
  left_inv := fun e => Subtype.ext (by simp)
  right_inv := fun e => Subtype.ext (by simp)

/-- Transposed cellular edges are original edges with the two edge classes
exchanged. -/
noncomputable def transposeEdgeEquiv (P : TannerSquarePresentation) :
    Edge (transposePresentation P) ≃ Edge P where
  toFun
    | Sum.inl e => Sum.inr (transposeXQEdgeEquiv P e)
    | Sum.inr e => Sum.inl (transposeQZEdgeEquiv P e)
  invFun
    | Sum.inl e => Sum.inr ((transposeQZEdgeEquiv P).symm e)
    | Sum.inr e => Sum.inl ((transposeXQEdgeEquiv P).symm e)
  left_inv := by
    intro e
    rcases e with e | e <;> simp
  right_inv := by
    intro e
    rcases e with e | e <;> simp

@[simp] theorem transposeXQEdgeEquiv_faceXQEdge
    (P : TannerSquarePresentation) (f : P.Face) (i : Two) :
    transposeXQEdgeEquiv P (faceXQEdge (transposePresentation P) f i) =
      faceQZEdge P f i := rfl

@[simp] theorem transposeQZEdgeEquiv_faceQZEdge
    (P : TannerSquarePresentation) (f : P.Face) (i : Two) :
    transposeQZEdgeEquiv P (faceQZEdge (transposePresentation P) f i) =
      faceXQEdge P f i := rfl

@[simp] theorem transpose_faceXQEdge (P : TannerSquarePresentation)
    (f : P.Face) (i : Two) :
    transposeEdgeEquiv P
        (Sum.inl (faceXQEdge (transposePresentation P) f i)) =
      (Sum.inr (faceQZEdge P f i) : Edge P) := by
  rfl

@[simp] theorem transpose_faceQZEdge (P : TannerSquarePresentation)
    (f : P.Face) (i : Two) :
    transposeEdgeEquiv P
        (Sum.inr (faceQZEdge (transposePresentation P) f i)) =
      (Sum.inl (faceXQEdge P f i) : Edge P) := by
  rfl

/-- X-Q incidence over F2. -/
def xqIncidenceMatrix (P : TannerSquarePresentation) : Matrix P.X P.Q Field :=
  fun x q => if P.xq x q = true then 1 else 0

/-- Q-Z incidence over F2. -/
def qzIncidenceMatrix (P : TannerSquarePresentation) : Matrix P.Q P.Z Field :=
  fun q z => if P.qz q z = true then 1 else 0

/-- The endpoint-incidence matrix of the cellular one-skeleton. -/
def edgeVertexMatrix (P : TannerSquarePresentation) : Matrix (Vertex P) (Edge P) Field
  | .x x, Sum.inl e => if x = e.1.1 then 1 else 0
  | .q q, Sum.inl e => if q = e.1.2 then 1 else 0
  | .q q, Sum.inr e => if q = e.1.1 then 1 else 0
  | .z z, Sum.inr e => if z = e.1.2 then 1 else 0
  | _, _ => 0

/-- The four-edge boundary of each Tanner-square face. -/
def faceEdgeMatrix (P : TannerSquarePresentation) : Matrix (Edge P) P.Face Field :=
  fun e f =>
    (if e = (Sum.inl (faceXQEdge P f 0) : Edge P) then 1 else 0) +
    (if e = (Sum.inr (faceQZEdge P f 0) : Edge P) then 1 else 0) +
    (if e = (Sum.inl (faceXQEdge P f 1) : Edge P) then 1 else 0) +
    (if e = (Sum.inr (faceQZEdge P f 1) : Edge P) then 1 else 0)

/-- A paired shared-Q fiber contributes zero in characteristic two. -/
theorem sharedQ_indicator_sum_zero (P : TannerSquarePresentation) (x : P.X) (z : P.Z) :
    (∑ q : P.Q, if P.xq x q && P.qz q z then (1 : Field) else 0) = 0 := by
  classical
  let shared : Finset P.Q := Finset.univ.filter fun q => P.xq x q && P.qz q z
  have hsubtype :
      (∑ q ∈ shared, (1 : Field)) =
        ∑ q : SharedQ P.data x z, (1 : Field) := by
    exact Finset.sum_subtype shared (by simp [shared]) (fun _ => (1 : Field))
  have hpair :
      (∑ fi : FaceOver P.data x z × Two, (1 : Field)) =
        ∑ q : SharedQ P.data x z, (1 : Field) := by
    exact Fintype.sum_equiv (P.faceCornerEquiv x z)
      (fun _ => (1 : Field)) (fun _ => (1 : Field)) (fun _ => rfl)
  calc
    (∑ q : P.Q, if P.xq x q && P.qz q z then (1 : Field) else 0) =
        ∑ q ∈ shared, (1 : Field) := by
      simp [shared]
    _ = ∑ q : SharedQ P.data x z, (1 : Field) := hsubtype
    _ = ∑ fi : FaceOver P.data x z × Two, (1 : Field) := hpair.symm
    _ = 0 := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [show (Fintype.card Two : Field) = 0 by
        change (2 : ZMod 2) = 0
        decide]
      simp

/-- The Tanner incidence product vanishes by the explicit perfect pairing. -/
theorem xqIncidenceMatrix_mul_qzIncidenceMatrix (P : TannerSquarePresentation) :
    xqIncidenceMatrix P * qzIncidenceMatrix P = 0 := by
  classical
  ext x z
  rw [Matrix.mul_apply]
  simp only [xqIncidenceMatrix, qzIncidenceMatrix]
  calc
    (∑ q : P.Q,
        (if P.xq x q = true then 1 else 0) *
          (if P.qz q z = true then 1 else 0)) =
        ∑ q : P.Q,
          if P.xq x q && P.qz q z then (1 : Field) else 0 := by
      apply Finset.sum_congr rfl
      intro q _hq
      by_cases hx : P.xq x q = true <;>
        by_cases hz : P.qz q z = true <;> simp [hx, hz]
    _ = 0 := sharedQ_indicator_sum_zero P x z

/-- Summing an equality indicator selects its target. -/
private theorem sum_mul_eqIndicator {A : Type} [Fintype A] [DecidableEq A]
    (w : A → Field) (a : A) :
    (∑ b : A, w b * if b = a then 1 else 0) = w a := by
  classical
  simp

private theorem field_add_self (a : Field) : a + a = 0 := by
  exact ZModModule.add_self a

private theorem field_two_pairs (a b : Field) : ((a + a) + b) + b = 0 := by
  rw [field_add_self, zero_add, field_add_self]

/-- Cellular edge-to-vertex followed by face-to-edge is zero. -/
theorem edgeVertexMatrix_mul_faceEdgeMatrix (P : TannerSquarePresentation) :
    edgeVertexMatrix P * faceEdgeMatrix P = 0 := by
  classical
  ext v f
  rw [Matrix.mul_apply]
  simp only [faceEdgeMatrix, mul_add, Finset.sum_add_distrib]
  simp only [sum_mul_eqIndicator]
  cases v with
  | x x =>
      simp [edgeVertexMatrix, faceXQEdge]
      exact field_add_self (if x = P.faceX f then (1 : Field) else 0)
  | q q =>
      simp [edgeVertexMatrix, faceXQEdge, faceQZEdge]
      exact field_two_pairs
          (if q = P.faceQ f 0 then (1 : Field) else 0)
          (if q = P.faceQ f 1 then (1 : Field) else 0)
  | z z =>
      simp [edgeVertexMatrix, faceQZEdge]
      exact field_add_self (if z = P.faceZ f then (1 : Field) else 0)

/-- Cellular edge-to-vertex boundary. -/
noncomputable def cellularBoundary1 (P : TannerSquarePresentation) :
    Word Field (Edge P) →ₗ[Field] Word Field (Vertex P) :=
  Matrix.toLin' (edgeVertexMatrix P)

/-- Cellular face-to-edge boundary. -/
noncomputable def cellularBoundary2 (P : TannerSquarePresentation) :
    Word Field P.Face →ₗ[Field] Word Field (Edge P) :=
  Matrix.toLin' (faceEdgeMatrix P)

/-- The constructed cellular boundaries compose to zero. -/
theorem cellularBoundary_squared (P : TannerSquarePresentation) :
    (cellularBoundary1 P).comp (cellularBoundary2 P) = 0 := by
  rw [cellularBoundary1, cellularBoundary2, ← Matrix.toLin'_mul]
  rw [edgeVertexMatrix_mul_faceEdgeMatrix]
  simp

/-- The constructed cellular coboundaries. -/
noncomputable def cellularCoboundary0 (P : TannerSquarePresentation) :=
  wordLinearMapTranspose (cellularBoundary1 P)

noncomputable def cellularCoboundary1 (P : TannerSquarePresentation) :=
  wordLinearMapTranspose (cellularBoundary2 P)

/-- The constructed cellular coboundaries compose to zero. -/
theorem cellularCoboundary_squared (P : TannerSquarePresentation) :
    (cellularCoboundary1 P).comp (cellularCoboundary0 P) = 0 := by
  rw [cellularCoboundary1, cellularCoboundary0]
  rw [← wordLinearMapTranspose_comp]
  rw [cellularBoundary_squared]
  exact wordLinearMapTranspose_zero

/-- The chain complex constructed from a Tanner-square presentation. -/
noncomputable def cellularChainComplex (P : TannerSquarePresentation) :
    ChainComplexData Field
      (Word Field (Vertex P)) (Word Field (Edge P)) (Word Field P.Face) where
  boundary1 := cellularBoundary1 P
  boundary2 := cellularBoundary2 P
  boundary_squared := cellularBoundary_squared P

/-! ## Exact bridge to the #844 base seed -/

abbrev BaseFace := Fin 4

def baseFaceX : BaseFace → BaseX := ![0, 0, 1, 1]
def baseFaceZ : BaseFace → BaseZ := ![0, 1, 0, 1]
def baseFaceQ : BaseFace → Two → BaseQubit :=
  !![0, 4;
     1, 4;
     2, 4;
     3, 4]

def baseTannerSquareData : TannerSquareData where
  X := BaseX
  Q := BaseQubit
  Z := BaseZ
  Face := BaseFace
  xFintype := inferInstance
  qFintype := inferInstance
  zFintype := inferInstance
  faceFintype := inferInstance
  xDecidableEq := inferInstance
  qDecidableEq := inferInstance
  zDecidableEq := inferInstance
  faceDecidableEq := inferInstance
  xq := fun x q => decide (baseBoundary1Matrix x q ≠ 0)
  qz := fun q z => decide (baseBoundary2Matrix q z ≠ 0)
  faceX := baseFaceX
  faceZ := baseFaceZ
  faceQ := baseFaceQ
  faceQ_xq := by native_decide
  faceQ_qz := by native_decide

/-- The four owner-verified base faces form the required perfect pairing. -/
def baseTannerSquarePresentation : TannerSquarePresentation where
  data := baseTannerSquareData
  perfectPairing := by
    intro x z
    native_decide +revert

/-- The four base faces have the distinct opposite-coordinate pairs
`(0,0)`, `(0,1)`, `(1,0)`, and `(1,1)`. -/
def baseTannerSquareCellularRegular :
    TannerSquareCellularRegular baseTannerSquarePresentation where
  faceXZ_injective := by
    native_decide +revert

@[simp] theorem baseFace_card : Fintype.card BaseFace = 4 := by simp [BaseFace]

@[simp] theorem baseXQEdge_card : Fintype.card (XQEdge baseTannerSquarePresentation) = 6 := by
  native_decide

@[simp] theorem baseQZEdge_card : Fintype.card (QZEdge baseTannerSquarePresentation) = 6 := by
  native_decide

theorem base_xqIncidenceMatrix_eq :
    xqIncidenceMatrix baseTannerSquarePresentation = baseBoundary1Matrix := by
  change (fun (x : BaseX) (q : BaseQubit) =>
    if decide (baseBoundary1Matrix x q ≠ 0) then (1 : Field) else 0) = _
  funext x q
  fin_cases x <;> fin_cases q <;> decide

theorem base_qzIncidenceMatrix_eq :
    qzIncidenceMatrix baseTannerSquarePresentation = baseBoundary2Matrix := by
  change (fun (q : BaseQubit) (z : BaseZ) =>
    if decide (baseBoundary2Matrix q z ≠ 0) then (1 : Field) else 0) = _
  funext q z
  fin_cases q <;> fin_cases z <;> decide

/-! ## Constructed stars, closures, and boundary cell sets -/

private def faceUsesXQEdge (P : TannerSquarePresentation) (f : P.Face)
    (e : XQEdge P) : Bool :=
  decide (e = faceXQEdge P f 0 ∨ e = faceXQEdge P f 1)

private def faceUsesQZEdge (P : TannerSquarePresentation) (f : P.Face)
    (e : QZEdge P) : Bool :=
  decide (e = faceQZEdge P f 0 ∨ e = faceQZEdge P f 1)

private theorem transpose_faceUsesXQEdge (P : TannerSquarePresentation)
    (f : P.Face) (e : XQEdge (transposePresentation P)) :
    faceUsesXQEdge (transposePresentation P) f e =
      faceUsesQZEdge P f (transposeXQEdgeEquiv P e) := by
  apply Bool.decide_congr
  constructor
  · rintro (h | h)
    · left
      simpa using congrArg (transposeXQEdgeEquiv P) h
    · right
      simpa using congrArg (transposeXQEdgeEquiv P) h
  · rintro (h | h)
    · left
      apply (transposeXQEdgeEquiv P).injective
      simpa using h
    · right
      apply (transposeXQEdgeEquiv P).injective
      simpa using h

private theorem transpose_faceUsesQZEdge (P : TannerSquarePresentation)
    (f : P.Face) (e : QZEdge (transposePresentation P)) :
    faceUsesQZEdge (transposePresentation P) f e =
      faceUsesXQEdge P f (transposeQZEdgeEquiv P e) := by
  apply Bool.decide_congr
  constructor
  · rintro (h | h)
    · left
      simpa using congrArg (transposeQZEdgeEquiv P) h
    · right
      simpa using congrArg (transposeQZEdgeEquiv P) h
  · rintro (h | h)
    · left
      apply (transposeQZEdgeEquiv P).injective
      simpa using h
    · right
      apply (transposeQZEdgeEquiv P).injective
      simpa using h

/-- Faces in the closed X-star. -/
def xStarFaceMember (P : TannerSquarePresentation) (x : P.X) (f : P.Face) : Bool :=
  decide (P.faceX f = x)

/-- Edges in the closed X-star, constructed from its face boundaries. -/
def xStarEdgeMember (P : TannerSquarePresentation) (x : P.X) : Edge P → Bool
  | Sum.inl e => decide (∃ f : P.Face,
      xStarFaceMember P x f = true ∧ faceUsesXQEdge P f e = true)
  | Sum.inr e => decide (∃ f : P.Face,
      xStarFaceMember P x f = true ∧ faceUsesQZEdge P f e = true)

/-- Vertices in the closed X-star, constructed from its face corners. -/
def xStarVertexMember (P : TannerSquarePresentation) (x : P.X) : Vertex P → Bool
  | .x x' => decide (x' = x)
  | .q q => decide (∃ f : P.Face,
      xStarFaceMember P x f = true ∧
        (q = P.faceQ f 0 ∨ q = P.faceQ f 1))
  | .z z => decide (∃ f : P.Face,
      xStarFaceMember P x f = true ∧ z = P.faceZ f)

abbrev XStarFace (P : TannerSquarePresentation) (x : P.X) :=
  {f : P.Face // xStarFaceMember P x f}

abbrev XStarEdge (P : TannerSquarePresentation) (x : P.X) :=
  {e : Edge P // xStarEdgeMember P x e}

abbrev XStarVertex (P : TannerSquarePresentation) (x : P.X) :=
  {v : Vertex P // xStarVertexMember P x v}

/-- The X-star boundary consists of its Q-Z sides. -/
def xStarBoundaryEdgeMember (P : TannerSquarePresentation) (x : P.X) : Edge P → Bool
  | Sum.inl _ => false
  | Sum.inr e => decide (∃ f : P.Face,
      xStarFaceMember P x f = true ∧ faceUsesQZEdge P f e = true)

/-- The X-star boundary vertices are the endpoints of its Q-Z sides. -/
def xStarBoundaryVertexMember (P : TannerSquarePresentation) (x : P.X) : Vertex P → Bool
  | .x _ => false
  | .q q => decide (∃ f : P.Face,
      xStarFaceMember P x f = true ∧
        (q = P.faceQ f 0 ∨ q = P.faceQ f 1))
  | .z z => decide (∃ f : P.Face,
      xStarFaceMember P x f = true ∧ z = P.faceZ f)

abbrev XStarBoundaryEdge (P : TannerSquarePresentation) (x : P.X) :=
  {e : Edge P // xStarBoundaryEdgeMember P x e}

abbrev XStarBoundaryVertex (P : TannerSquarePresentation) (x : P.X) :=
  {v : Vertex P // xStarBoundaryVertexMember P x v}

theorem xStarBoundaryVertexMember_to_star (P : TannerSquarePresentation)
    (x : P.X) (v : Vertex P) (hv : xStarBoundaryVertexMember P x v) :
    xStarVertexMember P x v := by
  rcases v with x' | q | z
  · simp [xStarBoundaryVertexMember] at hv
  · simpa [xStarBoundaryVertexMember, xStarVertexMember] using hv
  · simpa [xStarBoundaryVertexMember, xStarVertexMember] using hv

theorem xStarBoundaryEdgeMember_to_star (P : TannerSquarePresentation)
    (x : P.X) (e : Edge P) (he : xStarBoundaryEdgeMember P x e) :
    xStarEdgeMember P x e := by
  rcases e with e | e
  · simp [xStarBoundaryEdgeMember] at he
  · simpa [xStarBoundaryEdgeMember, xStarEdgeMember] using he

/-- Forget only the boundary label, retaining membership in the closed star. -/
def xStarBoundaryVertexToStar (P : TannerSquarePresentation) (x : P.X) :
    XStarBoundaryVertex P x → XStarVertex P x := fun v =>
  ⟨v.1, xStarBoundaryVertexMember_to_star P x v.1 v.2⟩

def xStarBoundaryEdgeToStar (P : TannerSquarePresentation) (x : P.X) :
    XStarBoundaryEdge P x → XStarEdge P x := fun e =>
  ⟨e.1, xStarBoundaryEdgeMember_to_star P x e.1 e.2⟩

/-- Faces in the closed Z-star. -/
def zStarFaceMember (P : TannerSquarePresentation) (z : P.Z) (f : P.Face) : Bool :=
  decide (P.faceZ f = z)

/-- Edges in the closed Z-star. -/
def zStarEdgeMember (P : TannerSquarePresentation) (z : P.Z) : Edge P → Bool
  | Sum.inl e => decide (∃ f : P.Face,
      zStarFaceMember P z f = true ∧ faceUsesXQEdge P f e = true)
  | Sum.inr e => decide (∃ f : P.Face,
      zStarFaceMember P z f = true ∧ faceUsesQZEdge P f e = true)

/-- Vertices in the closed Z-star. -/
def zStarVertexMember (P : TannerSquarePresentation) (z : P.Z) : Vertex P → Bool
  | .x x => decide (∃ f : P.Face,
      zStarFaceMember P z f = true ∧ x = P.faceX f)
  | .q q => decide (∃ f : P.Face,
      zStarFaceMember P z f = true ∧
        (q = P.faceQ f 0 ∨ q = P.faceQ f 1))
  | .z z' => decide (z' = z)

abbrev ZStarFace (P : TannerSquarePresentation) (z : P.Z) :=
  {f : P.Face // zStarFaceMember P z f}

abbrev ZStarEdge (P : TannerSquarePresentation) (z : P.Z) :=
  {e : Edge P // zStarEdgeMember P z e}

abbrev ZStarVertex (P : TannerSquarePresentation) (z : P.Z) :=
  {v : Vertex P // zStarVertexMember P z v}

/-- The Z-star boundary consists of its X-Q sides. -/
def zStarBoundaryEdgeMember (P : TannerSquarePresentation) (z : P.Z) : Edge P → Bool
  | Sum.inl e => decide (∃ f : P.Face,
      zStarFaceMember P z f = true ∧ faceUsesXQEdge P f e = true)
  | Sum.inr _ => false

/-- The Z-star boundary vertices are the endpoints of its X-Q sides. -/
def zStarBoundaryVertexMember (P : TannerSquarePresentation) (z : P.Z) : Vertex P → Bool
  | .x x => decide (∃ f : P.Face,
      zStarFaceMember P z f = true ∧ x = P.faceX f)
  | .q q => decide (∃ f : P.Face,
      zStarFaceMember P z f = true ∧
        (q = P.faceQ f 0 ∨ q = P.faceQ f 1))
  | .z _ => false

abbrev ZStarBoundaryEdge (P : TannerSquarePresentation) (z : P.Z) :=
  {e : Edge P // zStarBoundaryEdgeMember P z e}

abbrev ZStarBoundaryVertex (P : TannerSquarePresentation) (z : P.Z) :=
  {v : Vertex P // zStarBoundaryVertexMember P z v}

@[simp] theorem transpose_xStarFaceMember (P : TannerSquarePresentation)
    (z : P.Z) (f : P.Face) :
    xStarFaceMember (transposePresentation P) z f = zStarFaceMember P z f := rfl

@[simp] theorem transpose_xStarVertexMember (P : TannerSquarePresentation)
    (z : P.Z) (v : Vertex (transposePresentation P)) :
    xStarVertexMember (transposePresentation P) z v =
      zStarVertexMember P z (transposeVertexEquiv P v) := by
  rcases v with z' | q | x' <;> rfl

@[simp] theorem transpose_xStarEdgeMember (P : TannerSquarePresentation)
    (z : P.Z) (e : Edge (transposePresentation P)) :
    xStarEdgeMember (transposePresentation P) z e =
      zStarEdgeMember P z (transposeEdgeEquiv P e) := by
  rcases e with e | e
  · simp only [xStarEdgeMember, zStarEdgeMember]
    apply Bool.decide_congr
    constructor <;> rintro ⟨f, hf, he⟩
    · exact ⟨f, hf, (transpose_faceUsesXQEdge P f e) ▸ he⟩
    · exact ⟨f, hf, (transpose_faceUsesXQEdge P f e).symm ▸ he⟩
  · simp only [xStarEdgeMember, zStarEdgeMember]
    apply Bool.decide_congr
    constructor <;> rintro ⟨f, hf, he⟩
    · exact ⟨f, hf, (transpose_faceUsesQZEdge P f e) ▸ he⟩
    · exact ⟨f, hf, (transpose_faceUsesQZEdge P f e).symm ▸ he⟩

@[simp] theorem transpose_xStarBoundaryVertexMember
    (P : TannerSquarePresentation) (z : P.Z)
    (v : Vertex (transposePresentation P)) :
    xStarBoundaryVertexMember (transposePresentation P) z v =
      zStarBoundaryVertexMember P z (transposeVertexEquiv P v) := by
  rcases v with z' | q | x' <;> rfl

@[simp] theorem transpose_xStarBoundaryEdgeMember
    (P : TannerSquarePresentation) (z : P.Z)
    (e : Edge (transposePresentation P)) :
    xStarBoundaryEdgeMember (transposePresentation P) z e =
      zStarBoundaryEdgeMember P z (transposeEdgeEquiv P e) := by
  rcases e with e | e
  · rfl
  · simp only [xStarBoundaryEdgeMember, zStarBoundaryEdgeMember]
    apply Bool.decide_congr
    constructor <;> rintro ⟨f, hf, he⟩
    · exact ⟨f, hf, (transpose_faceUsesQZEdge P f e) ▸ he⟩
    · exact ⟨f, hf, (transpose_faceUsesQZEdge P f e).symm ▸ he⟩

/-- Transpose X-star faces are exactly the original Z-star faces. -/
noncomputable def transposeXStarFaceEquiv (P : TannerSquarePresentation) (z : P.Z) :
    XStarFace (transposePresentation P) z ≃ ZStarFace P z where
  toFun := fun f => ⟨f.1, f.2⟩
  invFun := fun f => ⟨f.1, f.2⟩
  left_inv := fun f => Subtype.ext rfl
  right_inv := fun f => Subtype.ext rfl

/-- Transpose X-star vertices are exactly the original Z-star vertices. -/
noncomputable def transposeXStarVertexEquiv (P : TannerSquarePresentation) (z : P.Z) :
    XStarVertex (transposePresentation P) z ≃ ZStarVertex P z where
  toFun := fun v => ⟨transposeVertexEquiv P v.1, by simpa using v.2⟩
  invFun := fun v => ⟨(transposeVertexEquiv P).symm v.1, by
    rw [transpose_xStarVertexMember, Equiv.apply_symm_apply]
    exact v.2⟩
  left_inv := fun v => Subtype.ext (Equiv.symm_apply_apply _ _)
  right_inv := fun v => Subtype.ext (Equiv.apply_symm_apply _ _)

/-- Transpose X-star edges are exactly the original Z-star edges. -/
noncomputable def transposeXStarEdgeEquiv (P : TannerSquarePresentation) (z : P.Z) :
    XStarEdge (transposePresentation P) z ≃ ZStarEdge P z where
  toFun := fun e => ⟨transposeEdgeEquiv P e.1, by simpa using e.2⟩
  invFun := fun e => ⟨(transposeEdgeEquiv P).symm e.1, by
    rw [transpose_xStarEdgeMember, Equiv.apply_symm_apply]
    exact e.2⟩
  left_inv := fun e => Subtype.ext (Equiv.symm_apply_apply _ _)
  right_inv := fun e => Subtype.ext (Equiv.apply_symm_apply _ _)

/-- The same identification restricted to boundary vertices. -/
noncomputable def transposeXStarBoundaryVertexEquiv
    (P : TannerSquarePresentation) (z : P.Z) :
    XStarBoundaryVertex (transposePresentation P) z ≃ ZStarBoundaryVertex P z where
  toFun := fun v => ⟨transposeVertexEquiv P v.1, by simpa using v.2⟩
  invFun := fun v => ⟨(transposeVertexEquiv P).symm v.1, by
    rw [transpose_xStarBoundaryVertexMember, Equiv.apply_symm_apply]
    exact v.2⟩
  left_inv := fun v => Subtype.ext (Equiv.symm_apply_apply _ _)
  right_inv := fun v => Subtype.ext (Equiv.apply_symm_apply _ _)

/-- The same identification restricted to boundary edges. -/
noncomputable def transposeXStarBoundaryEdgeEquiv
    (P : TannerSquarePresentation) (z : P.Z) :
    XStarBoundaryEdge (transposePresentation P) z ≃ ZStarBoundaryEdge P z where
  toFun := fun e => ⟨transposeEdgeEquiv P e.1, by simpa using e.2⟩
  invFun := fun e => ⟨(transposeEdgeEquiv P).symm e.1, by
    rw [transpose_xStarBoundaryEdgeMember, Equiv.apply_symm_apply]
    exact e.2⟩
  left_inv := fun e => Subtype.ext (Equiv.symm_apply_apply _ _)
  right_inv := fun e => Subtype.ext (Equiv.apply_symm_apply _ _)

@[simp] theorem transposeXStarFace_card (P : TannerSquarePresentation) (z : P.Z) :
    Fintype.card (XStarFace (transposePresentation P) z) =
      Fintype.card (ZStarFace P z) :=
  Fintype.card_congr (transposeXStarFaceEquiv P z)

@[simp] theorem transposeXStarVertex_card (P : TannerSquarePresentation) (z : P.Z) :
    Fintype.card (XStarVertex (transposePresentation P) z) =
      Fintype.card (ZStarVertex P z) :=
  Fintype.card_congr (transposeXStarVertexEquiv P z)

@[simp] theorem transposeXStarEdge_card (P : TannerSquarePresentation) (z : P.Z) :
    Fintype.card (XStarEdge (transposePresentation P) z) =
      Fintype.card (ZStarEdge P z) :=
  Fintype.card_congr (transposeXStarEdgeEquiv P z)

@[simp] theorem transposeXStarBoundaryVertex_card
    (P : TannerSquarePresentation) (z : P.Z) :
    Fintype.card (XStarBoundaryVertex (transposePresentation P) z) =
      Fintype.card (ZStarBoundaryVertex P z) :=
  Fintype.card_congr (transposeXStarBoundaryVertexEquiv P z)

@[simp] theorem transposeXStarBoundaryEdge_card
    (P : TannerSquarePresentation) (z : P.Z) :
    Fintype.card (XStarBoundaryEdge (transposePresentation P) z) =
      Fintype.card (ZStarBoundaryEdge P z) :=
  Fintype.card_congr (transposeXStarBoundaryEdgeEquiv P z)

/-! ## Generic finite coordinates -/

/-- Restrict coordinates to a constructed Boolean-labelled finite subset. -/
def coordinateRestriction {A : Type} [Fintype A] [DecidableEq A]
    (member : A → Bool) :
    Word Field A →ₗ[Field] Word Field {a : A // member a} where
  toFun := fun w a => w a.1
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- Extend coordinates by zero from a constructed Boolean-labelled subset. -/
def coordinateExtensionZero {A : Type} [Fintype A] [DecidableEq A]
    (member : A → Bool) :
    Word Field {a : A // member a} →ₗ[Field] Word Field A where
  toFun := fun w a => if h : member a then w ⟨a, h⟩ else 0
  map_add' := by
    intros
    ext a
    by_cases h : member a <;> simp [h]
  map_smul' := by
    intros
    ext a
    by_cases h : member a <;> simp [h]

@[simp]
theorem coordinateRestriction_apply {A : Type} [Fintype A] [DecidableEq A]
    (member : A → Bool) (w : Word Field A) (a : {a : A // member a}) :
    coordinateRestriction member w a = w a.1 := rfl

@[simp]
theorem coordinateExtensionZero_apply_mem {A : Type} [Fintype A] [DecidableEq A]
    (member : A → Bool) (w : Word Field {a : A // member a})
    (a : {a : A // member a}) :
    coordinateExtensionZero member w a.1 = w a := by
  simp [coordinateExtensionZero, a.2]

/-- Canonical finite bases for the constructed Tanner cells. -/
noncomputable def vertexBasis (P : TannerSquarePresentation) :
    Basis (Vertex P) Field (Word Field (Vertex P)) := Pi.basisFun Field (Vertex P)

noncomputable def edgeBasis (P : TannerSquarePresentation) :
    Basis (Edge P) Field (Word Field (Edge P)) := Pi.basisFun Field (Edge P)

noncomputable def faceBasis (P : TannerSquarePresentation) :
    Basis P.Face Field (Word Field P.Face) := Pi.basisFun Field P.Face

/-! ## Odd subdivision tags -/

/-- An odd replacement scale large enough to contain a nontrivial square grid. -/
structure OddScale where
  ell : Nat
  odd : ell % 2 = 1
  three_le : 3 ≤ ell

/-- The source's half-scale `m = (ell - 1) / 2`. -/
def OddScale.half (S : OddScale) : Nat := (S.ell - 1) / 2

theorem OddScale.two_half_add_one (S : OddScale) : 2 * S.half + 1 = S.ell := by
  have hodd := S.odd
  unfold OddScale.half
  omega

theorem OddScale.half_pos (S : OddScale) : 0 < S.half := by
  have hthree := S.three_le
  unfold OddScale.half
  omega

/-- Original vertices, path-interior vertices, and square-interior vertices. -/
abbrev SubdivisionVertex (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :=
  XStarVertex P x ⊕
    ((XStarEdge P x × Fin (S.half - 1)) ⊕
      (XStarFace P x × Fin (S.half - 1) × Fin (S.half - 1)))

/-- Boundary-path segments plus horizontal and vertical square-interior segments. -/
abbrev SubdivisionEdge (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :=
  (XStarEdge P x × Fin S.half) ⊕
    ((XStarFace P x × Fin S.half × Fin (S.half - 1)) ⊕
      (XStarFace P x × Fin (S.half - 1) × Fin S.half))

/-- The canonical `m × m` small squares in each original face. -/
abbrev SubdivisionFace (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :=
  XStarFace P x × Fin S.half × Fin S.half

/-- Boundary labels are retained exactly on original boundary vertices and
interior points of original boundary edges. -/
def subdivisionBoundaryVertexMember (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) : SubdivisionVertex P x S → Bool
  | Sum.inl v => xStarBoundaryVertexMember P x v.1
  | Sum.inr (Sum.inl ei) => xStarBoundaryEdgeMember P x ei.1.1
  | Sum.inr (Sum.inr _) => false

/-- Boundary labels are retained exactly on segments of original boundary edges. -/
def subdivisionBoundaryEdgeMember (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) : SubdivisionEdge P x S → Bool
  | Sum.inl ei => xStarBoundaryEdgeMember P x ei.1.1
  | Sum.inr _ => false

abbrev SubdivisionBoundaryVertex (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) := {v : SubdivisionVertex P x S // subdivisionBoundaryVertexMember P x S v}

abbrev SubdivisionBoundaryEdge (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) := {e : SubdivisionEdge P x S // subdivisionBoundaryEdgeMember P x S e}

/-- Retain an original boundary vertex as a tagged subdivision boundary vertex. -/
def subdivisionOriginalBoundaryVertex (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (v : XStarBoundaryVertex P x) :
    SubdivisionBoundaryVertex P x S :=
  ⟨Sum.inl (xStarBoundaryVertexToStar P x v), v.2⟩

/-- Retain one segment of an original boundary edge with its boundary label. -/
def subdivisionOriginalBoundaryEdge (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (e : XStarBoundaryEdge P x) (k : Fin S.half) :
    SubdivisionBoundaryEdge P x S :=
  ⟨Sum.inl (xStarBoundaryEdgeToStar P x e, k), e.2⟩

/-- The original-vertex tag preserves the boundary label definitionally. -/
theorem subdivision_original_boundary_label (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (v : XStarVertex P x) :
    subdivisionBoundaryVertexMember P x S (Sum.inl v) =
      xStarBoundaryVertexMember P x v.1 := rfl

/-- The exact scale-five fixture. -/
def scaleFive : OddScale where
  ell := 5
  odd := by decide
  three_le := by decide

@[simp] theorem scaleFive_half : scaleFive.half = 2 := by decide

@[simp] theorem baseX0StarVertex_card :
    Fintype.card (XStarVertex baseTannerSquarePresentation (0 : BaseX)) = 6 := by native_decide

@[simp] theorem baseX0StarEdge_card :
    Fintype.card (XStarEdge baseTannerSquarePresentation (0 : BaseX)) = 7 := by native_decide

@[simp] theorem baseX0StarFace_card :
    Fintype.card (XStarFace baseTannerSquarePresentation (0 : BaseX)) = 2 := by native_decide

@[simp] theorem baseX0StarBoundaryVertex_card :
    Fintype.card (XStarBoundaryVertex baseTannerSquarePresentation (0 : BaseX)) = 5 := by native_decide

@[simp] theorem baseX0StarBoundaryEdge_card :
    Fintype.card (XStarBoundaryEdge baseTannerSquarePresentation (0 : BaseX)) = 4 := by native_decide

@[simp] theorem baseX0SubdivisionVertex_card :
    Fintype.card (SubdivisionVertex baseTannerSquarePresentation (0 : BaseX) scaleFive) = 15 := by
  native_decide

@[simp] theorem baseX0SubdivisionEdge_card :
    Fintype.card (SubdivisionEdge baseTannerSquarePresentation (0 : BaseX) scaleFive) = 22 := by
  native_decide

@[simp] theorem baseX0SubdivisionFace_card :
    Fintype.card (SubdivisionFace baseTannerSquarePresentation (0 : BaseX) scaleFive) = 8 := by
  native_decide

@[simp] theorem baseX0SubdivisionBoundaryVertex_card :
    Fintype.card (SubdivisionBoundaryVertex baseTannerSquarePresentation (0 : BaseX) scaleFive) = 9 := by
  native_decide

@[simp] theorem baseX0SubdivisionBoundaryEdge_card :
    Fintype.card (SubdivisionBoundaryEdge baseTannerSquarePresentation (0 : BaseX) scaleFive) = 8 := by
  native_decide

/-! ## Constructed subdivision incidence -/

/-- A face of an X-star supplies each of its four star edges. -/
def xStarFaceXQEdge (P : TannerSquarePresentation) (x : P.X)
    (f : XStarFace P x) (i : Two) : XStarEdge P x :=
  ⟨Sum.inl (faceXQEdge P f.1 i), by
    have hf : P.faceX f.1 = x := by
      simpa [xStarFaceMember] using f.2
    simp only [xStarEdgeMember]
    simp only [decide_eq_true_eq]
    refine ⟨f.1, ?_, ?_⟩
    · simpa [xStarFaceMember] using hf
    · fin_cases i <;> simp [faceUsesXQEdge]⟩

def xStarFaceQZEdge (P : TannerSquarePresentation) (x : P.X)
    (f : XStarFace P x) (i : Two) : XStarEdge P x :=
  ⟨Sum.inr (faceQZEdge P f.1 i), by
    have hf : P.faceX f.1 = x := by
      simpa [xStarFaceMember] using f.2
    simp only [xStarEdgeMember]
    simp only [decide_eq_true_eq]
    refine ⟨f.1, ?_, ?_⟩
    · simpa [xStarFaceMember] using hf
    · fin_cases i <;> simp [faceUsesQZEdge]⟩

/-- A face of a Z-star supplies each of its two boundary X-Q edges. -/
def zStarFaceXQEdge (P : TannerSquarePresentation) (z : P.Z)
    (f : ZStarFace P z) (i : Two) : ZStarEdge P z :=
  ⟨Sum.inl (faceXQEdge P f.1 i), by
    have hf : P.faceZ f.1 = z := by
      simpa [zStarFaceMember] using f.2
    change decide (∃ face : P.Face,
      zStarFaceMember P z face = true ∧
        decide (faceXQEdge P f.1 i = faceXQEdge P face 0 ∨
          faceXQEdge P f.1 i = faceXQEdge P face 1) = true) = true
    rw [decide_eq_true_eq]
    refine ⟨f.1, ?_, ?_⟩
    · simpa [zStarFaceMember] using hf
    · fin_cases i <;> simp⟩

/-- A face of a Z-star supplies each of its two radial Q-Z edges. -/
def zStarFaceQZEdge (P : TannerSquarePresentation) (z : P.Z)
    (f : ZStarFace P z) (i : Two) : ZStarEdge P z :=
  ⟨Sum.inr (faceQZEdge P f.1 i), by
    have hf : P.faceZ f.1 = z := by
      simpa [zStarFaceMember] using f.2
    change decide (∃ face : P.Face,
      zStarFaceMember P z face = true ∧
        decide (faceQZEdge P f.1 i = faceQZEdge P face 0 ∨
          faceQZEdge P f.1 i = faceQZEdge P face 1) = true) = true
    rw [decide_eq_true_eq]
    refine ⟨f.1, ?_, ?_⟩
    · simpa [zStarFaceMember] using hf
    · fin_cases i <;> simp⟩

/-- The four corner vertices supplied by an X-star face. -/
def xStarFaceXVertex (P : TannerSquarePresentation) (x : P.X)
    (f : XStarFace P x) : XStarVertex P x :=
  ⟨Vertex.x (P.faceX f.1), by
    have hf : P.faceX f.1 = x := by simpa [xStarFaceMember] using f.2
    simp [xStarVertexMember, hf]⟩

def xStarFaceQVertex (P : TannerSquarePresentation) (x : P.X)
    (f : XStarFace P x) (i : Two) : XStarVertex P x :=
  ⟨Vertex.q (P.faceQ f.1 i), by
    have hf : P.faceX f.1 = x := by simpa [xStarFaceMember] using f.2
    simp only [xStarVertexMember, decide_eq_true_eq]
    refine ⟨f.1, ?_, ?_⟩
    · simpa [xStarFaceMember] using hf
    · fin_cases i <;> simp⟩

def xStarFaceZVertex (P : TannerSquarePresentation) (x : P.X)
    (f : XStarFace P x) : XStarVertex P x :=
  ⟨Vertex.z (P.faceZ f.1), by
    have hf : P.faceX f.1 = x := by simpa [xStarFaceMember] using f.2
    simp only [xStarVertexMember, decide_eq_true_eq]
    exact ⟨f.1, by simpa [xStarFaceMember] using hf, rfl⟩⟩

/-- Grid-compatible enumeration of the four vertices of one original face:
`(0,0)=X`, `(0,1)=Q1`, `(1,0)=Q0`, and `(1,1)=Z`. -/
def xStarFaceCorner (P : TannerSquarePresentation) (x : P.X)
    (f : XStarFace P x) (corner : Two × Two) : XStarVertex P x :=
  if corner.1 = 0 then
    if corner.2 = 0 then xStarFaceXVertex P x f
    else xStarFaceQVertex P x f 1
  else if corner.2 = 0 then xStarFaceQVertex P x f 0
  else xStarFaceZVertex P x f

@[simp] theorem xStarFaceCorner_zero_zero
    (P : TannerSquarePresentation) (x : P.X) (f : XStarFace P x) :
    xStarFaceCorner P x f (0, 0) = xStarFaceXVertex P x f := by
  simp [xStarFaceCorner]

@[simp] theorem xStarFaceCorner_zero_one
    (P : TannerSquarePresentation) (x : P.X) (f : XStarFace P x) :
    xStarFaceCorner P x f (0, 1) = xStarFaceQVertex P x f 1 := by
  simp [xStarFaceCorner]

@[simp] theorem xStarFaceCorner_one_zero
    (P : TannerSquarePresentation) (x : P.X) (f : XStarFace P x) :
    xStarFaceCorner P x f (1, 0) = xStarFaceQVertex P x f 0 := by
  simp [xStarFaceCorner]

@[simp] theorem xStarFaceCorner_one_one
    (P : TannerSquarePresentation) (x : P.X) (f : XStarFace P x) :
    xStarFaceCorner P x f (1, 1) = xStarFaceZVertex P x f := by
  simp [xStarFaceCorner]

/-- The four tagged vertices of one original face are pairwise distinct. -/
theorem xStarFaceCorner_injective
    (P : TannerSquarePresentation) (x : P.X) (f : XStarFace P x) :
    Function.Injective (xStarFaceCorner P x f) := by
  rintro ⟨firstI, firstJ⟩ ⟨secondI, secondJ⟩ h
  have hq : P.faceQ f.1 0 ≠ P.faceQ f.1 1 :=
    Function.Injective.ne (P.faceQ_injective f.1) (by decide)
  have hq' : P.faceQ f.1 1 ≠ P.faceQ f.1 0 := Ne.symm hq
  fin_cases firstI <;> fin_cases firstJ <;>
    fin_cases secondI <;> fin_cases secondJ <;>
    simp [xStarFaceCorner, xStarFaceXVertex, xStarFaceQVertex,
      xStarFaceZVertex, hq, hq'] at h ⊢

private theorem xStarFaceXQEdge_injective
    (P : TannerSquarePresentation) (x : P.X) (f : XStarFace P x) :
    Function.Injective (xStarFaceXQEdge P x f) := by
  intro first second h
  apply P.faceQ_injective f.1
  have hvalue := congrArg Subtype.val h
  have hedge := Sum.inl.inj hvalue
  exact congrArg (fun edge : XQEdge P => edge.1.2) hedge

private theorem xStarFaceQZEdge_injective
    (P : TannerSquarePresentation) (x : P.X) (f : XStarFace P x) :
    Function.Injective (xStarFaceQZEdge P x f) := by
  intro first second h
  apply P.faceQ_injective f.1
  have hvalue := congrArg Subtype.val h
  have hedge := Sum.inr.inj hvalue
  exact congrArg (fun edge : QZEdge P => edge.1.1) hedge

@[simp] private theorem xStarFaceXQEdge_ne_QZEdge
    (P : TannerSquarePresentation) (x : P.X) (f : XStarFace P x)
    (i j : Two) :
    xStarFaceXQEdge P x f i ≠ xStarFaceQZEdge P x f j := by
  intro h
  have hvalue := congrArg Subtype.val h
  cases hvalue

@[simp] private theorem xStarFaceQZEdge_ne_XQEdge
    (P : TannerSquarePresentation) (x : P.X) (f : XStarFace P x)
    (i j : Two) :
    xStarFaceQZEdge P x f i ≠ xStarFaceXQEdge P x f j :=
  Ne.symm (xStarFaceXQEdge_ne_QZEdge P x f j i)

/-- Endpoints of a constructed X-star edge. -/
def xStarEdgeStart (P : TannerSquarePresentation) (x : P.X)
    (e : XStarEdge P x) : XStarVertex P x := by
  rcases e with ⟨e, he⟩
  rcases e with eq | eq
  · refine ⟨Vertex.x eq.1.1, ?_⟩
    simp only [xStarEdgeMember, decide_eq_true_eq] at he
    rcases he with ⟨f, hf, huse⟩
    have huse' : eq = faceXQEdge P f 0 ∨ eq = faceXQEdge P f 1 := by
      simpa [faceUsesXQEdge] using huse
    have hx : eq.1.1 = P.faceX f := by
      rcases huse' with huse | huse
      · exact congrArg (fun e : XQEdge P => e.1.1) huse
      · exact congrArg (fun e : XQEdge P => e.1.1) huse
    simp [xStarVertexMember, hx]
    simpa [xStarFaceMember] using hf
  · refine ⟨Vertex.q eq.1.1, ?_⟩
    simp only [xStarEdgeMember, decide_eq_true_eq] at he
    rcases he with ⟨f, hf, huse⟩
    have huse' : eq = faceQZEdge P f 0 ∨ eq = faceQZEdge P f 1 := by
      simpa [faceUsesQZEdge] using huse
    simp only [xStarVertexMember, decide_eq_true_eq]
    refine ⟨f, hf, ?_⟩
    rcases huse' with huse | huse
    · exact Or.inl (congrArg (fun e : QZEdge P => e.1.1) huse)
    · exact Or.inr (congrArg (fun e : QZEdge P => e.1.1) huse)

def xStarEdgeEnd (P : TannerSquarePresentation) (x : P.X)
    (e : XStarEdge P x) : XStarVertex P x := by
  rcases e with ⟨e, he⟩
  rcases e with eq | eq
  · refine ⟨Vertex.q eq.1.2, ?_⟩
    simp only [xStarEdgeMember, decide_eq_true_eq] at he
    rcases he with ⟨f, hf, huse⟩
    have huse' : eq = faceXQEdge P f 0 ∨ eq = faceXQEdge P f 1 := by
      simpa [faceUsesXQEdge] using huse
    simp only [xStarVertexMember, decide_eq_true_eq]
    refine ⟨f, hf, ?_⟩
    rcases huse' with huse | huse
    · exact Or.inl (congrArg (fun e : XQEdge P => e.1.2) huse)
    · exact Or.inr (congrArg (fun e : XQEdge P => e.1.2) huse)
  · refine ⟨Vertex.z eq.1.2, ?_⟩
    simp only [xStarEdgeMember, decide_eq_true_eq] at he
    rcases he with ⟨f, hf, huse⟩
    have huse' : eq = faceQZEdge P f 0 ∨ eq = faceQZEdge P f 1 := by
      simpa [faceUsesQZEdge] using huse
    simp only [xStarVertexMember, decide_eq_true_eq]
    refine ⟨f, hf, ?_⟩
    rcases huse' with huse | huse
    · exact congrArg (fun e : QZEdge P => e.1.2) huse
    · exact congrArg (fun e : QZEdge P => e.1.2) huse

private def finCastGrid {m : Nat} (i : Fin m) : Fin (m + 1) :=
  ⟨i.1, Nat.lt_succ_of_lt i.2⟩

private def finSuccGrid {m : Nat} (i : Fin m) : Fin (m + 1) :=
  ⟨i.1 + 1, by omega⟩

/-- The successor embedding into the finite grid increments the coordinate. -/
theorem finSuccGrid_val {m : Nat} (i : Fin m) :
    (finSuccGrid i).1 = i.1 + 1 := rfl

private def finInteriorGrid (S : OddScale) (i : Fin (S.half - 1)) : Fin (S.half + 1) :=
  ⟨i.1 + 1, by have := S.half_pos; omega⟩

private def finInteriorIndex (S : OddScale) (i : Fin (S.half + 1))
    (h0 : i.1 ≠ 0) (hlast : i.1 ≠ S.half) : Fin (S.half - 1) :=
  ⟨i.1 - 1, by have := i.2; omega⟩

/-- A segment of an original star edge starts either at the original endpoint
or at the preceding path-interior tag. -/
def subdivisionSegmentStart (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (e : XStarEdge P x) (k : Fin S.half) :
    SubdivisionVertex P x S :=
  if h : k.1 = 0 then
    Sum.inl (xStarEdgeStart P x e)
  else
    Sum.inr (Sum.inl (e, ⟨k.1 - 1, by have := k.2; omega⟩))

/-- A segment of an original star edge ends either at the original endpoint
or at the following path-interior tag. -/
def subdivisionSegmentEnd (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (e : XStarEdge P x) (k : Fin S.half) :
    SubdivisionVertex P x S :=
  if h : k.1 + 1 = S.half then
    Sum.inl (xStarEdgeEnd P x e)
  else
    Sum.inr (Sum.inl (e, ⟨k.1, by have := k.2; omega⟩))

/-- The tagged vertex at one grid node of a subdivided X-star face. -/
def subdivisionGridVertex (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (f : XStarFace P x)
    (i j : Fin (S.half + 1)) : SubdivisionVertex P x S :=
  if hi0 : i.1 = 0 then
    if hj0 : j.1 = 0 then Sum.inl (xStarFaceXVertex P x f)
    else if hjm : j.1 = S.half then Sum.inl (xStarFaceQVertex P x f 1)
    else Sum.inr (Sum.inl
      (xStarFaceXQEdge P x f 1, finInteriorIndex S j hj0 hjm))
  else if him : i.1 = S.half then
    if hj0 : j.1 = 0 then Sum.inl (xStarFaceQVertex P x f 0)
    else if hjm : j.1 = S.half then Sum.inl (xStarFaceZVertex P x f)
    else Sum.inr (Sum.inl
      (xStarFaceQZEdge P x f 0, finInteriorIndex S j hj0 hjm))
  else if hj0 : j.1 = 0 then
    Sum.inr (Sum.inl
      (xStarFaceXQEdge P x f 0, finInteriorIndex S i hi0 him))
  else if hjm : j.1 = S.half then
    Sum.inr (Sum.inl
      (xStarFaceQZEdge P x f 1, finInteriorIndex S i hi0 him))
  else
    Sum.inr (Sum.inr
      (f, finInteriorIndex S i hi0 him, finInteriorIndex S j hj0 hjm))

/-- Horizontal and vertical grid segments, using original-edge tags on the
outer sides and face-interior tags elsewhere. -/
def subdivisionHorizontalEdge (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (f : XStarFace P x) (i : Fin S.half)
    (j : Fin (S.half + 1)) : SubdivisionEdge P x S :=
  if hj0 : j.1 = 0 then Sum.inl (xStarFaceXQEdge P x f 0, i)
  else if hjm : j.1 = S.half then Sum.inl (xStarFaceQZEdge P x f 1, i)
  else Sum.inr (Sum.inl (f, i, finInteriorIndex S j hj0 hjm))

def subdivisionVerticalEdge (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (f : XStarFace P x) (i : Fin (S.half + 1))
    (j : Fin S.half) : SubdivisionEdge P x S :=
  if hi0 : i.1 = 0 then Sum.inl (xStarFaceXQEdge P x f 1, j)
  else if him : i.1 = S.half then Sum.inl (xStarFaceQZEdge P x f 0, j)
  else Sum.inr (Sum.inr (f, finInteriorIndex S i hi0 him, j))

/-- Constructed endpoints for every tagged subdivision edge. -/
def subdivisionEdgeStart (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) : SubdivisionEdge P x S → SubdivisionVertex P x S
  | Sum.inl ei => subdivisionSegmentStart P x S ei.1 ei.2
  | Sum.inr (Sum.inl h) =>
      subdivisionGridVertex P x S h.1 (finCastGrid h.2.1) (finInteriorGrid S h.2.2)
  | Sum.inr (Sum.inr v) =>
      subdivisionGridVertex P x S v.1 (finInteriorGrid S v.2.1) (finCastGrid v.2.2)

def subdivisionEdgeEnd (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) : SubdivisionEdge P x S → SubdivisionVertex P x S
  | Sum.inl ei => subdivisionSegmentEnd P x S ei.1 ei.2
  | Sum.inr (Sum.inl h) =>
      subdivisionGridVertex P x S h.1 (finSuccGrid h.2.1) (finInteriorGrid S h.2.2)
  | Sum.inr (Sum.inr v) =>
      subdivisionGridVertex P x S v.1 (finInteriorGrid S v.2.1) (finSuccGrid v.2.2)

@[simp]
theorem xStarEdgeStart_faceXQEdge (P : TannerSquarePresentation) (x : P.X)
    (f : XStarFace P x) (i : Two) :
    xStarEdgeStart P x (xStarFaceXQEdge P x f i) = xStarFaceXVertex P x f := by
  apply Subtype.ext
  rfl

@[simp]
theorem xStarEdgeEnd_faceXQEdge (P : TannerSquarePresentation) (x : P.X)
    (f : XStarFace P x) (i : Two) :
    xStarEdgeEnd P x (xStarFaceXQEdge P x f i) = xStarFaceQVertex P x f i := by
  apply Subtype.ext
  rfl

@[simp]
theorem xStarEdgeStart_faceQZEdge (P : TannerSquarePresentation) (x : P.X)
    (f : XStarFace P x) (i : Two) :
    xStarEdgeStart P x (xStarFaceQZEdge P x f i) = xStarFaceQVertex P x f i := by
  apply Subtype.ext
  rfl

@[simp]
theorem xStarEdgeEnd_faceQZEdge (P : TannerSquarePresentation) (x : P.X)
    (f : XStarFace P x) (i : Two) :
    xStarEdgeEnd P x (xStarFaceQZEdge P x f i) = xStarFaceZVertex P x f := by
  apply Subtype.ext
  rfl

@[simp]
private theorem finInteriorGrid_finInteriorIndex (S : OddScale)
    (i : Fin (S.half + 1)) (h0 : i.1 ≠ 0) (hlast : i.1 ≠ S.half) :
    finInteriorGrid S (finInteriorIndex S i h0 hlast) = i := by
  apply Fin.ext
  simp [finInteriorGrid, finInteriorIndex]
  omega

private def gridLast (S : OddScale) : Fin (S.half + 1) :=
  ⟨S.half, by omega⟩

/-- Partial coordinate decoder used only to prove that the explicit grid tags
retain their coordinates. -/
private def subdivisionGridCoordinate
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (f : XStarFace P x) :
    SubdivisionVertex P x S → Option (Fin (S.half + 1) × Fin (S.half + 1))
  | Sum.inl vertex =>
      if vertex = xStarFaceXVertex P x f then some (0, 0)
      else if vertex = xStarFaceQVertex P x f 1 then some (0, gridLast S)
      else if vertex = xStarFaceQVertex P x f 0 then some (gridLast S, 0)
      else if vertex = xStarFaceZVertex P x f then
        some (gridLast S, gridLast S)
      else none
  | Sum.inr (Sum.inl edgeInterior) =>
      if edgeInterior.1 = xStarFaceXQEdge P x f 1 then
        some (0, finInteriorGrid S edgeInterior.2)
      else if edgeInterior.1 = xStarFaceQZEdge P x f 0 then
        some (gridLast S, finInteriorGrid S edgeInterior.2)
      else if edgeInterior.1 = xStarFaceXQEdge P x f 0 then
        some (finInteriorGrid S edgeInterior.2, 0)
      else if edgeInterior.1 = xStarFaceQZEdge P x f 1 then
        some (finInteriorGrid S edgeInterior.2, gridLast S)
      else none
  | Sum.inr (Sum.inr faceInterior) =>
      if faceInterior.1 = f then
        some (finInteriorGrid S faceInterior.2.1,
          finInteriorGrid S faceInterior.2.2)
      else none

set_option linter.unusedSimpArgs false in
private theorem subdivisionGridCoordinate_gridVertex
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (f : XStarFace P x) (i j : Fin (S.half + 1)) :
    subdivisionGridCoordinate P x S f
        (subdivisionGridVertex P x S f i j) = some (i, j) := by
  have hm0 : S.half ≠ 0 := Nat.ne_of_gt S.half_pos
  have hxq : xStarFaceXQEdge P x f 0 ≠ xStarFaceXQEdge P x f 1 :=
    Function.Injective.ne (xStarFaceXQEdge_injective P x f) (by decide)
  have hqz : xStarFaceQZEdge P x f 0 ≠ xStarFaceQZEdge P x f 1 :=
    Function.Injective.ne (xStarFaceQZEdge_injective P x f) (by decide)
  have hqz' : xStarFaceQZEdge P x f 1 ≠ xStarFaceQZEdge P x f 0 := Ne.symm hqz
  have hq : P.faceQ f.1 0 ≠ P.faceQ f.1 1 :=
    Function.Injective.ne (P.faceQ_injective f.1) (by decide)
  by_cases hi0 : i = 0
  · subst i
    by_cases hj0 : j = 0
    · subst j
      simp [subdivisionGridVertex, subdivisionGridCoordinate, hm0,
        xStarFaceXVertex, xStarFaceQVertex, xStarFaceZVertex, hq]
    · by_cases hjm : j = gridLast S
      · subst j
        simp [gridLast, subdivisionGridVertex, subdivisionGridCoordinate,
          hm0, xStarFaceXVertex, xStarFaceQVertex, xStarFaceZVertex, hq]
      · have hj0' : j.1 ≠ 0 := by
          intro h
          apply hj0
          apply Fin.ext
          simpa using h
        have hjm' : j.1 ≠ S.half := by
          intro h
          apply hjm
          apply Fin.ext
          simpa [gridLast] using h
        simp [subdivisionGridVertex, subdivisionGridCoordinate, hm0,
          hj0', hjm', finInteriorGrid_finInteriorIndex, hxq, hqz]
  · by_cases him : i = gridLast S
    · subst i
      by_cases hj0 : j = 0
      · subst j
        simp [gridLast, subdivisionGridVertex, subdivisionGridCoordinate,
          hm0, xStarFaceXVertex, xStarFaceQVertex, xStarFaceZVertex, hq]
      · by_cases hjm : j = gridLast S
        · subst j
          simp [gridLast, subdivisionGridVertex, subdivisionGridCoordinate,
            hm0, xStarFaceXVertex, xStarFaceQVertex, xStarFaceZVertex, hq]
        · have hj0' : j.1 ≠ 0 := by
            intro h
            apply hj0
            apply Fin.ext
            simpa using h
          have hjm' : j.1 ≠ S.half := by
            intro h
            apply hjm
            apply Fin.ext
            simpa [gridLast] using h
          simp [gridLast, subdivisionGridVertex, subdivisionGridCoordinate,
            hm0, hj0', hjm', finInteriorGrid_finInteriorIndex, hxq, hqz]
    · have hi0' : i.1 ≠ 0 := by
        intro h
        apply hi0
        apply Fin.ext
        simpa using h
      have him' : i.1 ≠ S.half := by
        intro h
        apply him
        apply Fin.ext
        simpa [gridLast] using h
      by_cases hj0 : j = 0
      · subst j
        simp [subdivisionGridVertex, subdivisionGridCoordinate, hi0', him',
          hm0, finInteriorGrid_finInteriorIndex, hxq, hqz]
      · by_cases hjm : j = gridLast S
        · subst j
          simp [gridLast, subdivisionGridVertex, subdivisionGridCoordinate,
            hi0', him', hm0, finInteriorGrid_finInteriorIndex, hxq, hqz, hqz']
        · have hj0' : j.1 ≠ 0 := by
            intro h
            apply hj0
            apply Fin.ext
            simpa using h
          have hjm' : j.1 ≠ S.half := by
            intro h
            apply hjm
            apply Fin.ext
            simpa [gridLast] using h
          simp [subdivisionGridVertex, subdivisionGridCoordinate, hi0', him',
            hj0', hjm', finInteriorGrid_finInteriorIndex]

/-- Grid coordinates are retained injectively inside every fixed original
face, including all four boundary sides and corners. -/
theorem subdivisionGridVertex_fixedFace_injective
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (f : XStarFace P x) :
    Function.Injective (fun ij : Fin (S.half + 1) × Fin (S.half + 1) =>
      subdivisionGridVertex P x S f ij.1 ij.2) := by
  intro first second h
  have hdecoded := congrArg (subdivisionGridCoordinate P x S f) h
  simpa [subdivisionGridCoordinate_gridVertex] using hdecoded

/-- A grid vertex equal to a stored face-interior tag retains the old face
and both interior coordinates.  This proposition-level decoder is the public
boundary-normalization companion to `subdivisionGridVertex_fixedFace_injective`;
it returns no selected cell, edge, or path. -/
theorem subdivisionGridVertex_eq_faceInterior_coordinates
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (first second : XStarFace P x)
    (a b : Fin (S.half + 1)) (i j : Fin (S.half - 1))
    (h : subdivisionGridVertex P x S first a b =
      Sum.inr (Sum.inr (second, i, j))) :
    first = second ∧ a.1 = i.1 + 1 ∧ b.1 = j.1 + 1 := by
  have hdecoded := congrArg (subdivisionGridCoordinate P x S first) h
  rw [subdivisionGridCoordinate_gridVertex] at hdecoded
  simp only [subdivisionGridCoordinate] at hdecoded
  split at hdecoded <;> rename_i hface
  · have hfirst : first = second := hface.symm
    subst second
    have hcoordinates : (a, b) =
        (finInteriorGrid S i, finInteriorGrid S j) := by
      exact Option.some.inj hdecoded
    have ha := congrArg (fun pair => pair.1.1) hcoordinates
    have hb := congrArg (fun pair => pair.2.1) hcoordinates
    exact ⟨rfl, by simpa [finInteriorGrid] using ha,
      by simpa [finInteriorGrid] using hb⟩
  · cases hdecoded

/-- A grid vertex equal to a stored edge-interior tag identifies the exact
side of the old face and retains the interior coordinate on that side. -/
theorem subdivisionGridVertex_eq_edgeInterior_coordinates
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (a b : Fin (S.half + 1))
    (edge : XStarEdge P x) (index : Fin (S.half - 1))
    (h : subdivisionGridVertex P x S face a b =
      Sum.inr (Sum.inl (edge, index))) :
    (edge = xStarFaceXQEdge P x face 1 ∧
        a.1 = 0 ∧ b.1 = index.1 + 1) ∨
      (edge = xStarFaceQZEdge P x face 0 ∧
        a.1 = S.half ∧ b.1 = index.1 + 1) ∨
      (edge = xStarFaceXQEdge P x face 0 ∧
        a.1 = index.1 + 1 ∧ b.1 = 0) ∨
      (edge = xStarFaceQZEdge P x face 1 ∧
        a.1 = index.1 + 1 ∧ b.1 = S.half) := by
  have hdecoded := congrArg (subdivisionGridCoordinate P x S face) h
  rw [subdivisionGridCoordinate_gridVertex] at hdecoded
  simp only [subdivisionGridCoordinate] at hdecoded
  split at hdecoded <;> rename_i hxqOne
  · left
    have coordinates := Option.some.inj hdecoded
    exact ⟨hxqOne, by
      simpa using congrArg (fun pair => pair.1.1) coordinates,
      by simpa [finInteriorGrid] using
        congrArg (fun pair => pair.2.1) coordinates⟩
  · split at hdecoded <;> rename_i hqzZero
    · right; left
      have coordinates := Option.some.inj hdecoded
      exact ⟨hqzZero, by
        simpa [gridLast] using congrArg (fun pair => pair.1.1) coordinates,
        by simpa [finInteriorGrid] using
          congrArg (fun pair => pair.2.1) coordinates⟩
    · split at hdecoded <;> rename_i hxqZero
      · right; right; left
        have coordinates := Option.some.inj hdecoded
        exact ⟨hxqZero, by
          simpa [finInteriorGrid] using
            congrArg (fun pair => pair.1.1) coordinates,
          by simpa using congrArg (fun pair => pair.2.1) coordinates⟩
      · split at hdecoded <;> rename_i hqzOne
        · right; right; right
          have coordinates := Option.some.inj hdecoded
          exact ⟨hqzOne, by
            simpa [finInteriorGrid] using
              congrArg (fun pair => pair.1.1) coordinates,
            by simpa [gridLast] using
              congrArg (fun pair => pair.2.1) coordinates⟩
        · cases hdecoded

@[simp] theorem subdivisionGridVertex_edgeInterior_xq0
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (index : Fin (S.half - 1)) :
    subdivisionGridVertex P x S face
        ⟨index.1 + 1, by have := index.2; omega⟩ 0 =
      Sum.inr (Sum.inl (xStarFaceXQEdge P x face 0, index)) := by
  have hnot : index.1 + 1 ≠ S.half := by have := index.2; omega
  simp [subdivisionGridVertex, hnot, finInteriorIndex]

@[simp] theorem subdivisionGridVertex_edgeInterior_xq1
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (index : Fin (S.half - 1)) :
    subdivisionGridVertex P x S face 0
        ⟨index.1 + 1, by have := index.2; omega⟩ =
      Sum.inr (Sum.inl (xStarFaceXQEdge P x face 1, index)) := by
  have hnot : index.1 + 1 ≠ S.half := by have := index.2; omega
  simp [subdivisionGridVertex, hnot, finInteriorIndex]

@[simp] theorem subdivisionGridVertex_edgeInterior_qz0
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (index : Fin (S.half - 1)) :
    subdivisionGridVertex P x S face
        ⟨S.half, by omega⟩
        ⟨index.1 + 1, by have := index.2; omega⟩ =
      Sum.inr (Sum.inl (xStarFaceQZEdge P x face 0, index)) := by
  have hnot : index.1 + 1 ≠ S.half := by have := index.2; omega
  have hpos := S.half_pos
  simp [subdivisionGridVertex, hnot, finInteriorIndex, S.half_pos.ne']

@[simp] theorem subdivisionGridVertex_edgeInterior_qz1
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (index : Fin (S.half - 1)) :
    subdivisionGridVertex P x S face
        ⟨index.1 + 1, by have := index.2; omega⟩
        ⟨S.half, by omega⟩ =
      Sum.inr (Sum.inl (xStarFaceQZEdge P x face 1, index)) := by
  have hnot : index.1 + 1 ≠ S.half := by have := index.2; omega
  have hpos := S.half_pos
  simp [subdivisionGridVertex, hnot, finInteriorIndex, S.half_pos.ne']

private theorem subdivisionGridVertex_fixedFace_coordinates
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (f : XStarFace P x) {firstI firstJ secondI secondJ : Fin (S.half + 1)}
    (h : subdivisionGridVertex P x S f firstI firstJ =
      subdivisionGridVertex P x S f secondI secondJ) :
    firstI = secondI ∧ firstJ = secondJ := by
  have hpair : (firstI, firstJ) = (secondI, secondJ) :=
    subdivisionGridVertex_fixedFace_injective P x S f (by simpa using h)
  exact Prod.mk.inj hpair

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 800000 in
theorem subdivisionHorizontalEdge_start (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (f : XStarFace P x) (i : Fin S.half)
    (j : Fin (S.half + 1)) :
    subdivisionEdgeStart P x S (subdivisionHorizontalEdge P x S f i j) =
      subdivisionGridVertex P x S f (finCastGrid i) j := by
  have hm := S.half_pos
  have hm0 : S.half ≠ 0 := Nat.ne_of_gt hm
  have him : i.1 ≠ S.half := by omega
  let last : Fin (S.half + 1) := ⟨S.half, by omega⟩
  by_cases hjzero : j = 0
  · subst j
    by_cases hi0 : i.1 = 0
    ·
      simp [subdivisionHorizontalEdge, subdivisionEdgeStart,
        subdivisionSegmentStart, subdivisionGridVertex, finCastGrid, hm0, hi0]
    ·
      simp [subdivisionHorizontalEdge, subdivisionEdgeStart,
        subdivisionSegmentStart, subdivisionGridVertex, finCastGrid,
        finInteriorIndex, hm0, hi0, him]
  · by_cases hjlast : j = last
    · subst j
      by_cases hi0 : i.1 = 0
      ·
        simp [last, subdivisionHorizontalEdge, subdivisionEdgeStart,
          subdivisionSegmentStart, subdivisionGridVertex, finCastGrid, hm0, hi0]
      ·
        simp [last, subdivisionHorizontalEdge, subdivisionEdgeStart,
          subdivisionSegmentStart, subdivisionGridVertex, finCastGrid,
          finInteriorIndex, hm0, hi0, him]
    · have hj0 : j.1 ≠ 0 := by
        intro h
        apply hjzero
        apply Fin.ext
        simpa using h
      have hjm : j.1 ≠ S.half := by
        intro h
        apply hjlast
        apply Fin.ext
        simpa [last] using h
      by_cases hi0 : i.1 = 0
      ·
        simp [subdivisionHorizontalEdge, subdivisionEdgeStart,
          subdivisionGridVertex, finCastGrid, finInteriorGrid,
          finInteriorIndex, Fin.ext_iff, hm0, hjzero, hjlast, hj0, hjm, hi0]
        have hpred : j.1 - 1 + 1 ≠ S.half := by omega
        simp [hpred]
      ·
        simp [subdivisionHorizontalEdge, subdivisionEdgeStart,
          subdivisionGridVertex, finCastGrid, finInteriorGrid,
          finInteriorIndex, Fin.ext_iff, hm0, hjzero, hjlast, hj0, hjm, hi0, him]
        have hpred : j.1 - 1 + 1 ≠ S.half := by omega
        simp [hpred]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 800000 in
theorem subdivisionHorizontalEdge_end (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (f : XStarFace P x) (i : Fin S.half)
    (j : Fin (S.half + 1)) :
    subdivisionEdgeEnd P x S (subdivisionHorizontalEdge P x S f i j) =
      subdivisionGridVertex P x S f (finSuccGrid i) j := by
  have hm := S.half_pos
  have hm0 : S.half ≠ 0 := Nat.ne_of_gt hm
  have hisucc0 : i.1 + 1 ≠ 0 := by omega
  let last : Fin (S.half + 1) := ⟨S.half, by omega⟩
  by_cases hjzero : j = 0
  · subst j
    by_cases hilast : i.1 + 1 = S.half <;>
      simp [subdivisionHorizontalEdge, subdivisionEdgeEnd,
        subdivisionSegmentEnd, subdivisionGridVertex, finSuccGrid,
        finInteriorIndex, hm0, hisucc0, hilast]
  · by_cases hjlast : j = last
    · subst j
      by_cases hilast : i.1 + 1 = S.half <;>
        simp [last, subdivisionHorizontalEdge, subdivisionEdgeEnd,
          subdivisionSegmentEnd, subdivisionGridVertex, finSuccGrid,
          finInteriorIndex, hm0, hisucc0, hilast]
    · have hj0 : j.1 ≠ 0 := by
        intro h
        apply hjzero
        apply Fin.ext
        simpa using h
      have hjm : j.1 ≠ S.half := by
        intro h
        apply hjlast
        apply Fin.ext
        simpa [last] using h
      by_cases hilast : i.1 + 1 = S.half
      · simp [subdivisionHorizontalEdge, subdivisionEdgeEnd,
          subdivisionGridVertex, finSuccGrid, finInteriorGrid,
          finInteriorIndex, hm0, hj0, hjm, hisucc0, hilast]
        have hpred : j.1 - 1 + 1 ≠ S.half := by omega
        simp [hpred]
      · simp [subdivisionHorizontalEdge, subdivisionEdgeEnd,
          subdivisionGridVertex, finSuccGrid, finInteriorGrid,
          finInteriorIndex, hm0, hj0, hjm, hisucc0, hilast]
        have hpred : j.1 - 1 + 1 ≠ S.half := by omega
        simp [hpred]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 800000 in
theorem subdivisionVerticalEdge_start (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (f : XStarFace P x) (i : Fin (S.half + 1))
    (j : Fin S.half) :
    subdivisionEdgeStart P x S (subdivisionVerticalEdge P x S f i j) =
      subdivisionGridVertex P x S f i (finCastGrid j) := by
  have hm := S.half_pos
  have hm0 : S.half ≠ 0 := Nat.ne_of_gt hm
  have hjm : j.1 ≠ S.half := by omega
  let last : Fin (S.half + 1) := ⟨S.half, by omega⟩
  by_cases hizero : i = 0
  · subst i
    by_cases hj0 : j.1 = 0
    · simp [subdivisionVerticalEdge, subdivisionEdgeStart,
        subdivisionSegmentStart, subdivisionGridVertex, finCastGrid,
        hm0, hj0, hjm]
    · simp [subdivisionVerticalEdge, subdivisionEdgeStart,
        subdivisionSegmentStart, subdivisionGridVertex, finCastGrid,
        finInteriorIndex, hm0, hj0, hjm]
  · by_cases hilast : i = last
    · subst i
      by_cases hj0 : j.1 = 0
      · simp [last, subdivisionVerticalEdge, subdivisionEdgeStart,
          subdivisionSegmentStart, subdivisionGridVertex, finCastGrid,
          hm0, hj0, hjm]
      · simp [last, subdivisionVerticalEdge, subdivisionEdgeStart,
          subdivisionSegmentStart, subdivisionGridVertex, finCastGrid,
          finInteriorIndex, hm0, hj0, hjm]
    · have hi0 : i.1 ≠ 0 := by
        intro h
        apply hizero
        apply Fin.ext
        simpa using h
      have him : i.1 ≠ S.half := by
        intro h
        apply hilast
        apply Fin.ext
        simpa [last] using h
      by_cases hj0 : j.1 = 0
      · simp [subdivisionVerticalEdge, subdivisionEdgeStart,
          subdivisionGridVertex, finCastGrid, finInteriorGrid,
          finInteriorIndex, hi0, him, hj0, hjm]
        have hpred : i.1 - 1 + 1 ≠ S.half := by omega
        simp [hpred]
      · simp [subdivisionVerticalEdge, subdivisionEdgeStart,
          subdivisionGridVertex, finCastGrid, finInteriorGrid,
          finInteriorIndex, hi0, him, hj0, hjm]
        have hpred : i.1 - 1 + 1 ≠ S.half := by omega
        simp [hpred]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 800000 in
theorem subdivisionVerticalEdge_end (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (f : XStarFace P x) (i : Fin (S.half + 1))
    (j : Fin S.half) :
    subdivisionEdgeEnd P x S (subdivisionVerticalEdge P x S f i j) =
      subdivisionGridVertex P x S f i (finSuccGrid j) := by
  have hm := S.half_pos
  have hm0 : S.half ≠ 0 := Nat.ne_of_gt hm
  have hjsucc0 : j.1 + 1 ≠ 0 := by omega
  let last : Fin (S.half + 1) := ⟨S.half, by omega⟩
  by_cases hizero : i = 0
  · subst i
    by_cases hjlast : j.1 + 1 = S.half <;>
      simp [subdivisionVerticalEdge, subdivisionEdgeEnd,
        subdivisionSegmentEnd, subdivisionGridVertex, finSuccGrid,
        finInteriorIndex, hm0, hjsucc0, hjlast]
  · by_cases hilast : i = last
    · subst i
      by_cases hjlast : j.1 + 1 = S.half <;>
        simp [last, subdivisionVerticalEdge, subdivisionEdgeEnd,
          subdivisionSegmentEnd, subdivisionGridVertex, finSuccGrid,
          finInteriorIndex, hm0, hjsucc0, hjlast]
    · have hi0 : i.1 ≠ 0 := by
        intro h
        apply hizero
        apply Fin.ext
        simpa using h
      have him : i.1 ≠ S.half := by
        intro h
        apply hilast
        apply Fin.ext
        simpa [last] using h
      by_cases hjlast : j.1 + 1 = S.half
      · simp [subdivisionVerticalEdge, subdivisionEdgeEnd,
          subdivisionGridVertex, finSuccGrid, finInteriorGrid,
          finInteriorIndex, hi0, him, hjsucc0, hjlast]
        have hpred : i.1 - 1 + 1 ≠ S.half := by omega
        simp [hpred]
      · simp [subdivisionVerticalEdge, subdivisionEdgeEnd,
          subdivisionGridVertex, finSuccGrid, finInteriorGrid,
          finInteriorIndex, hi0, him, hjsucc0, hjlast]
        have hpred : i.1 - 1 + 1 ≠ S.half := by omega
        simp [hpred]

/-- The four local slots of a canonical small square, ordered as
horizontal-low, horizontal-high, vertical-low, vertical-high. -/
def subdivisionFaceBoundaryEdge
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : SubdivisionFace P x S) (slot : Two × Two) :
    SubdivisionEdge P x S :=
  if slot.1 = 0 then
    if slot.2 = 0 then
      subdivisionHorizontalEdge P x S face.1 face.2.1 (finCastGrid face.2.2)
    else
      subdivisionHorizontalEdge P x S face.1 face.2.1 (finSuccGrid face.2.2)
  else if slot.2 = 0 then
    subdivisionVerticalEdge P x S face.1 (finCastGrid face.2.1) face.2.2
  else
    subdivisionVerticalEdge P x S face.1 (finSuccGrid face.2.1) face.2.2

@[simp] theorem subdivisionFaceBoundaryEdge_zero_zero
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : SubdivisionFace P x S) :
    subdivisionFaceBoundaryEdge P x S face (0, 0) =
      subdivisionHorizontalEdge P x S face.1 face.2.1
        (finCastGrid face.2.2) := by
  simp [subdivisionFaceBoundaryEdge]

@[simp] theorem subdivisionFaceBoundaryEdge_zero_one
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : SubdivisionFace P x S) :
    subdivisionFaceBoundaryEdge P x S face (0, 1) =
      subdivisionHorizontalEdge P x S face.1 face.2.1
        (finSuccGrid face.2.2) := by
  simp [subdivisionFaceBoundaryEdge]

@[simp] theorem subdivisionFaceBoundaryEdge_one_zero
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : SubdivisionFace P x S) :
    subdivisionFaceBoundaryEdge P x S face (1, 0) =
      subdivisionVerticalEdge P x S face.1
        (finCastGrid face.2.1) face.2.2 := by
  simp [subdivisionFaceBoundaryEdge]

@[simp] theorem subdivisionFaceBoundaryEdge_one_one
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : SubdivisionFace P x S) :
    subdivisionFaceBoundaryEdge P x S face (1, 1) =
      subdivisionVerticalEdge P x S face.1
        (finSuccGrid face.2.1) face.2.2 := by
  simp [subdivisionFaceBoundaryEdge]

/-- The four boundary edges of a small square retain distinct local slots. -/
theorem subdivisionFaceBoundaryEdge_injective
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : SubdivisionFace P x S) :
    Function.Injective (subdivisionFaceBoundaryEdge P x S face) := by
  rintro ⟨firstKind, firstSide⟩ ⟨secondKind, secondSide⟩ h
  have hstart := congrArg (subdivisionEdgeStart P x S) h
  have hend := congrArg (subdivisionEdgeEnd P x S) h
  fin_cases firstKind <;> fin_cases firstSide <;>
    fin_cases secondKind <;> fin_cases secondSide
  all_goals
    simp [subdivisionFaceBoundaryEdge,
      subdivisionHorizontalEdge_start, subdivisionHorizontalEdge_end,
      subdivisionVerticalEdge_start, subdivisionVerticalEdge_end] at hstart hend
  all_goals try rfl
  all_goals
    first
    | have hcoordinates := subdivisionGridVertex_fixedFace_coordinates
        P x S face.1 hstart
      simp [finCastGrid, finSuccGrid, Fin.ext_iff] at hcoordinates
    | have hcoordinates := subdivisionGridVertex_fixedFace_coordinates
        P x S face.1 hend
      simp [finCastGrid, finSuccGrid, Fin.ext_iff] at hcoordinates

/-- Every tagged original star edge has different typed endpoints. -/
theorem xStarEdgeStart_ne_end (P : TannerSquarePresentation) (x : P.X)
    (edge : XStarEdge P x) :
    xStarEdgeStart P x edge ≠ xStarEdgeEnd P x edge := by
  rcases edge with ⟨edge, hstar⟩
  rcases edge with edge | edge <;>
    simp [xStarEdgeStart, xStarEdgeEnd]

private theorem subdivisionSegmentStart_ne_end
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : XStarEdge P x) (segment : Fin S.half) :
    subdivisionSegmentStart P x S edge segment ≠
      subdivisionSegmentEnd P x S edge segment := by
  by_cases hstart : segment.1 = 0
  · let zero : Fin S.half := ⟨0, S.half_pos⟩
    have hzero : segment = zero := by
      apply Fin.ext
      simpa [zero] using hstart
    subst segment
    by_cases hend : 1 = S.half
    · simpa [subdivisionSegmentStart, subdivisionSegmentEnd, hstart, hend]
        using xStarEdgeStart_ne_end P x edge
    · simp [subdivisionSegmentStart, subdivisionSegmentEnd, hstart, hend]
  · by_cases hend : segment.1 + 1 = S.half
    · simp [subdivisionSegmentStart, subdivisionSegmentEnd, hstart, hend]
    · simp [subdivisionSegmentStart, subdivisionSegmentEnd, hstart, hend,
        Fin.ext_iff]
      omega

/-- Every explicitly constructed subdivision edge has distinct endpoints. -/
theorem subdivisionEdgeStart_ne_end
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : SubdivisionEdge P x S) :
    subdivisionEdgeStart P x S edge ≠ subdivisionEdgeEnd P x S edge := by
  rcases edge with edge | edge
  · exact subdivisionSegmentStart_ne_end P x S edge.1 edge.2
  · rcases edge with horizontal | vertical
    · intro h
      change subdivisionGridVertex P x S horizontal.1
          (finCastGrid horizontal.2.1) (finInteriorGrid S horizontal.2.2) =
        subdivisionGridVertex P x S horizontal.1
          (finSuccGrid horizontal.2.1) (finInteriorGrid S horizontal.2.2) at h
      have hcoordinates := subdivisionGridVertex_fixedFace_coordinates
        P x S horizontal.1 h
      have hfirst := hcoordinates.1
      simp [finCastGrid, finSuccGrid, Fin.ext_iff] at hfirst
    · intro h
      change subdivisionGridVertex P x S vertical.1
          (finInteriorGrid S vertical.2.1) (finCastGrid vertical.2.2) =
        subdivisionGridVertex P x S vertical.1
          (finInteriorGrid S vertical.2.1) (finSuccGrid vertical.2.2) at h
      have hcoordinates := subdivisionGridVertex_fixedFace_coordinates
        P x S vertical.1 h
      have hsecond := hcoordinates.2
      simp [finCastGrid, finSuccGrid, Fin.ext_iff] at hsecond

/-- Endpoint incidence for the canonical subdivision. -/
noncomputable def subdivisionEdgeVertexMatrix (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) :
    Matrix (SubdivisionVertex P x S) (SubdivisionEdge P x S) Field := by
  classical
  exact fun v e =>
    (if v = subdivisionEdgeStart P x S e then 1 else 0) +
    (if v = subdivisionEdgeEnd P x S e then 1 else 0)

/-- The four grid edges bounding one canonical small square. -/
noncomputable def subdivisionFaceEdgeMatrix (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) :
    Matrix (SubdivisionEdge P x S) (SubdivisionFace P x S) Field := by
  classical
  exact fun e fij =>
    let f := fij.1
    let i := fij.2.1
    let j := fij.2.2
    (if e = subdivisionHorizontalEdge P x S f i (finCastGrid j) then 1 else 0) +
    (if e = subdivisionVerticalEdge P x S f (finSuccGrid i) j then 1 else 0) +
    (if e = subdivisionHorizontalEdge P x S f i (finSuccGrid j) then 1 else 0) +
    (if e = subdivisionVerticalEdge P x S f (finCastGrid i) j then 1 else 0)

/-- Matrix incidence of a canonical small square is exactly membership in its
four locally enumerated boundary slots. -/
theorem subdivisionFaceEdgeMatrix_eq_one_iff
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : SubdivisionEdge P x S) (face : SubdivisionFace P x S) :
    subdivisionFaceEdgeMatrix P x S edge face = 1 ↔
      ∃ slot : Two × Two,
        subdivisionFaceBoundaryEdge P x S face slot = edge := by
  classical
  have hinjective := subdivisionFaceBoundaryEdge_injective P x S face
  have h00_11 := Function.Injective.ne hinjective
    (show (0, 0) ≠ ((1, 1) : Two × Two) by decide)
  have h00_01 := Function.Injective.ne hinjective
    (show (0, 0) ≠ ((0, 1) : Two × Two) by decide)
  have h00_10 := Function.Injective.ne hinjective
    (show (0, 0) ≠ ((1, 0) : Two × Two) by decide)
  have h11_01 := Function.Injective.ne hinjective
    (show (1, 1) ≠ ((0, 1) : Two × Two) by decide)
  have h11_10 := Function.Injective.ne hinjective
    (show (1, 1) ≠ ((1, 0) : Two × Two) by decide)
  have h01_10 := Function.Injective.ne hinjective
    (show (0, 1) ≠ ((1, 0) : Two × Two) by decide)
  simp only [subdivisionFaceBoundaryEdge_zero_zero,
    subdivisionFaceBoundaryEdge_zero_one,
    subdivisionFaceBoundaryEdge_one_zero,
    subdivisionFaceBoundaryEdge_one_one] at h00_11 h00_01 h00_10 h11_01 h11_10 h01_10
  change
    ((((if edge = subdivisionFaceBoundaryEdge P x S face (0, 0) then 1 else 0) +
        (if edge = subdivisionFaceBoundaryEdge P x S face (1, 1) then 1 else 0)) +
        (if edge = subdivisionFaceBoundaryEdge P x S face (0, 1) then 1 else 0)) +
        (if edge = subdivisionFaceBoundaryEdge P x S face (1, 0) then 1 else 0) = 1) ↔ _
  constructor
  · intro hmatrix
    by_cases h00 : edge = subdivisionFaceBoundaryEdge P x S face (0, 0)
    · exact ⟨(0, 0), h00.symm⟩
    · by_cases h11 : edge = subdivisionFaceBoundaryEdge P x S face (1, 1)
      · exact ⟨(1, 1), h11.symm⟩
      · by_cases h01 : edge = subdivisionFaceBoundaryEdge P x S face (0, 1)
        · exact ⟨(0, 1), h01.symm⟩
        · by_cases h10 : edge = subdivisionFaceBoundaryEdge P x S face (1, 0)
          · exact ⟨(1, 0), h10.symm⟩
          · simp only [subdivisionFaceBoundaryEdge_zero_zero] at h00
            simp only [subdivisionFaceBoundaryEdge_one_one] at h11
            simp only [subdivisionFaceBoundaryEdge_zero_one] at h01
            simp only [subdivisionFaceBoundaryEdge_one_zero] at h10
            simp [h00, h11, h01, h10] at hmatrix
  · rintro ⟨slot, rfl⟩
    rcases slot with ⟨kind, side⟩
    fin_cases kind <;> fin_cases side <;>
      simp [h00_11, h00_01, h00_10,
        h11_01, h11_10, h01_10, Ne.symm h00_11, Ne.symm h00_01,
        Ne.symm h00_10, Ne.symm h11_01, Ne.symm h11_10, Ne.symm h01_10]

/-- Every canonical small square has zero endpoint boundary. -/
theorem subdivisionEdgeVertexMatrix_mul_faceEdgeMatrix
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    subdivisionEdgeVertexMatrix P x S * subdivisionFaceEdgeMatrix P x S = 0 := by
  classical
  ext v fij
  rcases fij with ⟨f, i, j⟩
  rw [Matrix.mul_apply]
  simp only [subdivisionFaceEdgeMatrix, mul_add, Finset.sum_add_distrib,
    sum_mul_eqIndicator, subdivisionEdgeVertexMatrix]
  rw [subdivisionHorizontalEdge_start, subdivisionHorizontalEdge_end,
    subdivisionVerticalEdge_start, subdivisionVerticalEdge_end]
  rw [subdivisionHorizontalEdge_start, subdivisionHorizontalEdge_end,
    subdivisionVerticalEdge_start, subdivisionVerticalEdge_end]
  ring_nf
  simp [show (2 : Field) = 0 by
    change (2 : ZMod 2) = 0
    decide]

/-- Constructed edge-to-vertex boundary of the canonical subdivision. -/
noncomputable def subdivisionBoundary1 (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) :
    Word Field (SubdivisionEdge P x S) →ₗ[Field]
      Word Field (SubdivisionVertex P x S) := by
  classical
  exact Matrix.toLin' (subdivisionEdgeVertexMatrix P x S)

/-- Constructed face-to-edge boundary of the canonical subdivision. -/
noncomputable def subdivisionBoundary2 (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) :
    Word Field (SubdivisionFace P x S) →ₗ[Field]
      Word Field (SubdivisionEdge P x S) := by
  classical
  exact Matrix.toLin' (subdivisionFaceEdgeMatrix P x S)

/-- The constructed subdivision boundary squares to zero. -/
theorem subdivisionBoundary_squared (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) :
    (subdivisionBoundary1 P x S).comp (subdivisionBoundary2 P x S) = 0 := by
  classical
  rw [subdivisionBoundary1, subdivisionBoundary2, ← Matrix.toLin'_mul]
  rw [subdivisionEdgeVertexMatrix_mul_faceEdgeMatrix]
  simp

noncomputable def subdivisionCoboundary0 (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) := wordLinearMapTranspose (subdivisionBoundary1 P x S)

noncomputable def subdivisionCoboundary1 (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) := wordLinearMapTranspose (subdivisionBoundary2 P x S)

/-- The constructed subdivision coboundary squares to zero. -/
theorem subdivisionCoboundary_squared (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) :
    (subdivisionCoboundary1 P x S).comp (subdivisionCoboundary0 P x S) = 0 := by
  rw [subdivisionCoboundary1, subdivisionCoboundary0]
  rw [← wordLinearMapTranspose_comp]
  rw [subdivisionBoundary_squared]
  exact wordLinearMapTranspose_zero

/-- The chain complex constructed from the canonical tagged subdivision. -/
noncomputable def subdivisionChainComplex (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) :
    ChainComplexData Field
      (Word Field (SubdivisionVertex P x S))
      (Word Field (SubdivisionEdge P x S))
      (Word Field (SubdivisionFace P x S)) where
  boundary1 := subdivisionBoundary1 P x S
  boundary2 := subdivisionBoundary2 P x S
  boundary_squared := subdivisionBoundary_squared P x S

/-! ## Quotient-free two-copy boundary cylinder -/

private theorem xStarBoundaryEdge_start_mem (P : TannerSquarePresentation) (x : P.X)
    (e : XStarEdge P x) (he : xStarBoundaryEdgeMember P x e.1) :
    xStarBoundaryVertexMember P x (xStarEdgeStart P x e).1 := by
  rcases e with ⟨e, hstar⟩
  rcases e with eq | eq
  · simp [xStarBoundaryEdgeMember] at he
  · simp only [xStarBoundaryEdgeMember, decide_eq_true_eq] at he
    rcases he with ⟨f, hf, huse⟩
    have huse' : eq = faceQZEdge P f 0 ∨ eq = faceQZEdge P f 1 := by
      simpa [faceUsesQZEdge] using huse
    simp only [xStarEdgeStart, xStarBoundaryVertexMember, decide_eq_true_eq]
    refine ⟨f, hf, ?_⟩
    rcases huse' with huse | huse
    · exact Or.inl (congrArg (fun a : QZEdge P => a.1.1) huse)
    · exact Or.inr (congrArg (fun a : QZEdge P => a.1.1) huse)

private theorem xStarBoundaryEdge_end_mem (P : TannerSquarePresentation) (x : P.X)
    (e : XStarEdge P x) (he : xStarBoundaryEdgeMember P x e.1) :
    xStarBoundaryVertexMember P x (xStarEdgeEnd P x e).1 := by
  rcases e with ⟨e, hstar⟩
  rcases e with eq | eq
  · simp [xStarBoundaryEdgeMember] at he
  · simp only [xStarBoundaryEdgeMember, decide_eq_true_eq] at he
    rcases he with ⟨f, hf, huse⟩
    have huse' : eq = faceQZEdge P f 0 ∨ eq = faceQZEdge P f 1 := by
      simpa [faceUsesQZEdge] using huse
    simp only [xStarEdgeEnd, xStarBoundaryVertexMember, decide_eq_true_eq]
    refine ⟨f, hf, ?_⟩
    rcases huse' with huse | huse
    · exact congrArg (fun a : QZEdge P => a.1.2) huse
    · exact congrArg (fun a : QZEdge P => a.1.2) huse

/-- Start endpoint of a boundary segment, retaining its boundary label. -/
def subdivisionBoundaryEdgeStart (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (e : SubdivisionBoundaryEdge P x S) :
    SubdivisionBoundaryVertex P x S := by
  rcases e with ⟨e, he⟩
  rcases e with ei | interior
  · rcases ei with ⟨starEdge, k⟩
    refine ⟨subdivisionEdgeStart P x S (Sum.inl (starEdge, k)), ?_⟩
    simp only [subdivisionBoundaryEdgeMember] at he
    by_cases hk : k.1 = 0
    · simpa [subdivisionEdgeStart, subdivisionSegmentStart, hk,
        subdivisionBoundaryVertexMember] using
          xStarBoundaryEdge_start_mem P x starEdge he
    · simp [subdivisionEdgeStart, subdivisionSegmentStart, hk,
        subdivisionBoundaryVertexMember, he]
  · simp [subdivisionBoundaryEdgeMember] at he

/-- End endpoint of a boundary segment, retaining its boundary label. -/
def subdivisionBoundaryEdgeEnd (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (e : SubdivisionBoundaryEdge P x S) :
    SubdivisionBoundaryVertex P x S := by
  rcases e with ⟨e, he⟩
  rcases e with ei | interior
  · rcases ei with ⟨starEdge, k⟩
    refine ⟨subdivisionEdgeEnd P x S (Sum.inl (starEdge, k)), ?_⟩
    simp only [subdivisionBoundaryEdgeMember] at he
    by_cases hk : k.1 + 1 = S.half
    · simpa [subdivisionEdgeEnd, subdivisionSegmentEnd, hk,
        subdivisionBoundaryVertexMember] using
          xStarBoundaryEdge_end_mem P x starEdge he
    · simp [subdivisionEdgeEnd, subdivisionSegmentEnd, hk,
        subdivisionBoundaryVertexMember, he]
  · simp [subdivisionBoundaryEdgeMember] at he

@[simp] theorem subdivisionBoundaryEdgeStart_value
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (e : SubdivisionBoundaryEdge P x S) :
    (subdivisionBoundaryEdgeStart P x S e).1 =
      subdivisionEdgeStart P x S e.1 := by
  rcases e with ⟨e, he⟩
  rcases e with ei | interior
  · rfl
  · simp [subdivisionBoundaryEdgeMember] at he

@[simp] theorem subdivisionBoundaryEdgeEnd_value
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (e : SubdivisionBoundaryEdge P x S) :
    (subdivisionBoundaryEdgeEnd P x S e).1 =
      subdivisionEdgeEnd P x S e.1 := by
  rcases e with ⟨e, he⟩
  rcases e with ei | interior
  · rfl
  · simp [subdivisionBoundaryEdgeMember] at he

/-- Boundary labels do not identify the two endpoints of a constructed
boundary segment. -/
theorem subdivisionBoundaryEdgeStart_ne_end
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : SubdivisionBoundaryEdge P x S) :
    subdivisionBoundaryEdgeStart P x S edge ≠
      subdivisionBoundaryEdgeEnd P x S edge := by
  intro h
  have hvalue := congrArg Subtype.val h
  rw [subdivisionBoundaryEdgeStart_value,
    subdivisionBoundaryEdgeEnd_value] at hvalue
  exact subdivisionEdgeStart_ne_end P x S edge.1 hvalue

/-- The constructed boundary is one-dimensional and has no two-cells. -/
abbrev SubdivisionBoundaryFace (_P : TannerSquarePresentation) (_x : _P.X)
    (_S : OddScale) := Fin 0

/-- Endpoint incidence intrinsic to the constructed subdivision boundary. -/
noncomputable def subdivisionBoundaryEdgeVertexMatrix
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Matrix (SubdivisionBoundaryVertex P x S)
      (SubdivisionBoundaryEdge P x S) Field := by
  classical
  exact fun v e =>
    (if v = subdivisionBoundaryEdgeStart P x S e then 1 else 0) +
    (if v = subdivisionBoundaryEdgeEnd P x S e then 1 else 0)

/-- Edge-to-vertex boundary of the constructed boundary subcomplex. -/
noncomputable def subdivisionBoundarySubcomplexBoundary1
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Word Field (SubdivisionBoundaryEdge P x S) →ₗ[Field]
      Word Field (SubdivisionBoundaryVertex P x S) := by
  classical
  exact Matrix.toLin' (subdivisionBoundaryEdgeVertexMatrix P x S)

/-- The boundary subcomplex has the definitionally zero face boundary. -/
noncomputable def subdivisionBoundarySubcomplexBoundary2
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Word Field (SubdivisionBoundaryFace P x S) →ₗ[Field]
      Word Field (SubdivisionBoundaryEdge P x S) := 0

theorem subdivisionBoundarySubcomplexBoundary_squared
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    (subdivisionBoundarySubcomplexBoundary1 P x S).comp
      (subdivisionBoundarySubcomplexBoundary2 P x S) = 0 := by
  simp [subdivisionBoundarySubcomplexBoundary2]

/-- The boundary labels and endpoint incidence form a constructed chain complex. -/
noncomputable def subdivisionBoundarySubcomplex
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    ChainComplexData Field
      (Word Field (SubdivisionBoundaryVertex P x S))
      (Word Field (SubdivisionBoundaryEdge P x S))
      (Word Field (SubdivisionBoundaryFace P x S)) where
  boundary1 := subdivisionBoundarySubcomplexBoundary1 P x S
  boundary2 := subdivisionBoundarySubcomplexBoundary2 P x S
  boundary_squared := subdivisionBoundarySubcomplexBoundary_squared P x S

/-- Degree zero of the quotient-free two-copy boundary cylinder. -/
abbrev DoubleCylinderVertex (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) := Two × SubdivisionVertex P x S

/-- Two copies of all edges plus one vertical edge for each boundary vertex. -/
abbrev DoubleCylinderEdge (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) :=
  (Two × SubdivisionEdge P x S) ⊕ SubdivisionBoundaryVertex P x S

/-- Two copies of all faces plus one rectangle for each boundary edge. -/
abbrev DoubleCylinderFace (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) :=
  (Two × SubdivisionFace P x S) ⊕ SubdivisionBoundaryEdge P x S

@[simp] theorem baseX0DoubleCylinderVertex_card :
    Fintype.card (DoubleCylinderVertex baseTannerSquarePresentation
      (0 : BaseX) scaleFive) = 30 := by native_decide

@[simp] theorem baseX0DoubleCylinderEdge_card :
    Fintype.card (DoubleCylinderEdge baseTannerSquarePresentation
      (0 : BaseX) scaleFive) = 53 := by native_decide

@[simp] theorem baseX0DoubleCylinderFace_card :
    Fintype.card (DoubleCylinderFace baseTannerSquarePresentation
      (0 : BaseX) scaleFive) = 24 := by native_decide

/-- Edge-to-vertex incidence for the quotient-free cylinder.  End edges keep
their copy tag; a vertical edge joins the two copies of its boundary vertex. -/
noncomputable def doubleCylinderEdgeVertexMatrix
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Matrix (DoubleCylinderVertex P x S) (DoubleCylinderEdge P x S) Field := by
  classical
  exact fun tv e => match e with
    | Sum.inl se =>
        if tv.1 = se.1 then subdivisionEdgeVertexMatrix P x S tv.2 se.2 else 0
    | Sum.inr bv => if tv.2 = bv.1 then 1 else 0

/-- Face-to-edge incidence for the quotient-free cylinder.  A rectangle has
its two end edges and the two vertical edges at the boundary-edge endpoints. -/
noncomputable def doubleCylinderFaceEdgeMatrix
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Matrix (DoubleCylinderEdge P x S) (DoubleCylinderFace P x S) Field := by
  classical
  exact fun e face => match face with
    | Sum.inl sf => match e with
        | Sum.inl se =>
            if se.1 = sf.1 then subdivisionFaceEdgeMatrix P x S se.2 sf.2 else 0
        | Sum.inr _ => 0
    | Sum.inr be => match e with
        | Sum.inl se => if se.2 = be.1 then 1 else 0
        | Sum.inr bv =>
            (if bv = subdivisionBoundaryEdgeStart P x S be then 1 else 0) +
            (if bv = subdivisionBoundaryEdgeEnd P x S be then 1 else 0)

@[simp] theorem doubleCylinder_end_edge_boundary
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (t : Two) (v : SubdivisionVertex P x S) (e : SubdivisionEdge P x S) :
    doubleCylinderEdgeVertexMatrix P x S (t, v) (Sum.inl (t, e)) =
      subdivisionEdgeVertexMatrix P x S v e := by
  simp [doubleCylinderEdgeVertexMatrix]

@[simp] theorem doubleCylinder_vertical_edge_boundary
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (t : Two)
    (bv : SubdivisionBoundaryVertex P x S) :
    doubleCylinderEdgeVertexMatrix P x S (t, bv.1) (Sum.inr bv) = 1 := by
  classical
  simp [doubleCylinderEdgeVertexMatrix]

@[simp] theorem doubleCylinder_end_face_boundary
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (t : Two) (e : SubdivisionEdge P x S) (f : SubdivisionFace P x S) :
    doubleCylinderFaceEdgeMatrix P x S (Sum.inl (t, e)) (Sum.inl (t, f)) =
      subdivisionFaceEdgeMatrix P x S e f := by
  simp [doubleCylinderFaceEdgeMatrix]

@[simp] theorem doubleCylinder_rectangle_end_boundary
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (t : Two) (be : SubdivisionBoundaryEdge P x S) :
    doubleCylinderFaceEdgeMatrix P x S (Sum.inl (t, be.1)) (Sum.inr be) = 1 := by
  simp [doubleCylinderFaceEdgeMatrix]

theorem doubleCylinder_rectangle_vertical_start
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (be : SubdivisionBoundaryEdge P x S)
    (hne : subdivisionBoundaryEdgeStart P x S be ≠
      subdivisionBoundaryEdgeEnd P x S be) :
    doubleCylinderFaceEdgeMatrix P x S
      (Sum.inr (subdivisionBoundaryEdgeStart P x S be)) (Sum.inr be) = 1 := by
  classical
  simp [doubleCylinderFaceEdgeMatrix, hne]

theorem doubleCylinder_rectangle_vertical_end
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (be : SubdivisionBoundaryEdge P x S)
    (hne : subdivisionBoundaryEdgeStart P x S be ≠
      subdivisionBoundaryEdgeEnd P x S be) :
    doubleCylinderFaceEdgeMatrix P x S
      (Sum.inr (subdivisionBoundaryEdgeEnd P x S be)) (Sum.inr be) = 1 := by
  classical
  simp [doubleCylinderFaceEdgeMatrix, Ne.symm hne]

/-- The four corners of a boundary rectangle, indexed exactly by
`(copy, endpoint)`. -/
def doubleCylinderRectangleCorner
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (rectangle : SubdivisionBoundaryEdge P x S) (corner : Two × Two) :
    DoubleCylinderVertex P x S :=
  (corner.1,
    if corner.2 = 0 then (subdivisionBoundaryEdgeStart P x S rectangle).1
    else (subdivisionBoundaryEdgeEnd P x S rectangle).1)

@[simp] theorem doubleCylinderRectangleCorner_copy_zero
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (rectangle : SubdivisionBoundaryEdge P x S) (copy : Two) :
    doubleCylinderRectangleCorner P x S rectangle (copy, 0) =
      (copy, (subdivisionBoundaryEdgeStart P x S rectangle).1) := by
  simp [doubleCylinderRectangleCorner]

@[simp] theorem doubleCylinderRectangleCorner_copy_one
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (rectangle : SubdivisionBoundaryEdge P x S) (copy : Two) :
    doubleCylinderRectangleCorner P x S rectangle (copy, 1) =
      (copy, (subdivisionBoundaryEdgeEnd P x S rectangle).1) := by
  simp [doubleCylinderRectangleCorner]

/-- The four tagged rectangle corners are pairwise distinct. -/
theorem doubleCylinderRectangleCorner_injective
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (rectangle : SubdivisionBoundaryEdge P x S) :
    Function.Injective (doubleCylinderRectangleCorner P x S rectangle) := by
  have hedge := subdivisionEdgeStart_ne_end P x S rectangle.1
  rintro ⟨firstCopy, firstEndpoint⟩ ⟨secondCopy, secondEndpoint⟩ h
  fin_cases firstCopy <;> fin_cases firstEndpoint <;>
    fin_cases secondCopy <;> fin_cases secondEndpoint <;>
    simp [doubleCylinderRectangleCorner, hedge, Ne.symm hedge] at h ⊢

/-- The rectangle boundary slots are, in order, the two end-copy edges and
the vertical edges at the start and end vertices. -/
def doubleCylinderRectangleBoundaryEdge
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (rectangle : SubdivisionBoundaryEdge P x S) (slot : Two × Two) :
    DoubleCylinderEdge P x S :=
  if slot.1 = 0 then
    Sum.inl (slot.2, rectangle.1)
  else if slot.2 = 0 then
    Sum.inr (subdivisionBoundaryEdgeStart P x S rectangle)
  else
    Sum.inr (subdivisionBoundaryEdgeEnd P x S rectangle)

@[simp] theorem doubleCylinderRectangleBoundaryEdge_zero
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (rectangle : SubdivisionBoundaryEdge P x S) (copy : Two) :
    doubleCylinderRectangleBoundaryEdge P x S rectangle (0, copy) =
      Sum.inl (copy, rectangle.1) := by
  simp [doubleCylinderRectangleBoundaryEdge]

@[simp] theorem doubleCylinderRectangleBoundaryEdge_one_zero
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (rectangle : SubdivisionBoundaryEdge P x S) :
    doubleCylinderRectangleBoundaryEdge P x S rectangle (1, 0) =
      Sum.inr (subdivisionBoundaryEdgeStart P x S rectangle) := by
  simp [doubleCylinderRectangleBoundaryEdge]

@[simp] theorem doubleCylinderRectangleBoundaryEdge_one_one
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (rectangle : SubdivisionBoundaryEdge P x S) :
    doubleCylinderRectangleBoundaryEdge P x S rectangle (1, 1) =
      Sum.inr (subdivisionBoundaryEdgeEnd P x S rectangle) := by
  simp [doubleCylinderRectangleBoundaryEdge]

/-- The two end-copy and two vertical rectangle edges retain distinct slots. -/
theorem doubleCylinderRectangleBoundaryEdge_injective
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (rectangle : SubdivisionBoundaryEdge P x S) :
    Function.Injective
      (doubleCylinderRectangleBoundaryEdge P x S rectangle) := by
  have hne := subdivisionBoundaryEdgeStart_ne_end P x S rectangle
  rintro ⟨firstKind, firstTag⟩ ⟨secondKind, secondTag⟩ h
  fin_cases firstKind <;> fin_cases firstTag <;>
    fin_cases secondKind <;> fin_cases secondTag <;>
    simp [doubleCylinderRectangleBoundaryEdge, hne, Ne.symm hne] at h ⊢

/-- Rectangle matrix incidence is exactly membership in the four explicit
boundary slots. -/
theorem doubleCylinderFaceEdgeMatrix_rectangle_eq_one_iff
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : DoubleCylinderEdge P x S)
    (rectangle : SubdivisionBoundaryEdge P x S) :
    doubleCylinderFaceEdgeMatrix P x S edge (Sum.inr rectangle) = 1 ↔
      ∃ slot : Two × Two,
        doubleCylinderRectangleBoundaryEdge P x S rectangle slot = edge := by
  classical
  have hne := subdivisionBoundaryEdgeStart_ne_end P x S rectangle
  rcases edge with endEdge | vertical
  · rcases endEdge with ⟨copy, edge⟩
    fin_cases copy
    · constructor
      · intro hmatrix
        have hedge : edge = rectangle.1 := by
          by_contra hne'
          simp [doubleCylinderFaceEdgeMatrix, hne'] at hmatrix
        exact ⟨(0, 0), by
          simp [doubleCylinderRectangleBoundaryEdge, hedge]⟩
      · rintro ⟨⟨kind, tag⟩, hslot⟩
        fin_cases kind <;> fin_cases tag
        all_goals simp [doubleCylinderRectangleBoundaryEdge] at hslot
        simp [doubleCylinderFaceEdgeMatrix, hslot]
    · constructor
      · intro hmatrix
        have hedge : edge = rectangle.1 := by
          by_contra hne'
          simp [doubleCylinderFaceEdgeMatrix, hne'] at hmatrix
        exact ⟨(0, 1), by
          simp [doubleCylinderRectangleBoundaryEdge, hedge]⟩
      · rintro ⟨⟨kind, tag⟩, hslot⟩
        fin_cases kind <;> fin_cases tag
        all_goals simp [doubleCylinderRectangleBoundaryEdge] at hslot
        simp [doubleCylinderFaceEdgeMatrix, hslot]
  · constructor
    · intro hmatrix
      by_cases hstart : vertical = subdivisionBoundaryEdgeStart P x S rectangle
      · exact ⟨(1, 0), by
          simp [doubleCylinderRectangleBoundaryEdge, hstart]⟩
      · by_cases hend : vertical = subdivisionBoundaryEdgeEnd P x S rectangle
        · exact ⟨(1, 1), by
            simp [doubleCylinderRectangleBoundaryEdge, hend]⟩
        · simp [doubleCylinderFaceEdgeMatrix, hstart, hend] at hmatrix
    · rintro ⟨⟨kind, tag⟩, hslot⟩
      fin_cases kind <;> fin_cases tag
      all_goals simp [doubleCylinderRectangleBoundaryEdge] at hslot
      · subst vertical
        simp [doubleCylinderFaceEdgeMatrix, hne]
      · subst vertical
        simp [doubleCylinderFaceEdgeMatrix, Ne.symm hne]

/-- Assumption-free start-vertical incidence, derived from constructed boundary
nondegeneracy. -/
theorem doubleCylinder_rectangle_vertical_start_from_construction
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (rectangle : SubdivisionBoundaryEdge P x S) :
    doubleCylinderFaceEdgeMatrix P x S
      (Sum.inr (subdivisionBoundaryEdgeStart P x S rectangle))
      (Sum.inr rectangle) = 1 :=
  doubleCylinder_rectangle_vertical_start P x S rectangle
    (subdivisionBoundaryEdgeStart_ne_end P x S rectangle)

/-- Assumption-free end-vertical incidence, derived from constructed boundary
nondegeneracy. -/
theorem doubleCylinder_rectangle_vertical_end_from_construction
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (rectangle : SubdivisionBoundaryEdge P x S) :
    doubleCylinderFaceEdgeMatrix P x S
      (Sum.inr (subdivisionBoundaryEdgeEnd P x S rectangle))
      (Sum.inr rectangle) = 1 :=
  doubleCylinder_rectangle_vertical_end P x S rectangle
    (subdivisionBoundaryEdgeStart_ne_end P x S rectangle)

private theorem subtype_two_endpoint_sum
    {A B : Type} [Fintype A] [DecidableEq A] [DecidableEq B]
    (v : B) (value : A → B) (a b : A) :
    (∑ c : A, if v = value c then
      ((if c = a then (1 : Field) else 0) +
        (if c = b then 1 else 0)) else 0) =
      (if v = value a then 1 else 0) + (if v = value b then 1 else 0) := by
  calc
    _ = ∑ c : A, (if v = value c then (1 : Field) else 0) *
        ((if c = a then 1 else 0) + (if c = b then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro c _hc
      by_cases h : v = value c <;> simp [h]
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, sum_mul_eqIndicator]

set_option maxHeartbeats 800000 in
/-- The quotient-free cylinder boundary squares to zero. -/
theorem doubleCylinderEdgeVertexMatrix_mul_faceEdgeMatrix
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    doubleCylinderEdgeVertexMatrix P x S *
      doubleCylinderFaceEdgeMatrix P x S = 0 := by
  classical
  ext tv face
  rcases tv with ⟨t, v⟩
  rcases face with sf | be
  · rcases sf with ⟨s, f⟩
    rw [Matrix.mul_apply]
    simp only [Fintype.sum_sum_type]
    rw [Fintype.sum_prod_type]
    fin_cases t <;> fin_cases s <;>
      simp [doubleCylinderEdgeVertexMatrix, doubleCylinderFaceEdgeMatrix,
        ← Matrix.mul_apply, subdivisionEdgeVertexMatrix_mul_faceEdgeMatrix]
  · rw [Matrix.mul_apply]
    simp only [Fintype.sum_sum_type]
    rw [Fintype.sum_prod_type]
    simp [doubleCylinderEdgeVertexMatrix, doubleCylinderFaceEdgeMatrix,
      subdivisionEdgeVertexMatrix]
    change
      (((if v = subdivisionEdgeStart P x S be.1 then (1 : Field) else 0) +
          (if v = subdivisionEdgeEnd P x S be.1 then 1 else 0)) +
        ∑ bv : SubdivisionBoundaryVertex P x S,
          if v = bv.1 then
            ((if bv = subdivisionBoundaryEdgeStart P x S be then 1 else 0) +
              (if bv = subdivisionBoundaryEdgeEnd P x S be then 1 else 0))
          else 0) = 0
    letI : DecidableEq (SubdivisionBoundaryVertex P x S) := Subtype.instDecidableEq
    have hsum :
        (∑ bv : SubdivisionBoundaryVertex P x S,
          if v = bv.1 then
            ((if bv = subdivisionBoundaryEdgeStart P x S be then (1 : Field) else 0) +
              (if bv = subdivisionBoundaryEdgeEnd P x S be then 1 else 0))
          else 0) =
        (if v = (subdivisionBoundaryEdgeStart P x S be).1 then 1 else 0) +
          (if v = (subdivisionBoundaryEdgeEnd P x S be).1 then 1 else 0) := by
      exact subtype_two_endpoint_sum v
        (fun bv : SubdivisionBoundaryVertex P x S => bv.1)
        (subdivisionBoundaryEdgeStart P x S be)
        (subdivisionBoundaryEdgeEnd P x S be)
    rw [hsum]
    simpa using field_add_self
      ((if v = (subdivisionBoundaryEdgeStart P x S be).1 then (1 : Field) else 0) +
        (if v = (subdivisionBoundaryEdgeEnd P x S be).1 then 1 else 0))

/-- Constructed edge-to-vertex boundary of the quotient-free cylinder. -/
noncomputable def doubleCylinderBoundary1
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Word Field (DoubleCylinderEdge P x S) →ₗ[Field]
      Word Field (DoubleCylinderVertex P x S) := by
  classical
  exact Matrix.toLin' (doubleCylinderEdgeVertexMatrix P x S)

/-- Constructed face-to-edge boundary of the quotient-free cylinder. -/
noncomputable def doubleCylinderBoundary2
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Word Field (DoubleCylinderFace P x S) →ₗ[Field]
      Word Field (DoubleCylinderEdge P x S) := by
  classical
  exact Matrix.toLin' (doubleCylinderFaceEdgeMatrix P x S)

/-- The constructed quotient-free cylinder boundary squares to zero. -/
theorem doubleCylinderBoundary_squared
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    (doubleCylinderBoundary1 P x S).comp (doubleCylinderBoundary2 P x S) = 0 := by
  classical
  rw [doubleCylinderBoundary1, doubleCylinderBoundary2, ← Matrix.toLin'_mul]
  rw [doubleCylinderEdgeVertexMatrix_mul_faceEdgeMatrix]
  simp

/-- The quotient-free two-copy cylinder as constructed chain data. -/
noncomputable def doubleCylinderChainComplex
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    ChainComplexData Field
      (Word Field (DoubleCylinderVertex P x S))
      (Word Field (DoubleCylinderEdge P x S))
      (Word Field (DoubleCylinderFace P x S)) where
  boundary1 := doubleCylinderBoundary1 P x S
  boundary2 := doubleCylinderBoundary2 P x S
  boundary_squared := doubleCylinderBoundary_squared P x S

noncomputable def doubleCylinderCoboundary0
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :=
  wordLinearMapTranspose (doubleCylinderBoundary1 P x S)

noncomputable def doubleCylinderCoboundary1
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :=
  wordLinearMapTranspose (doubleCylinderBoundary2 P x S)

/-- The constructed cylinder coboundary also squares to zero. -/
theorem doubleCylinderCoboundary_squared
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    (doubleCylinderCoboundary1 P x S).comp
      (doubleCylinderCoboundary0 P x S) = 0 := by
  rw [doubleCylinderCoboundary1, doubleCylinderCoboundary0]
  rw [← wordLinearMapTranspose_comp]
  rw [doubleCylinderBoundary_squared]
  exact wordLinearMapTranspose_zero

/-! ## Constructed restriction, inclusion, bases, and duality adapters -/

/-- Restrict subdivision vertex coordinates to its constructed boundary. -/
noncomputable def subdivisionBoundaryVertexRestriction
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Word Field (SubdivisionVertex P x S) →ₗ[Field]
      Word Field (SubdivisionBoundaryVertex P x S) := by
  classical
  exact coordinateRestriction (subdivisionBoundaryVertexMember P x S)

/-- Extend constructed boundary-vertex coordinates by zero. -/
noncomputable def subdivisionBoundaryVertexExtensionZero
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Word Field (SubdivisionBoundaryVertex P x S) →ₗ[Field]
      Word Field (SubdivisionVertex P x S) := by
  classical
  exact coordinateExtensionZero (subdivisionBoundaryVertexMember P x S)

/-- Restrict subdivision edge coordinates to its constructed boundary. -/
noncomputable def subdivisionBoundaryEdgeRestriction
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Word Field (SubdivisionEdge P x S) →ₗ[Field]
      Word Field (SubdivisionBoundaryEdge P x S) := by
  classical
  exact coordinateRestriction (subdivisionBoundaryEdgeMember P x S)

/-- Extend constructed boundary-edge coordinates by zero. -/
noncomputable def subdivisionBoundaryEdgeExtensionZero
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Word Field (SubdivisionBoundaryEdge P x S) →ₗ[Field]
      Word Field (SubdivisionEdge P x S) := by
  classical
  exact coordinateExtensionZero (subdivisionBoundaryEdgeMember P x S)

/-- Coordinate inclusion of either cylinder end. -/
def doubleCylinderEndInclusion
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) (t : Two) :
    Word Field (SubdivisionVertex P x S) →ₗ[Field]
      Word Field (DoubleCylinderVertex P x S) where
  toFun := fun w tv => if tv.1 = t then w tv.2 else 0
  map_add' := by
    intros
    ext tv
    by_cases h : tv.1 = t <;> simp [h]
  map_smul' := by
    intros
    ext tv
    by_cases h : tv.1 = t <;> simp [h]

/-- Coordinate restriction to either cylinder end. -/
def doubleCylinderEndRestriction
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) (t : Two) :
    Word Field (DoubleCylinderVertex P x S) →ₗ[Field]
      Word Field (SubdivisionVertex P x S) where
  toFun := fun w v => w (t, v)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp] theorem doubleCylinderEndInclusion_apply
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (t : Two) (w : Word Field (SubdivisionVertex P x S))
    (v : SubdivisionVertex P x S) :
    doubleCylinderEndInclusion P x S t w (t, v) = w v := by
  simp [doubleCylinderEndInclusion]

noncomputable def subdivisionVertexBasis
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Basis (SubdivisionVertex P x S) Field
      (Word Field (SubdivisionVertex P x S)) :=
  Pi.basisFun Field (SubdivisionVertex P x S)

noncomputable def subdivisionEdgeBasis
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Basis (SubdivisionEdge P x S) Field
      (Word Field (SubdivisionEdge P x S)) :=
  Pi.basisFun Field (SubdivisionEdge P x S)

noncomputable def subdivisionFaceBasis
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Basis (SubdivisionFace P x S) Field
      (Word Field (SubdivisionFace P x S)) :=
  Pi.basisFun Field (SubdivisionFace P x S)

/-- Duality adapter for the already constructed subdivision complex. -/
noncomputable def subdivisionDualChainComplex
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :=
  dualChainComplex (subdivisionChainComplex P x S)

/-- Duality adapter for the already constructed cylinder complex. -/
noncomputable def doubleCylinderDualChainComplex
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :=
  dualChainComplex (doubleCylinderChainComplex P x S)

/-! ## Z-star consumer route via the theorem-derived transpose -/

/-- Z-star subdivision cells reuse the X-star construction on the transpose. -/
abbrev ZSubdivisionVertex (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) :=
  SubdivisionVertex (transposePresentation P) z S

abbrev ZSubdivisionEdge (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) :=
  SubdivisionEdge (transposePresentation P) z S

abbrev ZSubdivisionFace (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) :=
  SubdivisionFace (transposePresentation P) z S

abbrev ZSubdivisionBoundaryVertex (P : TannerSquarePresentation)
    (z : P.Z) (S : OddScale) :=
  SubdivisionBoundaryVertex (transposePresentation P) z S

abbrev ZSubdivisionBoundaryEdge (P : TannerSquarePresentation)
    (z : P.Z) (S : OddScale) :=
  SubdivisionBoundaryEdge (transposePresentation P) z S

abbrev ZDoubleCylinderVertex (P : TannerSquarePresentation) (z : P.Z)
    (S : OddScale) := DoubleCylinderVertex (transposePresentation P) z S

abbrev ZDoubleCylinderEdge (P : TannerSquarePresentation) (z : P.Z)
    (S : OddScale) := DoubleCylinderEdge (transposePresentation P) z S

abbrev ZDoubleCylinderFace (P : TannerSquarePresentation) (z : P.Z)
    (S : OddScale) := DoubleCylinderFace (transposePresentation P) z S

/-- Constructed Z-star subdivision complex, with no duplicated chain input. -/
noncomputable def zSubdivisionChainComplex
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) :=
  subdivisionChainComplex (transposePresentation P) z S

theorem zSubdivisionBoundary_squared
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) :
    (subdivisionBoundary1 (transposePresentation P) z S).comp
      (subdivisionBoundary2 (transposePresentation P) z S) = 0 :=
  subdivisionBoundary_squared (transposePresentation P) z S

theorem zSubdivisionCoboundary_squared
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) :
    (subdivisionCoboundary1 (transposePresentation P) z S).comp
      (subdivisionCoboundary0 (transposePresentation P) z S) = 0 :=
  subdivisionCoboundary_squared (transposePresentation P) z S

/-- Constructed Z-star boundary subcomplex via the same transpose route. -/
noncomputable def zSubdivisionBoundarySubcomplex
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) :=
  subdivisionBoundarySubcomplex (transposePresentation P) z S

/-- Constructed Z-star quotient-free cylinder via the same transpose route. -/
noncomputable def zDoubleCylinderChainComplex
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) :=
  doubleCylinderChainComplex (transposePresentation P) z S

theorem zDoubleCylinderBoundary_squared
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) :
    (doubleCylinderBoundary1 (transposePresentation P) z S).comp
      (doubleCylinderBoundary2 (transposePresentation P) z S) = 0 :=
  doubleCylinderBoundary_squared (transposePresentation P) z S

theorem zDoubleCylinderCoboundary_squared
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) :
    (doubleCylinderCoboundary1 (transposePresentation P) z S).comp
      (doubleCylinderCoboundary0 (transposePresentation P) z S) = 0 :=
  doubleCylinderCoboundary_squared (transposePresentation P) z S

noncomputable def zSubdivisionBoundaryVertexRestriction
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) :=
  subdivisionBoundaryVertexRestriction (transposePresentation P) z S

noncomputable def zSubdivisionBoundaryVertexExtensionZero
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) :=
  subdivisionBoundaryVertexExtensionZero (transposePresentation P) z S

noncomputable def zSubdivisionBoundaryEdgeRestriction
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) :=
  subdivisionBoundaryEdgeRestriction (transposePresentation P) z S

noncomputable def zSubdivisionBoundaryEdgeExtensionZero
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) :=
  subdivisionBoundaryEdgeExtensionZero (transposePresentation P) z S

noncomputable def zDoubleCylinderEndInclusion
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) (t : Two) :=
  doubleCylinderEndInclusion (transposePresentation P) z S t

noncomputable def zDoubleCylinderEndRestriction
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) (t : Two) :=
  doubleCylinderEndRestriction (transposePresentation P) z S t

/-- Duality adapters consume only the constructed Z-star complexes. -/
noncomputable def zSubdivisionDualChainComplex
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) :=
  subdivisionDualChainComplex (transposePresentation P) z S

noncomputable def zDoubleCylinderDualChainComplex
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) :=
  doubleCylinderDualChainComplex (transposePresentation P) z S
end BDL26FiniteTannerSquare
end Coding
end QEC
