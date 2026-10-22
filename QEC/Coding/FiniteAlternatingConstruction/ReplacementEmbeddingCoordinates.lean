import QEC.Coding.FiniteAlternatingConstruction.ReplacementEmbedding
import QEC.Coding.FiniteAlternatingConstruction.QuantitativeBounds
import QEC.Coding.FiniteAlternatingConstruction.BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Coordinates and packing ingredients for the concrete replacement

Perfect pairing identifies actual face owners and exact flat-patch slots, including
all collapsed candidates. Constructed RX/RZ maps realize the materialized vertices,
edges, face centers, and transpose geometry. Local containment and triangle-frame
packing lemmas give the canonical one-step RX/RZ density handoff, with odd rounding,
unit Tanner edges, degree bounds, affine gluing and intrinsic local restrictions.
The incoming density counts the actual auxiliary triangle labels.
-/

namespace QEC.Coding.BDL26ReplacementEmbedding

open scoped InnerProductSpace

open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds

/-- An actual boundary edge determines its face and its corner by perfect pairing. -/
theorem faceCornerBoundaryEdge_injective (P : TannerSquarePresentation) :
    Function.Injective (faceCornerBoundaryEdge P) := by
  intro a b h
  apply (faceCornerWedge_bijective P).1
  apply Subtype.ext
  have hx : P.faceX a.1 = P.faceX b.1 := congrArg Sigma.fst h
  have he : faceQZEdge P a.1 a.2 = faceQZEdge P b.1 b.2 := by
    have hv := congrArg
      (fun e : Σ x : P.X, XStarBoundaryEdge P x => e.2.1) h
    exact Sum.inr.inj hv
  exact Prod.ext hx (congrArg Subtype.val he)

/-- Canonical boundary ownership equivalence, derived rather than assumed. -/
noncomputable def faceCornerBoundaryEquiv (P : TannerSquarePresentation) :
    P.Face × BDL26FiniteTannerSquare.Two ≃ Σ x : P.X, XStarBoundaryEdge P x :=
  Equiv.ofBijective (faceCornerBoundaryEdge P)
    ⟨faceCornerBoundaryEdge_injective P, faceCornerBoundaryEdge_surjective P⟩

/-- Boundary incidences have exactly two labels per old face. -/
theorem xStarBoundaryEdge_total (P : TannerSquarePresentation) :
    (∑ x : P.X, Fintype.card (XStarBoundaryEdge P x)) = 2 * Fintype.card P.Face := by
  have h := Fintype.card_congr (faceCornerBoundaryEquiv P)
  simpa only [Fintype.card_sigma, Fintype.card_prod, BDL26FiniteTannerSquare.Two,
    Fintype.card_fin, Nat.mul_comm] using h.symm

/-- The local doubled-face count is exact, including boundary rectangles. -/
theorem doubleCylinderFace_total (P : TannerSquarePresentation) (S : OddScale) :
    (∑ x : P.X, Fintype.card (DoubleCylinderFace P x S)) =
      (2 * S.half ^ 2 + 2 * S.half) * Fintype.card P.Face := by
  have hf : (∑ x : P.X, Fintype.card (XStarFace P x)) = Fintype.card P.Face := by
    simpa only [Fintype.card_sigma] using Fintype.card_congr (xStarFaceEquiv P)
  simp only [doubleCylinderFace_card, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, hf, xStarBoundaryEdge_total]
  ring

/-- Actual RX and the explicit flat patch have the same exact face multiplicity.
This cardinal equality does not identify their geometric realizations. -/
theorem rxFace_card_eq_flatCell (P : TannerSquarePresentation) (S : OddScale) :
    Fintype.card (RXFace P S) = Fintype.card P.Face * Fintype.card (FlatCell S) := by
  have hlocal : Fintype.card (RXLocalFace P S) =
      (∑ x : P.X, Fintype.card (DoubleCylinderFace P x S)) * 4 := by
    simp only [RXLocalFace, Fintype.card_sigma, Fintype.card_prod,
      BDL26FiniteTannerSquare.Two, Fintype.card_fin, ← Finset.sum_mul]
  have hold : Fintype.card (RXOldZFace P) = 2 * Fintype.card P.Face := by
    simp only [RXOldZFace, Fintype.card_prod, BDL26FiniteTannerSquare.Two,
      Fintype.card_fin, Nat.mul_comm]
  change Fintype.card (RXLocalFace P S ⊕ (RXXQGlueFace P S ⊕ RXOldZFace P)) = _
  rw [Fintype.card_sum, Fintype.card_sum, hlocal, doubleCylinderFace_total,
    rxGlueFace_card, hold, flatCell_card, ← S.two_half_add_one]
  ring

/-! ## Canonical face ownership and local patch slots -/

/-- The four corners of a local grid square retain both endpoint bits. -/
abbrev PatchCorner := BDL26FiniteTannerSquare.Two × BDL26FiniteTannerSquare.Two

abbrev PlaneSlot (S : OddScale) :=
  (BDL26FiniteTannerSquare.Two × (Fin S.half × Fin S.half)) × PatchCorner

abbrev BoundarySlot (S : OddScale) :=
  BDL26FiniteTannerSquare.Two × (Fin S.half × PatchCorner)

abbrev QEdgeSlot (S : OddScale) :=
  (BDL26FiniteTannerSquare.Two × Fin S.half) ⊕ Fin 1

abbrev GlueSlot (S : OddScale) :=
  BDL26FiniteTannerSquare.Two × (QEdgeSlot S × BDL26FiniteTannerSquare.Two)

/-- Slot families follow the actual RX constructors, with owner information removed. -/
abbrev PatchSlot (S : OddScale) :=
  (PlaneSlot S ⊕ BoundarySlot S) ⊕ (GlueSlot S ⊕ BDL26FiniteTannerSquare.Two)

private def planarLocalCoordinates (P : TannerSquarePresentation) (S : OddScale) :
    (Σ x : P.X,
      (BDL26FiniteTannerSquare.Two × SubdivisionFace P x S) × PatchCorner) ≃
      P.Face × PlaneSlot S where
  toFun c := (c.2.1.2.1.1, ((c.2.1.1, c.2.1.2.2), c.2.2))
  invFun c := ⟨P.faceX c.1,
    (c.2.1.1, (oldFaceInXStar P c.1, c.2.1.2)), c.2.2⟩
  left_inv := by
    rintro ⟨x, ⟨copy, ⟨⟨f, hf⟩, i, j⟩⟩, corner⟩
    have hx : P.faceX f = x := by simpa [xStarFaceMember] using hf
    subst x
    rfl
  right_inv := fun _ => rfl

/-- A subdivided boundary segment has a unique original face, side and interval. -/
noncomputable def boundarySegmentCoordinates (P : TannerSquarePresentation) (S : OddScale) :
    (Σ x : P.X, SubdivisionBoundaryEdge P x S) ≃
      (P.Face × BDL26FiniteTannerSquare.Two) × Fin S.half :=
  (Equiv.sigmaCongrRight fun x => subdivisionBoundaryEdgeEquiv P x S).trans
    ((Equiv.sigmaProdDistrib (fun x => XStarBoundaryEdge P x) (Fin S.half)).symm.trans
      (Equiv.prodCongr (faceCornerBoundaryEquiv P).symm (Equiv.refl _)))

private def boundarySlotReassociate (P : TannerSquarePresentation) (S : OddScale) :
    ((P.Face × BDL26FiniteTannerSquare.Two) × Fin S.half) × PatchCorner ≃
      P.Face × BoundarySlot S where
  toFun c := (c.1.1.1, c.1.1.2, c.1.2, c.2)
  invFun c := (((c.1, c.2.1), c.2.2.1), c.2.2.2)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

private noncomputable def rectangleLocalCoordinates
    (P : TannerSquarePresentation) (S : OddScale) :
    (Σ x : P.X, SubdivisionBoundaryEdge P x S × PatchCorner) ≃
      P.Face × BoundarySlot S :=
  (Equiv.sigmaProdDistrib (fun x => SubdivisionBoundaryEdge P x S) PatchCorner).symm.trans
    ((Equiv.prodCongr (boundarySegmentCoordinates P S) (Equiv.refl _)).trans
      (boundarySlotReassociate P S))

/-- Actual local faces retain their original owner and planar/rectangle slot. -/
noncomputable def rxLocalFaceCoordinates (P : TannerSquarePresentation) (S : OddScale) :
    RXLocalFace P S ≃ P.Face × (PlaneSlot S ⊕ BoundarySlot S) :=
  (Equiv.sigmaCongrRight fun x =>
    Equiv.sumProdDistrib (BDL26FiniteTannerSquare.Two × SubdivisionFace P x S)
      (SubdivisionBoundaryEdge P x S) PatchCorner).trans
    ((Equiv.sigmaSumDistrib
      (fun x => (BDL26FiniteTannerSquare.Two × SubdivisionFace P x S) × PatchCorner)
      (fun x => SubdivisionBoundaryEdge P x S × PatchCorner)).trans
      ((Equiv.sumCongr (planarLocalCoordinates P S) (rectangleLocalCoordinates P S)).trans
        (Equiv.prodSumDistrib P.Face (PlaneSlot S) (BoundarySlot S)).symm))

/-- Actual Q-cylinder edges separate the old incident Z from the copy/interval tag. -/
def qDoubleCylinderEdgeCoordinates (P : TannerSquarePresentation) (q : P.Q) (S : OddScale) :
    QDoubleCylinderEdge P q S ≃ QStarEdge P q × QEdgeSlot S where
  toFun
    | .inl (copy, edge, i) => (edge, .inl (copy, i))
    | .inr edge => (edge, .inr 0)
  invFun
    | (edge, .inl (copy, i)) => .inl (copy, edge, i)
    | (edge, .inr _) => .inr edge
  left_inv := by rintro (⟨copy, edge, i⟩ | edge) <;> rfl
  right_inv := by
    rintro ⟨edge, c | c⟩
    · rfl
    · have hc : c = 0 := Subsingleton.elim _ _
      subst c
      rfl

private def qGlueFiberReassociate (P : TannerSquarePresentation) (a : XQEdge P) (S : OddScale) :
    QDoubleCylinderEdge P a.1.2 S × BDL26FiniteTannerSquare.Two ≃
      QStarEdge P a.1.2 × (QEdgeSlot S × BDL26FiniteTannerSquare.Two) :=
  (Equiv.prodCongr (qDoubleCylinderEdgeCoordinates P a.1.2 S) (Equiv.refl _)).trans
    (Equiv.prodAssoc _ _ _)

/-- Perfect pairing gives the old face and ordered side of each actual glue face. -/
noncomputable def rxGlueFaceCoordinates (P : TannerSquarePresentation) (S : OddScale) :
    RXXQGlueFace P S ≃ P.Face × GlueSlot S :=
  (Equiv.sigmaCongrRight fun a => qGlueFiberReassociate P a S).trans
    ((Equiv.sigmaProdDistrib (fun a : XQEdge P => QStarEdge P a.1.2)
      (QEdgeSlot S × BDL26FiniteTannerSquare.Two)).symm.trans
      ((Equiv.prodCongr
        ((xqQStarEdgeEquiv P).trans
          (Equiv.ofBijective (faceCornerWedge P) (faceCornerWedge_bijective P)).symm)
        (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _)))

/-- Canonical ownership and slots for every actual RX face, not a cardinality cast. -/
noncomputable def rxFaceSlotEquiv (P : TannerSquarePresentation) (S : OddScale) :
    RXFace P S ≃ P.Face × PatchSlot S :=
  (Equiv.sumCongr (rxLocalFaceCoordinates P S)
    ((Equiv.sumCongr (rxGlueFaceCoordinates P S) (Equiv.refl _)).trans
      (Equiv.prodSumDistrib P.Face (GlueSlot S) BDL26FiniteTannerSquare.Two).symm)).trans
    (Equiv.prodSumDistrib P.Face (PlaneSlot S ⊕ BoundarySlot S)
      (GlueSlot S ⊕ BDL26FiniteTannerSquare.Two)).symm

/-! ## Fine-grid coordinates, retaining the last odd strip -/

/-- Interior fine coordinates retain their coarse interval and endpoint bit. -/
abbrev FineCoordinate (S : OddScale) :=
  (Fin S.half × BDL26FiniteTannerSquare.Two) ⊕ Fin 1

private def castFinEquiv {n m : Nat} (h : n = m) : Fin n ≃ Fin m where
  toFun := Fin.cast h
  invFun := Fin.cast h.symm
  left_inv := by intro i; apply Fin.ext; rfl
  right_inv := by intro i; apply Fin.ext; rfl

/-- The actual index is `2*i+bit`, with the odd final coordinate retained separately. -/
def fineCoordinateEquiv (S : OddScale) : FineCoordinate S ≃ Fin S.ell :=
  (Equiv.sumCongr (finProdFinEquiv :
    Fin S.half × BDL26FiniteTannerSquare.Two ≃ Fin (S.half * 2))
    (Equiv.refl (Fin 1))).trans
    (finSumFinEquiv.trans (castFinEquiv (by have := S.two_half_add_one; omega)))

@[simp] theorem fineCoordinate_interior_val (S : OddScale)
    (i : Fin S.half) (bit : BDL26FiniteTannerSquare.Two) :
    (fineCoordinateEquiv S (.inl (i, bit))).val = 2 * i.val + bit.val := by
  simp [fineCoordinateEquiv, castFinEquiv, finProdFinEquiv, finSumFinEquiv, Nat.add_comm]

@[simp] theorem fineCoordinate_last (S : OddScale) (i : Fin 1) :
    fineCoordinateEquiv S (.inr i) = lastStrip S := by
  apply Fin.ext
  have hi : i.val = 0 := by omega
  have hodd := S.two_half_add_one
  simp [fineCoordinateEquiv, castFinEquiv, finSumFinEquiv, lastStrip, hi]
  omega

abbrev RawPositiveCell (S : OddScale) :=
  BDL26FiniteTannerSquare.Two × (FineCoordinate S × FineCoordinate S)

abbrev RawSeamCell (S : OddScale) := BDL26FiniteTannerSquare.Two × FineCoordinate S

abbrev RawFlatCell (S : OddScale) :=
  RawPositiveCell S ⊕ (RawSeamCell S ⊕ RawSeamCell S)

/-- Interpret materialized face slots as planar grid squares or collapsed seams. -/
def patchSlotToRawFlat (S : OddScale) : PatchSlot S → RawFlatCell S
  | .inl (.inl ((copy, i, j), a, b)) => .inl (copy, .inl (i, a), .inl (j, b))
  | .inl (.inr (side, i, copy, endpoint)) =>
      if side = 0 then .inr (.inr (copy, .inl (i, endpoint)))
      else .inr (.inl (copy, .inl (i, endpoint)))
  | .inr (.inl (side, .inl (copy, i), endpoint)) =>
      if side = 0 then .inl (copy, .inr 0, .inl (i, endpoint))
      else .inl (copy, .inl (i, endpoint), .inr 0)
  | .inr (.inl (side, .inr _, copy)) =>
      if side = 0 then .inr (.inl (copy, .inr 0))
      else .inr (.inr (copy, .inr 0))
  | .inr (.inr copy) => .inl (copy, .inr 0, .inr 0)

/-- Explicit inverse retains original side/copy/endpoint tags, including seams. -/
def rawFlatToPatchSlot (S : OddScale) : RawFlatCell S → PatchSlot S
  | .inl (copy, .inl (i, a), .inl (j, b)) => .inl (.inl ((copy, i, j), a, b))
  | .inl (copy, .inr _, .inl (i, endpoint)) =>
      .inr (.inl (0, .inl (copy, i), endpoint))
  | .inl (copy, .inl (i, endpoint), .inr _) =>
      .inr (.inl (1, .inl (copy, i), endpoint))
  | .inl (copy, .inr _, .inr _) => .inr (.inr copy)
  | .inr (.inl (copy, .inl (i, endpoint))) => .inl (.inr (1, i, copy, endpoint))
  | .inr (.inr (copy, .inl (i, endpoint))) => .inl (.inr (0, i, copy, endpoint))
  | .inr (.inl (copy, .inr _)) => .inr (.inl (0, .inr 0, copy))
  | .inr (.inr (copy, .inr _)) => .inr (.inl (1, .inr 0, copy))

/-- Constructor-level round trips, with no enumeration or choice of a matching. -/
def patchSlotRawFlatEquiv (S : OddScale) : PatchSlot S ≃ RawFlatCell S where
  toFun := patchSlotToRawFlat S
  invFun := rawFlatToPatchSlot S
  left_inv := by
    intro c
    rcases c with c | c
    · rcases c with c | ⟨side, i, copy, endpoint⟩
      · rcases c with ⟨⟨copy, i, j⟩, a, b⟩
        rfl
      · fin_cases side <;> simp [patchSlotToRawFlat, rawFlatToPatchSlot]
    · rcases c with ⟨side, edge, endpoint⟩ | copy
      · rcases edge with ⟨copy, i⟩ | last
        · fin_cases side <;> simp [patchSlotToRawFlat, rawFlatToPatchSlot]
        · have hlast : last = 0 := Subsingleton.elim _ _
          subst last
          fin_cases side <;> simp [patchSlotToRawFlat, rawFlatToPatchSlot]
      · rfl
  right_inv := by
    intro c
    rcases c with ⟨copy, i, j⟩ | c
    · rcases i with ⟨i, a⟩ | i <;> rcases j with ⟨j, b⟩ | j
      · rfl
      · have h : j = 0 := Subsingleton.elim _ _
        subst j
        rfl
      · have h : i = 0 := Subsingleton.elim _ _
        subst i
        rfl
      · have hi : i = 0 := Subsingleton.elim _ _
        have hj : j = 0 := Subsingleton.elim _ _
        subst i
        subst j
        rfl
    · rcases c with ⟨copy, c⟩ | ⟨copy, c⟩ <;> rcases c with ⟨i, endpoint⟩ | last
      · rfl
      · have h : last = 0 := Subsingleton.elim _ _
        subst last
        rfl
      · rfl
      · have h : last = 0 := Subsingleton.elim _ _
        subst last
        rfl

/-- The fine index map on every cell family preserves the cell labels. -/
def rawFlatCellEquiv (S : OddScale) : RawFlatCell S ≃ FlatCell S :=
  Equiv.sumCongr
    (Equiv.prodCongr (Equiv.refl _)
      (Equiv.prodCongr (fineCoordinateEquiv S) (fineCoordinateEquiv S)))
    (Equiv.sumCongr
      (Equiv.prodCongr (Equiv.refl _) (fineCoordinateEquiv S))
      (Equiv.prodCongr (Equiv.refl _) (fineCoordinateEquiv S)))

/-- Actual RX face labels have canonical old-face/grid coordinates. -/
noncomputable def rxFaceFlatEquiv (P : TannerSquarePresentation) (S : OddScale) :
    RXFace P S ≃ P.Face × FlatCell S :=
  (rxFaceSlotEquiv P S).trans
    (Equiv.prodCongr (Equiv.refl _)
      ((patchSlotRawFlatEquiv S).trans (rawFlatCellEquiv S)))

/-- Actual RZ face coordinates use the proved materialized transpose adapter. -/
noncomputable def rzFaceFlatEquiv (P : TannerSquarePresentation) (S : OddScale) :
    BDL26RZLocalReplacement.RZFace P S ≃ P.Face × FlatCell S :=
  (rzFaceEquiv P S).trans (rxFaceFlatEquiv (transposePresentation P) S)


/-! ## Constructed point maps before the metric estimates

These maps use the original vertex positions as data. They neither request a
replacement embedding nor assume its density. Their remaining compatibility
with every materialized face is a separate proof obligation of #854.
-/

noncomputable section PointMaps

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Two affine triangles meet on the original X-Z diagonal. -/
def foldedSquare (x q₀ q₁ z : E) (u v : ℝ) : E :=
  if v ≤ u then (1 - u) • x + (u - v) • q₀ + v • z
  else (1 - v) • x + (v - u) • q₁ + u • z

@[simp] theorem foldedSquare_diagonal (x q₀ q₁ z : E) (u : ℝ) :
    foldedSquare x q₀ q₁ z u u = (1 - u) • x + u • z := by
  simp [foldedSquare]

/-- Both branches agree on their common diagonal; no planarity is imposed. -/
theorem foldedSquare_branches_agree (x q₀ q₁ z : E) (u : ℝ) :
    (1 - u) • x + (u - u) • q₀ + u • z =
      (1 - u) • x + (u - u) • q₁ + u • z := by
  simp

@[simp] theorem foldedSquare_bottom (x q₀ q₁ z : E) (u : ℝ) (hu : 0 ≤ u) :
    foldedSquare x q₀ q₁ z u 0 = (1 - u) • x + u • q₀ := by
  simp [foldedSquare, hu]

@[simp] theorem foldedSquare_left (x q₀ q₁ z : E) (v : ℝ) (hv : 0 ≤ v) :
    foldedSquare x q₀ q₁ z 0 v = (1 - v) • x + v • q₁ := by
  by_cases h : v ≤ 0
  · have : v = 0 := le_antisymm h hv
    subst v
    simp [foldedSquare]
  · simp [foldedSquare, h]

@[simp] theorem foldedSquare_right (x q₀ q₁ z : E) (v : ℝ) (hv : v ≤ 1) :
    foldedSquare x q₀ q₁ z 1 v = (1 - v) • q₀ + v • z := by
  simp [foldedSquare, hv]

@[simp] theorem foldedSquare_top (x q₀ q₁ z : E) (u : ℝ) (hu : u ≤ 1) :
    foldedSquare x q₀ q₁ z u 1 = (1 - u) • q₁ + u • z := by
  by_cases h : 1 ≤ u
  · have : u = 1 := le_antisymm hu h
    subst u
    simp [foldedSquare]
  · simp [foldedSquare, h]

/-- An old face uses only the four supplied original vertex positions. -/
def facePoint (P : TannerSquarePresentation) (J : Vertex P → E)
    (f : P.Face) (u v : ℝ) : E :=
  foldedSquare (J (.x (P.faceX f))) (J (.q (P.faceQ f 0)))
    (J (.q (P.faceQ f 1))) (J (.z (P.faceZ f))) u v

/-- The actual fine grid retains the exact odd denominator, not its real target. -/
def faceGrid (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) : GridMap S E :=
  fun i j => facePoint P J f ((i.val : ℝ) / S.ell) ((j.val : ℝ) / S.ell)

/-- The contracted old corner occurs at `(ell-1)/ell`, strictly before the boundary. -/
def contractionRatio (S : OddScale) : ℝ := (2 * (S.half : ℝ)) / S.ell

/-- X-star old vertices are contracted about their actual owner X. -/
def starVertexPoint (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (v : XStarVertex P x) : E :=
  (1 - contractionRatio S) • J (.x x) + contractionRatio S • J v.1

/-- All shared subdivision-edge points are defined from the actual edge endpoints. -/
def subdivisionVertexPoint (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) : SubdivisionVertex P x S → E
  | .inl v => starVertexPoint P S J x v
  | .inr (.inl (edge, i)) =>
      let t : ℝ := ((i.val : ℝ) + 1) / S.half
      (1 - t) • starVertexPoint P S J x (xStarEdgeStart P x edge) +
        t • starVertexPoint P S J x (xStarEdgeEnd P x edge)
  | .inr (.inr (f, i, j)) =>
      facePoint P J f.1 (2 * ((i.val : ℝ) + 1) / S.ell)
        (2 * ((j.val : ℝ) + 1) / S.ell)

/-- Both actual X-cylinder copies have the same point positions. -/
def rxZeroPoint (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (v : RX0 P S) : E :=
  subdivisionVertexPoint P S J v.1 v.2.2

/-- The Q-local path starts at its actual Q and stops one fine step before Z. -/
def qSubdivisionVertexPoint (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (q : P.Q) : QSubdivisionVertex P q S → E
  | .inl (.inl _) => J (.q q)
  | .inl (.inr edge) =>
      (1 - contractionRatio S) • J (.q q) + contractionRatio S • J (.z edge.1)
  | .inr (edge, i) =>
      let t : ℝ := 2 * ((i.val : ℝ) + 1) / S.ell
      (1 - t) • J (.q q) + t • J (.z edge.1)

/-- New Q coordinates use actual X-cylinder edge midpoints or Q-local vertices. -/
def rxOnePoint (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) : RX1 P S → E
  | .inl ⟨x, edge⟩ =>
      (1 / 2 : ℝ) • (subdivisionVertexPoint P S J x
        (tannerDoubleCylinderEdgeStart P x S edge).2 +
        subdivisionVertexPoint P S J x (tannerDoubleCylinderEdgeEnd P x S edge).2)
  | .inr ⟨q, _, vertex⟩ => qSubdivisionVertexPoint P S J q vertex

/-- New local face centers follow the X-Z diagonal, also when the old square is folded.
Boundary rectangles and Q-cylinder edge coordinates are genuine endpoint midpoints. -/
def rxTwoPoint (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) : RX2 P S → E
  | .inl (.inl ⟨_, .inl (_, f, i, j)⟩) =>
      facePoint P J f.1 ((2 * (i.val : ℝ) + 1) / S.ell)
        ((2 * (j.val : ℝ) + 1) / S.ell)
  | .inl (.inl ⟨x, .inr edge⟩) =>
      (1 / 2 : ℝ) • (subdivisionVertexPoint P S J x
        (subdivisionEdgeStart P x S edge.1) +
        subdivisionVertexPoint P S J x (subdivisionEdgeEnd P x S edge.1))
  | .inl (.inr ⟨q, edge⟩) =>
      (1 / 2 : ℝ) • (qSubdivisionVertexPoint P S J q
        (qDoubleCylinderEdgeStart P q S edge).2 +
        qSubdivisionVertexPoint P S J q (qDoubleCylinderEdgeEnd P q S edge).2)
  | .inr (z, _) => J (.z z)

/-- Copy tags are retained in the domain even though their positions coincide. -/
theorem rxZeroPoint_copy_eq (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (v : SubdivisionVertex P x S)
    (a b : BDL26FiniteTannerSquare.Two) :
    rxZeroPoint P S J ⟨x, a, v⟩ = rxZeroPoint P S J ⟨x, b, v⟩ := rfl

/-- The contracted coordinate is nonnegative and lies strictly before the last grid edge. -/
theorem contractionRatio_bounds (S : OddScale) :
    0 ≤ contractionRatio S ∧ contractionRatio S < 1 := by
  have he : (0 : ℝ) < S.ell := by exact_mod_cast (show 0 < S.ell by have := S.three_le; omega)
  have ho : 2 * (S.half : ℝ) + 1 = S.ell := by exact_mod_cast S.two_half_add_one
  constructor
  · exact div_nonneg (by positivity) he.le
  · apply (div_lt_one he).2
    linarith

@[simp] theorem lower_last_normalized (S : OddScale) :
    ((lower S (lastStrip S)).val : ℝ) / S.ell = contractionRatio S := by
  have h : S.ell - 1 = 2 * S.half := by have := S.two_half_add_one; omega
  simp [lower, lastStrip, contractionRatio, h]

@[simp] theorem upper_last_normalized (S : OddScale) :
    ((upper S (lastStrip S)).val : ℝ) / S.ell = 1 := by
  have hp : 0 < S.ell := by have := S.three_le; omega
  have h : S.ell - 1 + 1 = S.ell := by omega
  simp [upper, lastStrip, h, Nat.ne_of_gt hp]

/-- The actual old-Z face X corner is the contracted diagonal point. -/
theorem oldZFaceX_point (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (copy : BDL26FiniteTannerSquare.Two) :
    rxZeroPoint P S J (oldZFaceX P S (f, copy)) =
      facePoint P J f (contractionRatio S) (contractionRatio S) := by
  simp [rxZeroPoint, oldZFaceX, subdivisionVertexPoint, starVertexPoint,
    xStarFaceZVertex, oldFaceInXStar, facePoint]

/-- The actual old-Z face Q0 lies on the right boundary, including its one-step offset. -/
theorem oldZFaceQ0_point (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (copy : BDL26FiniteTannerSquare.Two) :
    rxOnePoint P S J (oldZFaceQ P S 0 (f, copy)) =
      facePoint P J f 1 (contractionRatio S) := by
  simp [rxOnePoint, oldZFaceQ, qSubdivisionVertexPoint, facePoint,
    foldedSquare_right, (contractionRatio_bounds S).2.le]

/-- The other actual old-Z Q corner lies on the top boundary. -/
theorem oldZFaceQ1_point (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (copy : BDL26FiniteTannerSquare.Two) :
    rxOnePoint P S J (oldZFaceQ P S 1 (f, copy)) =
      facePoint P J f (contractionRatio S) 1 := by
  simp [rxOnePoint, oldZFaceQ, qSubdivisionVertexPoint, facePoint,
    foldedSquare_top, (contractionRatio_bounds S).2.le]

/-- The final corner is the original Z position, with copy multiplicity retained. -/
theorem oldZFaceZ_point (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (copy : BDL26FiniteTannerSquare.Two) :
    rxTwoPoint P S J (oldZFaceZ P S (f, copy)) = facePoint P J f 1 1 := by
  simp [rxTwoPoint, oldZFaceZ, facePoint]

/-- Face realization is constructed from the four actual global replacement point maps. -/
noncomputable def rxFaceImage (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : RXFace P S) : Set E :=
  convexHull ℝ {rxZeroPoint P S J (rxFaceX P S f),
    rxOnePoint P S J (rxFaceQ P S f 0), rxTwoPoint P S J (rxFaceZ P S f)} ∪
  convexHull ℝ {rxZeroPoint P S J (rxFaceX P S f),
    rxTwoPoint P S J (rxFaceZ P S f), rxOnePoint P S J (rxFaceQ P S f 1)}

/-- The actual old-Z family realizes the terminal fine-grid square, not just its count. -/
theorem oldZFace_image (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (copy : BDL26FiniteTannerSquare.Two) :
    rxFaceImage P S J (.inr (.inr (f, copy))) =
      positiveImage S (faceGrid P S J f) (copy, lastStrip S, lastStrip S) := by
  simp only [rxFaceImage, rxFaceX, rxFaceQ, rxFaceZ,
    oldZFaceX_point, oldZFaceQ0_point, oldZFaceQ1_point, oldZFaceZ_point,
    positiveImage, faceGrid, lower_last_normalized, upper_last_normalized]

/-- Shared old-Z X corners agree geometrically because their actual global vertex agrees. -/
theorem oldZFaceX_shared_point (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f g : P.Face) (copy : BDL26FiniteTannerSquare.Two)
    (hx : P.faceX f = P.faceX g) (hz : P.faceZ f = P.faceZ g) :
    rxZeroPoint P S J (oldZFaceX P S (f, copy)) =
      rxZeroPoint P S J (oldZFaceX P S (g, copy)) :=
  congrArg (rxZeroPoint P S J) (oldZFaceX_congr P S f g copy hx hz)

/-- Shared old-Z Q corners agree using actual Q/Z tags, independently of the face label. -/
theorem oldZFaceQ_shared_point (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f g : P.Face)
    (a b copy : BDL26FiniteTannerSquare.Two)
    (hq : P.faceQ f a = P.faceQ g b) (hz : P.faceZ f = P.faceZ g) :
    rxOnePoint P S J (oldZFaceQ P S a (f, copy)) =
      rxOnePoint P S J (oldZFaceQ P S b (g, copy)) :=
  congrArg (rxOnePoint P S J) (oldZFaceQ_congr P S f g a b copy hq hz)

/-- A terminal Q rung's actual X endpoint is the contracted old Z in its X star. -/
theorem rungFaceX_point (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (a : XQEdge P) (edge : QStarEdge P a.1.2)
    (copy : BDL26FiniteTannerSquare.Two) :
    rxZeroPoint P S J (glueFaceX P S ⟨a, .inr edge, copy⟩) =
      (1 - contractionRatio S) • J (.x a.1.1) + contractionRatio S • J (.z edge.1) := by
  fin_cases copy <;> rfl

/-- The actual X-local vertical edge collapses to its common endpoint. -/
theorem rungFaceQ0_point (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (a : XQEdge P) (edge : QStarEdge P a.1.2)
    (copy : BDL26FiniteTannerSquare.Two) :
    rxOnePoint P S J (glueFaceQ0 P S ⟨a, .inr edge, copy⟩) =
      (1 - contractionRatio S) • J (.x a.1.1) + contractionRatio S • J (.z edge.1) := by
  change (1 / 2 : ℝ) •
    (((1 - contractionRatio S) • J (.x a.1.1) + contractionRatio S • J (.z edge.1)) +
      ((1 - contractionRatio S) • J (.x a.1.1) + contractionRatio S • J (.z edge.1))) = _
  module

/-- The other endpoint of a terminal-rung glue face belongs to the Q-local path. -/
theorem rungFaceQ1_point (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (a : XQEdge P) (edge : QStarEdge P a.1.2)
    (copy : BDL26FiniteTannerSquare.Two) :
    rxOnePoint P S J (glueFaceQ1 P S ⟨a, .inr edge, copy⟩) =
      (1 - contractionRatio S) • J (.q a.1.2) + contractionRatio S • J (.z edge.1) := by
  fin_cases copy <;> rfl

/-- The Q-local vertical edge also collapses, while its domain label remains distinct. -/
theorem rungFaceZ_point (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (a : XQEdge P) (edge : QStarEdge P a.1.2)
    (copy : BDL26FiniteTannerSquare.Two) :
    rxTwoPoint P S J (glueFaceZ P S ⟨a, .inr edge, copy⟩) =
      (1 - contractionRatio S) • J (.q a.1.2) + contractionRatio S • J (.z edge.1) := by
  change (1 / 2 : ℝ) •
    (((1 - contractionRatio S) • J (.q a.1.2) + contractionRatio S • J (.z edge.1)) +
      ((1 - contractionRatio S) • J (.q a.1.2) + contractionRatio S • J (.z edge.1))) = _
  module

/-- The actual zero-area terminal glue face has a constructed segment image. -/
theorem rungFace_image (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (a : XQEdge P) (edge : QStarEdge P a.1.2)
    (copy : BDL26FiniteTannerSquare.Two) :
    rxFaceImage P S J (.inr (.inl ⟨a, .inr edge, copy⟩)) =
      segment ℝ
        ((1 - contractionRatio S) • J (.x a.1.1) + contractionRatio S • J (.z edge.1))
        ((1 - contractionRatio S) • J (.q a.1.2) + contractionRatio S • J (.z edge.1)) := by
  simp [rxFaceImage, rxFaceX, rxFaceQ, rxFaceZ, twoSelect,
    rungFaceX_point, rungFaceQ0_point, rungFaceQ1_point, rungFaceZ_point,
    Set.insert_comm, convexHull_pair, segment_symm]

/-- A boundary rectangle's materialized corner determines its endpoint position. -/
def rectangleEndpointPoint (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (edge : SubdivisionBoundaryEdge P x S)
    (endpoint : BDL26FiniteTannerSquare.Two) : E :=
  if endpoint = 0 then subdivisionVertexPoint P S J x (subdivisionEdgeStart P x S edge.1)
  else subdivisionVertexPoint P S J x (subdivisionEdgeEnd P x S edge.1)

/-- The center is constructed from the actual boundary edge, independently of its owner face. -/
def rectangleMidpoint (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (edge : SubdivisionBoundaryEdge P x S) : E :=
  (1 / 2 : ℝ) • (subdivisionVertexPoint P S J x (subdivisionEdgeStart P x S edge.1) +
    subdivisionVertexPoint P S J x (subdivisionEdgeEnd P x S edge.1))

theorem rectangleFaceX_point (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (edge : SubdivisionBoundaryEdge P x S)
    (copy endpoint : BDL26FiniteTannerSquare.Two) :
    rxZeroPoint P S J (localFaceX P S ⟨x, .inr edge, copy, endpoint⟩) =
      rectangleEndpointPoint P S J x edge endpoint := by
  fin_cases endpoint <;>
    simp [rxZeroPoint, localFaceX, doubleCylinderRectangleCorner, rectangleEndpointPoint]

theorem rectangleFaceQ0_point (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (edge : SubdivisionBoundaryEdge P x S)
    (copy endpoint : BDL26FiniteTannerSquare.Two) :
    rxOnePoint P S J (localFaceQ0 P S ⟨x, .inr edge, copy, endpoint⟩) =
      rectangleMidpoint P S J x edge := rfl

theorem rectangleFaceQ1_point (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (edge : SubdivisionBoundaryEdge P x S)
    (copy endpoint : BDL26FiniteTannerSquare.Two) :
    rxOnePoint P S J (localFaceQ1 P S ⟨x, .inr edge, copy, endpoint⟩) =
      rectangleEndpointPoint P S J x edge endpoint := by
  by_cases h : endpoint = 0 <;>
    simp [rxOnePoint, localFaceQ1, localFaceQ1Edge, localFaceQ1EdgeAt,
      doubleCylinderRectangleBoundaryEdge, tannerDoubleCylinderEdgeStart,
      tannerDoubleCylinderEdgeEnd, rectangleEndpointPoint, h] <;> module

theorem rectangleFaceZ_point (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (edge : SubdivisionBoundaryEdge P x S)
    (copy endpoint : BDL26FiniteTannerSquare.Two) :
    rxTwoPoint P S J (localFaceZ P S ⟨x, .inr edge, copy, endpoint⟩) =
      rectangleMidpoint P S J x edge := rfl

/-- Every actual boundary-rectangle quadrant has a segment image, even for degenerate input. -/
theorem rectangleFace_image (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (edge : SubdivisionBoundaryEdge P x S)
    (copy endpoint : BDL26FiniteTannerSquare.Two) :
    rxFaceImage P S J (.inl ⟨x, .inr edge, copy, endpoint⟩) =
      segment ℝ (rectangleEndpointPoint P S J x edge endpoint)
        (rectangleMidpoint P S J x edge) := by
  simp [rxFaceImage, rxFaceX, rxFaceQ, rxFaceZ, twoSelect,
    rectangleFaceX_point, rectangleFaceQ0_point, rectangleFaceQ1_point,
    rectangleFaceZ_point, Set.insert_comm, convexHull_pair, segment_symm]

/-- A terminal rung is specified by an actual old face, side and copy. -/
def terminalRungFace (P : TannerSquarePresentation) (S : OddScale)
    (f : P.Face) (side copy : BDL26FiniteTannerSquare.Two) : RXFace P S :=
  .inr (.inl ⟨faceXQEdge P f side,
    .inr ⟨P.faceZ f, P.data.faceQ_qz f side⟩, copy⟩)

/-- Side zero's terminal rung is horizontal; its boundary-rectangle family is vertical. -/
theorem terminalRung_zero_image (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (copy : BDL26FiniteTannerSquare.Two) :
    rxFaceImage P S J (terminalRungFace P S f 0 copy) =
      horizontalImage S (faceGrid P S J f) (copy, lastStrip S) := by
  rw [terminalRungFace, rungFace_image]
  simp [horizontalImage, faceGrid, facePoint, faceXQEdge,
    lower_last_normalized, upper_last_normalized, (contractionRatio_bounds S).2.le]

/-- Side one's terminal rung is the vertical terminal seam. -/
theorem terminalRung_one_image (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (copy : BDL26FiniteTannerSquare.Two) :
    rxFaceImage P S J (terminalRungFace P S f 1 copy) =
      verticalImage S (faceGrid P S J f) (copy, lastStrip S) := by
  rw [terminalRungFace, rungFace_image]
  simp [verticalImage, faceGrid, facePoint, faceXQEdge,
    lower_last_normalized, upper_last_normalized, (contractionRatio_bounds S).2.le]

/-- Both actual terminal-rung families are contained in the actual old-Z face image. -/
theorem terminalRung_image_subset_oldZ (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (side copy : BDL26FiniteTannerSquare.Two) :
    rxFaceImage P S J (terminalRungFace P S f side copy) ⊆
      rxFaceImage P S J (.inr (.inr (f, copy))) := by
  rw [oldZFace_image]
  fin_cases side
  · change rxFaceImage P S J (terminalRungFace P S f 0 copy) ⊆ _
    rw [terminalRung_zero_image]
    simpa [cellImage, charge] using
      cellImage_subset_charge S (faceGrid P S J f) (.inr (.inl (copy, lastStrip S)))
  · change rxFaceImage P S J (terminalRungFace P S f 1 copy) ⊆ _
    rw [terminalRung_one_image]
    simpa [cellImage, charge] using
      cellImage_subset_charge S (faceGrid P S J f) (.inr (.inr (copy, lastStrip S)))

/-! ## Actual subdivision boundary coordinates -/

/-- Radial contraction about X commutes with either affine triangle of the folded face. -/
theorem foldedSquare_contract (x q₀ q₁ z : E) (r u v : ℝ) (hr : 0 ≤ r) :
    foldedSquare x q₀ q₁ z (r * u) (r * v) =
      (1 - r) • x + r • foldedSquare x q₀ q₁ z u v := by
  rcases eq_or_lt_of_le hr with hr | hr
  · subst r
    simp [foldedSquare]
  · have horder : r * v ≤ r * u ↔ v ≤ u := mul_le_mul_iff_right₀ hr
    simp only [foldedSquare, horder]
    split_ifs <;> module

private theorem facePoint_contract (P : TannerSquarePresentation) (J : Vertex P → E)
    (f : P.Face) (r u v : ℝ) (hr : 0 ≤ r) :
    facePoint P J f (r * u) (r * v) =
      (1 - r) • J (.x (P.faceX f)) + r • facePoint P J f u v :=
  foldedSquare_contract _ _ _ _ r u v hr

private theorem interior_parameter_bounds (S : OddScale) (i : Fin (S.half - 1)) :
    0 ≤ ((i.val : ℝ) + 1) / S.half ∧ ((i.val : ℝ) + 1) / S.half ≤ 1 := by
  have hh : (0 : ℝ) < S.half := by exact_mod_cast S.half_pos
  constructor
  · positivity
  · apply (div_le_one hh).2
    exact_mod_cast (show i.val + 1 ≤ S.half by have := i.isLt; omega)

private theorem interior_parameter_scaled (S : OddScale) (i : Fin (S.half - 1)) :
    2 * ((i.val : ℝ) + 1) / S.ell =
      contractionRatio S * (((i.val : ℝ) + 1) / S.half) := by
  have hh : (S.half : ℝ) ≠ 0 := by exact_mod_cast S.half_pos.ne'
  have he : (S.ell : ℝ) ≠ 0 := by exact_mod_cast (show S.ell ≠ 0 by have := S.three_le; omega)
  simp only [contractionRatio]
  field_simp [hh, he]
  <;> ring

/-- Every actual X-Q0 interior tag has the horizontal contracted-grid coordinate. -/
theorem subdivisionVertexPoint_xq0 (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (f : XStarFace P x) (i : Fin (S.half - 1)) :
    subdivisionVertexPoint P S J x (.inr (.inl (xStarFaceXQEdge P x f 0, i))) =
      facePoint P J f.1 (2 * ((i.val : ℝ) + 1) / S.ell) 0 := by
  have hx : P.faceX f.1 = x := by simpa [xStarFaceMember] using f.2
  have hp := facePoint_contract P J f.1 (contractionRatio S)
    (((i.val : ℝ) + 1) / S.half) 0 (contractionRatio_bounds S).1
  rw [interior_parameter_scaled]
  rw [show (0 : ℝ) = contractionRatio S * 0 by ring, hp]
  simp only [mul_zero] at *
  simp [subdivisionVertexPoint, starVertexPoint, xStarFaceXQEdge,
    xStarEdgeStart, xStarEdgeEnd, faceXQEdge, facePoint,
    foldedSquare_bottom, (interior_parameter_bounds S i).1, hx]
  module

/-- Every actual X-Q1 interior tag has the vertical contracted-grid coordinate. -/
theorem subdivisionVertexPoint_xq1 (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (f : XStarFace P x) (i : Fin (S.half - 1)) :
    subdivisionVertexPoint P S J x (.inr (.inl (xStarFaceXQEdge P x f 1, i))) =
      facePoint P J f.1 0 (2 * ((i.val : ℝ) + 1) / S.ell) := by
  have hx : P.faceX f.1 = x := by simpa [xStarFaceMember] using f.2
  have hp := facePoint_contract P J f.1 (contractionRatio S)
    0 (((i.val : ℝ) + 1) / S.half) (contractionRatio_bounds S).1
  rw [interior_parameter_scaled]
  rw [show (0 : ℝ) = contractionRatio S * 0 by ring, hp]
  simp only [mul_zero] at *
  simp [subdivisionVertexPoint, starVertexPoint, xStarFaceXQEdge,
    xStarEdgeStart, xStarEdgeEnd, faceXQEdge, facePoint,
    foldedSquare_left, (interior_parameter_bounds S i).1, hx]
  module

/-- Actual Q0-Z interior tags lie on the right contracted side, with shared endpoints. -/
theorem subdivisionVertexPoint_qz0 (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (f : XStarFace P x) (i : Fin (S.half - 1)) :
    subdivisionVertexPoint P S J x (.inr (.inl (xStarFaceQZEdge P x f 0, i))) =
      facePoint P J f.1 (contractionRatio S) (2 * ((i.val : ℝ) + 1) / S.ell) := by
  have hx : P.faceX f.1 = x := by simpa [xStarFaceMember] using f.2
  have hp := facePoint_contract P J f.1 (contractionRatio S)
    1 (((i.val : ℝ) + 1) / S.half) (contractionRatio_bounds S).1
  simp only [mul_one] at hp
  rw [interior_parameter_scaled, hp]
  simp [subdivisionVertexPoint, starVertexPoint, xStarFaceQZEdge,
    xStarEdgeStart, xStarEdgeEnd, faceQZEdge, facePoint,
    foldedSquare_right, (interior_parameter_bounds S i).2, hx]
  module

/-- Actual Q1-Z interior tags lie on the top contracted side. -/
theorem subdivisionVertexPoint_qz1 (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (f : XStarFace P x) (i : Fin (S.half - 1)) :
    subdivisionVertexPoint P S J x (.inr (.inl (xStarFaceQZEdge P x f 1, i))) =
      facePoint P J f.1 (2 * ((i.val : ℝ) + 1) / S.ell) (contractionRatio S) := by
  have hx : P.faceX f.1 = x := by simpa [xStarFaceMember] using f.2
  have hp := facePoint_contract P J f.1 (contractionRatio S)
    (((i.val : ℝ) + 1) / S.half) 1 (contractionRatio_bounds S).1
  simp only [mul_one] at hp
  rw [interior_parameter_scaled, hp]
  simp [subdivisionVertexPoint, starVertexPoint, xStarFaceQZEdge,
    xStarEdgeStart, xStarEdgeEnd, faceQZEdge, facePoint,
    foldedSquare_top, (interior_parameter_bounds S i).2, hx]
  module

/-- Every materialized grid vertex has the common folded-square position, including
all four corners, shared edge tags, and the face-interior tags. -/
theorem subdivisionVertexPoint_grid (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (f : XStarFace P x)
    (i j : Fin (S.half + 1)) :
    subdivisionVertexPoint P S J x (subdivisionGridVertex P x S f i j) =
      facePoint P J f.1 (2 * (i.val : ℝ) / S.ell) (2 * (j.val : ℝ) / S.ell) := by
  have hhalf : S.half ≠ 0 := S.half_pos.ne'
  have hr : (0 : ℝ) ≤ 2 * (S.half : ℝ) / S.ell := (contractionRatio_bounds S).1
  have hx : P.faceX f.1 = x := by simpa [xStarFaceMember] using f.2
  have hpred (k : Fin (S.half + 1)) (hk : k.val ≠ 0) :
      (((k.val - 1 : Nat) : ℝ) + 1) = k.val := by
    exact_mod_cast (Nat.sub_add_cancel (show 1 ≤ k.val by omega))
  by_cases hi0 : i.val = 0
  · by_cases hj0 : j.val = 0
    · simp [subdivisionGridVertex, hhalf, hr, hi0, hj0, subdivisionVertexPoint, starVertexPoint,
        xStarFaceXVertex, facePoint, foldedSquare, hx]
      module
    · by_cases hjm : j.val = S.half
      · simp [subdivisionGridVertex, hhalf, hr, hi0, hj0, hjm, subdivisionVertexPoint, starVertexPoint,
          xStarFaceQVertex, facePoint, contractionRatio,
          foldedSquare_left, hr, hx]
      · simp only [subdivisionGridVertex, hi0, hj0, hjm, dif_pos, dif_neg, dite_true, dite_false, hhalf]
        rw [subdivisionVertexPoint_xq1]
        change facePoint P J f.1 0 (2 * (((j.val - 1 : Nat) : ℝ) + 1) / S.ell) = _
        simp [hi0, hpred j hj0]
  · by_cases him : i.val = S.half
    · by_cases hj0 : j.val = 0
      · simp [subdivisionGridVertex, hhalf, hr, hi0, him, hj0, subdivisionVertexPoint, starVertexPoint,
          xStarFaceQVertex, facePoint, contractionRatio,
          foldedSquare_bottom, hr, hx]
      · by_cases hjm : j.val = S.half
        · simp [subdivisionGridVertex, hhalf, hr, hi0, him, hj0, hjm, subdivisionVertexPoint,
            starVertexPoint, xStarFaceZVertex, facePoint, contractionRatio, hx]
        · simp only [subdivisionGridVertex, hi0, him, hj0, hjm, dif_pos, dif_neg, dite_true, dite_false, hhalf]
          rw [subdivisionVertexPoint_qz0]
          change facePoint P J f.1 (contractionRatio S)
            (2 * (((j.val - 1 : Nat) : ℝ) + 1) / S.ell) = _
          simp [him, hpred j hj0, contractionRatio]
    · by_cases hj0 : j.val = 0
      · simp only [subdivisionGridVertex, hi0, him, hj0, dif_pos, dif_neg, dite_true, dite_false, hhalf]
        rw [subdivisionVertexPoint_xq0]
        change facePoint P J f.1 (2 * (((i.val - 1 : Nat) : ℝ) + 1) / S.ell) 0 = _
        simp [hj0, hpred i hi0]
      · by_cases hjm : j.val = S.half
        · simp only [subdivisionGridVertex, hi0, him, hj0, hjm, dif_pos, dif_neg, dite_true, dite_false, hhalf]
          rw [subdivisionVertexPoint_qz1]
          change facePoint P J f.1 (2 * (((i.val - 1 : Nat) : ℝ) + 1) / S.ell)
            (contractionRatio S) = _
          simp [hjm, hpred i hi0, contractionRatio]
        · simp only [subdivisionGridVertex, hi0, him, hj0, hjm, dif_pos, dif_neg, dite_true, dite_false, hhalf,
            subdivisionVertexPoint]
          change facePoint P J f.1 (2 * (((i.val - 1 : Nat) : ℝ) + 1) / S.ell)
            (2 * (((j.val - 1 : Nat) : ℝ) + 1) / S.ell) = _
          rw [hpred i hi0, hpred j hj0]

/-- The second affine chart includes the diagonal because both charts agree there. -/
theorem foldedSquare_of_u_le_v (x q₀ q₁ z : E) {u v : ℝ} (h : u ≤ v) :
    foldedSquare x q₀ q₁ z u v = (1 - v) • x + (v - u) • q₁ + u • z := by
  by_cases h' : v ≤ u
  · have huv : u = v := le_antisymm h h'
    subst v
    simp [foldedSquare]
  · simp [foldedSquare, h']

/-- Midpoints in the lower affine triangle are computed from the actual endpoints. -/
theorem foldedSquare_midpoint_lower (x q₀ q₁ z : E) {u₀ v₀ u₁ v₁ : ℝ}
    (h₀ : v₀ ≤ u₀) (h₁ : v₁ ≤ u₁) :
    (1 / 2 : ℝ) • (foldedSquare x q₀ q₁ z u₀ v₀ + foldedSquare x q₀ q₁ z u₁ v₁) =
      foldedSquare x q₀ q₁ z ((u₀ + u₁) / 2) ((v₀ + v₁) / 2) := by
  have hm : (v₀ + v₁) / 2 ≤ (u₀ + u₁) / 2 := by linarith
  simp only [foldedSquare, if_pos h₀, if_pos h₁, if_pos hm]
  module

/-- The analogous midpoint identity in the upper affine triangle. -/
theorem foldedSquare_midpoint_upper (x q₀ q₁ z : E) {u₀ v₀ u₁ v₁ : ℝ}
    (h₀ : u₀ ≤ v₀) (h₁ : u₁ ≤ v₁) :
    (1 / 2 : ℝ) • (foldedSquare x q₀ q₁ z u₀ v₀ + foldedSquare x q₀ q₁ z u₁ v₁) =
      foldedSquare x q₀ q₁ z ((u₀ + u₁) / 2) ((v₀ + v₁) / 2) := by
  have hm : (u₀ + u₁) / 2 ≤ (v₀ + v₁) / 2 := by linarith
  rw [foldedSquare_of_u_le_v x q₀ q₁ z h₀,
    foldedSquare_of_u_le_v x q₀ q₁ z h₁, foldedSquare_of_u_le_v x q₀ q₁ z hm]
  module

/-- Actual horizontal subdivision endpoints never cross the old diagonal in their interior. -/
theorem subdivisionHorizontalEdge_midpoint (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (f : XStarFace P x)
    (i : Fin S.half) (j : Fin (S.half + 1)) :
    (1 / 2 : ℝ) •
      (subdivisionVertexPoint P S J x
        (subdivisionEdgeStart P x S (subdivisionHorizontalEdge P x S f i j)) +
       subdivisionVertexPoint P S J x
        (subdivisionEdgeEnd P x S (subdivisionHorizontalEdge P x S f i j))) =
      facePoint P J f.1 ((2 * (i.val : ℝ) + 1) / S.ell)
        (2 * (j.val : ℝ) / S.ell) := by
  rw [subdivisionHorizontalEdge_start, subdivisionHorizontalEdge_end,
    subdivisionVertexPoint_grid, subdivisionVertexPoint_grid]
  change (1 / 2 : ℝ) •
    (facePoint P J f.1 (2 * (i.val : ℝ) / S.ell) (2 * (j.val : ℝ) / S.ell) +
     facePoint P J f.1 (2 * ((i.val + 1 : Nat) : ℝ) / S.ell) (2 * (j.val : ℝ) / S.ell)) = _
  have he : (0 : ℝ) < S.ell := by exact_mod_cast (show 0 < S.ell by have := S.three_le; omega)
  have havg : (2 * (i.val : ℝ) / S.ell + 2 * ((i.val + 1 : Nat) : ℝ) / S.ell) / 2 =
      (2 * (i.val : ℝ) + 1) / S.ell := by push_cast; ring
  by_cases hji : j.val ≤ i.val
  · have h₀ : 2 * (j.val : ℝ) / S.ell ≤ 2 * (i.val : ℝ) / S.ell := by
      apply (div_le_div_iff_of_pos_right he).2
      exact_mod_cast Nat.mul_le_mul_left 2 hji
    have h₁ : 2 * (j.val : ℝ) / S.ell ≤ 2 * ((i.val + 1 : Nat) : ℝ) / S.ell := by
      apply (div_le_div_iff_of_pos_right he).2
      exact_mod_cast Nat.mul_le_mul_left 2 (show j.val ≤ i.val + 1 by omega)
    simpa only [facePoint, havg, add_self_div_two] using
      foldedSquare_midpoint_lower (J (.x (P.faceX f.1))) (J (.q (P.faceQ f.1 0)))
        (J (.q (P.faceQ f.1 1))) (J (.z (P.faceZ f.1))) h₀ h₁
  · have h₀ : 2 * (i.val : ℝ) / S.ell ≤ 2 * (j.val : ℝ) / S.ell := by
      apply (div_le_div_iff_of_pos_right he).2
      exact_mod_cast Nat.mul_le_mul_left 2 (show i.val ≤ j.val by omega)
    have h₁ : 2 * ((i.val + 1 : Nat) : ℝ) / S.ell ≤ 2 * (j.val : ℝ) / S.ell := by
      apply (div_le_div_iff_of_pos_right he).2
      exact_mod_cast Nat.mul_le_mul_left 2 (show i.val + 1 ≤ j.val by omega)
    simpa only [facePoint, havg, add_self_div_two] using
      foldedSquare_midpoint_upper (J (.x (P.faceX f.1))) (J (.q (P.faceQ f.1 0)))
        (J (.q (P.faceQ f.1 1))) (J (.z (P.faceZ f.1))) h₀ h₁

/-- Actual vertical subdivision endpoints also stay within one old affine triangle. -/
theorem subdivisionVerticalEdge_midpoint (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (f : XStarFace P x)
    (i : Fin (S.half + 1)) (j : Fin S.half) :
    (1 / 2 : ℝ) •
      (subdivisionVertexPoint P S J x
        (subdivisionEdgeStart P x S (subdivisionVerticalEdge P x S f i j)) +
       subdivisionVertexPoint P S J x
        (subdivisionEdgeEnd P x S (subdivisionVerticalEdge P x S f i j))) =
      facePoint P J f.1 (2 * (i.val : ℝ) / S.ell)
        ((2 * (j.val : ℝ) + 1) / S.ell) := by
  rw [subdivisionVerticalEdge_start, subdivisionVerticalEdge_end,
    subdivisionVertexPoint_grid, subdivisionVertexPoint_grid]
  change (1 / 2 : ℝ) •
    (facePoint P J f.1 (2 * (i.val : ℝ) / S.ell) (2 * (j.val : ℝ) / S.ell) +
     facePoint P J f.1 (2 * (i.val : ℝ) / S.ell) (2 * ((j.val + 1 : Nat) : ℝ) / S.ell)) = _
  have he : (0 : ℝ) < S.ell := by exact_mod_cast (show 0 < S.ell by have := S.three_le; omega)
  have havg : (2 * (j.val : ℝ) / S.ell + 2 * ((j.val + 1 : Nat) : ℝ) / S.ell) / 2 =
      (2 * (j.val : ℝ) + 1) / S.ell := by push_cast; ring
  by_cases hji : j.val + 1 ≤ i.val
  · have h₀ : 2 * (j.val : ℝ) / S.ell ≤ 2 * (i.val : ℝ) / S.ell := by
      apply (div_le_div_iff_of_pos_right he).2
      exact_mod_cast Nat.mul_le_mul_left 2 (show j.val ≤ i.val by omega)
    have h₁ : 2 * ((j.val + 1 : Nat) : ℝ) / S.ell ≤ 2 * (i.val : ℝ) / S.ell := by
      apply (div_le_div_iff_of_pos_right he).2
      exact_mod_cast Nat.mul_le_mul_left 2 hji
    simpa only [facePoint, havg, add_self_div_two] using
      foldedSquare_midpoint_lower (J (.x (P.faceX f.1))) (J (.q (P.faceQ f.1 0)))
        (J (.q (P.faceQ f.1 1))) (J (.z (P.faceZ f.1))) h₀ h₁
  · have h₀ : 2 * (i.val : ℝ) / S.ell ≤ 2 * (j.val : ℝ) / S.ell := by
      apply (div_le_div_iff_of_pos_right he).2
      exact_mod_cast Nat.mul_le_mul_left 2 (show i.val ≤ j.val by omega)
    have h₁ : 2 * (i.val : ℝ) / S.ell ≤ 2 * ((j.val + 1 : Nat) : ℝ) / S.ell := by
      apply (div_le_div_iff_of_pos_right he).2
      exact_mod_cast Nat.mul_le_mul_left 2 (show i.val ≤ j.val + 1 by omega)
    simpa only [facePoint, havg, add_self_div_two] using
      foldedSquare_midpoint_upper (J (.x (P.faceX f.1))) (J (.q (P.faceQ f.1 0)))
        (J (.q (P.faceQ f.1 1))) (J (.z (P.faceZ f.1))) h₀ h₁

/-- The actual planar-face X corner uses its materialized coarse corner. -/
theorem planarFaceX_point (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (f : XStarFace P x) (i j : Fin S.half)
    (copy a b : BDL26FiniteTannerSquare.Two) :
    rxZeroPoint P S J (localFaceX P S ⟨x, .inl (copy, f, i, j), a, b⟩) =
      facePoint P J f.1 (2 * ((gridEndpoint i a).val : ℝ) / S.ell)
        (2 * ((gridEndpoint j b).val : ℝ) / S.ell) :=
  subdivisionVertexPoint_grid P S J x f (gridEndpoint i a) (gridEndpoint j b)

/-- The actual horizontal Q corner lies at the midpoint of its tagged subdivision edge. -/
theorem planarFaceQ0_point (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (f : XStarFace P x) (i j : Fin S.half)
    (copy a b : BDL26FiniteTannerSquare.Two) :
    rxOnePoint P S J (localFaceQ0 P S ⟨x, .inl (copy, f, i, j), a, b⟩) =
      facePoint P J f.1 ((2 * (i.val : ℝ) + 1) / S.ell)
        (2 * ((gridEndpoint j b).val : ℝ) / S.ell) := by
  have hb : subdivisionFaceBoundaryEdge P x S (f, i, j) (0, b) =
      subdivisionHorizontalEdge P x S f i (gridEndpoint j b) := by
    fin_cases b <;> rfl
  change (1 / 2 : ℝ) •
    (subdivisionVertexPoint P S J x
      (subdivisionEdgeStart P x S (subdivisionFaceBoundaryEdge P x S (f, i, j) (0, b))) +
     subdivisionVertexPoint P S J x
      (subdivisionEdgeEnd P x S (subdivisionFaceBoundaryEdge P x S (f, i, j) (0, b)))) = _
  rw [hb]
  exact subdivisionHorizontalEdge_midpoint P S J x f i (gridEndpoint j b)

/-- The actual vertical Q corner lies at its tagged subdivision-edge midpoint. -/
theorem planarFaceQ1_point (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (f : XStarFace P x) (i j : Fin S.half)
    (copy a b : BDL26FiniteTannerSquare.Two) :
    rxOnePoint P S J (localFaceQ1 P S ⟨x, .inl (copy, f, i, j), a, b⟩) =
      facePoint P J f.1 (2 * ((gridEndpoint i a).val : ℝ) / S.ell)
        ((2 * (j.val : ℝ) + 1) / S.ell) := by
  have hb : subdivisionFaceBoundaryEdge P x S (f, i, j) (1, a) =
      subdivisionVerticalEdge P x S f (gridEndpoint i a) j := by
    fin_cases a <;> rfl
  change (1 / 2 : ℝ) •
    (subdivisionVertexPoint P S J x
      (subdivisionEdgeStart P x S (subdivisionFaceBoundaryEdge P x S (f, i, j) (1, a))) +
     subdivisionVertexPoint P S J x
      (subdivisionEdgeEnd P x S (subdivisionFaceBoundaryEdge P x S (f, i, j) (1, a)))) = _
  rw [hb]
  exact subdivisionVerticalEdge_midpoint P S J x f (gridEndpoint i a) j

/-- The actual local Z center is the odd fine-grid point in both directions. -/
theorem planarFaceZ_point (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (f : XStarFace P x) (i j : Fin S.half)
    (copy a b : BDL26FiniteTannerSquare.Two) :
    rxTwoPoint P S J (localFaceZ P S ⟨x, .inl (copy, f, i, j), a, b⟩) =
      facePoint P J f.1 ((2 * (i.val : ℝ) + 1) / S.ell)
        ((2 * (j.val : ℝ) + 1) / S.ell) := rfl

/-- The same-edge Q-to-X map translates every actual Q-path coordinate by one
fixed contraction offset, independently of its root witness. -/
theorem qToXSubdivisionVertexAtRoot_point (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (q : P.Q) (x : P.X) (hxq : P.xq x q = true)
    (root : QStarEdge P q) (v : QSubdivisionVertex P q S) :
    subdivisionVertexPoint P S J x (qToXSubdivisionVertexAtRoot P q x hxq S root v) =
      (1 - contractionRatio S) • J (.x x) + qSubdivisionVertexPoint P S J q v -
        (1 - contractionRatio S) • J (.q q) := by
  rcases v with (u | edge) | ⟨edge, i⟩
  · change (1 - contractionRatio S) • J (.x x) + contractionRatio S • J (.q q) = _
    simp only [qSubdivisionVertexPoint]
    module
  · change (1 - contractionRatio S) • J (.x x) + contractionRatio S • J (.z edge.1) = _
    simp only [qSubdivisionVertexPoint]
    module
  · change
      (1 - ((i.val : ℝ) + 1) / S.half) •
          ((1 - contractionRatio S) • J (.x x) + contractionRatio S • J (.q q)) +
        (((i.val : ℝ) + 1) / S.half) •
          ((1 - contractionRatio S) • J (.x x) + contractionRatio S • J (.z edge.1)) = _
    simp only [qSubdivisionVertexPoint]
    rw [interior_parameter_scaled]
    module

/-- Coordinates of the actual starting vertex of a Q-local path segment. -/
theorem qSubdivisionEdgeStart_point (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (q : P.Q) (edge : QStarEdge P q) (i : Fin S.half) :
    qSubdivisionVertexPoint P S J q (qSubdivisionEdgeStart P q S (edge, i)) =
      (1 - 2 * (i.val : ℝ) / S.ell) • J (.q q) +
        (2 * (i.val : ℝ) / S.ell) • J (.z edge.1) := by
  by_cases hi : i.val = 0
  · simp [qSubdivisionEdgeStart, hi, qSubdivisionVertexPoint, qStarEdgeStart]
  · have hp : (((i.val - 1 : Nat) : ℝ) + 1) = i.val := by
      exact_mod_cast Nat.sub_add_cancel (show 1 ≤ i.val by omega)
    simp [qSubdivisionEdgeStart, hi, qSubdivisionVertexPoint, hp]

/-- Coordinates of the actual ending vertex, including the terminal contracted Z. -/
theorem qSubdivisionEdgeEnd_point (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (q : P.Q) (edge : QStarEdge P q) (i : Fin S.half) :
    qSubdivisionVertexPoint P S J q (qSubdivisionEdgeEnd P q S (edge, i)) =
      (1 - 2 * ((i.val : ℝ) + 1) / S.ell) • J (.q q) +
        (2 * ((i.val : ℝ) + 1) / S.ell) • J (.z edge.1) := by
  by_cases hi : i.val + 1 = S.half
  · have hr : (i.val : ℝ) + 1 = S.half := by exact_mod_cast hi
    simp [qSubdivisionEdgeEnd, hi, qSubdivisionVertexPoint, qStarEdgeEnd,
      contractionRatio, hr]
  · simp [qSubdivisionEdgeEnd, hi, qSubdivisionVertexPoint]

/-- Both endpoints determine the actual Q-path segment midpoint. -/
theorem qSubdivisionEdge_midpoint (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (q : P.Q) (edge : QStarEdge P q) (i : Fin S.half) :
    (1 / 2 : ℝ) •
      (qSubdivisionVertexPoint P S J q (qSubdivisionEdgeStart P q S (edge, i)) +
       qSubdivisionVertexPoint P S J q (qSubdivisionEdgeEnd P q S (edge, i))) =
      (1 - (2 * (i.val : ℝ) + 1) / S.ell) • J (.q q) +
        ((2 * (i.val : ℝ) + 1) / S.ell) • J (.z edge.1) := by
  rw [qSubdivisionEdgeStart_point, qSubdivisionEdgeEnd_point]
  module

/-- A path-strip face keeps the old ordered corner, copy, segment and endpoint labels. -/
def pathStripFace (P : TannerSquarePresentation) (S : OddScale) (f : P.Face)
    (side copy : BDL26FiniteTannerSquare.Two) (i : Fin S.half)
    (endpoint : BDL26FiniteTannerSquare.Two) : RXFace P S :=
  .inr (.inl ⟨⟨(P.faceX f, P.faceQ f side), P.data.faceQ_xq f side⟩,
    .inl (copy, ⟨P.faceZ f, P.data.faceQ_qz f side⟩, i), endpoint⟩)

/-- The path-strip Z corner is the genuine Q-local segment midpoint. -/
theorem pathStripFaceZ_point (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (side copy : BDL26FiniteTannerSquare.Two)
    (i : Fin S.half) (endpoint : BDL26FiniteTannerSquare.Two) :
    rxTwoPoint P S J (rxFaceZ P S (pathStripFace P S f side copy i endpoint)) =
      (1 - (2 * (i.val : ℝ) + 1) / S.ell) • J (.q (P.faceQ f side)) +
        ((2 * (i.val : ℝ) + 1) / S.ell) • J (.z (P.faceZ f)) :=
  qSubdivisionEdge_midpoint P S J (P.faceQ f side)
    ⟨P.faceZ f, P.data.faceQ_qz f side⟩ i

/-- The actual glue X and Q1 endpoints differ by the same old X-Q offset. -/
theorem glueFaceX_point_offset (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (a : XQEdge P) (edge : QDoubleCylinderEdge P a.1.2 S)
    (endpoint : BDL26FiniteTannerSquare.Two) :
    rxZeroPoint P S J (glueFaceX P S ⟨a, edge, endpoint⟩) =
      (1 - contractionRatio S) • J (.x a.1.1) +
        rxOnePoint P S J (glueFaceQ1 P S ⟨a, edge, endpoint⟩) -
        (1 - contractionRatio S) • J (.q a.1.2) := by
  let root := qDoubleCylinderUnderlyingStarEdge P a.1.2 S edge
  fin_cases endpoint
  · change subdivisionVertexPoint P S J a.1.1
        (tannerDoubleCylinderEdgeStart P a.1.1 S
          (qToXDoubleCylinderEdgeRaw P a.1.2 a.1.1 a.2 S edge)).2 = _
    rw [← qToXDoubleCylinderEdgeRaw_start P a.1.2 a.1.1 a.2 S root edge]
    exact qToXSubdivisionVertexAtRoot_point P S J a.1.2 a.1.1 a.2 root
      (qDoubleCylinderEdgeStart P a.1.2 S edge).2
  · change subdivisionVertexPoint P S J a.1.1
        (tannerDoubleCylinderEdgeEnd P a.1.1 S
          (qToXDoubleCylinderEdgeRaw P a.1.2 a.1.1 a.2 S edge)).2 = _
    rw [← qToXDoubleCylinderEdgeRaw_end P a.1.2 a.1.1 a.2 S root edge]
    exact qToXSubdivisionVertexAtRoot_point P S J a.1.2 a.1.1 a.2 root
      (qDoubleCylinderEdgeEnd P a.1.2 S edge).2

/-- The actual glue midpoint pair has that identical geometric offset. -/
theorem glueFaceQ0_point_offset (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (a : XQEdge P) (edge : QDoubleCylinderEdge P a.1.2 S)
    (endpoint : BDL26FiniteTannerSquare.Two) :
    rxOnePoint P S J (glueFaceQ0 P S ⟨a, edge, endpoint⟩) =
      (1 - contractionRatio S) • J (.x a.1.1) +
        rxTwoPoint P S J (glueFaceZ P S ⟨a, edge, endpoint⟩) -
        (1 - contractionRatio S) • J (.q a.1.2) := by
  have h₀ := glueFaceX_point_offset P S J a edge 0
  have h₁ := glueFaceX_point_offset P S J a edge 1
  simp only [rxZeroPoint, glueFaceX, rxOnePoint, glueFaceQ1,
    BDL26RXLocalReplacement.edgeEndpoint, twoSelect_zero, twoSelect_one] at h₀ h₁
  simp only [rxOnePoint, glueFaceQ0, rxTwoPoint, glueFaceZ]
  rw [h₀, h₁]
  module

/-- The original point map transported by the explicit X/Z vertex swap. -/
def transposePointMap (P : TannerSquarePresentation) (J : Vertex P → E) :
    Vertex (transposePresentation P) → E := J ∘ transposeVertexEquiv P

/-- Actual global RZ X positions are centers in the transposed construction. -/
def rzXPoint (P : TannerSquarePresentation) (S : OddScale) (J : Vertex P → E) :
    BDL26RZLocalReplacement.RZX P S → E :=
  rxTwoPoint (transposePresentation P) S (transposePointMap P J)

/-- Actual global RZ Q positions use the shared materialized edge/vertex tags. -/
def rzQPoint (P : TannerSquarePresentation) (S : OddScale) (J : Vertex P → E) :
    BDL26RZLocalReplacement.RZQ P S → E :=
  rxOnePoint (transposePresentation P) S (transposePointMap P J)

/-- Actual global RZ Z positions are the transposed contracted grid vertices. -/
def rzZPoint (P : TannerSquarePresentation) (S : OddScale) (J : Vertex P → E) :
    BDL26RZLocalReplacement.RZZ P S → E :=
  rxZeroPoint (transposePresentation P) S (transposePointMap P J)

/-- Every Q-to-Z vertex tag agrees with the same-edge transpose construction;
the chosen cone-point root affects no materialized vertex. -/
theorem qToZDoubleCylinderVertex_eq_raw (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (q : P.Q) (z : P.Z)
    (hqz : P.qz q z = true) (root : QStarEdge (transposePresentation P) q)
    (v : QDoubleCylinderVertex (transposePresentation P) q S) :
    qToZDoubleCylinderVertex P A q z hqz S v =
      qToXDoubleCylinderVertexAtRoot (transposePresentation P) q z hqz S root v := by
  rcases v with ⟨copy, (u | edge) | ⟨edge, i⟩⟩ <;> rfl

/-- The actual Q-to-Z edge map preserves the same explicit edge in the transpose. -/
theorem qToZDoubleCylinderEdge_eq_raw (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (q : P.Q) (z : P.Z)
    (hqz : P.qz q z = true) (edge : QDoubleCylinderEdge (transposePresentation P) q S) :
    qToZDoubleCylinderEdge P A q z hqz S edge =
      qToXDoubleCylinderEdgeRaw (transposePresentation P) q z hqz S edge := by
  rcases edge with ⟨copy, edge⟩ | edge <;> rfl

/-- The RZ face X endpoint matches the concrete transposed RX Z endpoint. -/
theorem rzFaceX_transpose (P : TannerSquarePresentation) (S : OddScale)
    (f : BDL26RZLocalReplacement.RZFace P S) :
    BDL26RZLocalReplacement.rzFaceX P S f =
      rxFaceZ (transposePresentation P) S (rzFaceEquiv P S f) := by
  rcases f with localFace | glue | old
  · rfl
  · rcases glue with ⟨⟨⟨q, z⟩, hqz⟩, edge, endpoint⟩
    rfl
  · rfl

/-- The RZ face Z endpoint matches the concrete transposed RX X endpoint. -/
theorem rzFaceZ_transpose (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (f : BDL26RZLocalReplacement.RZFace P S) :
    BDL26RZLocalReplacement.rzFaceZ P A S f =
      rxFaceX (transposePresentation P) S (rzFaceEquiv P S f) := by
  rcases f with ⟨z, cell, a, b⟩ | ⟨⟨⟨q, z⟩, hqz⟩, edge, endpoint⟩ | ⟨old, copy⟩
  · rcases cell with ⟨copy, f, i, j⟩ | boundary
    · fin_cases a <;> fin_cases b <;> rfl
    · fin_cases a <;> fin_cases b <;> rfl
  · let root := qDoubleCylinderUnderlyingStarEdge (transposePresentation P) q S edge
    fin_cases endpoint
    · change (⟨z, qToZDoubleCylinderVertex P A q z hqz S
          (qDoubleCylinderEdgeStart (transposePresentation P) q S edge)⟩ :
          BDL26RZLocalReplacement.RZZ P S) = _
      rw [qToZDoubleCylinderVertex_eq_raw P A S q z hqz root]
      exact congrArg (fun v : DoubleCylinderVertex (transposePresentation P) z S =>
        (⟨z, v⟩ : BDL26RZLocalReplacement.RZZ P S))
        (qToXDoubleCylinderEdgeRaw_start (transposePresentation P) q z hqz S root edge)
    · change (⟨z, qToZDoubleCylinderVertex P A q z hqz S
          (qDoubleCylinderEdgeEnd (transposePresentation P) q S edge)⟩ :
          BDL26RZLocalReplacement.RZZ P S) = _
      rw [qToZDoubleCylinderVertex_eq_raw P A S q z hqz root]
      exact congrArg (fun v : DoubleCylinderVertex (transposePresentation P) z S =>
        (⟨z, v⟩ : BDL26RZLocalReplacement.RZZ P S))
        (qToXDoubleCylinderEdgeRaw_end (transposePresentation P) q z hqz S root edge)
  · rfl

/-- Both ordered Q endpoints also match their actual transposed materialized tags. -/
theorem rzFaceQ_transpose (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (f : BDL26RZLocalReplacement.RZFace P S)
    (corner : BDL26FiniteTannerSquare.Two) :
    BDL26RZLocalReplacement.rzFaceQ P A S f corner =
      rxFaceQ (transposePresentation P) S (rzFaceEquiv P S f) corner := by
  rcases f with ⟨z, cell, a, b⟩ | ⟨⟨⟨q, z⟩, hqz⟩, edge, endpoint⟩ | ⟨old, copy⟩
  · rcases cell with ⟨copy, f, i, j⟩ | boundary
    · fin_cases corner <;> fin_cases a <;> fin_cases b <;> rfl
    · fin_cases corner <;> fin_cases a <;> fin_cases b <;> rfl
  · fin_cases corner
    · change (Sum.inl ⟨z, qToZDoubleCylinderEdge P A q z hqz S edge⟩ :
          BDL26RZLocalReplacement.RZQ P S) = _
      rw [qToZDoubleCylinderEdge_eq_raw]
      rfl
    · rfl
  · rfl

/-- RZ images use its actual global endpoint maps and original X-Z diagonal. -/
noncomputable def rzFaceImage (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (J : Vertex P → E) (f : BDL26RZLocalReplacement.RZFace P S) : Set E :=
  convexHull ℝ {rzXPoint P S J (BDL26RZLocalReplacement.rzFaceX P S f),
    rzQPoint P S J (BDL26RZLocalReplacement.rzFaceQ P A S f 0),
    rzZPoint P S J (BDL26RZLocalReplacement.rzFaceZ P A S f)} ∪
  convexHull ℝ {rzXPoint P S J (BDL26RZLocalReplacement.rzFaceX P S f),
    rzZPoint P S J (BDL26RZLocalReplacement.rzFaceZ P A S f),
    rzQPoint P S J (BDL26RZLocalReplacement.rzFaceQ P A S f 1)}

/-- The materialized RZ image is the RX image on the transpose, with no image assumption. -/
theorem rzFaceImage_eq_transpose (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (J : Vertex P → E) (f : BDL26RZLocalReplacement.RZFace P S) :
    rzFaceImage P A S J f =
      rxFaceImage (transposePresentation P) S (transposePointMap P J) (rzFaceEquiv P S f) := by
  simp only [rzFaceImage, rzFaceX_transpose, rzFaceZ_transpose, rzFaceQ_transpose,
    rzXPoint, rzQPoint, rzZPoint, rxFaceImage]
  congr 1 <;> congr 1 <;> ext p <;> simp only [Set.mem_insert_iff, Set.mem_singleton_iff] <;> tauto

/-- A materialized boundary-rectangle quadrant is contained in the adjacent actual
Q-path glue face. The subset follows from their shared endpoint and midpoint tags. -/
theorem rectangle_image_subset_glue (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (a : XQEdge P)
    (edge : QSubdivisionEdge P a.1.2 S)
    (copy endpoint : BDL26FiniteTannerSquare.Two) :
    rxFaceImage P S J (.inl ⟨a.1.1,
        .inr (qToXSubdivisionBoundaryEdge P a.1.2 a.1.1 a.2 S edge), copy, endpoint⟩) ⊆
      rxFaceImage P S J (.inr (.inl ⟨a, .inl (copy, edge), endpoint⟩)) := by
  rw [rectangleFace_image]
  have hx : rectangleEndpointPoint P S J a.1.1
      (qToXSubdivisionBoundaryEdge P a.1.2 a.1.1 a.2 S edge) endpoint =
      rxZeroPoint P S J (glueFaceX P S ⟨a, .inl (copy, edge), endpoint⟩) := by
    fin_cases endpoint <;> rfl
  have hq : rectangleMidpoint P S J a.1.1
      (qToXSubdivisionBoundaryEdge P a.1.2 a.1.1 a.2 S edge) =
      rxOnePoint P S J (glueFaceQ0 P S ⟨a, .inl (copy, edge), endpoint⟩) := rfl
  rw [hx, hq]
  simp only [rxFaceImage, rxFaceX, rxFaceQ, rxFaceZ, twoSelect_zero, twoSelect_one]
  exact (segment_subset_convexHull (by simp) (by simp)).trans Set.subset_union_left

/-- The lower affine chart lies in the actual incoming triangle. -/
theorem foldedSquare_mem_lower_triangle (x q₀ q₁ z : E) {u v : ℝ}
    (hu : u ≤ 1) (hv : 0 ≤ v) (hvu : v ≤ u) :
    foldedSquare x q₀ q₁ z u v ∈ convexHull ℝ {x, q₀, z} := by
  have h := (convex_convexHull ℝ ({x, q₀, z} : Set E)).sum_mem
    (t := Finset.univ) (w := ![1 - u, u - v, v]) (z := ![x, q₀, z])
    (by intro i _; fin_cases i <;> dsimp <;> linarith)
    (by simp [Fin.sum_univ_succ] <;> ring)
    (by intro i _; apply subset_convexHull; fin_cases i <;> simp)
  simpa [Fin.sum_univ_succ, foldedSquare, hvu, add_assoc] using h

/-- The upper affine chart lies in its actual incoming triangle, including the fold. -/
theorem foldedSquare_mem_upper_triangle (x q₀ q₁ z : E) {u v : ℝ}
    (hv : v ≤ 1) (hu : 0 ≤ u) (huv : u ≤ v) :
    foldedSquare x q₀ q₁ z u v ∈ convexHull ℝ {x, z, q₁} := by
  have h := (convex_convexHull ℝ ({x, z, q₁} : Set E)).sum_mem
    (t := Finset.univ) (w := ![1 - v, u, v - u]) (z := ![x, z, q₁])
    (by intro i _; fin_cases i <;> dsimp <;> linarith)
    (by simp [Fin.sum_univ_succ] <;> ring)
    (by intro i _; apply subset_convexHull; fin_cases i <;> simp)
  rw [foldedSquare_of_u_le_v x q₀ q₁ z huv]
  simpa [Fin.sum_univ_succ, add_assoc, add_comm, add_left_comm] using h

end PointMaps


noncomputable section TriangleFrame

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A unit direction constructed from a nonzero side, with zero totalization. -/
def triangleUnitDirection (b : E) : E := ‖b‖⁻¹ • b

/-- The actual perpendicular component of the second side. -/
def triangleAltitudeVector (b c : E) : E :=
  c - ⟪triangleUnitDirection b, c⟫_ℝ • triangleUnitDirection b

theorem triangleUnitDirection_norm {b : E} (hb : b ≠ 0) :
    ‖triangleUnitDirection b‖ = 1 := norm_smul_inv_norm hb

theorem triangleUnitDirection_inner {b : E} (hb : b ≠ 0) :
    ⟪triangleUnitDirection b, b⟫_ℝ = ‖b‖ := by
  rw [triangleUnitDirection, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hn : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb
  field_simp [hn]

theorem triangleAltitudeVector_orthogonal {b c : E} (hb : b ≠ 0) :
    ⟪triangleUnitDirection b, triangleAltitudeVector b c⟫_ℝ = 0 := by
  simp [triangleAltitudeVector, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, triangleUnitDirection_norm hb]

theorem triangleAltitudeVector_norm_le {b c : E} (hb : b ≠ 0) :
    ‖triangleAltitudeVector b c‖ ≤ ‖c‖ := by
  have hd : ⟪triangleUnitDirection b, c⟫_ℝ • triangleUnitDirection b +
      triangleAltitudeVector b c = c := by
    simp [triangleAltitudeVector]
  have ho : ⟪⟪triangleUnitDirection b, c⟫_ℝ • triangleUnitDirection b,
      triangleAltitudeVector b c⟫_ℝ = 0 := by
    rw [real_inner_smul_left, triangleAltitudeVector_orthogonal hb, mul_zero]
  have hs := norm_add_sq_eq_norm_sq_add_norm_sq_real ho
  rw [hd] at hs
  nlinarith [norm_nonneg (triangleAltitudeVector b c), norm_nonneg c,
    sq_nonneg ‖⟪triangleUnitDirection b, c⟫_ℝ • triangleUnitDirection b‖]

theorem triangleAltitudeDirection_inner_base {b c : E} (hb : b ≠ 0) :
    ⟪triangleUnitDirection (triangleAltitudeVector b c), b⟫_ℝ = 0 := by
  have hd : b = ‖b‖ • triangleUnitDirection b := by
    simp [triangleUnitDirection, smul_smul, norm_ne_zero_iff.mpr hb]
  have ho : ⟪triangleAltitudeVector b c, triangleUnitDirection b⟫_ℝ = 0 := by
    rw [real_inner_comm, triangleAltitudeVector_orthogonal hb]
  calc
    ⟪triangleUnitDirection (triangleAltitudeVector b c), b⟫_ℝ =
        ⟪triangleUnitDirection (triangleAltitudeVector b c), ‖b‖ • triangleUnitDirection b⟫_ℝ :=
      congrArg (fun v => ⟪triangleUnitDirection (triangleAltitudeVector b c), v⟫_ℝ) hd
    _ = 0 := by
      rw [real_inner_smul_right]
      change ‖b‖ * ⟪‖triangleAltitudeVector b c‖⁻¹ • triangleAltitudeVector b c,
        triangleUnitDirection b⟫_ℝ = 0
      rw [real_inner_smul_left, ho]
      ring

theorem triangleAltitudeDirection_inner_side {b c : E}
    (hb : b ≠ 0) (hc : triangleAltitudeVector b c ≠ 0) :
    ⟪triangleUnitDirection (triangleAltitudeVector b c), c⟫_ℝ =
      ‖triangleAltitudeVector b c‖ := by
  have he : ⟪triangleUnitDirection (triangleAltitudeVector b c),
      triangleUnitDirection b⟫_ℝ = 0 := by
    rw [triangleUnitDirection, real_inner_smul_left, real_inner_comm,
      triangleAltitudeVector_orthogonal hb, mul_zero]
  have hd : c = ⟪triangleUnitDirection b, c⟫_ℝ • triangleUnitDirection b +
      triangleAltitudeVector b c := by simp [triangleAltitudeVector]
  calc
    ⟪triangleUnitDirection (triangleAltitudeVector b c), c⟫_ℝ =
        ⟪triangleUnitDirection (triangleAltitudeVector b c),
          ⟪triangleUnitDirection b, c⟫_ℝ • triangleUnitDirection b +
            triangleAltitudeVector b c⟫_ℝ := congrArg _ hd
    _ = ‖triangleAltitudeVector b c‖ := by
      rw [inner_add_right, real_inner_smul_right, he, mul_zero, zero_add,
        triangleUnitDirection_inner hc]

/-- These anchors are built from the two actual triangle side vectors. -/
def triangleLatticeAnchor (o b c : E) (ell : ℝ) (p : ℤ × ℤ) : E :=
  o + ((p.1 : ℝ) / ell) • b + ((p.2 : ℝ) / ell) • c

theorem triangleLatticeAnchor_first (o b c : E) (ell : ℝ) (p : ℤ × ℤ)
    (hb : b ≠ 0) :
    ⟪triangleUnitDirection b, triangleLatticeAnchor o b c ell p - o⟫_ℝ =
      (‖b‖ / ell) * p.1 + (⟪triangleUnitDirection b, c⟫_ℝ / ell) * p.2 := by
  have hd : triangleLatticeAnchor o b c ell p - o =
      ((p.1 : ℝ) / ell) • b + ((p.2 : ℝ) / ell) • c := by
    simp [triangleLatticeAnchor] <;> abel
  rw [hd, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    triangleUnitDirection_inner hb]
  ring

theorem triangleLatticeAnchor_second (o b c : E) (ell : ℝ) (p : ℤ × ℤ)
    (hb : b ≠ 0) (hc : triangleAltitudeVector b c ≠ 0) :
    ⟪triangleUnitDirection (triangleAltitudeVector b c),
      triangleLatticeAnchor o b c ell p - o⟫_ℝ =
      (‖triangleAltitudeVector b c‖ / ell) * p.2 := by
  have hd : triangleLatticeAnchor o b c ell p - o =
      ((p.1 : ℝ) / ell) • b + ((p.2 : ℝ) / ell) • c := by
    simp [triangleLatticeAnchor] <;> abel
  rw [hd, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    triangleAltitudeDirection_inner_base hb, triangleAltitudeDirection_inner_side hb hc]
  ring

/-- Unit directions turn an actual ball condition into a coordinate bound. -/
theorem unit_inner_coordinate_bound (e o z p : E) (he : ‖e‖ = 1)
    (hp : dist p z ≤ 2) : |⟪e, p - o⟫_ℝ - ⟪e, z - o⟫_ℝ| ≤ 2 := by
  have hd : (p - o) - (z - o) = p - z := by abel
  rw [← inner_sub_right, hd]
  have hi := abs_real_inner_le_norm e (p - z)
  rw [he, one_mul] at hi
  exact hi.trans (by simpa [dist_eq_norm] using hp)

/-- Packing is derived in the actual constructed triangle frame, with no frame
or point-count certificate supplied by the caller. -/
theorem triangle_lattice_card_le (s : Finset (ℤ × ℤ)) (o b c z : E) {ell : ℝ}
    (hell : 0 < ell) (hb : b ≠ 0) (hc : triangleAltitudeVector b c ≠ 0)
    (hbL : ‖b‖ ≤ ell) (hcL : ‖c‖ ≤ ell)
    (hmem : ∀ p ∈ s, dist (triangleLatticeAnchor o b c ell p) z ≤ 2) :
    (s.card : ℝ) ≤ 8 * Real.pi * ell ^ 2 / (‖b‖ * ‖triangleAltitudeVector b c‖) := by
  have hbp : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hcp : 0 < ‖triangleAltitudeVector b c‖ := norm_pos_iff.mpr hc
  have hbound := shear_lattice_card_le_pi s (div_pos hbp hell) (div_pos hcp hell)
    ((div_le_one hell).2 hbL)
    ((div_le_one hell).2 ((triangleAltitudeVector_norm_le hb).trans hcL))
    (c := ⟪triangleUnitDirection b, c⟫_ℝ / ell)
    (x := ⟪triangleUnitDirection b, z - o⟫_ℝ)
    (y := ⟪triangleUnitDirection (triangleAltitudeVector b c), z - o⟫_ℝ)
    (fun p hp => by
      rw [← triangleLatticeAnchor_first o b c ell p hb]
      exact unit_inner_coordinate_bound _ _ _ _ (triangleUnitDirection_norm hb) (hmem p hp))
    (fun p hp => by
      rw [← triangleLatticeAnchor_second o b c ell p hb hc]
      exact unit_inner_coordinate_bound _ _ _ _ (triangleUnitDirection_norm hc) (hmem p hp))
  convert hbound using 1 <;> field_simp [hell.ne', hbp.ne', hcp.ne'] <;> ring

end TriangleFrame

section AnchorGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual lower affine chart has an explicit injective integer lattice index. -/
theorem foldedSquare_lower_lattice (x q₀ q₁ z : E) {ell : ℝ}
    (hell : 0 < ell) (m n : ℤ) (hnm : n ≤ m) :
    foldedSquare x q₀ q₁ z ((m : ℝ) / ell) ((n : ℝ) / ell) =
      triangleLatticeAnchor x (q₀ - x) (z - x) ell (m - n, n) := by
  have h : (n : ℝ) / ell ≤ (m : ℝ) / ell :=
    (div_le_div_iff_of_pos_right hell).2 (by exact_mod_cast hnm)
  simp only [foldedSquare, if_pos h, triangleLatticeAnchor, Int.cast_sub]
  module

/-- The upper chart uses the other actual triangle and the exchanged integer coordinates. -/
theorem foldedSquare_upper_lattice (x q₀ q₁ z : E) {ell : ℝ}
    (hell : 0 < ell) (m n : ℤ) (hmn : m ≤ n) :
    foldedSquare x q₀ q₁ z ((m : ℝ) / ell) ((n : ℝ) / ell) =
      triangleLatticeAnchor x (q₁ - x) (z - x) ell (n - m, m) := by
  have h : (m : ℝ) / ell ≤ (n : ℝ) / ell :=
    (div_le_div_iff_of_pos_right hell).2 (by exact_mod_cast hmn)
  rw [foldedSquare_of_u_le_v x q₀ q₁ z h]
  simp only [triangleLatticeAnchor, Int.cast_sub]
  module

theorem lowerTriangleIndex_injective :
    Function.Injective (fun p : ℤ × ℤ => (p.1 - p.2, p.2)) := by
  intro p q hpq
  have h₀ := congrArg Prod.fst hpq
  have h₁ := congrArg Prod.snd hpq
  apply Prod.ext <;> dsimp at * <;> omega

theorem upperTriangleIndex_injective :
    Function.Injective (fun p : ℤ × ℤ => (p.2 - p.1, p.1)) := by
  intro p q hpq
  have h₀ := congrArg Prod.fst hpq
  have h₁ := congrArg Prod.snd hpq
  apply Prod.ext <;> dsimp at * <;> omega

/-- A genuine face-triangle hit transfers to its actual nearby anchor. -/
theorem triangle_hit_anchor_bound (anchor p q r center : E)
    (hp : dist p anchor ≤ 1) (hq : dist q anchor ≤ 1) (hr : dist r anchor ≤ 1)
    (hhit : (convexHull ℝ {p, q, r} ∩ Metric.closedBall center 1).Nonempty) :
    dist anchor center ≤ 2 := by
  obtain ⟨w, hw, hcenter⟩ := hhit
  have hsub : ({p, q, r} : Set E) ⊆ Metric.closedBall anchor 1 := by
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl <;> assumption
  have hanchor := convexHull_min hsub (convex_closedBall anchor 1) hw
  calc
    dist anchor center ≤ dist anchor w + dist w center := dist_triangle _ _ _
    _ ≤ 1 + 1 := add_le_add (by simpa [dist_comm] using hanchor) hcenter
    _ = 2 := by norm_num

end AnchorGeometry


noncomputable section WidthArea

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Source triangle width expressed directly by distances to all three opposite segments. -/
def TriangleWidthAtLeast (b c : E) (delta : ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → t ≤ 1 → delta ≤ ‖c - t • b‖) ∧
  (∀ t : ℝ, 0 ≤ t → t ≤ 1 → delta ≤ ‖b - t • c‖) ∧
  (∀ t : ℝ, 0 ≤ t → t ≤ 1 → delta ≤ ‖(1 - t) • b + t • c‖)

/-- Twice the triangle area, constructed from the chosen actual base and altitude. -/
def triangleAreaProduct (b c : E) : ℝ := ‖b‖ * ‖triangleAltitudeVector b c‖

theorem triangleAltitudeVector_norm_sq {b c : E} (hb : b ≠ 0) :
    ‖triangleAltitudeVector b c‖ ^ 2 =
      ‖c‖ ^ 2 - ⟪triangleUnitDirection b, c⟫_ℝ ^ 2 := by
  rw [triangleAltitudeVector, norm_sub_sq_real, real_inner_smul_right,
    norm_smul, Real.norm_eq_abs, triangleUnitDirection_norm hb, mul_one,
    sq_abs, real_inner_comm c (triangleUnitDirection b)]
  ring

/-- The Gram determinant certifies the area product without an orientation choice. -/
theorem triangleAreaProduct_sq (b c : E) :
    triangleAreaProduct b c ^ 2 = ‖b‖ ^ 2 * ‖c‖ ^ 2 - ⟪b, c⟫_ℝ ^ 2 := by
  by_cases hb : b = 0
  · subst b
    simp [triangleAreaProduct]
  · rw [triangleAreaProduct, mul_pow, triangleAltitudeVector_norm_sq hb]
    simp only [triangleUnitDirection, real_inner_smul_left]
    have hn : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb
    field_simp [hn]
    <;> ring

theorem triangleAreaProduct_swap (b c : E) :
    triangleAreaProduct b c = triangleAreaProduct c b := by
  have hsq : triangleAreaProduct b c ^ 2 = triangleAreaProduct c b ^ 2 := by
    rw [triangleAreaProduct_sq, triangleAreaProduct_sq, real_inner_comm c b]
    ring
  have hb : 0 ≤ triangleAreaProduct b c := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hc : 0 ≤ triangleAreaProduct c b := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith

theorem triangleAreaProduct_rebase (b c : E) :
    triangleAreaProduct b c = triangleAreaProduct (c - b) (-b) := by
  have hsq : triangleAreaProduct b c ^ 2 = triangleAreaProduct (c - b) (-b) ^ 2 := by
    rw [triangleAreaProduct_sq, triangleAreaProduct_sq, norm_sub_sq_real, norm_neg,
      inner_neg_right, inner_sub_left, real_inner_self_eq_norm_sq,
      real_inner_comm c b]
    ring
  have hb : 0 ≤ triangleAreaProduct b c := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hc : 0 ≤ triangleAreaProduct (c - b) (-b) := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith

/-- The foot on a longest side lies on that segment, so the source segment-width
bound applies to this altitude even when the triangle is obtuse. -/
theorem longest_side_altitude_lower {b c : E} {delta : ℝ} (hb : b ≠ 0)
    (hc : ‖c‖ ≤ ‖b‖) (hbc : ‖c - b‖ ≤ ‖b‖)
    (hwidth : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → delta ≤ ‖c - t • b‖) :
    delta ≤ ‖triangleAltitudeVector b c‖ := by
  have hn : 0 < ‖b‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hb)
  have hsq := norm_sub_sq_real c b
  rw [real_inner_comm b c] at hsq
  have hc2 : ‖c‖ ^ 2 ≤ ‖b‖ ^ 2 := by nlinarith [norm_nonneg c, norm_nonneg b]
  have hbc2 : ‖c - b‖ ^ 2 ≤ ‖b‖ ^ 2 := by
    nlinarith [norm_nonneg (c - b), norm_nonneg b]
  have hi0 : 0 ≤ ⟪b, c⟫_ℝ := by nlinarith [sq_nonneg ‖c‖]
  have hi1 : ⟪b, c⟫_ℝ ≤ ‖b‖ ^ 2 := by nlinarith [sq_nonneg ‖c - b‖]
  have ht0 : 0 ≤ ⟪b, c⟫_ℝ / ‖b‖ ^ 2 := div_nonneg hi0 hn.le
  have ht1 : ⟪b, c⟫_ℝ / ‖b‖ ^ 2 ≤ 1 := (div_le_one hn).2 hi1
  have hd : triangleAltitudeVector b c = c - (⟪b, c⟫_ℝ / ‖b‖ ^ 2) • b := by
    simp only [triangleAltitudeVector, triangleUnitDirection, real_inner_smul_left,
      smul_smul, div_eq_mul_inv, inv_pow]
    module
  rw [hd]
  exact hwidth _ ht0 ht1

/-- Source segment width and original side lengths give the invariant denominator
needed by lattice packing; no altitude lower bound is assumed by the caller. -/
theorem triangleAreaProduct_lower {b c : E} {delta side : ℝ}
    (hside : 0 < side) (hdelta : 0 ≤ delta)
    (hb : side ≤ ‖b‖) (hc : side ≤ ‖c‖) (hbc : side ≤ ‖c - b‖)
    (hwidth : TriangleWidthAtLeast b c delta) :
    side * delta ≤ triangleAreaProduct b c := by
  by_cases hcb : ‖c‖ ≤ ‖b‖
  · by_cases hdb : ‖c - b‖ ≤ ‖b‖
    · have hb0 : b ≠ 0 := norm_pos_iff.mp (hside.trans_le hb)
      exact mul_le_mul hb (longest_side_altitude_lower hb0 hcb hdb hwidth.1)
        hdelta (norm_nonneg b)
    · have hd0 : c - b ≠ 0 := norm_pos_iff.mp (hside.trans_le hbc)
      have hn : ‖-b - (c - b)‖ = ‖c‖ := by
        have he : -b - (c - b) = -c := by abel
        rw [he, norm_neg]
      have hw : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → delta ≤ ‖-b - t • (c - b)‖ := by
        intro t ht0 ht1
        have he : -b - t • (c - b) = -((1 - t) • b + t • c) := by module
        rw [he, norm_neg]
        exact hwidth.2.2 t ht0 ht1
      rw [triangleAreaProduct_rebase]
      exact mul_le_mul hbc (longest_side_altitude_lower hd0
        (by simpa using (lt_of_not_ge hdb).le)
        (by rw [hn]; exact hcb.trans (lt_of_not_ge hdb).le) hw)
        hdelta (norm_nonneg _)
  · by_cases hdc : ‖c - b‖ ≤ ‖c‖
    · have hc0 : c ≠ 0 := norm_pos_iff.mp (hside.trans_le hc)
      rw [triangleAreaProduct_swap]
      exact mul_le_mul hc (longest_side_altitude_lower hc0 (lt_of_not_ge hcb).le
        (by simpa only [norm_sub_rev] using hdc) hwidth.2.1)
        hdelta (norm_nonneg _)
    · have hd0 : c - b ≠ 0 := norm_pos_iff.mp (hside.trans_le hbc)
      have hn : ‖-b - (c - b)‖ = ‖c‖ := by
        have he : -b - (c - b) = -c := by abel
        rw [he, norm_neg]
      have hw : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → delta ≤ ‖-b - t • (c - b)‖ := by
        intro t ht0 ht1
        have he : -b - t • (c - b) = -((1 - t) • b + t • c) := by module
        rw [he, norm_neg]
        exact hwidth.2.2 t ht0 ht1
      rw [triangleAreaProduct_rebase]
      exact mul_le_mul hbc (longest_side_altitude_lower hd0
        (by rw [norm_neg]; exact (lt_of_not_ge hcb).le.trans (lt_of_not_ge hdc).le)
        (by rw [hn]; exact (lt_of_not_ge hdc).le) hw)
        hdelta (norm_nonneg _)

end WidthArea

section WidthPacking
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The finite count uses original side and segment-width hypotheses only. -/
theorem triangle_lattice_card_le_of_width (s : Finset (ℤ × ℤ)) (o b c z : E)
    {ell side delta : ℝ} (hell : 0 < ell) (hside : 0 < side) (hdelta : 0 < delta)
    (hb : side ≤ ‖b‖) (hc : side ≤ ‖c‖) (hbc : side ≤ ‖c - b‖)
    (hbL : ‖b‖ ≤ ell) (hcL : ‖c‖ ≤ ell)
    (hwidth : TriangleWidthAtLeast b c delta)
    (hmem : ∀ p ∈ s, dist (triangleLatticeAnchor o b c ell p) z ≤ 2) :
    (s.card : ℝ) ≤ 8 * Real.pi * ell ^ 2 / (side * delta) := by
  have hprod := triangleAreaProduct_lower hside hdelta.le hb hc hbc hwidth
  have hb0 : b ≠ 0 := norm_pos_iff.mp (hside.trans_le hb)
  have ha0 : triangleAltitudeVector b c ≠ 0 := by
    intro he
    have hpos := mul_pos hside hdelta
    simp [triangleAreaProduct, he] at hprod
    linarith
  exact (triangle_lattice_card_le s o b c z hell hb0 ha0 hbL hcL hmem).trans
    (div_le_div_of_nonneg_left (by positivity) (mul_pos hside hdelta) hprod)

end WidthPacking

noncomputable section GridCornerBounds
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual folded chart evaluated at integer grid parameters. -/
def foldedGridPoint (x q₀ q₁ z : E) (ell : ℝ) (m n : ℤ) : E :=
  foldedSquare x q₀ q₁ z ((m : ℝ) / ell) ((n : ℝ) / ell)

private theorem divided_step_norm_le_one {v : E} {ell : ℝ}
    (hell : 0 < ell) (hv : ‖v‖ ≤ ell) : ‖(1 / ell : ℝ) • v‖ ≤ 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hell)]
  simpa only [one_div_mul_eq_div] using (div_le_one hell).2 hv

/-- Every real corner of a fine cell is within one unit of its lower-left anchor.
The five hypotheses are exactly sides of the two original triangles. -/
theorem foldedGridPoint_corner_dist (x q₀ q₁ z : E) {ell : ℝ}
    (hell : 0 < ell) (m n : ℤ) (a b : BDL26FiniteTannerSquare.Two)
    (h₀ : ‖q₀ - x‖ ≤ ell) (h₁ : ‖q₁ - x‖ ≤ ell) (hz : ‖z - x‖ ≤ ell)
    (hz₀ : ‖z - q₀‖ ≤ ell) (hz₁ : ‖z - q₁‖ ≤ ell) :
    dist (foldedGridPoint x q₀ q₁ z ell (m + a.val) (n + b.val))
      (foldedGridPoint x q₀ q₁ z ell m n) ≤ 1 := by
  have hdiv {i j : ℤ} (h : i ≤ j) : (i : ℝ) / ell ≤ (j : ℝ) / ell :=
    (div_le_div_iff_of_pos_right hell).2 (by exact_mod_cast h)
  fin_cases a <;> fin_cases b
  · simp
  · have he : foldedGridPoint x q₀ q₁ z ell m (n + 1) -
        foldedGridPoint x q₀ q₁ z ell m n =
        if n + 1 ≤ m then (1 / ell : ℝ) • (z - q₀)
        else (1 / ell : ℝ) • (q₁ - x) := by
      by_cases h : n + 1 ≤ m
      · rw [if_pos h]
        simp only [foldedGridPoint, foldedSquare]
        rw [if_pos (hdiv h), if_pos (hdiv (show n ≤ m by omega))]
        simp only [Int.cast_add, Int.cast_one]
        module
      · rw [if_neg h]
        unfold foldedGridPoint
        rw [foldedSquare_of_u_le_v _ _ _ _ (hdiv (show m ≤ n + 1 by omega)),
          foldedSquare_of_u_le_v _ _ _ _ (hdiv (show m ≤ n by omega))]
        simp only [Int.cast_add, Int.cast_one]
        module
    simp only [Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, add_zero]
    rw [dist_eq_norm, he]
    split_ifs <;> exact divided_step_norm_le_one hell (by assumption)
  · have he : foldedGridPoint x q₀ q₁ z ell (m + 1) n -
        foldedGridPoint x q₀ q₁ z ell m n =
        if n ≤ m then (1 / ell : ℝ) • (q₀ - x)
        else (1 / ell : ℝ) • (z - q₁) := by
      by_cases h : n ≤ m
      · rw [if_pos h]
        simp only [foldedGridPoint, foldedSquare]
        rw [if_pos (hdiv h), if_pos (hdiv (show n ≤ m + 1 by omega))]
        simp only [Int.cast_add, Int.cast_one]
        module
      · rw [if_neg h]
        unfold foldedGridPoint
        rw [foldedSquare_of_u_le_v _ _ _ _ (hdiv (show m + 1 ≤ n by omega)),
          foldedSquare_of_u_le_v _ _ _ _ (hdiv (show m ≤ n by omega))]
        simp only [Int.cast_add, Int.cast_one]
        module
    simp only [Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, add_zero]
    rw [dist_eq_norm, he]
    split_ifs <;> exact divided_step_norm_le_one hell (by assumption)
  · have he : foldedGridPoint x q₀ q₁ z ell (m + 1) (n + 1) -
        foldedGridPoint x q₀ q₁ z ell m n = (1 / ell : ℝ) • (z - x) := by
      by_cases h : n ≤ m
      · simp only [foldedGridPoint, foldedSquare]
        rw [if_pos (hdiv h), if_pos (hdiv (show n + 1 ≤ m + 1 by omega))]
        simp only [Int.cast_add, Int.cast_one]
        module
      · unfold foldedGridPoint
        rw [foldedSquare_of_u_le_v _ _ _ _ (hdiv (show m + 1 ≤ n + 1 by omega)),
          foldedSquare_of_u_le_v _ _ _ _ (hdiv (show m ≤ n by omega))]
        simp only [Int.cast_add, Int.cast_one]
        module
    simp only [Fin.val_one, Nat.cast_one]
    rw [dist_eq_norm, he]
    exact divided_step_norm_le_one hell hz

end GridCornerBounds


section MaterializedSlots

/-- The actual planar quadrant has its original face owner and retained endpoint bits. -/
theorem rxFaceSlot_planar (P : TannerSquarePresentation) (S : OddScale) (f : P.Face)
    (i j : Fin S.half) (copy a b : BDL26FiniteTannerSquare.Two) :
    rxFaceSlotEquiv P S (.inl ⟨P.faceX f, .inl (copy, oldFaceInXStar P f, i, j), a, b⟩) =
      (f, .inl (.inl ((copy, i, j), a, b))) := rfl

/-- The actual old-Z quadrant retains its owner and coincident copy label. -/
theorem rxFaceSlot_oldZ (P : TannerSquarePresentation) (S : OddScale) (f : P.Face)
    (copy : BDL26FiniteTannerSquare.Two) :
    rxFaceSlotEquiv P S (.inr (.inr (f, copy))) = (f, .inr (.inr copy)) := rfl

/-- The actual path strip is matched to its unique face by perfect pairing. -/
theorem rxFaceSlot_pathStrip (P : TannerSquarePresentation) (S : OddScale) (f : P.Face)
    (side copy : BDL26FiniteTannerSquare.Two) (i : Fin S.half)
    (endpoint : BDL26FiniteTannerSquare.Two) :
    rxFaceSlotEquiv P S (pathStripFace P S f side copy i endpoint) =
      (f, .inr (.inl (side, .inl (copy, i), endpoint))) := by
  let e := Equiv.ofBijective (faceCornerWedge P) (faceCornerWedge_bijective P)
  have h : e.symm (faceCornerWedge P (f, side)) = (f, side) := e.symm_apply_apply (f, side)
  change (((e.symm (faceCornerWedge P (f, side))).1,
    .inr (.inl ((e.symm (faceCornerWedge P (f, side))).2, .inl (copy, i), endpoint))) : P.Face × PatchSlot S) = _
  rw [h]

/-- The actual terminal rung has the same unique original ordered corner. -/
theorem rxFaceSlot_terminalRung (P : TannerSquarePresentation) (S : OddScale) (f : P.Face)
    (side copy : BDL26FiniteTannerSquare.Two) :
    rxFaceSlotEquiv P S (terminalRungFace P S f side copy) =
      (f, .inr (.inl (side, .inr 0, copy))) := by
  let e := Equiv.ofBijective (faceCornerWedge P) (faceCornerWedge_bijective P)
  have h : e.symm (faceCornerWedge P (f, side)) = (f, side) := e.symm_apply_apply (f, side)
  change (((e.symm (faceCornerWedge P (f, side))).1,
    .inr (.inl ((e.symm (faceCornerWedge P (f, side))).2, .inr 0, copy))) : P.Face × PatchSlot S) = _
  rw [h]

/-- A boundary rectangle is constructed from the very same Q-path segment. -/
def boundaryRectangleFace (P : TannerSquarePresentation) (S : OddScale) (f : P.Face)
    (side copy : BDL26FiniteTannerSquare.Two) (i : Fin S.half)
    (endpoint : BDL26FiniteTannerSquare.Two) : RXFace P S :=
  .inl ⟨P.faceX f,
    .inr (qToXSubdivisionBoundaryEdge P (P.faceQ f side) (P.faceX f)
      (P.data.faceQ_xq f side) S (⟨P.faceZ f, P.data.faceQ_qz f side⟩, i)), copy, endpoint⟩

theorem rxFaceSlot_boundaryRectangle (P : TannerSquarePresentation) (S : OddScale)
    (f : P.Face) (side copy : BDL26FiniteTannerSquare.Two) (i : Fin S.half)
    (endpoint : BDL26FiniteTannerSquare.Two) :
    rxFaceSlotEquiv P S (boundaryRectangleFace P S f side copy i endpoint) =
      (f, .inl (.inr (side, i, copy, endpoint))) := by
  have h : (faceCornerBoundaryEquiv P).symm (faceCornerBoundaryEdge P (f, side)) =
      (f, side) := (faceCornerBoundaryEquiv P).symm_apply_apply (f, side)
  change ((((faceCornerBoundaryEquiv P).symm (faceCornerBoundaryEdge P (f, side))).1,
    .inl (.inr (((faceCornerBoundaryEquiv P).symm
      (faceCornerBoundaryEdge P (f, side))).2, i, copy, endpoint))) : P.Face × PatchSlot S) = _
  rw [h]

end MaterializedSlots

noncomputable section ActualSlotCharging
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Charge a materialized seam to its adjacent materialized positive-family face. -/
def chargePatchSlot (S : OddScale) : PatchSlot S → PatchSlot S
  | .inl (.inl p) => .inl (.inl p)
  | .inl (.inr (side, i, copy, endpoint)) =>
      .inr (.inl (side, .inl (copy, i), endpoint))
  | .inr (.inl (side, .inl edge, endpoint)) => .inr (.inl (side, .inl edge, endpoint))
  | .inr (.inl (_, .inr _, copy)) => .inr (.inr copy)
  | .inr (.inr copy) => .inr (.inr copy)

private theorem rxFaceSlot_inverse_of_forward (P : TannerSquarePresentation) (S : OddScale)
    (actual : RXFace P S) (f : P.Face) (slot : PatchSlot S)
    (h : rxFaceSlotEquiv P S actual = (f, slot)) :
    (rxFaceSlotEquiv P S).symm (f, slot) = actual := by
  rw [← h, Equiv.symm_apply_apply]

/-- The already proved local geometric containments cover every actual slot. -/
theorem actualSlotImage_subset_charge (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (slot : PatchSlot S) :
    rxFaceImage P S J ((rxFaceSlotEquiv P S).symm (f, slot)) ⊆
      rxFaceImage P S J ((rxFaceSlotEquiv P S).symm (f, chargePatchSlot S slot)) := by
  rcases slot with (plane | ⟨side, i, copy, endpoint⟩) | (⟨side, edge, endpoint⟩ | copy)
  · exact Set.Subset.rfl
  · change _ ⊆ rxFaceImage P S J
      ((rxFaceSlotEquiv P S).symm (f, .inr (.inl (side, .inl (copy, i), endpoint))))
    rw [rxFaceSlot_inverse_of_forward P S _ _ _
        (rxFaceSlot_boundaryRectangle P S f side copy i endpoint),
      rxFaceSlot_inverse_of_forward P S _ _ _
        (rxFaceSlot_pathStrip P S f side copy i endpoint)]
    exact rectangle_image_subset_glue P S J (faceXQEdge P f side)
      (⟨P.faceZ f, P.data.faceQ_qz f side⟩, i) copy endpoint
  · rcases edge with edge | last
    · exact Set.Subset.rfl
    · have hl : last = 0 := Subsingleton.elim _ _
      subst last
      change _ ⊆ rxFaceImage P S J ((rxFaceSlotEquiv P S).symm (f, .inr (.inr endpoint)))
      rw [rxFaceSlot_inverse_of_forward P S _ _ _ (rxFaceSlot_terminalRung P S f side endpoint),
        rxFaceSlot_inverse_of_forward P S _ _ _ (rxFaceSlot_oldZ P S f endpoint)]
      exact terminalRung_image_subset_oldZ P S J f side endpoint
  · exact Set.Subset.rfl

/-- Slot charging agrees with the explicit fine-coordinate charging map. -/
theorem chargePatchSlot_flat (S : OddScale) (slot : PatchSlot S) :
    rawFlatCellEquiv S (patchSlotToRawFlat S (chargePatchSlot S slot)) =
      .inl (charge S (rawFlatCellEquiv S (patchSlotToRawFlat S slot))) := by
  rcases slot with (plane | ⟨side, i, copy, endpoint⟩) | (⟨side, edge, endpoint⟩ | copy)
  · rfl
  · fin_cases side <;> simp [chargePatchSlot, patchSlotToRawFlat, rawFlatCellEquiv, charge]
  · rcases edge with edge | last
    · fin_cases side <;> simp [chargePatchSlot, patchSlotToRawFlat, rawFlatCellEquiv, charge]
    · fin_cases side <;> simp [chargePatchSlot, patchSlotToRawFlat, rawFlatCellEquiv, charge]
  · simp [chargePatchSlot, patchSlotToRawFlat, rawFlatCellEquiv, charge]

/-- Actual images indexed by the proved canonical face equivalence. -/
def actualFlatImage (P : TannerSquarePresentation) (S : OddScale) (J : Vertex P → E)
    (c : P.Face × FlatCell S) : Set E := rxFaceImage P S J ((rxFaceFlatEquiv P S).symm c)

/-- All materialized collapsed labels charge geometrically to an actual positive face. -/
theorem actualFlatImage_subset_charge (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (cell : FlatCell S) :
    actualFlatImage P S J (f, cell) ⊆ actualFlatImage P S J (f, .inl (charge S cell)) := by
  let e := (patchSlotRawFlatEquiv S).trans (rawFlatCellEquiv S)
  let slot := e.symm cell
  have hs : e slot = cell := e.apply_symm_apply cell
  have hc : e (chargePatchSlot S slot) = .inl (charge S cell) := by
    change rawFlatCellEquiv S (patchSlotToRawFlat S (chargePatchSlot S slot)) = _
    rw [chargePatchSlot_flat]
    exact congrArg (fun c => Sum.inl (charge S c)) hs
  have h := actualSlotImage_subset_charge P S J f slot
  change rxFaceImage P S J ((rxFaceSlotEquiv P S).symm (f, e.symm cell)) ⊆
    rxFaceImage P S J ((rxFaceSlotEquiv P S).symm (f, e.symm (.inl (charge S cell))))
  rw [← hc, e.symm_apply_apply]
  exact h

/-- The factor three counts every actual collapsed label, including coincident images. -/
theorem actualFlatHits_card_le_three_mul_positive (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (region : Set E) :
    (familyHits (actualFlatImage P S J) region).card ≤
      3 * (familyHits (fun p : P.Face × PositiveCell S =>
        actualFlatImage P S J (p.1, .inl p.2)) region).card :=
  familyHits_card_le_three_mul_positive S (actualFlatImage P S J) region
    (actualFlatImage_subset_charge P S J)

end ActualSlotCharging

section ActualHitReindexing
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Reindexing the actual geometric hit set preserves all labeled multiplicities. -/
theorem actualRXHits_card_eq_flat (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (region : Set E) :
    (familyHits (rxFaceImage P S J) region).card =
      (familyHits (actualFlatImage P S J) region).card := by
  classical
  apply Finset.card_bij (fun f _ => rxFaceFlatEquiv P S f)
  · intro f hf
    simp only [familyHits, Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    simpa only [actualFlatImage, Equiv.symm_apply_apply] using hf
  · intro f _ g _ h
    exact (rxFaceFlatEquiv P S).injective h
  · intro c hc
    refine ⟨(rxFaceFlatEquiv P S).symm c, ?_, (rxFaceFlatEquiv P S).apply_symm_apply c⟩
    have hhit : (actualFlatImage P S J c ∩ region).Nonempty :=
      (Finset.mem_filter.mp hc).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hhit⟩

end ActualHitReindexing


noncomputable section PathStripFineCoordinates
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Every actual Q-path endpoint has its coarse-grid endpoint parameter. -/
theorem pathStripFaceQ1_linear (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (side copy : BDL26FiniteTannerSquare.Two)
    (i : Fin S.half) (endpoint : BDL26FiniteTannerSquare.Two) :
    rxOnePoint P S J (rxFaceQ P S (pathStripFace P S f side copy i endpoint) 1) =
      (1 - 2 * ((gridEndpoint i endpoint).val : ℝ) / S.ell) • J (.q (P.faceQ f side)) +
        (2 * ((gridEndpoint i endpoint).val : ℝ) / S.ell) • J (.z (P.faceZ f)) := by
  fin_cases endpoint
  · simpa [pathStripFace, rxFaceQ, twoSelect_one, glueFaceQ1, BDL26RXLocalReplacement.edgeEndpoint, twoSelect,
      twoSelect_zero, qDoubleCylinderEdgeStart, rxOnePoint, gridEndpoint,
      lowerGridIndex] using
      qSubdivisionEdgeStart_point P S J (P.faceQ f side)
        ⟨P.faceZ f, P.data.faceQ_qz f side⟩ i
  · simpa [pathStripFace, rxFaceQ, twoSelect_one, glueFaceQ1, BDL26RXLocalReplacement.edgeEndpoint, twoSelect,
      qDoubleCylinderEdgeEnd, rxOnePoint, gridEndpoint, upperGridIndex, Nat.cast_add,
      Nat.cast_one] using
      qSubdivisionEdgeEnd_point P S J (P.faceQ f side)
        ⟨P.faceZ f, P.data.faceQ_qz f side⟩ i

private theorem gridEndpoint_parameter_le_ratio (S : OddScale) (i : Fin S.half)
    (endpoint : BDL26FiniteTannerSquare.Two) :
    2 * ((gridEndpoint i endpoint).val : ℝ) / S.ell ≤ contractionRatio S := by
  have hell : (0 : ℝ) < S.ell := by exact_mod_cast (show 0 < S.ell by have := S.three_le; omega)
  apply (div_le_div_iff_of_pos_right hell).2
  exact_mod_cast Nat.mul_le_mul_left 2 (Nat.le_of_lt_succ (gridEndpoint i endpoint).isLt)

private theorem gridMidpoint_parameter_le_ratio (S : OddScale) (i : Fin S.half) :
    (2 * (i.val : ℝ) + 1) / S.ell ≤ contractionRatio S := by
  have hell : (0 : ℝ) < S.ell := by exact_mod_cast (show 0 < S.ell by have := S.three_le; omega)
  apply (div_le_div_iff_of_pos_right hell).2
  have hi : (i.val : ℝ) + 1 ≤ S.half := by exact_mod_cast (show i.val + 1 ≤ S.half by omega)
  linarith

/-- A path-strip endpoint on the outer edge has its actual folded-chart coordinate. -/
theorem pathStripFaceQ1_fine (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (copy : BDL26FiniteTannerSquare.Two)
    (i : Fin S.half) (endpoint : BDL26FiniteTannerSquare.Two) :
    rxOnePoint P S J (rxFaceQ P S (pathStripFace P S f 0 copy i endpoint) 1) =
      facePoint P J f 1 (2 * ((gridEndpoint i endpoint).val : ℝ) / S.ell) := by
  rw [pathStripFaceQ1_linear]
  simp only [facePoint, foldedSquare_right _ _ _ _ _
    ((gridEndpoint_parameter_le_ratio S i endpoint).trans (contractionRatio_bounds S).2.le)]

/-- The X corner lies on the inner edge of the final fine-grid column. -/
theorem pathStripFaceX_fine (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (copy : BDL26FiniteTannerSquare.Two)
    (i : Fin S.half) (endpoint : BDL26FiniteTannerSquare.Two) :
    rxZeroPoint P S J (rxFaceX P S (pathStripFace P S f 0 copy i endpoint)) =
      facePoint P J f (contractionRatio S) (2 * ((gridEndpoint i endpoint).val : ℝ) / S.ell) := by
  have h := glueFaceX_point_offset P S J (faceXQEdge P f 0)
    (.inl (copy, ⟨P.faceZ f, P.data.faceQ_qz f 0⟩, i)) endpoint
  rw [show rxZeroPoint P S J (rxFaceX P S (pathStripFace P S f 0 copy i endpoint)) =
    (1 - contractionRatio S) • J (.x (P.faceX f)) +
      rxOnePoint P S J (rxFaceQ P S (pathStripFace P S f 0 copy i endpoint) 1) -
      (1 - contractionRatio S) • J (.q (P.faceQ f 0)) from h]
  rw [pathStripFaceQ1_linear]
  simp only [facePoint, foldedSquare, if_pos (gridEndpoint_parameter_le_ratio S i endpoint)]
  module

/-- The same-edge Q midpoint is the inner edge midpoint of that fine column. -/
theorem pathStripFaceQ0_fine (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (copy : BDL26FiniteTannerSquare.Two)
    (i : Fin S.half) (endpoint : BDL26FiniteTannerSquare.Two) :
    rxOnePoint P S J (rxFaceQ P S (pathStripFace P S f 0 copy i endpoint) 0) =
      facePoint P J f (contractionRatio S) ((2 * (i.val : ℝ) + 1) / S.ell) := by
  have h := glueFaceQ0_point_offset P S J (faceXQEdge P f 0)
    (.inl (copy, ⟨P.faceZ f, P.data.faceQ_qz f 0⟩, i)) endpoint
  rw [show rxOnePoint P S J (rxFaceQ P S (pathStripFace P S f 0 copy i endpoint) 0) =
    (1 - contractionRatio S) • J (.x (P.faceX f)) +
      rxTwoPoint P S J (rxFaceZ P S (pathStripFace P S f 0 copy i endpoint)) -
      (1 - contractionRatio S) • J (.q (P.faceQ f 0)) from h]
  rw [pathStripFaceZ_point]
  simp only [facePoint, foldedSquare, if_pos (gridMidpoint_parameter_le_ratio S i)]
  module

end PathStripFineCoordinates

noncomputable section PathStripUpperFineCoordinates
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem pathStripFaceZ_fine (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (copy : BDL26FiniteTannerSquare.Two)
    (i : Fin S.half) (endpoint : BDL26FiniteTannerSquare.Two) :
    rxTwoPoint P S J (rxFaceZ P S (pathStripFace P S f 0 copy i endpoint)) =
      facePoint P J f 1 ((2 * (i.val : ℝ) + 1) / S.ell) := by
  rw [pathStripFaceZ_point]
  simp only [facePoint, foldedSquare_right _ _ _ _ _
    ((gridMidpoint_parameter_le_ratio S i).trans (contractionRatio_bounds S).2.le)]

theorem pathStripFaceQ1_fine_upper (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (copy : BDL26FiniteTannerSquare.Two)
    (i : Fin S.half) (endpoint : BDL26FiniteTannerSquare.Two) :
    rxOnePoint P S J (rxFaceQ P S (pathStripFace P S f 1 copy i endpoint) 1) =
      facePoint P J f (2 * ((gridEndpoint i endpoint).val : ℝ) / S.ell) 1 := by
  rw [pathStripFaceQ1_linear]
  simp only [facePoint, foldedSquare_top _ _ _ _ _
    ((gridEndpoint_parameter_le_ratio S i endpoint).trans (contractionRatio_bounds S).2.le)]

theorem pathStripFaceX_fine_upper (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (copy : BDL26FiniteTannerSquare.Two)
    (i : Fin S.half) (endpoint : BDL26FiniteTannerSquare.Two) :
    rxZeroPoint P S J (rxFaceX P S (pathStripFace P S f 1 copy i endpoint)) =
      facePoint P J f (2 * ((gridEndpoint i endpoint).val : ℝ) / S.ell) (contractionRatio S) := by
  have h := glueFaceX_point_offset P S J (faceXQEdge P f 1)
    (.inl (copy, ⟨P.faceZ f, P.data.faceQ_qz f 1⟩, i)) endpoint
  rw [show rxZeroPoint P S J (rxFaceX P S (pathStripFace P S f 1 copy i endpoint)) =
    (1 - contractionRatio S) • J (.x (P.faceX f)) +
      rxOnePoint P S J (rxFaceQ P S (pathStripFace P S f 1 copy i endpoint) 1) -
      (1 - contractionRatio S) • J (.q (P.faceQ f 1)) from h]
  rw [pathStripFaceQ1_linear]
  simp only [facePoint]
  rw [foldedSquare_of_u_le_v _ _ _ _ (gridEndpoint_parameter_le_ratio S i endpoint)]
  module

theorem pathStripFaceQ0_fine_upper (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (copy : BDL26FiniteTannerSquare.Two)
    (i : Fin S.half) (endpoint : BDL26FiniteTannerSquare.Two) :
    rxOnePoint P S J (rxFaceQ P S (pathStripFace P S f 1 copy i endpoint) 0) =
      facePoint P J f ((2 * (i.val : ℝ) + 1) / S.ell) (contractionRatio S) := by
  have h := glueFaceQ0_point_offset P S J (faceXQEdge P f 1)
    (.inl (copy, ⟨P.faceZ f, P.data.faceQ_qz f 1⟩, i)) endpoint
  rw [show rxOnePoint P S J (rxFaceQ P S (pathStripFace P S f 1 copy i endpoint) 0) =
    (1 - contractionRatio S) • J (.x (P.faceX f)) +
      rxTwoPoint P S J (rxFaceZ P S (pathStripFace P S f 1 copy i endpoint)) -
      (1 - contractionRatio S) • J (.q (P.faceQ f 1)) from h]
  rw [pathStripFaceZ_point]
  simp only [facePoint]
  rw [foldedSquare_of_u_le_v _ _ _ _ (gridMidpoint_parameter_le_ratio S i)]
  module

theorem pathStripFaceZ_fine_upper (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (copy : BDL26FiniteTannerSquare.Two)
    (i : Fin S.half) (endpoint : BDL26FiniteTannerSquare.Two) :
    rxTwoPoint P S J (rxFaceZ P S (pathStripFace P S f 1 copy i endpoint)) =
      facePoint P J f ((2 * (i.val : ℝ) + 1) / S.ell) 1 := by
  rw [pathStripFaceZ_point]
  simp only [facePoint, foldedSquare_top _ _ _ _ _
    ((gridMidpoint_parameter_le_ratio S i).trans (contractionRatio_bounds S).2.le)]

end PathStripUpperFineCoordinates

section LabeledTrianglePacking
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Two retained copy labels cost exactly a factor two, even when their images coincide.
The numerical estimate is derived from the actual anchor geometry and incoming width. -/
theorem labeled_triangle_fiber_card_le {Label : Type*} (s : Finset Label)
    (copy : Label → Fin 2) (index : Label → ℤ × ℤ)
    (hinj : Set.InjOn (fun f => (copy f, index f)) (s : Set Label))
    (o b c z : E) {ell side delta : ℝ}
    (hell : 0 < ell) (hside : 0 < side) (hdelta : 0 < delta)
    (hb : side ≤ ‖b‖) (hc : side ≤ ‖c‖) (hbc : side ≤ ‖c - b‖)
    (hbL : ‖b‖ ≤ ell) (hcL : ‖c‖ ≤ ell)
    (hwidth : TriangleWidthAtLeast b c delta)
    (hmem : ∀ f ∈ s, dist (triangleLatticeAnchor o b c ell (index f)) z ≤ 2) :
    (s.card : ℝ) ≤ 16 * Real.pi * ell ^ 2 / (side * delta) := by
  classical
  let points := s.image index
  have hcard : s.card ≤ ((Finset.univ : Finset (Fin 2)) ×ˢ points).card := by
    apply Finset.card_le_card_of_injOn (fun f => (copy f, index f))
    · intro f hf
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_image_of_mem index hf⟩
    · exact hinj
  have hcount := triangle_lattice_card_le_of_width points o b c z hell hside hdelta
    hb hc hbc hbL hcL hwidth (fun p hp => by
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hp
      exact hmem f hf)
  have hcardR : (s.card : ℝ) ≤ 2 * (points.card : ℝ) := by
    exact_mod_cast (by simpa using hcard : s.card ≤ 2 * points.card)
  calc
    (s.card : ℝ) ≤ 2 * (points.card : ℝ) := hcardR
    _ ≤ 2 * (8 * Real.pi * ell ^ 2 / (side * delta)) :=
      mul_le_mul_of_nonneg_left hcount (by norm_num)
    _ = 16 * Real.pi * ell ^ 2 / (side * delta) := by ring

end LabeledTrianglePacking


noncomputable section PlanarFineCorners
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The endpoint bit is the actual lower/upper integer increment. -/
theorem gridEndpoint_val_add {n : Nat} (i : Fin n) (a : BDL26FiniteTannerSquare.Two) :
    (gridEndpoint i a).val = i.val + a.val := by
  fin_cases a <;> simp [gridEndpoint, twoSelect, lowerGridIndex, upperGridIndex]

/-- Complementing a retained two-valued endpoint has the expected integer coordinate. -/
@[simp] theorem two_complement_val (a : BDL26FiniteTannerSquare.Two) :
    (1 - a).val = 1 - a.val := by
  fin_cases a <;> rfl

/-- Actual fine-grid corners preserve both endpoint labels and the original face. -/
def faceFineCorner (P : TannerSquarePresentation) (S : OddScale) (J : Vertex P → E)
    (f : P.Face) (m n : ℤ) (a b : BDL26FiniteTannerSquare.Two) : E :=
  foldedGridPoint (J (.x (P.faceX f))) (J (.q (P.faceQ f 0)))
    (J (.q (P.faceQ f 1))) (J (.z (P.faceZ f))) S.ell (m + a.val) (n + b.val)

/-- A planar quadrant's X corner is a genuine corner of its assigned fine cell. -/
theorem planarFaceX_fineCorner (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (f : XStarFace P x) (i j : Fin S.half)
    (copy a b : BDL26FiniteTannerSquare.Two) :
    rxZeroPoint P S J (localFaceX P S ⟨x, .inl (copy, f, i, j), a, b⟩) =
      faceFineCorner P S J f.1 (2 * (i.val : ℤ) + a.val) (2 * (j.val : ℤ) + b.val) a b := by
  rw [planarFaceX_point]
  unfold facePoint faceFineCorner foldedGridPoint
  congr 1 <;> simp only [gridEndpoint_val_add, Int.cast_add, Int.cast_mul,
    Int.cast_ofNat, Int.cast_natCast, Nat.cast_add] <;> ring

/-- The horizontal Q corner uses the complementary horizontal endpoint bit. -/
theorem planarFaceQ0_fineCorner (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (f : XStarFace P x) (i j : Fin S.half)
    (copy a b : BDL26FiniteTannerSquare.Two) :
    rxOnePoint P S J (localFaceQ0 P S ⟨x, .inl (copy, f, i, j), a, b⟩) =
      faceFineCorner P S J f.1 (2 * (i.val : ℤ) + a.val) (2 * (j.val : ℤ) + b.val) (1 - a) b := by
  rw [planarFaceQ0_point]
  unfold facePoint faceFineCorner foldedGridPoint
  fin_cases a <;> norm_num only [two_complement_val, Fin.val_zero, Fin.val_one, sub_self, sub_zero,
    gridEndpoint_val_add, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
    Nat.cast_add, Nat.cast_zero, Nat.cast_one]
  all_goals congr 1 <;> ring

/-- The vertical Q corner uses the complementary vertical endpoint bit. -/
theorem planarFaceQ1_fineCorner (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (f : XStarFace P x) (i j : Fin S.half)
    (copy a b : BDL26FiniteTannerSquare.Two) :
    rxOnePoint P S J (localFaceQ1 P S ⟨x, .inl (copy, f, i, j), a, b⟩) =
      faceFineCorner P S J f.1 (2 * (i.val : ℤ) + a.val) (2 * (j.val : ℤ) + b.val) a (1 - b) := by
  rw [planarFaceQ1_point]
  unfold facePoint faceFineCorner foldedGridPoint
  fin_cases b <;> norm_num only [two_complement_val, Fin.val_zero, Fin.val_one, sub_self, sub_zero,
    gridEndpoint_val_add, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
    Nat.cast_add, Nat.cast_zero, Nat.cast_one]
  all_goals congr 1 <;> ring

/-- The actual local center is the fine-cell corner opposite the actual X corner. -/
theorem planarFaceZ_fineCorner (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (f : XStarFace P x) (i j : Fin S.half)
    (copy a b : BDL26FiniteTannerSquare.Two) :
    rxTwoPoint P S J (localFaceZ P S ⟨x, .inl (copy, f, i, j), a, b⟩) =
      faceFineCorner P S J f.1 (2 * (i.val : ℤ) + a.val) (2 * (j.val : ℤ) + b.val)
        (1 - a) (1 - b) := by
  rw [planarFaceZ_point]
  unfold facePoint faceFineCorner foldedGridPoint
  fin_cases a <;> fin_cases b <;> norm_num only [two_complement_val, Fin.val_zero, Fin.val_one, sub_self,
    sub_zero, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, Nat.cast_zero, Nat.cast_one]
  all_goals congr 1 <;> ring

end PlanarFineCorners

noncomputable section IncomingTriangles
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Incoming triangle labels retain the old face and its ordered Q corner. -/
def oldTriangleImage (P : TannerSquarePresentation) (J : Vertex P → E)
    (t : P.Face × BDL26FiniteTannerSquare.Two) : Set E :=
  convexHull ℝ {J (.x (P.faceX t.1)), J (.q (P.faceQ t.1 t.2)), J (.z (P.faceZ t.1))}

/-- The actual lower-left anchor of an old face's integer fine cell. -/
def faceFineAnchor (P : TannerSquarePresentation) (S : OddScale) (J : Vertex P → E)
    (f : P.Face) (m n : ℤ) : E :=
  foldedGridPoint (J (.x (P.faceX f))) (J (.q (P.faceQ f 0)))
    (J (.q (P.faceQ f 1))) (J (.z (P.faceZ f))) S.ell m n

/-- Integer parameter inequalities put a genuine fine corner in the old lower triangle. -/
theorem faceFineCorner_mem_lower (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (m n : ℤ) (a b : BDL26FiniteTannerSquare.Two)
    (hu : m + a.val ≤ (S.ell : ℤ)) (hv : 0 ≤ n + b.val)
    (hvu : n + b.val ≤ m + a.val) :
    faceFineCorner P S J f m n a b ∈ oldTriangleImage P J (f, 0) := by
  have hell : (0 : ℝ) < S.ell := by
    exact_mod_cast (show 0 < S.ell by have := S.three_le; omega)
  exact foldedSquare_mem_lower_triangle _ _ _ _
    ((div_le_one hell).2 (by exact_mod_cast hu))
    (div_nonneg (by exact_mod_cast hv) hell.le)
    ((div_le_div_iff_of_pos_right hell).2 (by exact_mod_cast hvu))

/-- The upper chart uses the second actual incoming triangle, including its diagonal. -/
theorem faceFineCorner_mem_upper (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (m n : ℤ) (a b : BDL26FiniteTannerSquare.Two)
    (hv : n + b.val ≤ (S.ell : ℤ)) (hu : 0 ≤ m + a.val)
    (huv : m + a.val ≤ n + b.val) :
    faceFineCorner P S J f m n a b ∈ oldTriangleImage P J (f, 1) := by
  have hell : (0 : ℝ) < S.ell := by
    exact_mod_cast (show 0 < S.ell by have := S.three_le; omega)
  have h := foldedSquare_mem_upper_triangle
    (J (.x (P.faceX f))) (J (.q (P.faceQ f 0))) (J (.q (P.faceQ f 1)))
    (J (.z (P.faceZ f)))
    (u := (((m + a.val : ℤ) : ℝ) / S.ell))
    (v := (((n + b.val : ℤ) : ℝ) / S.ell))
    ((div_le_one hell).2 (by exact_mod_cast hv))
    (div_nonneg (by exact_mod_cast hu) hell.le)
    ((div_le_div_iff_of_pos_right hell).2 (by exact_mod_cast huv))
  have hs : ({J (.x (P.faceX f)), J (.z (P.faceZ f)), J (.q (P.faceQ f 1))} : Set E) =
      {J (.x (P.faceX f)), J (.q (P.faceQ f 1)), J (.z (P.faceZ f))} := by
    ext v
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [hs] at h
  exact h

/-- The metric corner estimate is attached to the actual original-face coordinates. -/
theorem faceFineCorner_dist_anchor (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (m n : ℤ) (a b : BDL26FiniteTannerSquare.Two)
    (h₀ : ‖J (.q (P.faceQ f 0)) - J (.x (P.faceX f))‖ ≤ S.ell)
    (h₁ : ‖J (.q (P.faceQ f 1)) - J (.x (P.faceX f))‖ ≤ S.ell)
    (hz : ‖J (.z (P.faceZ f)) - J (.x (P.faceX f))‖ ≤ S.ell)
    (hz₀ : ‖J (.z (P.faceZ f)) - J (.q (P.faceQ f 0))‖ ≤ S.ell)
    (hz₁ : ‖J (.z (P.faceZ f)) - J (.q (P.faceQ f 1))‖ ≤ S.ell) :
    dist (faceFineCorner P S J f m n a b) (faceFineAnchor P S J f m n) ≤ 1 :=
  foldedGridPoint_corner_dist _ _ _ _
    (by exact_mod_cast (show 0 < S.ell by have := S.three_le; omega))
    m n a b h₀ h₁ hz hz₀ hz₁

end IncomingTriangles

section WidthPermutation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Source segment width is independent of the order of the two non-origin vertices. -/
theorem TriangleWidthAtLeast.swap {b c : E} {delta : ℝ}
    (h : TriangleWidthAtLeast b c delta) : TriangleWidthAtLeast c b delta := by
  refine ⟨h.2.1, h.1, ?_⟩
  intro t ht0 ht1
  have he : (1 - t) • c + t • b = (1 - (1 - t)) • b + (1 - t) • c := by module
  rw [he]
  exact h.2.2 (1 - t) (by linarith) (by linarith)

/-- Moving the origin to an existing triangle vertex preserves the same segment width. -/
theorem TriangleWidthAtLeast.rebase {b c : E} {delta : ℝ}
    (h : TriangleWidthAtLeast b c delta) : TriangleWidthAtLeast (c - b) (-b) delta := by
  constructor
  · intro t ht0 ht1
    have he : -b - t • (c - b) = -((1 - t) • b + t • c) := by module
    rw [he, norm_neg]
    exact h.2.2 t ht0 ht1
  constructor
  · intro t ht0 ht1
    have he : (c - b) - t • (-b) = c - (1 - t) • b := by module
    rw [he]
    exact h.1 (1 - t) (by linarith) (by linarith)
  · intro t ht0 ht1
    have he : (1 - t) • (c - b) + t • (-b) = -(b - (1 - t) • c) := by module
    rw [he, norm_neg]
    exact h.2.1 (1 - t) (by linarith) (by linarith)

/-- Swapping the original X/Z vertices, as in the actual RZ adapter, preserves width. -/
theorem TriangleWidthAtLeast.transpose {b c : E} {delta : ℝ}
    (h : TriangleWidthAtLeast b c delta) : TriangleWidthAtLeast (b - c) (-c) delta :=
  h.swap.rebase

end WidthPermutation

noncomputable section ActualPositiveFaces
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The explicit fine-coordinate equivalence on positive-family labels. -/
def rawPositiveCellEquiv (S : OddScale) : RawPositiveCell S ≃ PositiveCell S :=
  Equiv.prodCongr (Equiv.refl _)
    (Equiv.prodCongr (fineCoordinateEquiv S) (fineCoordinateEquiv S))

/-- Every positive-family face is constructed by its actual materialized constructor. -/
def rawPositiveFace (P : TannerSquarePresentation) (S : OddScale) (f : P.Face) :
    RawPositiveCell S → RXFace P S
  | (copy, .inl (i, a), .inl (j, b)) =>
      .inl ⟨P.faceX f, .inl (copy, oldFaceInXStar P f, i, j), a, b⟩
  | (copy, .inr _, .inl (i, endpoint)) => pathStripFace P S f 0 copy i endpoint
  | (copy, .inl (i, endpoint), .inr _) => pathStripFace P S f 1 copy i endpoint
  | (copy, .inr _, .inr _) => .inr (.inr (f, copy))

/-- Exact owner/slot correspondence for the constructed positive family. -/
theorem rawPositiveFace_slot (P : TannerSquarePresentation) (S : OddScale)
    (f : P.Face) (c : RawPositiveCell S) :
    rxFaceSlotEquiv P S (rawPositiveFace P S f c) =
      (f, rawFlatToPatchSlot S (.inl c)) := by
  rcases c with ⟨copy, (⟨i, a⟩ | last), (⟨j, b⟩ | last')⟩
  · exact rxFaceSlot_planar P S f i j copy a b
  · exact rxFaceSlot_pathStrip P S f 1 copy i a
  · exact rxFaceSlot_pathStrip P S f 0 copy j b
  · exact rxFaceSlot_oldZ P S f copy

/-- The materialized positive face has the displayed integer fine coordinates. -/
theorem rawPositiveFace_flat (P : TannerSquarePresentation) (S : OddScale)
    (f : P.Face) (c : RawPositiveCell S) :
    rxFaceFlatEquiv P S (rawPositiveFace P S f c) = (f, .inl (rawPositiveCellEquiv S c)) := by
  change (Equiv.prodCongr (Equiv.refl _)
    ((patchSlotRawFlatEquiv S).trans (rawFlatCellEquiv S)))
      (rxFaceSlotEquiv P S (rawPositiveFace P S f c)) = _
  rw [rawPositiveFace_slot]
  change (f, rawFlatCellEquiv S ((patchSlotRawFlatEquiv S)
    ((patchSlotRawFlatEquiv S).symm (.inl c)))) = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- Reindexing never replaces the actual image by a cardinality-chosen model. -/
theorem actualFlatImage_raw_positive (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (c : RawPositiveCell S) :
    actualFlatImage P S J (f, .inl (rawPositiveCellEquiv S c)) =
      rxFaceImage P S J (rawPositiveFace P S f c) := by
  unfold actualFlatImage
  rw [← rawPositiveFace_flat, Equiv.symm_apply_apply]

/-- A fine quadrant retains the actual X-Z diagonal, including its orientation bits. -/
def fineQuadrantImage (P : TannerSquarePresentation) (S : OddScale) (J : Vertex P → E)
    (f : P.Face) (m n : ℤ) (a b : BDL26FiniteTannerSquare.Two) : Set E :=
  convexHull ℝ {faceFineCorner P S J f m n a b,
    faceFineCorner P S J f m n (1 - a) b,
    faceFineCorner P S J f m n (1 - a) (1 - b)} ∪
  convexHull ℝ {faceFineCorner P S J f m n a b,
    faceFineCorner P S J f m n (1 - a) (1 - b),
    faceFineCorner P S J f m n a (1 - b)}

/-- All four actual planar corners identify the whole materialized planar image. -/
theorem rawPositiveFace_planar_image (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (i j : Fin S.half)
    (copy a b : BDL26FiniteTannerSquare.Two) :
    rxFaceImage P S J (rawPositiveFace P S f (copy, .inl (i, a), .inl (j, b))) =
      fineQuadrantImage P S J f (2 * (i.val : ℤ) + a.val) (2 * (j.val : ℤ) + b.val) a b := by
  simp only [rawPositiveFace, rxFaceImage, rxFaceX, rxFaceQ, rxFaceZ,
    twoSelect_zero, twoSelect_one, planarFaceX_fineCorner, planarFaceQ0_fineCorner,
    planarFaceQ1_fineCorner, planarFaceZ_fineCorner, fineQuadrantImage]
  rfl

end ActualPositiveFaces

section ActualTriangleIndices
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Interior endpoint bits remain explicit; the final strip starts at its lower edge. -/
def fineEndpointBit (S : OddScale) : FineCoordinate S → BDL26FiniteTannerSquare.Two
  | .inl (_, a) => a
  | .inr _ => 0

/-- Each selected old triangle has its explicit shear-lattice index. -/
def triangleGridIndex (side : BDL26FiniteTannerSquare.Two) (p : ℤ × ℤ) : ℤ × ℤ :=
  if side = 0 then (p.1 - p.2, p.2) else (p.2 - p.1, p.1)

theorem triangleGridIndex_injective (side : BDL26FiniteTannerSquare.Two) :
    Function.Injective (triangleGridIndex side) := by
  intro p q h
  by_cases hs : side = 0
  · simp only [triangleGridIndex, if_pos hs] at h
    exact lowerTriangleIndex_injective h
  · simp only [triangleGridIndex, if_neg hs] at h
    exact upperTriangleIndex_injective h

/-- The canonical actual face anchor is exactly the selected lower-chart lattice point. -/
theorem faceFineAnchor_lower_lattice (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (m n : ℤ) (h : n ≤ m) :
    faceFineAnchor P S J f m n =
      triangleLatticeAnchor (J (.x (P.faceX f)))
        (J (.q (P.faceQ f 0)) - J (.x (P.faceX f)))
        (J (.z (P.faceZ f)) - J (.x (P.faceX f))) S.ell
        (triangleGridIndex 0 (m, n)) := by
  simpa [faceFineAnchor, foldedGridPoint, triangleGridIndex] using
    foldedSquare_lower_lattice (J (.x (P.faceX f))) (J (.q (P.faceQ f 0)))
      (J (.q (P.faceQ f 1))) (J (.z (P.faceZ f)))
      (by exact_mod_cast (show 0 < S.ell by have := S.three_le; omega)) m n h

/-- The same actual anchor uses the upper triangle's explicitly exchanged lattice coordinates. -/
theorem faceFineAnchor_upper_lattice (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (m n : ℤ) (h : m ≤ n) :
    faceFineAnchor P S J f m n =
      triangleLatticeAnchor (J (.x (P.faceX f)))
        (J (.q (P.faceQ f 1)) - J (.x (P.faceX f)))
        (J (.z (P.faceZ f)) - J (.x (P.faceX f))) S.ell
        (triangleGridIndex 1 (m, n)) := by
  simpa [faceFineAnchor, foldedGridPoint, triangleGridIndex] using
    foldedSquare_upper_lattice (J (.x (P.faceX f))) (J (.q (P.faceQ f 0)))
      (J (.q (P.faceQ f 1))) (J (.z (P.faceZ f)))
      (by exact_mod_cast (show 0 < S.ell by have := S.three_le; omega)) m n h

end ActualTriangleIndices

/-- Equal actual fine coordinates have equal endpoint bits, including the last strip. -/
theorem fineEndpointBit_eq_of_coordinate_eq (S : OddScale) (i j : FineCoordinate S)
    (h : ((fineCoordinateEquiv S i).val : ℤ) = ((fineCoordinateEquiv S j).val : ℤ)) :
    fineEndpointBit S i = fineEndpointBit S j := by
  apply congrArg (fineEndpointBit S)
  apply (fineCoordinateEquiv S).injective
  apply Fin.ext
  exact_mod_cast h

section FineTriangleAssignment
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem convexHull_triple_subset {C : Set E} {p q r : E}
    (hC : Convex ℝ C) (hp : p ∈ C) (hq : q ∈ C) (hr : r ∈ C) :
    convexHull ℝ {p, q, r} ⊆ C :=
  convexHull_min (by
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hp, hq, hr⟩) hC

/-- A fine cell strictly below the fold stays in the actual old lower triangle. -/
theorem fineQuadrantImage_subset_lower (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (m n : ℤ) (a b : BDL26FiniteTannerSquare.Two)
    (hm : m + 1 ≤ (S.ell : ℤ)) (hn : 0 ≤ n) (hnm : n + 1 ≤ m) :
    fineQuadrantImage P S J f m n a b ⊆ oldTriangleImage P J (f, 0) := by
  have hc (u v : BDL26FiniteTannerSquare.Two) :
      faceFineCorner P S J f m n u v ∈ oldTriangleImage P J (f, 0) := by
    apply faceFineCorner_mem_lower
    all_goals have hu := u.isLt; have hv := v.isLt; omega
  exact Set.union_subset
    (convexHull_triple_subset (convex_convexHull ℝ _) (hc _ _) (hc _ _) (hc _ _))
    (convexHull_triple_subset (convex_convexHull ℝ _) (hc _ _) (hc _ _) (hc _ _))

/-- A fine cell strictly above the fold stays in the actual old upper triangle. -/
theorem fineQuadrantImage_subset_upper (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (m n : ℤ) (a b : BDL26FiniteTannerSquare.Two)
    (hn : n + 1 ≤ (S.ell : ℤ)) (hm : 0 ≤ m) (hmn : m + 1 ≤ n) :
    fineQuadrantImage P S J f m n a b ⊆ oldTriangleImage P J (f, 1) := by
  have hc (u v : BDL26FiniteTannerSquare.Two) :
      faceFineCorner P S J f m n u v ∈ oldTriangleImage P J (f, 1) := by
    apply faceFineCorner_mem_upper
    all_goals have hu := u.isLt; have hv := v.isLt; omega
  exact Set.union_subset
    (convexHull_triple_subset (convex_convexHull ℝ _) (hc _ _) (hc _ _) (hc _ _))
    (convexHull_triple_subset (convex_convexHull ℝ _) (hc _ _) (hc _ _) (hc _ _))

/-- Diagonal cells use their actual diagonal triangulation, never the tetrahedral hull. -/
theorem fineQuadrantImage_diagonal_subset (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (m : ℤ) (a : BDL26FiniteTannerSquare.Two)
    (hm0 : 0 ≤ m) (hm1 : m + 1 ≤ (S.ell : ℤ)) :
    fineQuadrantImage P S J f m m a a ⊆
      oldTriangleImage P J (f, 0) ∪ oldTriangleImage P J (f, 1) := by
  have hlow (u v : BDL26FiniteTannerSquare.Two) (hvu : v.val ≤ u.val) :
      faceFineCorner P S J f m m u v ∈ oldTriangleImage P J (f, 0) := by
    apply faceFineCorner_mem_lower
    all_goals have hu := u.isLt; have hv := v.isLt; omega
  have hupp (u v : BDL26FiniteTannerSquare.Two) (huv : u.val ≤ v.val) :
      faceFineCorner P S J f m m u v ∈ oldTriangleImage P J (f, 1) := by
    apply faceFineCorner_mem_upper
    all_goals have hu := u.isLt; have hv := v.isLt; omega
  fin_cases a
  · simp only [fineQuadrantImage, show (1 - (0 : BDL26FiniteTannerSquare.Two)) = 1 from rfl]
    exact Set.union_subset
      ((convexHull_triple_subset (convex_convexHull ℝ _) (hlow 0 0 (by decide))
        (hlow 1 0 (by decide)) (hlow 1 1 (by decide))).trans Set.subset_union_left)
      ((convexHull_triple_subset (convex_convexHull ℝ _) (hupp 0 0 (by decide))
        (hupp 1 1 (by decide)) (hupp 0 1 (by decide))).trans Set.subset_union_right)
  · simp only [fineQuadrantImage, show (1 - (1 : BDL26FiniteTannerSquare.Two)) = 0 from rfl]
    exact Set.union_subset
      ((convexHull_triple_subset (convex_convexHull ℝ _) (hupp 1 1 (by decide))
        (hupp 0 1 (by decide)) (hupp 0 0 (by decide))).trans Set.subset_union_right)
      ((convexHull_triple_subset (convex_convexHull ℝ _) (hlow 1 1 (by decide))
        (hlow 0 0 (by decide)) (hlow 1 0 (by decide))).trans Set.subset_union_left)

/-- Every actual fine-quadrant hit has an incoming-triangle witness with the correct lattice chart. -/
theorem fineQuadrantImage_hit_incoming (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (m n : ℤ) (a b : BDL26FiniteTannerSquare.Two)
    (hm0 : 0 ≤ m) (hn0 : 0 ≤ n) (hm1 : m + 1 ≤ (S.ell : ℤ))
    (hn1 : n + 1 ≤ (S.ell : ℤ)) (hdiag : m = n → a = b) (region : Set E)
    (hhit : (fineQuadrantImage P S J f m n a b ∩ region).Nonempty) :
    ((n ≤ m) ∧ (oldTriangleImage P J (f, 0) ∩ region).Nonempty) ∨
      ((m ≤ n) ∧ (oldTriangleImage P J (f, 1) ∩ region).Nonempty) := by
  obtain ⟨w, hw, hr⟩ := hhit
  rcases lt_trichotomy m n with hmn | he | hnm
  · exact .inr ⟨hmn.le, w,
      fineQuadrantImage_subset_upper P S J f m n a b hn1 hm0 (by omega) hw, hr⟩
  · subst n
    have hab := hdiag rfl
    subst b
    rcases fineQuadrantImage_diagonal_subset P S J f m a hm0 hm1 hw with h | h
    · exact .inl ⟨le_rfl, w, h, hr⟩
    · exact .inr ⟨le_rfl, w, h, hr⟩
  · exact .inl ⟨hnm.le, w,
      fineQuadrantImage_subset_lower P S J f m n a b hm1 hn0 (by omega) hw, hr⟩

end FineTriangleAssignment

section FineHitMetric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual fine-quadrant hit is at distance at most two from its genuine anchor. -/
theorem fineQuadrantImage_hit_anchor (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (m n : ℤ) (a b : BDL26FiniteTannerSquare.Two)
    (h₀ : ‖J (.q (P.faceQ f 0)) - J (.x (P.faceX f))‖ ≤ S.ell)
    (h₁ : ‖J (.q (P.faceQ f 1)) - J (.x (P.faceX f))‖ ≤ S.ell)
    (hz : ‖J (.z (P.faceZ f)) - J (.x (P.faceX f))‖ ≤ S.ell)
    (hz₀ : ‖J (.z (P.faceZ f)) - J (.q (P.faceQ f 0))‖ ≤ S.ell)
    (hz₁ : ‖J (.z (P.faceZ f)) - J (.q (P.faceQ f 1))‖ ≤ S.ell)
    (center : E)
    (hhit : (fineQuadrantImage P S J f m n a b ∩ Metric.closedBall center 1).Nonempty) :
    dist (faceFineAnchor P S J f m n) center ≤ 2 := by
  obtain ⟨w, hw, hball⟩ := hhit
  have hc (u v : BDL26FiniteTannerSquare.Two) :=
    faceFineCorner_dist_anchor P S J f m n u v h₀ h₁ hz hz₀ hz₁
  rcases hw with hw | hw
  · exact triangle_hit_anchor_bound _ _ _ _ _
      (hc a b) (hc (1 - a) b) (hc (1 - a) (1 - b)) ⟨w, hw, hball⟩
  · exact triangle_hit_anchor_bound _ _ _ _ _
      (hc a b) (hc (1 - a) (1 - b)) (hc a (1 - b)) ⟨w, hw, hball⟩

end FineHitMetric

noncomputable section PositiveImageBridge
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The integer address is read from the explicit constructor equivalence. -/
def rawFineInteger (S : OddScale) (i : FineCoordinate S) : ℤ :=
  (fineCoordinateEquiv S i).val

@[simp] theorem rawFineInteger_interior (S : OddScale) (i : Fin S.half)
    (a : BDL26FiniteTannerSquare.Two) :
    rawFineInteger S (.inl (i, a)) = 2 * (i.val : ℤ) + a.val := by
  simp [rawFineInteger]

@[simp] theorem rawFineInteger_last (S : OddScale) (i : Fin 1) :
    rawFineInteger S (.inr i) = 2 * (S.half : ℤ) := by
  have h : S.ell - 1 = 2 * S.half := by have := S.two_half_add_one; omega
  simp [rawFineInteger, fineCoordinate_last, lastStrip, h]

private theorem endpoint_coordinate (S : OddScale) (i : Fin S.half)
    (a : BDL26FiniteTannerSquare.Two) :
    (((2 * (i.val : ℤ) + a.val + a.val : ℤ) : ℝ) / S.ell) =
      2 * ((gridEndpoint i a).val : ℝ) / S.ell := by
  rw [gridEndpoint_val_add]
  push_cast
  ring

private theorem midpoint_coordinate (S : OddScale) (i : Fin S.half)
    (a : BDL26FiniteTannerSquare.Two) :
    (((2 * (i.val : ℤ) + a.val + (1 - a).val : ℤ) : ℝ) / S.ell) =
      (2 * (i.val : ℝ) + 1) / S.ell := by
  fin_cases a <;> norm_num <;> ring

private theorem last_upper_coordinate (S : OddScale) :
    (((2 * (S.half : ℤ) + 1 : ℤ) : ℝ) / S.ell) = 1 := by
  have h : 2 * (S.half : ℝ) + 1 = S.ell := by exact_mod_cast S.two_half_add_one
  have hp : (S.ell : ℝ) ≠ 0 := by have := S.three_le; exact_mod_cast (by omega : S.ell ≠ 0)
  push_cast
  rw [h, div_self hp]

private theorem last_upper_real (S : OddScale) :
    (2 * (S.half : ℝ) + 1) / S.ell = 1 := by
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, Int.cast_one] using
    last_upper_coordinate S

/-- The last column has the actual swapped Q-corner order. -/
theorem pathStripFace_image_fine (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (copy : BDL26FiniteTannerSquare.Two)
    (i : Fin S.half) (a : BDL26FiniteTannerSquare.Two) :
    rxFaceImage P S J (pathStripFace P S f 0 copy i a) =
      fineQuadrantImage P S J f (2 * S.half) (2 * i.val + a.val) 0 a := by
  unfold rxFaceImage
  rw [pathStripFaceX_fine, pathStripFaceQ0_fine, pathStripFaceQ1_fine,
    pathStripFaceZ_fine]
  simp only [fineQuadrantImage, faceFineCorner, foldedGridPoint,
    show (1 - (0 : BDL26FiniteTannerSquare.Two)) = 1 from rfl,
    Fin.val_zero, Fin.val_one, add_zero, endpoint_coordinate, midpoint_coordinate,
    last_upper_coordinate]
  norm_num only [Nat.cast_zero, Nat.cast_one, Int.cast_zero, Int.cast_one,
    add_zero, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]
  simp only [facePoint, contractionRatio, last_upper_real]
  change _ = convexHull ℝ {_, _, _} ∪ convexHull ℝ {_, _, _}
  rw [Set.union_comm]
  congr 1 <;> congr 1 <;> ext v <;> simp only [Set.mem_insert_iff, Set.mem_singleton_iff] <;> tauto

/-- The last row retains the actual horizontal-first corner order. -/
theorem pathStripFace_image_fine_upper (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (copy : BDL26FiniteTannerSquare.Two)
    (i : Fin S.half) (a : BDL26FiniteTannerSquare.Two) :
    rxFaceImage P S J (pathStripFace P S f 1 copy i a) =
      fineQuadrantImage P S J f (2 * i.val + a.val) (2 * S.half) a 0 := by
  unfold rxFaceImage
  rw [pathStripFaceX_fine_upper, pathStripFaceQ0_fine_upper,
    pathStripFaceQ1_fine_upper, pathStripFaceZ_fine_upper]
  simp only [fineQuadrantImage, faceFineCorner, foldedGridPoint,
    show (1 - (0 : BDL26FiniteTannerSquare.Two)) = 1 from rfl,
    Fin.val_zero, Fin.val_one, add_zero, endpoint_coordinate, midpoint_coordinate,
    last_upper_coordinate]
  norm_num only [Nat.cast_zero, Nat.cast_one, Int.cast_zero, Int.cast_one,
    add_zero, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]
  simp only [facePoint, contractionRatio, last_upper_real]

/-- The final diagonal cell is the actual old-Z face, for each retained copy. -/
theorem oldZFace_image_fine (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (copy : BDL26FiniteTannerSquare.Two) :
    rxFaceImage P S J (.inr (.inr (f, copy))) =
      fineQuadrantImage P S J f (2 * S.half) (2 * S.half) 0 0 := by
  simp only [rxFaceImage, rxFaceX, rxFaceQ, rxFaceZ,
    oldZFaceX_point, oldZFaceQ0_point, oldZFaceQ1_point, oldZFaceZ_point,
    fineQuadrantImage, faceFineCorner, foldedGridPoint,
    show (1 - (0 : BDL26FiniteTannerSquare.Two)) = 1 from rfl,
    Fin.val_zero, Fin.val_one, add_zero, last_upper_coordinate]
  norm_num only [Nat.cast_zero, Nat.cast_one, Int.cast_zero, Int.cast_one,
    add_zero, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]
  simp only [facePoint, contractionRatio, last_upper_real]

/-- Constructor-by-constructor image equality for the whole actual positive family. -/
theorem rawPositiveFace_image_fine (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (c : RawPositiveCell S) :
    rxFaceImage P S J (rawPositiveFace P S f c) =
      fineQuadrantImage P S J f (rawFineInteger S c.2.1) (rawFineInteger S c.2.2)
        (fineEndpointBit S c.2.1) (fineEndpointBit S c.2.2) := by
  rcases c with ⟨copy, (⟨i, a⟩ | last), (⟨j, b⟩ | last')⟩
  · simpa only [rawFineInteger_interior, fineEndpointBit] using
      rawPositiveFace_planar_image P S J f i j copy a b
  · simpa only [rawPositiveFace, rawFineInteger_interior, rawFineInteger_last,
      fineEndpointBit] using pathStripFace_image_fine_upper P S J f copy i a
  · simpa only [rawPositiveFace, rawFineInteger_interior, rawFineInteger_last,
      fineEndpointBit] using pathStripFace_image_fine P S J f copy j b
  · simpa only [rawPositiveFace, rawFineInteger_last, fineEndpointBit] using
      oldZFace_image_fine P S J f copy

end PositiveImageBridge

section ActualPositiveWitness
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every actual positive-cell hit is assigned to a hit incoming triangle in its actual chart. -/
theorem actualPositive_hit_incoming (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (c : PositiveCell S) (region : Set E)
    (hhit : (actualFlatImage P S J (f, .inl c) ∩ region).Nonempty) :
    (c.2.2.val ≤ c.2.1.val ∧ (oldTriangleImage P J (f, 0) ∩ region).Nonempty) ∨
      (c.2.1.val ≤ c.2.2.val ∧ (oldTriangleImage P J (f, 1) ∩ region).Nonempty) := by
  obtain ⟨raw, rfl⟩ := (rawPositiveCellEquiv S).surjective c
  rw [actualFlatImage_raw_positive, rawPositiveFace_image_fine] at hhit
  have hm := (fineCoordinateEquiv S raw.2.1).isLt
  have hn := (fineCoordinateEquiv S raw.2.2).isLt
  have h := fineQuadrantImage_hit_incoming P S J f
    (rawFineInteger S raw.2.1) (rawFineInteger S raw.2.2)
    (fineEndpointBit S raw.2.1) (fineEndpointBit S raw.2.2)
    (by unfold rawFineInteger; omega) (by unfold rawFineInteger; omega)
    (by unfold rawFineInteger; omega) (by unfold rawFineInteger; omega)
    (fineEndpointBit_eq_of_coordinate_eq S _ _) region hhit
  rcases h with ⟨hchart, hhit⟩ | ⟨hchart, hhit⟩
  · have hc : (fineCoordinateEquiv S raw.2.2).val ≤ (fineCoordinateEquiv S raw.2.1).val := by
      unfold rawFineInteger at hchart
      exact_mod_cast hchart
    exact .inl ⟨hc, hhit⟩
  · have hc : (fineCoordinateEquiv S raw.2.1).val ≤ (fineCoordinateEquiv S raw.2.2).val := by
      unfold rawFineInteger at hchart
      exact_mod_cast hchart
    exact .inr ⟨hc, hhit⟩

/-- The actual positive-family anchor lies within radius two of every unit-ball hit. -/
theorem actualPositive_hit_anchor (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (c : PositiveCell S)
    (h₀ : ‖J (.q (P.faceQ f 0)) - J (.x (P.faceX f))‖ ≤ S.ell)
    (h₁ : ‖J (.q (P.faceQ f 1)) - J (.x (P.faceX f))‖ ≤ S.ell)
    (hz : ‖J (.z (P.faceZ f)) - J (.x (P.faceX f))‖ ≤ S.ell)
    (hz₀ : ‖J (.z (P.faceZ f)) - J (.q (P.faceQ f 0))‖ ≤ S.ell)
    (hz₁ : ‖J (.z (P.faceZ f)) - J (.q (P.faceQ f 1))‖ ≤ S.ell)
    (center : E)
    (hhit : (actualFlatImage P S J (f, .inl c) ∩ Metric.closedBall center 1).Nonempty) :
    dist (faceFineAnchor P S J f c.2.1.val c.2.2.val) center ≤ 2 := by
  obtain ⟨raw, rfl⟩ := (rawPositiveCellEquiv S).surjective c
  rw [actualFlatImage_raw_positive, rawPositiveFace_image_fine] at hhit
  exact fineQuadrantImage_hit_anchor P S J f _ _ _ _ h₀ h₁ hz hz₀ hz₁ center hhit

end ActualPositiveWitness

section ActualPositivePacking
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual positive cells inject into their copy label and the selected triangle lattice. -/
theorem positive_triangleIndex_injective (S : OddScale)
    (side : BDL26FiniteTannerSquare.Two) :
    Function.Injective (fun c : PositiveCell S =>
      (c.1, triangleGridIndex side (c.2.1.val, c.2.2.val))) := by
  intro a b he
  have hc : a.1 = b.1 := congrArg
    (fun p : BDL26FiniteTannerSquare.Two × (ℤ × ℤ) => p.1) he
  have hi := triangleGridIndex_injective side (congrArg Prod.snd he)
  have hfirst : (a.2.1.val : ℤ) = (b.2.1.val : ℤ) := congrArg Prod.fst hi
  have hsecond : (a.2.2.val : ℤ) = (b.2.2.val : ℤ) := congrArg Prod.snd hi
  apply Prod.ext hc
  apply Prod.ext
  · apply Fin.ext
    exact_mod_cast hfirst
  · apply Fin.ext
    exact_mod_cast hsecond

/-- The count is derived for an actual materialized face family in one incoming triangle. -/
theorem actualPositive_triangle_fiber_card_le (P : TannerSquarePresentation)
    (S : OddScale) (J : Vertex P → E) (f : P.Face)
    (side : BDL26FiniteTannerSquare.Two) (s : Finset (PositiveCell S))
    (center : E) {lower width : ℝ} (hlower : 0 < lower) (hwidth : 0 < width)
    (hb : lower ≤ ‖J (.q (P.faceQ f side)) - J (.x (P.faceX f))‖)
    (hc : lower ≤ ‖J (.z (P.faceZ f)) - J (.x (P.faceX f))‖)
    (hbc : lower ≤ ‖J (.z (P.faceZ f)) - J (.q (P.faceQ f side))‖)
    (h₀ : ‖J (.q (P.faceQ f 0)) - J (.x (P.faceX f))‖ ≤ S.ell)
    (h₁ : ‖J (.q (P.faceQ f 1)) - J (.x (P.faceX f))‖ ≤ S.ell)
    (hz : ‖J (.z (P.faceZ f)) - J (.x (P.faceX f))‖ ≤ S.ell)
    (hz₀ : ‖J (.z (P.faceZ f)) - J (.q (P.faceQ f 0))‖ ≤ S.ell)
    (hz₁ : ‖J (.z (P.faceZ f)) - J (.q (P.faceQ f 1))‖ ≤ S.ell)
    (hthin : TriangleWidthAtLeast
      (J (.q (P.faceQ f side)) - J (.x (P.faceX f)))
      (J (.z (P.faceZ f)) - J (.x (P.faceX f))) width)
    (hchart : ∀ c ∈ s, if side = 0 then c.2.2.val ≤ c.2.1.val
      else c.2.1.val ≤ c.2.2.val)
    (hhit : ∀ c ∈ s,
      (actualFlatImage P S J (f, .inl c) ∩ Metric.closedBall center 1).Nonempty) :
    (s.card : ℝ) ≤ 16 * Real.pi * S.ell ^ 2 / (lower * width) := by
  have hell : (0 : ℝ) < S.ell := by
    exact_mod_cast (show 0 < S.ell by have := S.three_le; omega)
  have hbL : ‖J (.q (P.faceQ f side)) - J (.x (P.faceX f))‖ ≤ S.ell := by
    fin_cases side
    · exact h₀
    · exact h₁
  have hbc' : lower ≤ ‖(J (.z (P.faceZ f)) - J (.x (P.faceX f))) -
      (J (.q (P.faceQ f side)) - J (.x (P.faceX f)))‖ := by
    have he : (J (.z (P.faceZ f)) - J (.x (P.faceX f))) -
        (J (.q (P.faceQ f side)) - J (.x (P.faceX f))) =
        J (.z (P.faceZ f)) - J (.q (P.faceQ f side)) := by abel
    rw [he]
    exact hbc
  apply labeled_triangle_fiber_card_le s Prod.fst
    (fun c => triangleGridIndex side (c.2.1.val, c.2.2.val))
    (positive_triangleIndex_injective S side).injOn
    (J (.x (P.faceX f)))
    (J (.q (P.faceQ f side)) - J (.x (P.faceX f)))
    (J (.z (P.faceZ f)) - J (.x (P.faceX f))) center
    hell hlower hwidth hb hc hbc' hbL hz hthin
  intro c hcs
  have ha := actualPositive_hit_anchor P S J f c h₀ h₁ hz hz₀ hz₁ center (hhit c hcs)
  have hct := hchart c hcs
  fin_cases side
  · have hctNat : c.2.2.val ≤ c.2.1.val := by simpa using hct
    rw [faceFineAnchor_lower_lattice P S J f (c.2.1.val : ℤ) (c.2.2.val : ℤ)
      (by exact_mod_cast hctNat)] at ha
    exact ha
  · have hctNat : c.2.1.val ≤ c.2.2.val := by simpa using hct
    rw [faceFineAnchor_upper_lattice P S J f (c.2.1.val : ℤ) (c.2.2.val : ℤ)
      (by exact_mod_cast hctNat)] at ha
    exact ha

end ActualPositivePacking

/-- Sum a derived geometric estimate only over incoming labels actually hit. -/
theorem card_le_hit_labels_mul_fiber {A B : Type*} [DecidableEq B] (s : Finset A) (target : Finset B)
    (owner : A → B) (C : ℝ) (hC : 0 ≤ C)
    (howner : ∀ a ∈ s, owner a ∈ target)
    (hfiber : ∀ b ∈ s.image owner, ((s.filter (fun a => owner a = b)).card : ℝ) ≤ C) :
    (s.card : ℝ) ≤ (target.card : ℝ) * C := by
  classical
  have hcard : (s.image owner).card ≤ target.card :=
    Finset.card_le_card (by
      intro b hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      exact howner a ha)
  calc
    (s.card : ℝ) = ∑ b ∈ s.image owner, ((s.filter (fun a => owner a = b)).card : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_image owner s
    _ ≤ ∑ b ∈ s.image owner, C := Finset.sum_le_sum hfiber
    _ = ((s.image owner).card : ℝ) * C := by simp
    _ ≤ (target.card : ℝ) * C := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hC

noncomputable section ActualPositiveSelection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Choose a chart from proved actual hit geometry; this accepts no successor certificate. -/
def actualPositiveHitSide (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (c : PositiveCell S) (region : Set E) :
    BDL26FiniteTannerSquare.Two := by
  classical
  exact if c.2.2.val ≤ c.2.1.val ∧ (oldTriangleImage P J (f, 0) ∩ region).Nonempty
    then 0 else 1

/-- The selected old triangle really hits the same region and has the correct anchor chart. -/
theorem actualPositiveHitSide_spec (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (c : PositiveCell S) (region : Set E)
    (hhit : (actualFlatImage P S J (f, .inl c) ∩ region).Nonempty) :
    (if actualPositiveHitSide P S J f c region = 0 then c.2.2.val ≤ c.2.1.val
      else c.2.1.val ≤ c.2.2.val) ∧
      (oldTriangleImage P J (f, actualPositiveHitSide P S J f c region) ∩ region).Nonempty := by
  classical
  have h := actualPositive_hit_incoming P S J f c region hhit
  by_cases hl : c.2.2.val ≤ c.2.1.val ∧ (oldTriangleImage P J (f, 0) ∩ region).Nonempty
  · simpa [actualPositiveHitSide, hl] using hl
  · have hu := h.resolve_left hl
    simpa only [actualPositiveHitSide, if_neg hl,
      if_neg (show (1 : BDL26FiniteTannerSquare.Two) ≠ 0 by decide)] using hu

/-- Incoming geometry consists only of the old actual face sides and source segment widths. -/
structure IncomingFaceGeometry (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (lower width : ℝ) : Prop where
  side_lower : ∀ f side, lower ≤ ‖J (.q (P.faceQ f side)) - J (.x (P.faceX f))‖
  diagonal_lower : ∀ f, lower ≤ ‖J (.z (P.faceZ f)) - J (.x (P.faceX f))‖
  opposite_lower : ∀ f side, lower ≤ ‖J (.z (P.faceZ f)) - J (.q (P.faceQ f side))‖
  side_upper : ∀ f side, ‖J (.q (P.faceQ f side)) - J (.x (P.faceX f))‖ ≤ S.ell
  diagonal_upper : ∀ f, ‖J (.z (P.faceZ f)) - J (.x (P.faceX f))‖ ≤ S.ell
  opposite_upper : ∀ f side, ‖J (.z (P.faceZ f)) - J (.q (P.faceQ f side))‖ ≤ S.ell
  triangle_width : ∀ f side, TriangleWidthAtLeast
    (J (.q (P.faceQ f side)) - J (.x (P.faceX f)))
    (J (.z (P.faceZ f)) - J (.x (P.faceX f))) width

end ActualPositiveSelection

section ActualPositiveDensity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual positive labels are packed over only those original triangle labels hit by the ball. -/
theorem actualPositiveHits_card_le (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) {lower width : ℝ} (hlower : 0 < lower) (hwidth : 0 < width)
    (hgeo : IncomingFaceGeometry P S J lower width) (center : E) :
    ((familyHits (fun p : P.Face × PositiveCell S => actualFlatImage P S J (p.1, .inl p.2))
      (Metric.closedBall center 1)).card : ℝ) ≤
      ((familyHits (oldTriangleImage P J) (Metric.closedBall center 1)).card : ℝ) *
        (16 * Real.pi * S.ell ^ 2 / (lower * width)) := by
  classical
  let region := Metric.closedBall center 1
  let s := familyHits (fun p : P.Face × PositiveCell S => actualFlatImage P S J (p.1, .inl p.2)) region
  let owner (p : P.Face × PositiveCell S) : P.Face × BDL26FiniteTannerSquare.Two :=
    (p.1, actualPositiveHitSide P S J p.1 p.2 region)
  let C : ℝ := 16 * Real.pi * S.ell ^ 2 / (lower * width)
  have hhit (p : P.Face × PositiveCell S) (hp : p ∈ s) :
      (actualFlatImage P S J (p.1, .inl p.2) ∩ region).Nonempty :=
    (Finset.mem_filter.mp hp).2
  apply card_le_hit_labels_mul_fiber s (familyHits (oldTriangleImage P J) region) owner C
    (by dsimp [C]; positivity)
  · intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (actualPositiveHitSide_spec P S J p.1 p.2 region (hhit p hp)).2⟩
  · intro v hv
    let t := s.filter fun p => owner p = v
    have htowner (p : P.Face × PositiveCell S) (hp : p ∈ t) : p.1 = v.1 :=
      congrArg Prod.fst (Finset.mem_filter.mp hp).2
    have hinj : Set.InjOn Prod.snd (t : Set (P.Face × PositiveCell S)) := by
      intro p hp q hq he
      exact Prod.ext ((htowner p hp).trans (htowner q hq).symm) he
    have hcard : t.card = (t.image Prod.snd).card := (Finset.card_image_of_injOn hinj).symm
    change (t.card : ℝ) ≤ C
    rw [hcard]
    apply actualPositive_triangle_fiber_card_le P S J v.1 v.2 (t.image Prod.snd)
      center hlower hwidth (hgeo.side_lower _ _) (hgeo.diagonal_lower _)
      (hgeo.opposite_lower _ _) (hgeo.side_upper _ 0) (hgeo.side_upper _ 1)
      (hgeo.diagonal_upper _) (hgeo.opposite_upper _ 0) (hgeo.opposite_upper _ 1)
      (hgeo.triangle_width _ _)
    · intro c hc
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
      have hs := actualPositiveHitSide_spec P S J p.1 p.2 region
        (hhit p (Finset.mem_filter.mp hp).1)
      have he : actualPositiveHitSide P S J p.1 p.2 region = v.2 :=
        congrArg Prod.snd (Finset.mem_filter.mp hp).2
      simpa only [he] using hs.1
    · intro c hc
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
      have hs := hhit p (Finset.mem_filter.mp hp).1
      simpa only [htowner p hp] using hs

end ActualPositiveDensity

section ActualFullDensity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every actual RX face label, including all zero-area seams, obeys the derived packing count. -/
theorem actualRXHits_card_le (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) {lower width tPrime : ℝ}
    (hlower : 0 < lower) (hwidth : 0 < width)
    (hgeo : IncomingFaceGeometry P S J lower width) (center : E)
    (hincoming : ((familyHits (oldTriangleImage P J) (Metric.closedBall center 1)).card : ℝ) ≤ tPrime) :
    ((familyHits (rxFaceImage P S J) (Metric.closedBall center 1)).card : ℝ) ≤
      48 * Real.pi * tPrime * S.ell ^ 2 / (lower * width) := by
  rw [actualRXHits_card_eq_flat]
  have hcharge : ((familyHits (actualFlatImage P S J) (Metric.closedBall center 1)).card : ℝ) ≤
      3 * ((familyHits (fun p : P.Face × PositiveCell S =>
        actualFlatImage P S J (p.1, .inl p.2)) (Metric.closedBall center 1)).card : ℝ) := by
    exact_mod_cast actualFlatHits_card_le_three_mul_positive P S J (Metric.closedBall center 1)
  have hpositive := actualPositiveHits_card_le P S J hlower hwidth hgeo center
  have hbound := mul_le_mul_of_nonneg_right hincoming
    (show 0 ≤ 16 * Real.pi * (S.ell : ℝ) ^ 2 / (lower * width) by positivity)
  calc
    _ ≤ 3 * ((familyHits (fun p : P.Face × PositiveCell S =>
        actualFlatImage P S J (p.1, .inl p.2)) (Metric.closedBall center 1)).card : ℝ) := hcharge
    _ ≤ 3 * (tPrime * (16 * Real.pi * (S.ell : ℝ) ^ 2 / (lower * width))) :=
      mul_le_mul_of_nonneg_left (hpositive.trans hbound) (by norm_num)
    _ = 48 * Real.pi * tPrime * S.ell ^ 2 / (lower * width) := by ring

/-- The honest odd-rounding slack yields the exact source constant for the constructed RX map. -/
theorem actualRXHits_card_le_rounded (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) {alpha alpha2 gamma lambda tPrime : ℝ}
    (hlambda : 0 < lambda) (hgamma : 0 < gamma) (halpha2 : 1 < alpha2)
    (htPrime : 0 ≤ tPrime) (hscale : 13 ≤ (2 * alpha + 1) * lambda)
    (hround : (S.ell : ℝ) ≤ (2 * alpha + 1) * lambda + 2)
    (hgeo : IncomingFaceGeometry P S J ((alpha2 - 1) * lambda) (gamma * lambda))
    (center : E)
    (hincoming : ((familyHits (oldTriangleImage P J) (Metric.closedBall center 1)).card : ℝ) ≤ tPrime) :
    ((familyHits (rxFaceImage P S J) (Metric.closedBall center 1)).card : ℝ) ≤
      64 * Real.pi * tPrime * (2 * alpha + 1) ^ 2 / (gamma * (alpha2 - 1)) := by
  have hd := actualRXHits_card_le P S J (mul_pos (sub_pos.mpr halpha2) hlambda)
    (mul_pos hgamma hlambda) hgeo center hincoming
  have hs := rounded_density_handoff hscale (show 0 ≤ (S.ell : ℝ) by positivity) hround
    (show 0 ≤ Real.pi * tPrime / (((alpha2 - 1) * lambda) * (gamma * lambda)) by positivity)
  calc
    _ ≤ 48 * Real.pi * tPrime * S.ell ^ 2 /
        (((alpha2 - 1) * lambda) * (gamma * lambda)) := hd
    _ = 48 * (Real.pi * tPrime / (((alpha2 - 1) * lambda) * (gamma * lambda))) * S.ell ^ 2 := by ring
    _ ≤ 64 * (Real.pi * tPrime / (((alpha2 - 1) * lambda) * (gamma * lambda))) *
        ((2 * alpha + 1) * lambda) ^ 2 := hs
    _ = _ := by
      have hlambda0 : lambda ≠ 0 := ne_of_gt hlambda
      have hgamma0 : gamma ≠ 0 := ne_of_gt hgamma
      have ha : alpha2 - 1 ≠ 0 := ne_of_gt (sub_pos.mpr halpha2)
      field_simp
      <;> ring

end ActualFullDensity

section RZDensityGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Transposing X and Z preserves every incoming triangle label and its geometric image. -/
theorem oldTriangleImage_transpose (P : TannerSquarePresentation) (J : Vertex P → E)
    (f : P.Face) (side : BDL26FiniteTannerSquare.Two) :
    oldTriangleImage (transposePresentation P) (transposePointMap P J) (f, side) =
      oldTriangleImage P J (f, side) := by
  change convexHull ℝ {J (.z (P.faceZ f)), J (.q (P.faceQ f side)), J (.x (P.faceX f))} =
    convexHull ℝ {J (.x (P.faceX f)), J (.q (P.faceQ f side)), J (.z (P.faceZ f))}
  congr 1
  ext p
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- All old source-side and width hypotheses transport under the actual transpose. -/
theorem IncomingFaceGeometry.transpose (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) {lower width : ℝ} (h : IncomingFaceGeometry P S J lower width) :
    IncomingFaceGeometry (transposePresentation P) S (transposePointMap P J) lower width := by
  constructor
  · intro f side
    change lower ≤ ‖J (.q (P.faceQ f side)) - J (.z (P.faceZ f))‖
    rw [norm_sub_rev]
    exact h.opposite_lower f side
  · intro f
    change lower ≤ ‖J (.x (P.faceX f)) - J (.z (P.faceZ f))‖
    rw [norm_sub_rev]
    exact h.diagonal_lower f
  · intro f side
    change lower ≤ ‖J (.x (P.faceX f)) - J (.q (P.faceQ f side))‖
    rw [norm_sub_rev]
    exact h.side_lower f side
  · intro f side
    change ‖J (.q (P.faceQ f side)) - J (.z (P.faceZ f))‖ ≤ S.ell
    rw [norm_sub_rev]
    exact h.opposite_upper f side
  · intro f
    change ‖J (.x (P.faceX f)) - J (.z (P.faceZ f))‖ ≤ S.ell
    rw [norm_sub_rev]
    exact h.diagonal_upper f
  · intro f side
    change ‖J (.x (P.faceX f)) - J (.q (P.faceQ f side))‖ ≤ S.ell
    rw [norm_sub_rev]
    exact h.side_upper f side
  · intro f side
    change TriangleWidthAtLeast (J (.q (P.faceQ f side)) - J (.z (P.faceZ f)))
      (J (.x (P.faceX f)) - J (.z (P.faceZ f))) width
    have ht := (h.triangle_width f side).transpose
    have hb : (J (.q (P.faceQ f side)) - J (.x (P.faceX f))) -
        (J (.z (P.faceZ f)) - J (.x (P.faceX f))) =
        J (.q (P.faceQ f side)) - J (.z (P.faceZ f)) := by abel
    have hc : -(J (.z (P.faceZ f)) - J (.x (P.faceX f))) =
        J (.x (P.faceX f)) - J (.z (P.faceZ f)) := by abel
    rw [hb, hc] at ht
    exact ht

end RZDensityGeometry

section RZDensityCount
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every actual RZ label is counted through the proved materialized transpose equivalence. -/
theorem actualRZHits_card_eq_transpose (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (J : Vertex P → E) (region : Set E) :
    (familyHits (rzFaceImage P A S J) region).card =
      (familyHits (rxFaceImage (transposePresentation P) S (transposePointMap P J)) region).card := by
  classical
  apply Finset.card_bij (fun f _ => rzFaceEquiv P S f)
  · intro f hf
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have h := (Finset.mem_filter.mp hf).2
    simpa only [rzFaceImage_eq_transpose] using h
  · intro f _ g _ h
    exact (rzFaceEquiv P S).injective h
  · intro f hf
    refine ⟨(rzFaceEquiv P S).symm f, ?_, (rzFaceEquiv P S).apply_symm_apply f⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [rzFaceImage_eq_transpose, Equiv.apply_symm_apply] using (Finset.mem_filter.mp hf).2

/-- The actual RZ density estimate uses precisely the same incoming labeled triangle family. -/
theorem actualRZHits_card_le (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (J : Vertex P → E) {lower width tPrime : ℝ}
    (hlower : 0 < lower) (hwidth : 0 < width)
    (hgeo : IncomingFaceGeometry P S J lower width) (center : E)
    (hincoming : ((familyHits (oldTriangleImage P J) (Metric.closedBall center 1)).card : ℝ) ≤ tPrime) :
    ((familyHits (rzFaceImage P A S J) (Metric.closedBall center 1)).card : ℝ) ≤
      48 * Real.pi * tPrime * S.ell ^ 2 / (lower * width) := by
  rw [actualRZHits_card_eq_transpose]
  apply actualRXHits_card_le (transposePresentation P) S (transposePointMap P J)
    hlower hwidth (IncomingFaceGeometry.transpose P S J hgeo) center
  have he : oldTriangleImage (transposePresentation P) (transposePointMap P J) =
      oldTriangleImage P J := by
    funext p
    exact oldTriangleImage_transpose P J p.1 p.2
  rw [he]
  exact hincoming

end RZDensityCount

section FineEdgeLength
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Each horizontal fine side is one lattice step, including the fold and final strip. -/
theorem faceFineCorner_horizontal_dist (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) {lower width : ℝ} (hgeo : IncomingFaceGeometry P S J lower width)
    (f : P.Face) (m n : ℤ) (a b : BDL26FiniteTannerSquare.Two) :
    dist (faceFineCorner P S J f m n a b) (faceFineCorner P S J f m n (1 - a) b) ≤ 1 := by
  have h := faceFineCorner_dist_anchor P S J f m (n + b.val) 1 0
    (hgeo.side_upper f 0) (hgeo.side_upper f 1) (hgeo.diagonal_upper f)
    (hgeo.opposite_upper f 0) (hgeo.opposite_upper f 1)
  fin_cases a <;> fin_cases b <;>
    simpa [faceFineCorner, faceFineAnchor, dist_comm] using h

/-- Each vertical fine side is likewise an actual unit step. -/
theorem faceFineCorner_vertical_dist (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) {lower width : ℝ} (hgeo : IncomingFaceGeometry P S J lower width)
    (f : P.Face) (m n : ℤ) (a b : BDL26FiniteTannerSquare.Two) :
    dist (faceFineCorner P S J f m n a b) (faceFineCorner P S J f m n a (1 - b)) ≤ 1 := by
  have h := faceFineCorner_dist_anchor P S J f (m + a.val) n 0 1
    (hgeo.side_upper f 0) (hgeo.side_upper f 1) (hgeo.diagonal_upper f)
    (hgeo.opposite_upper f 0) (hgeo.opposite_upper f 1)
  fin_cases a <;> fin_cases b <;>
    simpa [faceFineCorner, faceFineAnchor, dist_comm] using h

end FineEdgeLength

section AdmissibleReplacementScale

/-- A sufficiently large choice can simultaneously meet any external lower bound and the
honest replacement-rounding threshold. No numerical LLL witness is supplied here. -/
theorem exists_replacement_scale_parameter (alpha lambdaLower : ℝ)
    (hA : 0 < 2 * alpha + 1) :
    ∃ lambda : ℝ, lambdaLower ≤ lambda ∧ 0 < lambda ∧
      13 ≤ (2 * alpha + 1) * lambda := by
  refine ⟨max lambdaLower (13 / (2 * alpha + 1)), le_max_left _ _, ?_, ?_⟩
  · exact lt_of_lt_of_le (div_pos (by norm_num) hA) (le_max_right _ _)
  · have h := (div_le_iff₀ hA).mp (le_max_right lambdaLower (13 / (2 * alpha + 1)))
    simpa only [mul_comm] using h

/-- The actual least odd scale lies at most two above the real threshold. -/
theorem leastOddScaleAbove_le_add_two (threshold : ℝ) (hone : 1 ≤ threshold) :
    ((leastOddScaleAbove threshold hone).ell : ℝ) ≤ threshold + 2 := by
  have hn : leastOddAbove ⌊threshold⌋₊ ≤ ⌊threshold⌋₊ + 2 := by
    unfold leastOddAbove
    omega
  have hf : (⌊threshold⌋₊ : ℝ) ≤ threshold := Nat.floor_le (by linarith)
  calc
    ((leastOddScaleAbove threshold hone).ell : ℝ) ≤ (⌊threshold⌋₊ : ℝ) + 2 := by
      exact_mod_cast hn
    _ ≤ threshold + 2 := by linarith

/-- The canonical source scale, rather than a caller-chosen rounded number, has the
strict lower bound and exact upper slack used by the replacement theorem. -/
theorem canonical_replacement_scale_bounds {alpha lambda : ℝ}
    (hscale : 13 ≤ (2 * alpha + 1) * lambda) :
    let S := leastOddScaleAbove ((2 * alpha + 1) * lambda) (by linarith)
    (2 * alpha + 1) * lambda < (S.ell : ℝ) ∧
      (S.ell : ℝ) ≤ (2 * alpha + 1) * lambda + 2 := by
  exact ⟨leastOddScaleAbove_gt _ _, leastOddScaleAbove_le_add_two _ _⟩

end AdmissibleReplacementScale

section RoundedRZDensity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The same exact source constant applies to the actual RZ map and every retained label. -/
theorem actualRZHits_card_le_rounded (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (J : Vertex P → E) {alpha alpha2 gamma lambda tPrime : ℝ}
    (hlambda : 0 < lambda) (hgamma : 0 < gamma) (halpha2 : 1 < alpha2)
    (htPrime : 0 ≤ tPrime) (hscale : 13 ≤ (2 * alpha + 1) * lambda)
    (hround : (S.ell : ℝ) ≤ (2 * alpha + 1) * lambda + 2)
    (hgeo : IncomingFaceGeometry P S J ((alpha2 - 1) * lambda) (gamma * lambda))
    (center : E)
    (hincoming : ((familyHits (oldTriangleImage P J) (Metric.closedBall center 1)).card : ℝ) ≤ tPrime) :
    ((familyHits (rzFaceImage P A S J) (Metric.closedBall center 1)).card : ℝ) ≤
      64 * Real.pi * tPrime * (2 * alpha + 1) ^ 2 / (gamma * (alpha2 - 1)) := by
  rw [actualRZHits_card_eq_transpose]
  apply actualRXHits_card_le_rounded (transposePresentation P) S (transposePointMap P J)
    hlambda hgamma halpha2 htPrime hscale hround
    (IncomingFaceGeometry.transpose P S J hgeo) center
  have he : oldTriangleImage (transposePresentation P) (transposePointMap P J) =
      oldTriangleImage P J := by
    funext p
    exact oldTriangleImage_transpose P J p.1 p.2
  rw [he]
  exact hincoming

/-- Perturbation bounds at the unrounded source length imply the input geometry
for its genuine larger odd replacement scale. -/
theorem incomingFaceGeometry_of_source_bounds (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) {L lower width : ℝ} (hL : L ≤ S.ell)
    (hsideLo : ∀ f side, lower ≤ ‖J (.q (P.faceQ f side)) - J (.x (P.faceX f))‖)
    (hdiagLo : ∀ f, lower ≤ ‖J (.z (P.faceZ f)) - J (.x (P.faceX f))‖)
    (hoppLo : ∀ f side, lower ≤ ‖J (.z (P.faceZ f)) - J (.q (P.faceQ f side))‖)
    (hsideUp : ∀ f side, ‖J (.q (P.faceQ f side)) - J (.x (P.faceX f))‖ ≤ L)
    (hdiagUp : ∀ f, ‖J (.z (P.faceZ f)) - J (.x (P.faceX f))‖ ≤ L)
    (hoppUp : ∀ f side, ‖J (.z (P.faceZ f)) - J (.q (P.faceQ f side))‖ ≤ L)
    (hthin : ∀ f side, TriangleWidthAtLeast
      (J (.q (P.faceQ f side)) - J (.x (P.faceX f)))
      (J (.z (P.faceZ f)) - J (.x (P.faceX f))) width) :
    IncomingFaceGeometry P S J lower width :=
  ⟨hsideLo, hdiagLo, hoppLo, fun f side => (hsideUp f side).trans hL,
    fun f => (hdiagUp f).trans hL, fun f side => (hoppUp f side).trans hL, hthin⟩

end RoundedRZDensity

section FaceBoundaryUnit
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The four Tanner edges of a realized square have length at most one. -/
def BoundaryUnit (x q₀ q₁ z : E) : Prop :=
  dist x q₀ ≤ 1 ∧ dist x q₁ ≤ 1 ∧ dist q₀ z ≤ 1 ∧ dist q₁ z ≤ 1

theorem BoundaryUnit.swap {x q₀ q₁ z : E} (h : BoundaryUnit x q₀ q₁ z) :
    BoundaryUnit x q₁ q₀ z := ⟨h.2.1, h.1, h.2.2.2, h.2.2.1⟩

/-- The actual X-Z diagonal choice leaves all four boundary edges as fine unit steps. -/
theorem fineQuadrant_boundaryUnit (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) {lower width : ℝ} (hgeo : IncomingFaceGeometry P S J lower width)
    (f : P.Face) (m n : ℤ) (a b : BDL26FiniteTannerSquare.Two) :
    BoundaryUnit (faceFineCorner P S J f m n a b)
      (faceFineCorner P S J f m n (1 - a) b)
      (faceFineCorner P S J f m n a (1 - b))
      (faceFineCorner P S J f m n (1 - a) (1 - b)) := by
  exact ⟨faceFineCorner_horizontal_dist P S J hgeo f m n a b,
    faceFineCorner_vertical_dist P S J hgeo f m n a b,
    faceFineCorner_vertical_dist P S J hgeo f m n (1 - a) b,
    faceFineCorner_horizontal_dist P S J hgeo f m n a (1 - b)⟩

/-- The predicate is evaluated on actual materialized global endpoints. -/
def rxFaceBoundaryUnit (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (c : RXFace P S) : Prop :=
  BoundaryUnit (rxZeroPoint P S J (rxFaceX P S c))
    (rxOnePoint P S J (rxFaceQ P S c 0))
    (rxOnePoint P S J (rxFaceQ P S c 1))
    (rxTwoPoint P S J (rxFaceZ P S c))

/-- Every planar materialized quadrant has the four genuine unit edges. -/
theorem planar_boundaryUnit (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) {lower width : ℝ} (hgeo : IncomingFaceGeometry P S J lower width)
    (f : P.Face) (i j : Fin S.half) (copy a b : BDL26FiniteTannerSquare.Two) :
    rxFaceBoundaryUnit P S J (rawPositiveFace P S f (copy, .inl (i, a), .inl (j, b))) := by
  simpa only [rxFaceBoundaryUnit, rawPositiveFace, rxFaceX, rxFaceQ, rxFaceZ,
    twoSelect_zero, twoSelect_one, planarFaceX_fineCorner, planarFaceQ0_fineCorner,
    planarFaceQ1_fineCorner, planarFaceZ_fineCorner, oldFaceInXStar] using
      fineQuadrant_boundaryUnit P S J hgeo f (2 * i.val + a.val) (2 * j.val + b.val) a b

/-- The final column's actual Q order is exchanged, with the same genuine unit boundary. -/
theorem pathStrip_boundaryUnit (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) {lower width : ℝ} (hgeo : IncomingFaceGeometry P S J lower width)
    (f : P.Face) (copy : BDL26FiniteTannerSquare.Two) (i : Fin S.half)
    (a : BDL26FiniteTannerSquare.Two) :
    rxFaceBoundaryUnit P S J (pathStripFace P S f 0 copy i a) := by
  have h := (fineQuadrant_boundaryUnit P S J hgeo f (2 * S.half) (2 * i.val + a.val) 0 a).swap
  unfold rxFaceBoundaryUnit
  rw [pathStripFaceX_fine, pathStripFaceQ0_fine, pathStripFaceQ1_fine, pathStripFaceZ_fine]
  simp only [faceFineCorner, foldedGridPoint,
    show (1 - (0 : BDL26FiniteTannerSquare.Two)) = 1 from rfl,
    Fin.val_zero, Fin.val_one, add_zero, endpoint_coordinate, midpoint_coordinate] at h
  norm_num only [Nat.cast_zero, Nat.cast_one, Int.cast_zero, Int.cast_one,
    add_zero, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat] at h
  simpa only [facePoint, contractionRatio, last_upper_real] using h

/-- The final row uses the usual Q order and the same actual fine unit steps. -/
theorem pathStrip_boundaryUnit_upper (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) {lower width : ℝ} (hgeo : IncomingFaceGeometry P S J lower width)
    (f : P.Face) (copy : BDL26FiniteTannerSquare.Two) (i : Fin S.half)
    (a : BDL26FiniteTannerSquare.Two) :
    rxFaceBoundaryUnit P S J (pathStripFace P S f 1 copy i a) := by
  have h := fineQuadrant_boundaryUnit P S J hgeo f (2 * i.val + a.val) (2 * S.half) a 0
  unfold rxFaceBoundaryUnit
  rw [pathStripFaceX_fine_upper, pathStripFaceQ0_fine_upper,
    pathStripFaceQ1_fine_upper, pathStripFaceZ_fine_upper]
  simp only [faceFineCorner, foldedGridPoint,
    show (1 - (0 : BDL26FiniteTannerSquare.Two)) = 1 from rfl,
    Fin.val_zero, Fin.val_one, add_zero, endpoint_coordinate, midpoint_coordinate] at h
  norm_num only [Nat.cast_zero, Nat.cast_one, Int.cast_zero, Int.cast_one,
    add_zero, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat] at h
  simpa only [facePoint, contractionRatio, last_upper_real] using h

/-- The final old-Z face is the last actual fine quadrant, for each coincident copy. -/
theorem oldZ_boundaryUnit (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) {lower width : ℝ} (hgeo : IncomingFaceGeometry P S J lower width)
    (f : P.Face) (copy : BDL26FiniteTannerSquare.Two) :
    rxFaceBoundaryUnit P S J (.inr (.inr (f, copy))) := by
  have h := fineQuadrant_boundaryUnit P S J hgeo f (2 * S.half) (2 * S.half) 0 0
  simp only [rxFaceBoundaryUnit, rxFaceX, rxFaceQ, rxFaceZ,
    oldZFaceX_point, oldZFaceQ0_point, oldZFaceQ1_point, oldZFaceZ_point]
  simp only [faceFineCorner, foldedGridPoint,
    show (1 - (0 : BDL26FiniteTannerSquare.Two)) = 1 from rfl,
    Fin.val_zero, Fin.val_one, add_zero] at h
  norm_num only [Nat.cast_zero, Nat.cast_one, Int.cast_zero, Int.cast_one,
    add_zero, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat] at h
  simpa only [facePoint, contractionRatio, last_upper_real] using h

end FaceBoundaryUnit

section SeamBoundaryUnit
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The contracted collar has exactly one fine step of width, including odd rounding. -/
theorem contraction_complement (S : OddScale) : 1 - contractionRatio S = 1 / S.ell := by
  have h : 2 * (S.half : ℝ) + 1 = S.ell := by exact_mod_cast S.two_half_add_one
  have he : (S.ell : ℝ) ≠ 0 := by exact_mod_cast (show S.ell ≠ 0 by have := S.three_le; omega)
  unfold contractionRatio
  field_simp
  linarith

/-- A terminal rung has actual endpoints separated by the contracted original X-Q edge. -/
theorem terminalRung_boundaryUnit (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) {lower width : ℝ} (hgeo : IncomingFaceGeometry P S J lower width)
    (f : P.Face) (side copy : BDL26FiniteTannerSquare.Two) :
    rxFaceBoundaryUnit P S J (terminalRungFace P S f side copy) := by
  have hell : (0 : ℝ) < S.ell := by exact_mod_cast (show 0 < S.ell by have := S.three_le; omega)
  have hd : dist
      ((1 - contractionRatio S) • J (.x (P.faceX f)) + contractionRatio S • J (.z (P.faceZ f)))
      ((1 - contractionRatio S) • J (.q (P.faceQ f side)) + contractionRatio S • J (.z (P.faceZ f))) ≤ 1 := by
    rw [dist_eq_norm]
    have he : ((1 - contractionRatio S) • J (.x (P.faceX f)) + contractionRatio S • J (.z (P.faceZ f))) -
        ((1 - contractionRatio S) • J (.q (P.faceQ f side)) + contractionRatio S • J (.z (P.faceZ f))) =
        (1 - contractionRatio S) • (J (.x (P.faceX f)) - J (.q (P.faceQ f side))) := by module
    rw [he, norm_smul, contraction_complement, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), norm_sub_rev]
    have h := mul_le_mul_of_nonneg_left (hgeo.side_upper f side)
      (show 0 ≤ 1 / (S.ell : ℝ) by positivity)
    simpa [ne_of_gt hell] using h
  simpa only [rxFaceBoundaryUnit, terminalRungFace, rxFaceX, rxFaceQ, rxFaceZ,
    twoSelect_zero, twoSelect_one, rungFaceX_point, rungFaceQ0_point, rungFaceQ1_point,
    rungFaceZ_point, faceXQEdge, BoundaryUnit, dist_self] using
      (show 0 ≤ (1 : ℝ) ∧ _ ∧ _ ∧ 0 ≤ (1 : ℝ) from ⟨by norm_num, hd, hd, by norm_num⟩)

/-- A collapsed rectangle retains the two actual neighboring path-edge endpoints. -/
theorem boundaryRectangle_boundaryUnit (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) {lower width : ℝ} (hgeo : IncomingFaceGeometry P S J lower width)
    (f : P.Face) (side copy : BDL26FiniteTannerSquare.Two) (i : Fin S.half)
    (endpoint : BDL26FiniteTannerSquare.Two) :
    rxFaceBoundaryUnit P S J (boundaryRectangleFace P S f side copy i endpoint) := by
  have hpath : rxFaceBoundaryUnit P S J (pathStripFace P S f side copy i endpoint) := by
    fin_cases side
    · exact pathStrip_boundaryUnit P S J hgeo f copy i endpoint
    · exact pathStrip_boundaryUnit_upper P S J hgeo f copy i endpoint
  let edge := qToXSubdivisionBoundaryEdge P (P.faceQ f side) (P.faceX f)
    (P.data.faceQ_xq f side) S (⟨P.faceZ f, P.data.faceQ_qz f side⟩, i)
  have hx : rectangleEndpointPoint P S J (P.faceX f) edge endpoint =
      rxZeroPoint P S J (rxFaceX P S (pathStripFace P S f side copy i endpoint)) := by
    fin_cases endpoint <;> rfl
  have hq : rectangleMidpoint P S J (P.faceX f) edge =
      rxOnePoint P S J (rxFaceQ P S (pathStripFace P S f side copy i endpoint) 0) := rfl
  have hd : dist (rectangleEndpointPoint P S J (P.faceX f) edge endpoint)
      (rectangleMidpoint P S J (P.faceX f) edge) ≤ 1 := by
    rw [hx, hq]
    exact hpath.1
  simpa only [rxFaceBoundaryUnit, boundaryRectangleFace, rxFaceX, rxFaceQ, rxFaceZ,
    twoSelect_zero, twoSelect_one, rectangleFaceX_point, rectangleFaceQ0_point,
    rectangleFaceQ1_point, rectangleFaceZ_point, BoundaryUnit, dist_self] using
      (show _ ∧ 0 ≤ (1 : ℝ) ∧ 0 ≤ (1 : ℝ) ∧ _ from ⟨hd, by norm_num, by norm_num, hd⟩)

end SeamBoundaryUnit

section AllFaceBoundaryUnit
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Constructor-complete unit-edge geometry, including every collapsed materialized face. -/
theorem rxFace_boundaryUnit (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) {lower width : ℝ} (hgeo : IncomingFaceGeometry P S J lower width)
    (c : RXFace P S) : rxFaceBoundaryUnit P S J c := by
  obtain ⟨p, hp⟩ := (rxFaceSlotEquiv P S).symm.surjective c
  rcases p with ⟨f, slot⟩
  rw [← hp]
  rcases slot with (plane | ⟨side, i, copy, endpoint⟩) | (⟨side, edge, endpoint⟩ | copy)
  · rcases plane with ⟨⟨copy, i, j⟩, a, b⟩
    rw [rxFaceSlot_inverse_of_forward P S _ _ _ (rxFaceSlot_planar P S f i j copy a b)]
    exact planar_boundaryUnit P S J hgeo f i j copy a b
  · rw [rxFaceSlot_inverse_of_forward P S _ _ _
      (rxFaceSlot_boundaryRectangle P S f side copy i endpoint)]
    exact boundaryRectangle_boundaryUnit P S J hgeo f side copy i endpoint
  · rcases edge with ⟨copy, i⟩ | last
    · rw [rxFaceSlot_inverse_of_forward P S _ _ _
        (rxFaceSlot_pathStrip P S f side copy i endpoint)]
      fin_cases side
      · exact pathStrip_boundaryUnit P S J hgeo f copy i endpoint
      · exact pathStrip_boundaryUnit_upper P S J hgeo f copy i endpoint
    · have hl : last = 0 := Subsingleton.elim _ _
      subst last
      rw [rxFaceSlot_inverse_of_forward P S _ _ _
        (rxFaceSlot_terminalRung P S f side endpoint)]
      exact terminalRung_boundaryUnit P S J hgeo f side endpoint
  · rw [rxFaceSlot_inverse_of_forward P S _ _ _ (rxFaceSlot_oldZ P S f copy)]
    exact oldZ_boundaryUnit P S J hgeo f copy

end AllFaceBoundaryUnit

section GlobalRXEdgeLength
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every actual successor X-Q incidence has unit endpoint distance. -/
theorem rxXQ_edge_dist (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) {lower width : ℝ} (hgeo : IncomingFaceGeometry P S J lower width)
    (x : RX0 P S) (q : RX1 P S) (hinc : rxXQIncidence P S x q = true) :
    dist (rxZeroPoint P S J x) (rxOnePoint P S J q) ≤ 1 := by
  obtain ⟨f, side, rfl, rfl⟩ := (rxXQIncidence_eq_true_iff P S x q).mp hinc
  have h := rxFace_boundaryUnit P S J hgeo f
  fin_cases side
  · exact h.1
  · exact h.2.1

/-- Every actual successor Q-Z incidence likewise has unit endpoint distance. -/
theorem rxQZ_edge_dist (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) {lower width : ℝ} (hgeo : IncomingFaceGeometry P S J lower width)
    (q : RX1 P S) (z : RX2 P S) (hinc : rxQZIncidence P S q z = true) :
    dist (rxOnePoint P S J q) (rxTwoPoint P S J z) ≤ 1 := by
  obtain ⟨f, side, rfl, rfl⟩ := (rxQZIncidence_eq_true_iff P S q z).mp hinc
  have h := rxFace_boundaryUnit P S J hgeo f
  fin_cases side
  · exact h.2.2.1
  · exact h.2.2.2

end GlobalRXEdgeLength

section GlobalRZEdgeLength
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Reversing the realized square swaps its boundary-edge directions without changing lengths. -/
theorem BoundaryUnit.reverse {x q₀ q₁ z : E} (h : BoundaryUnit x q₀ q₁ z) :
    BoundaryUnit z q₀ q₁ x := by
  exact ⟨by simpa only [dist_comm] using h.2.2.1,
    by simpa only [dist_comm] using h.2.2.2,
    by simpa only [dist_comm] using h.1,
    by simpa only [dist_comm] using h.2.1⟩

/-- The concrete RZ boundary uses the actual reversed RX endpoint maps. -/
theorem rzFace_boundaryUnit (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (J : Vertex P → E) {lower width : ℝ}
    (hgeo : IncomingFaceGeometry P S J lower width)
    (f : BDL26RZLocalReplacement.RZFace P S) :
    BoundaryUnit (rzXPoint P S J (BDL26RZLocalReplacement.rzFaceX P S f))
      (rzQPoint P S J (BDL26RZLocalReplacement.rzFaceQ P A S f 0))
      (rzQPoint P S J (BDL26RZLocalReplacement.rzFaceQ P A S f 1))
      (rzZPoint P S J (BDL26RZLocalReplacement.rzFaceZ P A S f)) := by
  have h := BoundaryUnit.reverse (rxFace_boundaryUnit (transposePresentation P) S (transposePointMap P J)
    (IncomingFaceGeometry.transpose P S J hgeo) (rzFaceEquiv P S f))
  simpa only [rxFaceBoundaryUnit, rzFaceX_transpose, rzFaceZ_transpose, rzFaceQ_transpose,
    rzXPoint, rzQPoint, rzZPoint] using h

private theorem geometric_xq_face_exists (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (x : P.X) (q : P.Q) (h : P.xq x q = true) :
    ∃ f : P.Face, ∃ c : BDL26FiniteTannerSquare.Two, P.faceX f = x ∧ P.faceQ f c = q := by
  let z := A.qzRoot q
  let shared : SharedQ P.data x z.1 := ⟨q, by simp [h, z.2]⟩
  obtain ⟨⟨f, c⟩, hc⟩ := (P.perfectPairing x z.1).2 shared
  exact ⟨f.1, c, f.2.1, congrArg Subtype.val hc⟩

private theorem geometric_qz_face_exists (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q) (z : P.Z) (h : P.qz q z = true) :
    ∃ f : P.Face, ∃ c : BDL26FiniteTannerSquare.Two, P.faceQ f c = q ∧ P.faceZ f = z := by
  let x := A.xqRoot q
  let shared : SharedQ P.data x.1 z := ⟨q, by simp [x.2, h]⟩
  obtain ⟨⟨f, c⟩, hc⟩ := (P.perfectPairing x.1 z).2 shared
  exact ⟨f.1, c, congrArg Subtype.val hc, f.2.2⟩

/-- The actual RZ X-Q incidence has a face witness from constructed successor admissibility. -/
theorem rzXQ_edge_dist (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (J : Vertex P → E)
    {lower width : ℝ} (hgeo : IncomingFaceGeometry P S J lower width)
    (x : BDL26RZLocalReplacement.RZX P S) (q : BDL26RZLocalReplacement.RZQ P S)
    (hinc : BDL26RZLocalReplacement.rzXQIncidence P A4.toTannerSquareAdmissible S x q = true) :
    dist (rzXPoint P S J x) (rzQPoint P S J q) ≤ 1 := by
  let successor := BDL26RZLocalReplacement.rzReplacementPresentation P A4.toTannerSquareAdmissible S
  let admissible := BDL26RZLocalReplacement.rzReplacementAdmissibleV4 P A4 R S
  obtain ⟨f, side, hx, hq⟩ := geometric_xq_face_exists successor admissible.toTannerSquareAdmissible x q hinc
  have h := rzFace_boundaryUnit P A4.toTannerSquareAdmissible S J hgeo f
  rw [← hx, ← hq]
  fin_cases side
  · exact h.1
  · exact h.2.1

/-- The corresponding actual RZ Q-Z incidence has the same unit bound. -/
theorem rzQZ_edge_dist (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (J : Vertex P → E)
    {lower width : ℝ} (hgeo : IncomingFaceGeometry P S J lower width)
    (q : BDL26RZLocalReplacement.RZQ P S) (z : BDL26RZLocalReplacement.RZZ P S)
    (hinc : BDL26RZLocalReplacement.rzQZIncidence P A4.toTannerSquareAdmissible S q z = true) :
    dist (rzQPoint P S J q) (rzZPoint P S J z) ≤ 1 := by
  let successor := BDL26RZLocalReplacement.rzReplacementPresentation P A4.toTannerSquareAdmissible S
  let admissible := BDL26RZLocalReplacement.rzReplacementAdmissibleV4 P A4 R S
  obtain ⟨f, side, hq, hz⟩ := geometric_qz_face_exists successor admissible.toTannerSquareAdmissible q z hinc
  have h := rzFace_boundaryUnit P A4.toTannerSquareAdmissible S J hgeo f
  rw [← hq, ← hz]
  fin_cases side
  · exact h.2.2.1
  · exact h.2.2.2

end GlobalRZEdgeLength

section AffineBoundaryGluing
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The affine chart for either of the actual X-Q-Z triangles of a Tanner square. -/
def tannerTrianglePoint (P : TannerSquarePresentation) (J : Vertex P → E)
    (f : P.Face) (side : BDL26FiniteTannerSquare.Two) (a b : ℝ) : E :=
  (1 - a - b) • J (.x (P.faceX f)) + a • J (.q (P.faceQ f side)) + b • J (.z (P.faceZ f))

/-- A single affine edge realization is indexed by the actual global X-Q edge. -/
def xqEdgePoint (P : TannerSquarePresentation) (J : Vertex P → E) (e : XQEdge P) (t : ℝ) : E :=
  (1 - t) • J (.x e.1.1) + t • J (.q e.1.2)

/-- The same construction for an actual global Q-Z edge. -/
def qzEdgePoint (P : TannerSquarePresentation) (J : Vertex P → E) (e : QZEdge P) (t : ℝ) : E :=
  (1 - t) • J (.q e.1.1) + t • J (.z e.1.2)

/-- Every local triangle agrees with its global X-Q boundary map. -/
theorem tannerTrianglePoint_xq (P : TannerSquarePresentation) (J : Vertex P → E)
    (f : P.Face) (side : BDL26FiniteTannerSquare.Two) (t : ℝ) :
    tannerTrianglePoint P J f side t 0 = xqEdgePoint P J (faceXQEdge P f side) t := by
  simp [tannerTrianglePoint, xqEdgePoint, faceXQEdge]

/-- The other triangle side agrees with its global Q-Z boundary map. -/
theorem tannerTrianglePoint_qz (P : TannerSquarePresentation) (J : Vertex P → E)
    (f : P.Face) (side : BDL26FiniteTannerSquare.Two) (t : ℝ) :
    tannerTrianglePoint P J f side (1 - t) t = qzEdgePoint P J (faceQZEdge P f side) t := by
  dsimp [tannerTrianglePoint, qzEdgePoint, faceQZEdge]
  module

/-- Both charts agree on the auxiliary X-Z diagonal, even when the square is folded. -/
theorem tannerTrianglePoint_diagonal (P : TannerSquarePresentation) (J : Vertex P → E)
    (f : P.Face) (t : ℝ) :
    tannerTrianglePoint P J f 0 0 t = tannerTrianglePoint P J f 1 0 t := by
  simp [tannerTrianglePoint]

/-- Actual shared X-Q labels force pointwise agreement of the affine triangle boundaries. -/
theorem tannerTrianglePoint_glue_xq (P : TannerSquarePresentation) (J : Vertex P → E)
    (f g : P.Face) (i j : BDL26FiniteTannerSquare.Two)
    (h : faceXQEdge P f i = faceXQEdge P g j) (t : ℝ) :
    tannerTrianglePoint P J f i t 0 = tannerTrianglePoint P J g j t 0 := by
  rw [tannerTrianglePoint_xq, tannerTrianglePoint_xq, h]

/-- Actual shared Q-Z labels give the dual boundary agreement. -/
theorem tannerTrianglePoint_glue_qz (P : TannerSquarePresentation) (J : Vertex P → E)
    (f g : P.Face) (i j : BDL26FiniteTannerSquare.Two)
    (h : faceQZEdge P f i = faceQZEdge P g j) (t : ℝ) :
    tannerTrianglePoint P J f i (1 - t) t = tannerTrianglePoint P J g j (1 - t) t := by
  rw [tannerTrianglePoint_qz, tannerTrianglePoint_qz, h]

end AffineBoundaryGluing


noncomputable section ConstructedLocalMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The affine two-triangle realization of a presented Tanner square. -/
def tannerFaceImage (P : TannerSquarePresentation) (J : Vertex P → E) (f : P.Face) : Set E :=
  convexHull ℝ {J (.x (P.faceX f)), J (.q (P.faceQ f 0)), J (.z (P.faceZ f))} ∪
    convexHull ℝ {J (.x (P.faceX f)), J (.z (P.faceZ f)), J (.q (P.faceQ f 1))}

/-- Locality and labeled two-cell density for the constructed piecewise-affine realization.
Distinct domain labels are counted even when their images coincide or collapse. -/
def IsBoundedDensityLocalMap (P : TannerSquarePresentation) (J : Vertex P → E) (t : ℝ) : Prop :=
  (∀ x q, P.xq x q = true → dist (J (.x x)) (J (.q q)) ≤ 1) ∧
  (∀ q z, P.qz q z = true → dist (J (.q q)) (J (.z z)) ≤ 1) ∧
  ∀ center, ((familyHits (tannerFaceImage P J) (Metric.closedBall center 1)).card : ℝ) ≤ t

/-- All vertices of the concrete RX successor receive their already constructed global point. -/
def rxVertexPoint (P : TannerSquarePresentation) (S : OddScale) (J : Vertex P → E) :
    Vertex (rxReplacementPresentation P S) → E
  | .x x => rxZeroPoint P S J x
  | .q q => rxOnePoint P S J q
  | .z z => rxTwoPoint P S J z

/-- The resulting square realization is definitionally the actual materialized face image. -/
theorem rxVertexPoint_faceImage (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : RXFace P S) :
    tannerFaceImage (rxReplacementPresentation P S) (rxVertexPoint P S J) f =
      rxFaceImage P S J f := rfl

/-- RZ likewise uses its actual transposed global endpoint maps. -/
def rzVertexPoint (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (J : Vertex P → E) :
    Vertex (BDL26RZLocalReplacement.rzReplacementPresentation P A S) → E
  | .x x => rzXPoint P S J x
  | .q q => rzQPoint P S J q
  | .z z => rzZPoint P S J z

theorem rzVertexPoint_faceImage (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (J : Vertex P → E) (f : BDL26RZLocalReplacement.RZFace P S) :
    tannerFaceImage (BDL26RZLocalReplacement.rzReplacementPresentation P A S)
      (rzVertexPoint P A S J) f = rzFaceImage P A S J f := rfl

/-- Finite hit families are independent of the enumeration instance and pointwise presentation. -/
theorem familyHits_congr_fintype {ι D : Type*} (I₁ I₂ : Fintype ι)
    (images₁ images₂ : ι → Set D) (he : ∀ i, images₁ i = images₂ i) (region : Set D) :
    @familyHits ι D I₁ images₁ region = @familyHits ι D I₂ images₂ region := by
  have hI : I₁ = I₂ := Subsingleton.elim _ _
  have himages : images₁ = images₂ := funext he
  subst I₂
  subst images₂
  rfl

/-- Compare hit families without reducing either packaged finite enumeration. -/
theorem rzVertexPoint_hits (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (J : Vertex P → E) (region : Set E) :
    familyHits (tannerFaceImage (BDL26RZLocalReplacement.rzReplacementPresentation P A S)
      (rzVertexPoint P A S J)) region = familyHits (rzFaceImage P A S J) region := by
  exact familyHits_congr_fintype
    (BDL26RZLocalReplacement.rzReplacementPresentation P A S).data.faceFintype
    (inferInstance : Fintype (BDL26RZLocalReplacement.RZFace P S))
    _ _ (rzVertexPoint_faceImage P A S J) region

/-- The RX output is constructed from input geometry; neither its map nor its density is supplied. -/
theorem rx_constructed_localMap (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) {lower width tPrime : ℝ} (hlower : 0 < lower) (hwidth : 0 < width)
    (hgeo : IncomingFaceGeometry P S J lower width)
    (hincoming : ∀ center,
      ((familyHits (oldTriangleImage P J) (Metric.closedBall center 1)).card : ℝ) ≤ tPrime) :
    IsBoundedDensityLocalMap (rxReplacementPresentation P S) (rxVertexPoint P S J)
      (48 * Real.pi * tPrime * S.ell ^ 2 / (lower * width)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x q h
    exact rxXQ_edge_dist P S J hgeo x q h
  · intro q z h
    exact rxQZ_edge_dist P S J hgeo q z h
  · intro center
    have he : tannerFaceImage (rxReplacementPresentation P S) (rxVertexPoint P S J) =
        rxFaceImage P S J := rfl
    rw [he]
    exact actualRXHits_card_le P S J hlower hwidth hgeo center (hincoming center)

/-- The RZ output uses constructed successor admissibility and the actual reversed geometry. -/
theorem rz_constructed_localMap (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (J : Vertex P → E)
    {lower width tPrime : ℝ} (hlower : 0 < lower) (hwidth : 0 < width)
    (hgeo : IncomingFaceGeometry P S J lower width)
    (hincoming : ∀ center,
      ((familyHits (oldTriangleImage P J) (Metric.closedBall center 1)).card : ℝ) ≤ tPrime) :
    IsBoundedDensityLocalMap
      (BDL26RZLocalReplacement.rzReplacementPresentation P A4.toTannerSquareAdmissible S)
      (rzVertexPoint P A4.toTannerSquareAdmissible S J)
      (48 * Real.pi * tPrime * S.ell ^ 2 / (lower * width)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x q h
    exact rzXQ_edge_dist P A4 R S J hgeo x q h
  · intro q z h
    exact rzQZ_edge_dist P A4 R S J hgeo q z h
  · intro center
    rw [rzVertexPoint_hits]
    exact actualRZHits_card_le P A4.toTannerSquareAdmissible S J hlower hwidth hgeo center (hincoming center)

end ConstructedLocalMap


section RoundedConstructedLocalMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The exact source constant is attained by the concrete RX vertex placement. -/
theorem rx_constructed_localMap_rounded (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) {alpha alpha2 gamma lambda tPrime : ℝ}
    (hlambda : 0 < lambda) (hgamma : 0 < gamma) (halpha2 : 1 < alpha2)
    (htPrime : 0 ≤ tPrime) (hscale : 13 ≤ (2 * alpha + 1) * lambda)
    (hround : (S.ell : ℝ) ≤ (2 * alpha + 1) * lambda + 2)
    (hgeo : IncomingFaceGeometry P S J ((alpha2 - 1) * lambda) (gamma * lambda))
    (hincoming : ∀ center,
      ((familyHits (oldTriangleImage P J) (Metric.closedBall center 1)).card : ℝ) ≤ tPrime) :
    IsBoundedDensityLocalMap (rxReplacementPresentation P S) (rxVertexPoint P S J)
      (64 * Real.pi * tPrime * (2 * alpha + 1) ^ 2 / (gamma * (alpha2 - 1))) := by
  refine ⟨fun x q h => rxXQ_edge_dist P S J hgeo x q h,
    fun q z h => rxQZ_edge_dist P S J hgeo q z h, ?_⟩
  intro center
  change ((familyHits (rxFaceImage P S J) (Metric.closedBall center 1)).card : ℝ) ≤ _
  exact actualRXHits_card_le_rounded P S J hlambda hgamma halpha2 htPrime hscale hround
    hgeo center (hincoming center)

/-- The dual placement has the same constant and actual successor incidences. -/
theorem rz_constructed_localMap_rounded (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (J : Vertex P → E) {alpha alpha2 gamma lambda tPrime : ℝ}
    (hlambda : 0 < lambda) (hgamma : 0 < gamma) (halpha2 : 1 < alpha2)
    (htPrime : 0 ≤ tPrime) (hscale : 13 ≤ (2 * alpha + 1) * lambda)
    (hround : (S.ell : ℝ) ≤ (2 * alpha + 1) * lambda + 2)
    (hgeo : IncomingFaceGeometry P S J ((alpha2 - 1) * lambda) (gamma * lambda))
    (hincoming : ∀ center,
      ((familyHits (oldTriangleImage P J) (Metric.closedBall center 1)).card : ℝ) ≤ tPrime) :
    IsBoundedDensityLocalMap
      (BDL26RZLocalReplacement.rzReplacementPresentation P A4.toTannerSquareAdmissible S)
      (rzVertexPoint P A4.toTannerSquareAdmissible S J)
      (64 * Real.pi * tPrime * (2 * alpha + 1) ^ 2 / (gamma * (alpha2 - 1))) := by
  refine ⟨fun x q h => rzXQ_edge_dist P A4 R S J hgeo x q h,
    fun q z h => rzQZ_edge_dist P A4 R S J hgeo q z h, ?_⟩
  intro center
  rw [rzVertexPoint_hits]
  exact actualRZHits_card_le_rounded P A4.toTannerSquareAdmissible S J
    hlambda hgamma halpha2 htPrime hscale hround hgeo center (hincoming center)

end RoundedConstructedLocalMap


section ConstructedDegreeBounds
open BDL26BoundedValence

/-- Both measured successor degree bounds accompany RX geometry on its actual presentation. -/
theorem rx_constructed_degrees (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (h : BoundedValence P) :
    BoundedValence (rxReplacementPresentation P S) ∧
      (∀ e : XQEdge (rxReplacementPresentation P S),
        Fintype.card (XQIncidentFace (rxReplacementPresentation P S) e) ≤ 4) ∧
      (∀ e : QZEdge (rxReplacementPresentation P S),
        Fintype.card (QZIncidentFace (rxReplacementPresentation P S) e) ≤ 4) := by
  have hv := BDL26BoundedValence.rx_boundedValence P A4 R S h
  exact ⟨hv, xqIncidentFace_card_le_four _ hv, qzIncidentFace_card_le_four _ hv⟩

/-- The RZ degree conclusion uses the actual constructed dual successor. -/
theorem rz_constructed_degrees (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (h : BoundedValence P) :
    let P' := BDL26RZLocalReplacement.rzReplacementPresentation P A4.toTannerSquareAdmissible S
    BoundedValence P' ∧
      (∀ e : XQEdge P', Fintype.card (XQIncidentFace P' e) ≤ 4) ∧
      (∀ e : QZEdge P', Fintype.card (QZIncidentFace P' e) ≤ 4) := by
  have hv := BDL26BoundedValence.rz_boundedValence P A4 R S h
  exact ⟨hv, xqIncidentFace_card_le_four _ hv, qzIncidentFace_card_le_four _ hv⟩

end ConstructedDegreeBounds


section CanonicalReplacementHandoff
open BDL26BoundedValence
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The source uses this canonical least odd scale, with its rounding proved above. -/
noncomputable def replacementScale (alpha lambda : ℝ)
    (hscale : 13 ≤ (2 * alpha + 1) * lambda) : OddScale :=
  leastOddScaleAbove ((2 * alpha + 1) * lambda) (by linarith)

/-- RX's deterministic handoff constructs its map and derives both measured degrees
at the canonical odd scale. Only the incoming geometry and incoming density are hypotheses. -/
theorem rx_canonical_handoff (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (hvalence : BoundedValence P) (J : Vertex P → E)
    {alpha alpha2 gamma lambda tPrime : ℝ}
    (hlambda : 0 < lambda) (hgamma : 0 < gamma) (halpha2 : 1 < alpha2)
    (htPrime : 0 ≤ tPrime) (hscale : 13 ≤ (2 * alpha + 1) * lambda)
    (hgeo : IncomingFaceGeometry P (replacementScale alpha lambda hscale) J
      ((alpha2 - 1) * lambda) (gamma * lambda))
    (hincoming : ∀ center,
      ((familyHits (oldTriangleImage P J) (Metric.closedBall center 1)).card : ℝ) ≤ tPrime) :
    let S := replacementScale alpha lambda hscale
    let Pnext := rxReplacementPresentation P S
    BoundedValence Pnext ∧
      (∀ e : XQEdge Pnext, Fintype.card (XQIncidentFace Pnext e) ≤ 4) ∧
      (∀ e : QZEdge Pnext, Fintype.card (QZIncidentFace Pnext e) ≤ 4) ∧
      IsBoundedDensityLocalMap Pnext (rxVertexPoint P S J)
        (64 * Real.pi * tPrime * (2 * alpha + 1) ^ 2 / (gamma * (alpha2 - 1))) := by
  let S := replacementScale alpha lambda hscale
  have hd := rx_constructed_degrees P A4 R S hvalence
  refine ⟨hd.1, hd.2.1, hd.2.2, ?_⟩
  exact rx_constructed_localMap_rounded P S J hlambda hgamma halpha2 htPrime hscale
    (canonical_replacement_scale_bounds hscale).2 hgeo hincoming

/-- The actual RZ successor has the same deterministic handoff and exact constant. -/
theorem rz_canonical_handoff (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (hvalence : BoundedValence P) (J : Vertex P → E)
    {alpha alpha2 gamma lambda tPrime : ℝ}
    (hlambda : 0 < lambda) (hgamma : 0 < gamma) (halpha2 : 1 < alpha2)
    (htPrime : 0 ≤ tPrime) (hscale : 13 ≤ (2 * alpha + 1) * lambda)
    (hgeo : IncomingFaceGeometry P (replacementScale alpha lambda hscale) J
      ((alpha2 - 1) * lambda) (gamma * lambda))
    (hincoming : ∀ center,
      ((familyHits (oldTriangleImage P J) (Metric.closedBall center 1)).card : ℝ) ≤ tPrime) :
    let S := replacementScale alpha lambda hscale
    let Pnext := BDL26RZLocalReplacement.rzReplacementPresentation P A4.toTannerSquareAdmissible S
    BoundedValence Pnext ∧
      (∀ e : XQEdge Pnext, Fintype.card (XQIncidentFace Pnext e) ≤ 4) ∧
      (∀ e : QZEdge Pnext, Fintype.card (QZIncidentFace Pnext e) ≤ 4) ∧
      IsBoundedDensityLocalMap Pnext (rzVertexPoint P A4.toTannerSquareAdmissible S J)
        (64 * Real.pi * tPrime * (2 * alpha + 1) ^ 2 / (gamma * (alpha2 - 1))) := by
  let S := replacementScale alpha lambda hscale
  have hd := rz_constructed_degrees P A4 R S hvalence
  refine ⟨hd.1, hd.2.1, hd.2.2, ?_⟩
  exact rz_constructed_localMap_rounded P A4 R S J hlambda hgamma halpha2 htPrime hscale
    (canonical_replacement_scale_bounds hscale).2 hgeo hincoming

end CanonicalReplacementHandoff


noncomputable section IntrinsicLocalCompatibility
open BDL26DecodingGraph
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Intrinsic local zero-cell coordinates are read from their concrete cylinders, before shifts. -/
def rxIntrinsicPoint (P : TannerSquarePresentation) (S : OddScale) (J : Vertex P → E) :
    (u : Vertex P) → RXZeroCell P S u → E
  | .x x, v => subdivisionVertexPoint P S J x v.2
  | .q q, v => qSubdivisionVertexPoint P S J q v.2
  | .z z, _ => J (.z z)

/-- The actual unshifted zero-cell inclusion commutes with the constructed successor map. -/
theorem rx_intrinsic_compatibility (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (u : Vertex P) (v : RXZeroCell P S u) :
    rxVertexPoint P S J (rxZeroInclude P S u v) = rxIntrinsicPoint P S J u v := by
  cases u <;> rfl

/-- The dual local coordinates use the concrete transposed cylinders. -/
def rzIntrinsicPoint (P : TannerSquarePresentation) (S : OddScale) (J : Vertex P → E) :
    (u : Vertex P) → RZZeroCell P S u → E
  | .x x, _ => J (.x x)
  | .q q, v => qSubdivisionVertexPoint (transposePresentation P) S (transposePointMap P J) q v.2
  | .z z, v => subdivisionVertexPoint (transposePresentation P) S (transposePointMap P J) z v.2

/-- Dual compatibility preserves the existing intrinsic-zero carrier exactly. -/
theorem rz_intrinsic_compatibility (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (J : Vertex P → E) (u : Vertex P) (v : RZZeroCell P S u) :
    rzVertexPoint P A S J (rzZeroInclude P A S u v) = rzIntrinsicPoint P S J u v := by
  cases u <;> rfl

/-- Each intrinsic X-local edge barycenter is the midpoint of its actual boundary points. -/
theorem rx_local_edge_midpoint (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (e : DoubleCylinderEdge P x S) :
    rxVertexPoint P S J (.q (.inl ⟨x, e⟩)) = (1 / 2 : ℝ) •
      (rxIntrinsicPoint P S J (.x x) (tannerDoubleCylinderEdgeStart P x S e) +
       rxIntrinsicPoint P S J (.x x) (tannerDoubleCylinderEdgeEnd P x S e)) := rfl

/-- The shifted Q-local edges have exactly the same affine midpoint compatibility. -/
theorem rx_q_local_edge_midpoint (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (q : P.Q) (e : QDoubleCylinderEdge P q S) :
    rxVertexPoint P S J (.z (.inl (.inr ⟨q, e⟩))) = (1 / 2 : ℝ) •
      (rxIntrinsicPoint P S J (.q q) (qDoubleCylinderEdgeStart P q S e) +
       rxIntrinsicPoint P S J (.q q) (qDoubleCylinderEdgeEnd P q S e)) := rfl


/-- The dual Z-local edge center has its actual intrinsic endpoints as affine midpoint. -/
theorem rz_local_edge_midpoint (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (J : Vertex P → E) (z : P.Z) (e : ZDoubleCylinderEdge P z S) :
    rzVertexPoint P A S J (.q (.inl ⟨z, e⟩)) = (1 / 2 : ℝ) •
      (rzIntrinsicPoint P S J (.z z)
        (tannerDoubleCylinderEdgeStart (transposePresentation P) z S e) +
       rzIntrinsicPoint P S J (.z z)
        (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S e)) := rfl

/-- The dual shifted Q-local edge center obeys the same concrete endpoint formula. -/
theorem rz_q_local_edge_midpoint (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (J : Vertex P → E) (q : P.Q)
    (e : QDoubleCylinderEdge (transposePresentation P) q S) :
    rzVertexPoint P A S J (.x (.inl (.inr ⟨q, e⟩))) = (1 / 2 : ℝ) •
      (rzIntrinsicPoint P S J (.q q)
        (qDoubleCylinderEdgeStart (transposePresentation P) q S e) +
       rzIntrinsicPoint P S J (.q q)
        (qDoubleCylinderEdgeEnd (transposePresentation P) q S e)) := rfl

end IntrinsicLocalCompatibility


section LocalFaceRestriction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Restricting a labeled family along an injection can only decrease its geometric hit count. -/
theorem familyHits_restrict_card_le {A B : Type*} [Fintype A] [Fintype B]
    (embed : A → B) (hinj : Function.Injective embed) (images : B → Set E) (region : Set E) :
    (familyHits (images ∘ embed) region).card ≤ (familyHits images region).card := by
  classical
  apply Finset.card_le_card_of_injOn embed
  · intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
  · intro a ha b hb h
    exact hinj h

/-- The local X complex's existing barycentric squares retain their actual global labels. -/
def rxLocalFaceInclude (P : TannerSquarePresentation) (S : OddScale) (x : P.X) :
    DoubleCylinderFace P x S × (BDL26FiniteTannerSquare.Two × BDL26FiniteTannerSquare.Two) →
      RXFace P S := fun f => .inl ⟨x, f⟩

theorem rxLocalFaceInclude_injective (P : TannerSquarePresentation) (S : OddScale) (x : P.X) :
    Function.Injective (rxLocalFaceInclude P S x) := by
  intro a b h
  exact eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inl.inj h)).2

/-- Every induced local square image has exactly its already constructed global geometry. -/
def rxLocalSquareImage (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) :
    DoubleCylinderFace P x S × (BDL26FiniteTannerSquare.Two × BDL26FiniteTannerSquare.Two) → Set E :=
  rxFaceImage P S J ∘ rxLocalFaceInclude P S x

/-- Local restriction preserves density with all its collapsed/coincident labels counted. -/
theorem rxLocalSquareImage_hits_le (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (region : Set E) :
    (familyHits (rxLocalSquareImage P S J x) region).card ≤
      (familyHits (rxFaceImage P S J) region).card :=
  familyHits_restrict_card_le _ (rxLocalFaceInclude_injective P S x) _ _

/-- Local square boundary lengths are inherited through the concrete face inclusion. -/
theorem rxLocalSquare_boundaryUnit (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) {lower width : ℝ} (hgeo : IncomingFaceGeometry P S J lower width)
    (x : P.X)
    (f : DoubleCylinderFace P x S × (BDL26FiniteTannerSquare.Two × BDL26FiniteTannerSquare.Two)) :
    rxFaceBoundaryUnit P S J (rxLocalFaceInclude P S x f) :=
  rxFace_boundaryUnit P S J hgeo _


/-- The dual local Z complex retains its existing materialized face tags. -/
def rzLocalFaceInclude (P : TannerSquarePresentation) (S : OddScale) (z : P.Z) :
    ZDoubleCylinderFace P z S × (BDL26FiniteTannerSquare.Two × BDL26FiniteTannerSquare.Two) →
      BDL26RZLocalReplacement.RZFace P S := fun f => .inl ⟨z, f⟩

theorem rzLocalFaceInclude_injective (P : TannerSquarePresentation) (S : OddScale) (z : P.Z) :
    Function.Injective (rzLocalFaceInclude P S z) := by
  intro a b h
  exact eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inl.inj h)).2

/-- Restriction to the dual intrinsic local squares keeps their actual affine images. -/
def rzLocalSquareImage (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (J : Vertex P → E) (z : P.Z) :
    ZDoubleCylinderFace P z S × (BDL26FiniteTannerSquare.Two × BDL26FiniteTannerSquare.Two) → Set E :=
  rzFaceImage P A S J ∘ rzLocalFaceInclude P S z

theorem rzLocalSquareImage_hits_le (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (J : Vertex P → E) (z : P.Z) (region : Set E) :
    (familyHits (rzLocalSquareImage P A S J z) region).card ≤
      (familyHits (rzFaceImage P A S J) region).card :=
  familyHits_restrict_card_le _ (rzLocalFaceInclude_injective P S z) _ _

end LocalFaceRestriction

section IntrinsicFaceDensity
variable {E : Type*}

/-- Grouping actual subcells into their parent cell never increases the hit count. -/
theorem familyHits_group_card_le {A B : Type*} [Fintype A] [Fintype B]
    (images : A × B → Set E) (region : Set E) :
    (familyHits (fun a => ⋃ b, images (a, b)) region).card ≤
      (familyHits images region).card := by
  classical
  have hsub : familyHits (fun a => ⋃ b, images (a, b)) region ⊆
      (familyHits images region).image Prod.fst := by
    intro a ha
    obtain ⟨p, hp⟩ := (Finset.mem_filter.mp ha).2
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hp.1
    exact Finset.mem_image.mpr ⟨(a, b),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨p, hb, hp.2⟩⟩, rfl⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le)

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual intrinsic X-local face is the union of its four Tanner quadrants. -/
def rxIntrinsicFaceImage (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (f : DoubleCylinderFace P x S) : Set E :=
  ⋃ corner, rxLocalSquareImage P S J x (f, corner)

/-- Original local-face labels, not only quadrant labels, inherit the global density bound. -/
theorem rxIntrinsicFaceImage_hits_le (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (region : Set E) :
    (familyHits (rxIntrinsicFaceImage P S J x) region).card ≤
      (familyHits (rxFaceImage P S J) region).card :=
  (familyHits_group_card_le (rxLocalSquareImage P S J x) region).trans
    (rxLocalSquareImage_hits_le P S J x region)

/-- The transposed intrinsic Z-local face has the same four actual quadrant images. -/
def rzIntrinsicFaceImage (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (J : Vertex P → E) (z : P.Z) (f : ZDoubleCylinderFace P z S) : Set E :=
  ⋃ corner, rzLocalSquareImage P A S J z (f, corner)

/-- The corresponding density restriction for the existing RZ intrinsic face carrier. -/
theorem rzIntrinsicFaceImage_hits_le (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (J : Vertex P → E) (z : P.Z) (region : Set E) :
    (familyHits (rzIntrinsicFaceImage P A S J z) region).card ≤
      (familyHits (rzFaceImage P A S J) region).card :=
  (familyHits_group_card_le (rzLocalSquareImage P A S J z) region).trans
    (rzLocalSquareImage_hits_le P A S J z region)

end IntrinsicFaceDensity

end QEC.Coding.BDL26ReplacementEmbedding
