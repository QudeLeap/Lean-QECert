import QEC.Coding.FiniteAlternatingConstruction.LocalRegularity

/-!
# BDL26 RZ local replacement

This module materializes the quotient-free `U_Z` successor tags frozen by the
BDL26 construction gate.  The carrier and face constructors below are explicit
finite sums over the original Tanner-square cells.  In particular, the
successor is not supplied by a caller and is not defined as an opaque transpose.

The first layer records the total endpoint functions needed for the constructed
successor presentation.  Pairing, admissibility, local cohomology, and induced
coordinate formulas are proved below from these constructors; none is stored in
a data field.
-/

namespace QEC
namespace Coding
namespace BDL26RZLocalReplacement

open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity

abbrev Field := BDL26FiniteTannerSquare.Field
abbrev Two := BDL26FiniteTannerSquare.Two

/-! ## Materialized quotient-free successor tags -/

/-- Degree-zero Tanner vertices of the materialized RZ successor. -/
abbrev RZX (P : TannerSquarePresentation) (S : OddScale) :=
  ((Sigma fun z : P.Z => ZDoubleCylinderFace P z S) ⊕
    (Sigma fun q : P.Q => QDoubleCylinderEdge (transposePresentation P) q S)) ⊕
    (P.X × Two)

/-- Degree-one Tanner vertices of the materialized RZ successor. -/
abbrev RZQ (P : TannerSquarePresentation) (S : OddScale) :=
  (Sigma fun z : P.Z => ZDoubleCylinderEdge P z S) ⊕
    (Sigma fun q : P.Q => QDoubleCylinderVertex (transposePresentation P) q S)

/-- Degree-two Tanner vertices of the materialized RZ successor. -/
abbrev RZZ (P : TannerSquarePresentation) (S : OddScale) :=
  Sigma fun z : P.Z => ZDoubleCylinderVertex P z S

/-- Local Z-star faces, with the two endpoint bits selecting one corner. -/
abbrev RZLocalFace (P : TannerSquarePresentation) (S : OddScale) :=
  Sigma fun z : P.Z => ZDoubleCylinderFace P z S × (Two × Two)

/-- Faces gluing one transposed Q-cylinder edge to its Z-boundary image. -/
abbrev RZQZGlueFace (P : TannerSquarePresentation) (S : OddScale) :=
  Sigma fun a : QZEdge P =>
    QDoubleCylinderEdge (transposePresentation P) a.1.1 S × Two

/-- The two copy faces retaining each original X endpoint. -/
abbrev RZOldXFace (P : TannerSquarePresentation) := P.Face × Two

/-- The exact three-family RZ face order. -/
abbrev RZFace (P : TannerSquarePresentation) (S : OddScale) :=
  RZLocalFace P S ⊕ (RZQZGlueFace P S ⊕ RZOldXFace P)

/-- Embed a grid index as the lower endpoint of a segment. -/
def lowerGridIndex {n : Nat} (i : Fin n) : Fin (n + 1) :=
  ⟨i.1, Nat.lt_succ_of_lt i.2⟩

/-- Embed a grid index as the upper endpoint of a segment. -/
def upperGridIndex {n : Nat} (i : Fin n) : Fin (n + 1) :=
  ⟨i.1 + 1, by omega⟩

/-- Select one of two values from its explicit endpoint bit. -/
def twoSelect {Value : Type} (first second : Value) (endpoint : Two) : Value :=
  if endpoint = 0 then first else second

/-- Select the lower or upper endpoint without any representative choice. -/
def gridEndpoint {n : Nat} (i : Fin n) (endpoint : Two) : Fin (n + 1) :=
  twoSelect (lowerGridIndex i) (upperGridIndex i) endpoint

/-- Select the start or end of an explicitly oriented edge. -/
def edgeEndpoint {Vertex Edge : Type} (start finish : Edge → Vertex)
    (edge : Edge) (endpoint : Two) : Vertex :=
  twoSelect (start edge) (finish edge) endpoint

private noncomputable def localCornerVertex
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale)
    (face : ZDoubleCylinderFace P z S) :
    (Two × Two) → ZDoubleCylinderVertex P z S
  | bits =>
      match face with
      | Sum.inl copyFace =>
          (copyFace.1,
            subdivisionGridVertex (transposePresentation P) z S copyFace.2.1
              (gridEndpoint copyFace.2.2.1 bits.1)
              (gridEndpoint copyFace.2.2.2 bits.2))
      | Sum.inr rectangle =>
          doubleCylinderRectangleCorner
            (transposePresentation P) z S rectangle bits

private noncomputable def localCornerEdge
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale)
    (face : ZDoubleCylinderFace P z S) :
    (Two × Two) × Two → ZDoubleCylinderEdge P z S
  | (bits, corner) =>
      match face with
      | Sum.inl copyFace =>
          if corner = 0 then
            Sum.inl (copyFace.1,
              subdivisionHorizontalEdge (transposePresentation P) z S
                copyFace.2.1 copyFace.2.2.1
                (gridEndpoint copyFace.2.2.2 bits.2))
          else
            Sum.inl (copyFace.1,
              subdivisionVerticalEdge (transposePresentation P) z S
                copyFace.2.1 (gridEndpoint copyFace.2.2.1 bits.1)
                copyFace.2.2.2)
      | Sum.inr rectangle =>
          if corner = 0 then Sum.inl (bits.1, rectangle.1)
          else Sum.inr
            (edgeEndpoint
              (subdivisionBoundaryEdgeStart (transposePresentation P) z S)
              (subdivisionBoundaryEdgeEnd (transposePresentation P) z S)
              rectangle bits.2)

private def localBoundarySlot (bits : Two × Two) (corner : Two) : Two × Two :=
  if corner = 0 then (0, bits.2) else (1, bits.1)

private theorem localCornerPair_injective
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale)
    (face : ZDoubleCylinderFace P z S) :
    Function.Injective (fun bc : (Two × Two) × Two =>
      (localCornerVertex P z S face bc.1,
        localCornerEdge P z S face bc)) := by
  classical
  rcases face with copyFace | rectangle
  · rcases copyFace with ⟨copy, face⟩
    rintro ⟨⟨firstI, firstJ⟩, firstCorner⟩
      ⟨⟨secondI, secondJ⟩, secondCorner⟩ h
    have hvertex := congrArg Prod.fst h
    have hedge := congrArg Prod.snd h
    change
      (copy, subdivisionGridVertex (transposePresentation P) z S face.1
          (gridEndpoint face.2.1 firstI) (gridEndpoint face.2.2 firstJ)) =
        (copy, subdivisionGridVertex (transposePresentation P) z S face.1
          (gridEndpoint face.2.1 secondI) (gridEndpoint face.2.2 secondJ))
      at hvertex
    have hgrid := congrArg Prod.snd hvertex
    change subdivisionGridVertex (transposePresentation P) z S face.1
        (gridEndpoint face.2.1 firstI) (gridEndpoint face.2.2 firstJ) =
      subdivisionGridVertex (transposePresentation P) z S face.1
        (gridEndpoint face.2.1 secondI) (gridEndpoint face.2.2 secondJ) at hgrid
    have hcoordinates := subdivisionGridVertex_fixedFace_injective
      (transposePresentation P) z S face.1
      (a₁ := (gridEndpoint face.2.1 firstI, gridEndpoint face.2.2 firstJ))
      (a₂ := (gridEndpoint face.2.1 secondI, gridEndpoint face.2.2 secondJ)) hgrid
    have hI : firstI = secondI := by
      fin_cases firstI <;> fin_cases secondI
      all_goals try rfl
      all_goals
        exfalso
        have hvalue := congrArg Fin.val (congrArg Prod.fst hcoordinates)
        simp [gridEndpoint, twoSelect, lowerGridIndex, upperGridIndex] at hvalue
    have hJ : firstJ = secondJ := by
      fin_cases firstJ <;> fin_cases secondJ
      all_goals try rfl
      all_goals
        exfalso
        have hvalue := congrArg Fin.val (congrArg Prod.snd hcoordinates)
        simp [gridEndpoint, twoSelect, lowerGridIndex, upperGridIndex] at hvalue
    subst secondI
    subst secondJ
    have hcorner : firstCorner = secondCorner := by
      have hedgeWrapped :
          (Sum.inl (copy, subdivisionFaceBoundaryEdge
              (transposePresentation P) z S face
                (localBoundarySlot (firstI, firstJ) firstCorner)) :
              ZDoubleCylinderEdge P z S) =
            (Sum.inl (copy, subdivisionFaceBoundaryEdge
              (transposePresentation P) z S face
                (localBoundarySlot (firstI, firstJ) secondCorner)) :
              ZDoubleCylinderEdge P z S) := by
        fin_cases firstI <;> fin_cases firstJ <;>
          fin_cases firstCorner <;> fin_cases secondCorner <;>
          simp [localCornerEdge, localBoundarySlot, gridEndpoint, twoSelect,
            lowerGridIndex, upperGridIndex, subdivisionFaceBoundaryEdge] at hedge ⊢
        all_goals exact hedge
      have hp := Sum.inl.inj hedgeWrapped
      have hedgeValue := congrArg Prod.snd hp
      have hslot := subdivisionFaceBoundaryEdge_injective
        (transposePresentation P) z S face
        (show subdivisionFaceBoundaryEdge (transposePresentation P) z S face
              (localBoundarySlot (firstI, firstJ) firstCorner) =
            subdivisionFaceBoundaryEdge (transposePresentation P) z S face
              (localBoundarySlot (firstI, firstJ) secondCorner) by
          simpa [localCornerEdge, localBoundarySlot, gridEndpoint,
            lowerGridIndex, upperGridIndex, subdivisionFaceBoundaryEdge]
            using hedgeValue)
      have hkind := congrArg Prod.fst hslot
      fin_cases firstCorner <;> fin_cases secondCorner <;>
        simp [localBoundarySlot] at hkind ⊢
    subst secondCorner
    rfl
  · rintro ⟨firstBits, firstCorner⟩ ⟨secondBits, secondCorner⟩ h
    have hbits := doubleCylinderRectangleCorner_injective
      (transposePresentation P) z S rectangle (congrArg Prod.fst h)
    cases hbits
    rcases firstBits with ⟨copy, endpoint⟩
    have hcorner : firstCorner = secondCorner := by
      fin_cases firstCorner <;> fin_cases secondCorner
      all_goals try rfl
      all_goals
        have hslots := doubleCylinderRectangleBoundaryEdge_injective
          (transposePresentation P) z S rectangle
        exfalso
        first
        | exact (Function.Injective.ne hslots
            (show (0, copy) ≠ ((1, endpoint) : Two × Two) by
              intro h; norm_num at h))
            (by simpa [localCornerEdge, edgeEndpoint,
              doubleCylinderRectangleBoundaryEdge] using congrArg Prod.snd h)
        | exact (Function.Injective.ne hslots
            (show (1, endpoint) ≠ ((0, copy) : Two × Two) by
              intro h; norm_num at h))
            (by simpa [localCornerEdge, edgeEndpoint,
              doubleCylinderRectangleBoundaryEdge] using congrArg Prod.snd h)
    subst secondCorner
    rfl

/-- The selected local Z corner determines its two endpoint bits once the
materialized local face is fixed.  This is the `F_local_Z` part of cellular
regularity; it uses only the explicit grid/rectangle constructors. -/
private theorem localCornerVertex_injective
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale)
    (face : ZDoubleCylinderFace P z S) :
    Function.Injective (localCornerVertex P z S face) := by
  classical
  rcases face with copyFace | rectangle
  · rcases copyFace with ⟨copy, face⟩
    rintro ⟨firstI, firstJ⟩ ⟨secondI, secondJ⟩ h
    change
      (copy, subdivisionGridVertex (transposePresentation P) z S face.1
          (gridEndpoint face.2.1 firstI) (gridEndpoint face.2.2 firstJ)) =
        (copy, subdivisionGridVertex (transposePresentation P) z S face.1
          (gridEndpoint face.2.1 secondI) (gridEndpoint face.2.2 secondJ)) at h
    have hcoordinates := subdivisionGridVertex_fixedFace_injective
      (transposePresentation P) z S face.1
      (a₁ := (gridEndpoint face.2.1 firstI, gridEndpoint face.2.2 firstJ))
      (a₂ := (gridEndpoint face.2.1 secondI, gridEndpoint face.2.2 secondJ))
      (congrArg Prod.snd h)
    apply Prod.ext
    · fin_cases firstI <;> fin_cases secondI
      all_goals try rfl
      all_goals
        exfalso
        have hvalue := congrArg Fin.val (congrArg Prod.fst hcoordinates)
        simp [gridEndpoint, twoSelect, lowerGridIndex, upperGridIndex] at hvalue
    · fin_cases firstJ <;> fin_cases secondJ
      all_goals try rfl
      all_goals
        exfalso
        have hvalue := congrArg Fin.val (congrArg Prod.snd hcoordinates)
        simp [gridEndpoint, twoSelect, lowerGridIndex, upperGridIndex] at hvalue
  · exact doubleCylinderRectangleCorner_injective
      (transposePresentation P) z S rectangle

/-- The final subdivision segment, which exists because an odd scale has
positive half-scale. -/
def lastHalfSegment (S : OddScale) : Fin S.half :=
  ⟨S.half - 1, by have := S.half_pos; omega⟩

/-- Regard an old face as a face of the Z-star obtained by materializing the
X-star of the transposed presentation. -/
noncomputable def oldFaceInZStar (P : TannerSquarePresentation) (f : P.Face) :
    XStarFace (transposePresentation P) (P.faceZ f) :=
  ⟨f, by
    simp [xStarFaceMember, transposePresentation, transposeTannerSquareData]⟩

/-! ## Local-face endpoints -/

/-- The two ordered corners of an original Tanner face are distinct; this is
derived from the presentation's sole perfect-pairing theorem. -/
theorem faceQ_zero_ne_one (P : TannerSquarePresentation) (face : P.Face) :
    P.faceQ face 0 ≠ P.faceQ face 1 := by
  intro hq
  let first : FaceOver P.data (P.faceX face) (P.faceZ face) × Two :=
    (⟨face, rfl, rfl⟩, 0)
  let second : FaceOver P.data (P.faceX face) (P.faceZ face) × Two :=
    (⟨face, rfl, rfl⟩, 1)
  have hshared : faceCornerToShared P.data (P.faceX face) (P.faceZ face) first =
      faceCornerToShared P.data (P.faceX face) (P.faceZ face) second := by
    apply Subtype.ext
    exact hq
  have hcorners := (P.perfectPairing (P.faceX face) (P.faceZ face)).1 hshared
  have hbits := congrArg (fun corner => corner.2.1) hcorners
  norm_num [first, second] at hbits

/-- The X endpoint of a local RZ face is its tagged Z-cylinder face. -/
def localFaceX (P : TannerSquarePresentation) (S : OddScale) :
    RZLocalFace P S → RZX P S
  | ⟨z, face, _⟩ => Sum.inl (Sum.inl ⟨z, face⟩)

/-- The selected Z endpoint of a local face.  End-copy squares use their grid
corner; boundary rectangles use the selected copy and boundary-edge endpoint. -/
noncomputable def localFaceZ (P : TannerSquarePresentation) (S : OddScale) :
    RZLocalFace P S → RZZ P S
  | ⟨z, Sum.inl copyFace, bits⟩ =>
      ⟨z, (copyFace.1,
        subdivisionGridVertex (transposePresentation P) z S copyFace.2.1
          (gridEndpoint copyFace.2.2.1 bits.1)
          (gridEndpoint copyFace.2.2.2 bits.2))⟩
  | ⟨z, Sum.inr boundaryEdge, bits⟩ =>
      ⟨z, (bits.1,
        (edgeEndpoint
          (subdivisionBoundaryEdgeStart (transposePresentation P) z S)
          (subdivisionBoundaryEdgeEnd (transposePresentation P) z S)
          boundaryEdge bits.2).1)⟩

/-- Ordered Q0 edge of a local RZ face. -/
noncomputable def localFaceQ0 (P : TannerSquarePresentation) (S : OddScale) :
    RZLocalFace P S → RZQ P S
  | ⟨z, Sum.inl copyFace, bits⟩ =>
      Sum.inl ⟨z, Sum.inl (copyFace.1,
        subdivisionHorizontalEdge (transposePresentation P) z S
          copyFace.2.1 copyFace.2.2.1
          (gridEndpoint copyFace.2.2.2 bits.2))⟩
  | ⟨z, Sum.inr boundaryEdge, bits⟩ =>
      Sum.inl ⟨z, Sum.inl (bits.1, boundaryEdge.1)⟩

/-- Ordered Q1 edge of a local RZ face. -/
noncomputable def localFaceQ1 (P : TannerSquarePresentation) (S : OddScale) :
    RZLocalFace P S → RZQ P S
  | ⟨z, Sum.inl copyFace, bits⟩ =>
      Sum.inl ⟨z, Sum.inl (copyFace.1,
        subdivisionVerticalEdge (transposePresentation P) z S
          copyFace.2.1 (gridEndpoint copyFace.2.2.1 bits.1)
          copyFace.2.2.2)⟩
  | ⟨z, Sum.inr boundaryEdge, bits⟩ =>
      Sum.inl ⟨z, Sum.inr
        (edgeEndpoint
          (subdivisionBoundaryEdgeStart (transposePresentation P) z S)
          (subdivisionBoundaryEdgeEnd (transposePresentation P) z S)
          boundaryEdge bits.2)⟩

/-! ## Q-Z glue endpoints -/

/-- A glue face retains the transposed Q-cylinder edge in the q summand of X. -/
def glueFaceX (P : TannerSquarePresentation) (S : OddScale) :
    RZQZGlueFace P S → RZX P S
  | ⟨a, edge, _⟩ => Sum.inl (Sum.inr ⟨a.1.1, edge⟩)

/-- The glue face's selected Z endpoint is the corresponding endpoint of the
same-edge Z-boundary image. -/
noncomputable def glueFaceZ (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) :
    RZQZGlueFace P S → RZZ P S
  | ⟨a, edge, endpoint⟩ =>
      ⟨a.1.2,
        qToZDoubleCylinderVertex P A a.1.1 a.1.2 a.2 S
          (edgeEndpoint
            (qDoubleCylinderEdgeStart (transposePresentation P) a.1.1 S)
            (qDoubleCylinderEdgeEnd (transposePresentation P) a.1.1 S)
            edge endpoint)⟩

/-- Ordered Q0 is the same-edge Z-boundary image. -/
noncomputable def glueFaceQ0 (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) :
    RZQZGlueFace P S → RZQ P S
  | ⟨a, edge, _⟩ =>
      Sum.inl ⟨a.1.2,
        qToZDoubleCylinderEdge P A a.1.1 a.1.2 a.2 S edge⟩

/-- Ordered Q1 is the selected transposed Q-cylinder endpoint. -/
noncomputable def glueFaceQ1 (P : TannerSquarePresentation) (S : OddScale) :
    RZQZGlueFace P S → RZQ P S
  | ⟨a, edge, endpoint⟩ =>
      Sum.inr ⟨a.1.1,
        edgeEndpoint
          (qDoubleCylinderEdgeStart (transposePresentation P) a.1.1 S)
          (qDoubleCylinderEdgeEnd (transposePresentation P) a.1.1 S)
          edge endpoint⟩

/-! ## Old-X copy-face endpoints -/

/-- The old X endpoint retains its copy tag. -/
def oldXFaceX (P : TannerSquarePresentation) (S : OddScale) :
    RZOldXFace P → RZX P S
  | (face, copy) => Sum.inr (P.faceX face, copy)

/-- The old-X face uses the copy-tagged old-X corner in its Z-star cylinder. -/
noncomputable def oldXFaceZ (P : TannerSquarePresentation) (S : OddScale) :
    RZOldXFace P → RZZ P S
  | (face, copy) =>
      ⟨P.faceZ face, (copy, Sum.inl
        (xStarFaceZVertex (transposePresentation P) (P.faceZ face)
          (oldFaceInZStar P face)))⟩

/-- The selected ordered Q corner is the copy-tagged Q-star endpoint frozen by
the owner-verified #892 recipe. -/
noncomputable def oldXFaceQ (P : TannerSquarePresentation) (S : OddScale)
    (corner : Two) : RZOldXFace P → RZQ P S
  | (face, copy) =>
      Sum.inr ⟨P.faceQ face corner,
        (copy, Sum.inl (Sum.inr
          (⟨P.faceX face, P.data.faceQ_xq face corner⟩ :
            QStarEdge (transposePresentation P) (P.faceQ face corner))))⟩

private theorem oldXFaceQ_maps_to_faceZ
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (face : P.Face) (copy corner : Two) :
    qToZDoubleCylinderVertex P A (P.faceQ face corner) (P.faceZ face)
        (P.data.faceQ_qz face corner) S
        (copy, Sum.inl (Sum.inr
          (⟨P.faceX face, P.data.faceQ_xq face corner⟩ :
            QStarEdge (transposePresentation P) (P.faceQ face corner)))) =
      (copy, Sum.inl (xStarFaceZVertex (transposePresentation P)
        (P.faceZ face) (oldFaceInZStar P face))) := by
  apply Prod.ext
  · rfl
  · apply congrArg Sum.inl
    apply Subtype.ext
    rfl

private theorem oldXFaceQ_congr
    (P : TannerSquarePresentation) (S : OddScale)
    (firstFace secondFace : P.Face) (firstCorner secondCorner copy : Two)
    (hX : P.faceX firstFace = P.faceX secondFace)
    (hQ : P.faceQ firstFace firstCorner =
      P.faceQ secondFace secondCorner) :
    oldXFaceQ P S firstCorner (firstFace, copy) =
      oldXFaceQ P S secondCorner (secondFace, copy) := by
  have hedge : HEq
      (⟨P.faceX firstFace, P.data.faceQ_xq firstFace firstCorner⟩ :
        QStarEdge (transposePresentation P)
          (P.faceQ firstFace firstCorner))
      (⟨P.faceX secondFace, P.data.faceQ_xq secondFace secondCorner⟩ :
        QStarEdge (transposePresentation P)
          (P.faceQ secondFace secondCorner)) := by
    apply (Subtype.heq_iff_coe_eq (fun x => by
      change P.xq x (P.faceQ firstFace firstCorner) = true ↔
        P.xq x (P.faceQ secondFace secondCorner) = true
      rw [hQ])).2
    exact hX
  simp only [oldXFaceQ]
  apply congrArg Sum.inr
  let wrap : (Sigma fun q : P.Q =>
      QStarEdge (transposePresentation P) q) →
      (Sigma fun q : P.Q =>
        QDoubleCylinderVertex (transposePresentation P) q S) :=
    fun edge => ⟨edge.1, (copy, Sum.inl (Sum.inr edge.2))⟩
  have hSigmaEdge :
      (⟨P.faceQ firstFace firstCorner,
        (⟨P.faceX firstFace,
          P.data.faceQ_xq firstFace firstCorner⟩ :
          QStarEdge (transposePresentation P)
            (P.faceQ firstFace firstCorner))⟩ :
        Sigma fun q : P.Q => QStarEdge (transposePresentation P) q) =
      (⟨P.faceQ secondFace secondCorner,
        (⟨P.faceX secondFace,
          P.data.faceQ_xq secondFace secondCorner⟩ :
          QStarEdge (transposePresentation P)
            (P.faceQ secondFace secondCorner))⟩ :
        Sigma fun q : P.Q => QStarEdge (transposePresentation P) q) :=
    Sigma.ext hQ hedge
  exact congrArg wrap hSigmaEdge

/-! ## Total ordered face-endpoint functions -/

def rzFaceX (P : TannerSquarePresentation) (S : OddScale) :
    RZFace P S → RZX P S
  | Sum.inl face => localFaceX P S face
  | Sum.inr (Sum.inl face) => glueFaceX P S face
  | Sum.inr (Sum.inr face) => oldXFaceX P S face

noncomputable def rzFaceZ (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) :
    RZFace P S → RZZ P S
  | Sum.inl face => localFaceZ P S face
  | Sum.inr (Sum.inl face) => glueFaceZ P A S face
  | Sum.inr (Sum.inr face) => oldXFaceZ P S face

noncomputable def rzFaceQ (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) :
    RZFace P S → Two → RZQ P S
  | Sum.inl face => fun corner =>
      twoSelect (localFaceQ0 P S face) (localFaceQ1 P S face) corner
  | Sum.inr (Sum.inl face) => fun corner =>
      twoSelect (glueFaceQ0 P A S face) (glueFaceQ1 P S face) corner
  | Sum.inr (Sum.inr face) => fun corner => oldXFaceQ P S corner face

/-! ## Raw successor incidence -/

/-- Constructor-level X-Q incidence for the materialized RZ successor.

The four cases are exactly the #892 recipe: a local double-cylinder face is
incident to its cellular boundary edges; a transposed Q-cylinder edge is
incident to its same-edge Z image and to its two endpoint Q vertices; and an
old-X copy is incident to the two final X-Q side segments selected by an old
face.  This relation contains no selected incident face and no validity field. -/
noncomputable def rzXQIncidence (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) :
    RZX P S → RZQ P S → Bool
  | Sum.inl (Sum.inl localFace), Sum.inl localEdge => by
      classical
      exact decide (Exists fun h : localEdge.1 = localFace.1 =>
        doubleCylinderFaceEdgeMatrix (transposePresentation P) localFace.1 S
          (h ▸ localEdge.2) localFace.2 = 1)
  | Sum.inl (Sum.inl _), Sum.inr _ => false
  | Sum.inl (Sum.inr qEdge), Sum.inl localEdge => by
      classical
      exact decide (Exists fun hqz : P.qz qEdge.1 localEdge.1 = true =>
        qToZDoubleCylinderEdge P A qEdge.1 localEdge.1 hqz S qEdge.2 =
          localEdge.2)
  | Sum.inl (Sum.inr qEdge), Sum.inr qVertex => by
      classical
      exact decide (Exists fun hq : qVertex.1 = qEdge.1 =>
        hq ▸ qVertex.2 =
            qDoubleCylinderEdgeStart (transposePresentation P) qEdge.1 S qEdge.2 ∨
          hq ▸ qVertex.2 =
            qDoubleCylinderEdgeEnd (transposePresentation P) qEdge.1 S qEdge.2)
  | Sum.inr _, Sum.inl _ => false
  | Sum.inr oldX, Sum.inr qVertex => by
      classical
      exact decide (Exists fun face : P.Face => Exists fun corner : Two =>
        P.faceX face = oldX.1 ∧
          oldXFaceQ P S corner (face, oldX.2) = Sum.inr qVertex)

/-- Constructor-level Q-Z incidence for the materialized RZ successor.

Local Z-cylinder edges use their explicit endpoint matrix.  A transposed
Q-cylinder vertex is incident to the same-tag vertex in every old Z neighbor,
via the theorem-derived #879 embedding. -/
noncomputable def rzQZIncidence (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) :
    RZQ P S → RZZ P S → Bool
  | Sum.inl localEdge, localVertex => by
      classical
      exact decide (Exists fun h : localVertex.1 = localEdge.1 =>
        doubleCylinderEdgeVertexMatrix (transposePresentation P) localEdge.1 S
          (h ▸ localVertex.2) localEdge.2 = 1)
  | Sum.inr qVertex, localVertex => by
      classical
      exact decide (Exists fun hqz : P.qz qVertex.1 localVertex.1 = true =>
        qToZDoubleCylinderVertex P A qVertex.1 localVertex.1 hqz S qVertex.2 =
          localVertex.2)

private theorem subdivisionFaceBoundaryEdge_matrix_eq_one
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : SubdivisionFace P x S) (slot : Two × Two) :
    subdivisionFaceEdgeMatrix P x S
        (subdivisionFaceBoundaryEdge P x S face slot) face = 1 :=
  (subdivisionFaceEdgeMatrix_eq_one_iff P x S _ face).2 ⟨slot, rfl⟩

private theorem doubleCylinderEndFaceBoundaryEdge_matrix_eq_one
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (copy : Two) (face : SubdivisionFace P x S) (slot : Two × Two) :
    doubleCylinderFaceEdgeMatrix P x S
        (Sum.inl (copy, subdivisionFaceBoundaryEdge P x S face slot))
        (Sum.inl (copy, face)) = 1 := by
  simpa using subdivisionFaceBoundaryEdge_matrix_eq_one P x S face slot

private theorem doubleCylinderRectangleBoundaryEdge_matrix_eq_one
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (rectangle : SubdivisionBoundaryEdge P x S) (slot : Two × Two) :
    doubleCylinderFaceEdgeMatrix P x S
        (doubleCylinderRectangleBoundaryEdge P x S rectangle slot)
        (Sum.inr rectangle) = 1 :=
  (doubleCylinderFaceEdgeMatrix_rectangle_eq_one_iff P x S _ rectangle).2
    ⟨slot, rfl⟩

private theorem subdivisionEdgeVertexMatrix_start_eq_one
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : SubdivisionEdge P x S) :
    subdivisionEdgeVertexMatrix P x S (subdivisionEdgeStart P x S edge) edge = 1 := by
  classical
  simp [subdivisionEdgeVertexMatrix, subdivisionEdgeStart_ne_end P x S edge]

private theorem subdivisionEdgeVertexMatrix_end_eq_one
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : SubdivisionEdge P x S) :
    subdivisionEdgeVertexMatrix P x S (subdivisionEdgeEnd P x S edge) edge = 1 := by
  classical
  simp [subdivisionEdgeVertexMatrix, subdivisionEdgeStart_ne_end P x S edge,
    Ne.symm (subdivisionEdgeStart_ne_end P x S edge)]

private theorem subdivisionBoundaryEdge_vertexMatrix_start_eq_one
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : SubdivisionBoundaryEdge P x S) :
    subdivisionEdgeVertexMatrix P x S
        (subdivisionBoundaryEdgeStart P x S edge).1 edge.1 = 1 := by
  rw [subdivisionBoundaryEdgeStart_value]
  exact subdivisionEdgeVertexMatrix_start_eq_one P x S edge.1

private theorem subdivisionBoundaryEdge_vertexMatrix_end_eq_one
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : SubdivisionBoundaryEdge P x S) :
    subdivisionEdgeVertexMatrix P x S
        (subdivisionBoundaryEdgeEnd P x S edge).1 edge.1 = 1 := by
  rw [subdivisionBoundaryEdgeEnd_value]
  exact subdivisionEdgeVertexMatrix_end_eq_one P x S edge.1

private theorem doubleCylinderEdgeVertexMatrix_start_eq_one
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : DoubleCylinderEdge P x S) :
    doubleCylinderEdgeVertexMatrix P x S
        (tannerDoubleCylinderEdgeStart P x S edge) edge = 1 := by
  rcases edge with ⟨copy, edge⟩ | vertex
  · simpa [tannerDoubleCylinderEdgeStart, doubleCylinderEdgeVertexMatrix]
      using subdivisionEdgeVertexMatrix_start_eq_one P x S edge
  · simp [tannerDoubleCylinderEdgeStart, doubleCylinderEdgeVertexMatrix]

private theorem doubleCylinderEdgeVertexMatrix_end_eq_one
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : DoubleCylinderEdge P x S) :
    doubleCylinderEdgeVertexMatrix P x S
        (tannerDoubleCylinderEdgeEnd P x S edge) edge = 1 := by
  rcases edge with ⟨copy, edge⟩ | vertex
  · simpa [tannerDoubleCylinderEdgeEnd, doubleCylinderEdgeVertexMatrix]
      using subdivisionEdgeVertexMatrix_end_eq_one P x S edge
  · simp [tannerDoubleCylinderEdgeEnd, doubleCylinderEdgeVertexMatrix]

private theorem subdivisionEdgeVertexMatrix_eq_one_iff
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (vertex : SubdivisionVertex P x S) (edge : SubdivisionEdge P x S) :
    subdivisionEdgeVertexMatrix P x S vertex edge = 1 ↔
      vertex = subdivisionEdgeStart P x S edge ∨
        vertex = subdivisionEdgeEnd P x S edge := by
  classical
  by_cases hstart : vertex = subdivisionEdgeStart P x S edge
  · subst vertex
    simp [subdivisionEdgeVertexMatrix,
      subdivisionEdgeStart_ne_end P x S edge]
  · by_cases hend : vertex = subdivisionEdgeEnd P x S edge
    · subst vertex
      simp [subdivisionEdgeVertexMatrix,
        Ne.symm (subdivisionEdgeStart_ne_end P x S edge)]
    · simp [subdivisionEdgeVertexMatrix, hstart, hend]

private theorem tannerDoubleCylinderEdgeStart_ne_end
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : DoubleCylinderEdge P x S) :
    tannerDoubleCylinderEdgeStart P x S edge ≠
      tannerDoubleCylinderEdgeEnd P x S edge := by
  rcases edge with ⟨copy, edge⟩ | boundaryVertex
  · simp only [tannerDoubleCylinderEdgeStart, tannerDoubleCylinderEdgeEnd]
    exact fun h => subdivisionEdgeStart_ne_end P x S edge
      (congrArg Prod.snd h)
  · simp [tannerDoubleCylinderEdgeStart, tannerDoubleCylinderEdgeEnd]

private theorem doubleCylinderEdgeVertexMatrix_eq_one_iff
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (vertex : DoubleCylinderVertex P x S) (edge : DoubleCylinderEdge P x S) :
    doubleCylinderEdgeVertexMatrix P x S vertex edge = 1 ↔
      vertex = tannerDoubleCylinderEdgeStart P x S edge ∨
        vertex = tannerDoubleCylinderEdgeEnd P x S edge := by
  classical
  rcases edge with ⟨copy, edge⟩ | boundaryVertex
  · rcases vertex with ⟨vertexCopy, vertex⟩
    fin_cases copy <;> fin_cases vertexCopy <;>
      simp [doubleCylinderEdgeVertexMatrix, tannerDoubleCylinderEdgeStart,
        tannerDoubleCylinderEdgeEnd,
        subdivisionEdgeVertexMatrix_eq_one_iff]
  · rcases vertex with ⟨copy, vertex⟩
    fin_cases copy <;>
      simp [doubleCylinderEdgeVertexMatrix, tannerDoubleCylinderEdgeStart,
        tannerDoubleCylinderEdgeEnd]

private theorem localCornerEdge_faceMatrix_eq_one
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale)
    (face : ZDoubleCylinderFace P z S) (bits : Two × Two) (corner : Two) :
    doubleCylinderFaceEdgeMatrix (transposePresentation P) z S
        (localCornerEdge P z S face (bits, corner)) face = 1 := by
  rcases face with ⟨copy, face⟩ | rectangle
  · rcases bits with ⟨first, second⟩
    fin_cases first <;> fin_cases second <;> fin_cases corner
    all_goals
      first
      | have h := doubleCylinderEndFaceBoundaryEdge_matrix_eq_one
            (transposePresentation P) z S copy face (0, 0)
        simp [localCornerEdge, gridEndpoint, twoSelect, lowerGridIndex, upperGridIndex,
          subdivisionFaceBoundaryEdge] at h ⊢
        exact h
      | have h := doubleCylinderEndFaceBoundaryEdge_matrix_eq_one
            (transposePresentation P) z S copy face (0, 1)
        simp [localCornerEdge, gridEndpoint, twoSelect, lowerGridIndex, upperGridIndex,
          subdivisionFaceBoundaryEdge] at h ⊢
        exact h
      | have h := doubleCylinderEndFaceBoundaryEdge_matrix_eq_one
            (transposePresentation P) z S copy face (1, 0)
        simp [localCornerEdge, gridEndpoint, twoSelect, lowerGridIndex, upperGridIndex,
          subdivisionFaceBoundaryEdge] at h ⊢
        exact h
      | have h := doubleCylinderEndFaceBoundaryEdge_matrix_eq_one
            (transposePresentation P) z S copy face (1, 1)
        simp [localCornerEdge, gridEndpoint, twoSelect, lowerGridIndex, upperGridIndex,
          subdivisionFaceBoundaryEdge] at h ⊢
        exact h
  · rcases bits with ⟨copy, endpoint⟩
    fin_cases copy <;> fin_cases endpoint <;> fin_cases corner
    all_goals
      first
      | simpa [localCornerEdge, edgeEndpoint, twoSelect,
          doubleCylinderRectangleBoundaryEdge] using
          doubleCylinderRectangleBoundaryEdge_matrix_eq_one
            (transposePresentation P) z S rectangle (0, 0)
      | simpa [localCornerEdge, edgeEndpoint, twoSelect,
          doubleCylinderRectangleBoundaryEdge] using
          doubleCylinderRectangleBoundaryEdge_matrix_eq_one
            (transposePresentation P) z S rectangle (0, 1)
      | simpa [localCornerEdge, edgeEndpoint, twoSelect,
          doubleCylinderRectangleBoundaryEdge] using
          doubleCylinderRectangleBoundaryEdge_matrix_eq_one
            (transposePresentation P) z S rectangle (1, 0)
      | simpa [localCornerEdge, edgeEndpoint, twoSelect,
          doubleCylinderRectangleBoundaryEdge] using
          doubleCylinderRectangleBoundaryEdge_matrix_eq_one
            (transposePresentation P) z S rectangle (1, 1)

private theorem localCornerEdge_vertexMatrix_eq_one
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale)
    (face : ZDoubleCylinderFace P z S) (bits : Two × Two) (corner : Two) :
    doubleCylinderEdgeVertexMatrix (transposePresentation P) z S
        (localCornerVertex P z S face bits)
        (localCornerEdge P z S face (bits, corner)) = 1 := by
  rcases face with ⟨copy, face⟩ | rectangle
  · rcases bits with ⟨first, second⟩
    fin_cases first <;> fin_cases second <;> fin_cases corner
    all_goals
      apply (doubleCylinderEdgeVertexMatrix_eq_one_iff
        (transposePresentation P) z S _ _).2
    all_goals
      simp [localCornerVertex, localCornerEdge, gridEndpoint, twoSelect,
        Fin.isValue, if_pos, if_false,
        lowerGridIndex, upperGridIndex, tannerDoubleCylinderEdgeStart,
        tannerDoubleCylinderEdgeEnd]
    all_goals
      first
      | left; exact (subdivisionHorizontalEdge_start
          (transposePresentation P) z S face.1 face.2.1 _).symm
      | right; exact (subdivisionHorizontalEdge_end
          (transposePresentation P) z S face.1 face.2.1 _).symm
      | left; exact (subdivisionVerticalEdge_start
          (transposePresentation P) z S face.1 _ face.2.2).symm
      | right; exact (subdivisionVerticalEdge_end
          (transposePresentation P) z S face.1 _ face.2.2).symm
  · rcases bits with ⟨copy, endpoint⟩
    fin_cases copy <;> fin_cases endpoint <;> fin_cases corner
    all_goals
      apply (doubleCylinderEdgeVertexMatrix_eq_one_iff
        (transposePresentation P) z S _ _).2
    all_goals
      simp [localCornerVertex, localCornerEdge, edgeEndpoint, twoSelect,
        doubleCylinderRectangleCorner, tannerDoubleCylinderEdgeStart,
        tannerDoubleCylinderEdgeEnd, subdivisionBoundaryEdgeStart_value,
        subdivisionBoundaryEdgeEnd_value]
    all_goals
      first
      | left; exact subdivisionBoundaryEdgeStart_value
          (transposePresentation P) z S rectangle
      | right; exact subdivisionBoundaryEdgeEnd_value
          (transposePresentation P) z S rectangle

private abbrev LocalCornerOver
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale)
    (face : ZDoubleCylinderFace P z S)
    (vertex : ZDoubleCylinderVertex P z S) :=
  {bits : Two × Two // localCornerVertex P z S face bits = vertex} × Two

private abbrev LocalSharedEdge
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale)
    (face : ZDoubleCylinderFace P z S)
    (vertex : ZDoubleCylinderVertex P z S) :=
  {edge : ZDoubleCylinderEdge P z S //
    doubleCylinderFaceEdgeMatrix (transposePresentation P) z S edge face = 1 ∧
      doubleCylinderEdgeVertexMatrix (transposePresentation P) z S
        vertex edge = 1}

private noncomputable def localCornerToSharedEdge
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale)
    (face : ZDoubleCylinderFace P z S)
    (vertex : ZDoubleCylinderVertex P z S) :
    LocalCornerOver P z S face vertex → LocalSharedEdge P z S face vertex
  | (bits, corner) =>
      ⟨localCornerEdge P z S face (bits.1, corner),
        localCornerEdge_faceMatrix_eq_one P z S face bits.1 corner, by
          simpa only [bits.2] using
            localCornerEdge_vertexMatrix_eq_one P z S face bits.1 corner⟩

private theorem localCornerToSharedEdge_injective
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale)
    (face : ZDoubleCylinderFace P z S)
    (vertex : ZDoubleCylinderVertex P z S) :
    Function.Injective (localCornerToSharedEdge P z S face vertex) := by
  rintro ⟨firstBits, firstCorner⟩ ⟨secondBits, secondCorner⟩ h
  have hvertex : localCornerVertex P z S face firstBits.1 =
      localCornerVertex P z S face secondBits.1 :=
    firstBits.2.trans secondBits.2.symm
  have hedge : localCornerEdge P z S face (firstBits.1, firstCorner) =
      localCornerEdge P z S face (secondBits.1, secondCorner) :=
    congrArg Subtype.val h
  have hpair := localCornerPair_injective P z S face
    (a₁ := (firstBits.1, firstCorner))
    (a₂ := (secondBits.1, secondCorner))
    (show
      (localCornerVertex P z S face firstBits.1,
          localCornerEdge P z S face (firstBits.1, firstCorner)) =
        (localCornerVertex P z S face secondBits.1,
          localCornerEdge P z S face (secondBits.1, secondCorner)) from
      Prod.ext hvertex hedge)
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun bc => bc.1) hpair
  · exact congrArg (fun bc => bc.2) hpair

private theorem localCornerToSharedEdge_surjective
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale)
    (face : ZDoubleCylinderFace P z S)
    (vertex : ZDoubleCylinderVertex P z S) :
    Function.Surjective (localCornerToSharedEdge P z S face vertex) := by
  classical
  intro shared
  rcases face with ⟨copy, face⟩ | rectangle
  · rcases shared with ⟨edge, hface, hvertex⟩
    rcases edge with ⟨edgeCopy, edge⟩ | vertical
    · have hcopy : edgeCopy = copy := by
        by_contra hne
        simp [doubleCylinderFaceEdgeMatrix, hne] at hface
      subst edgeCopy
      have hslot := (subdivisionFaceEdgeMatrix_eq_one_iff
          (transposePresentation P) z S edge face).1 (by
            simpa [doubleCylinderFaceEdgeMatrix] using hface)
      rcases hslot with ⟨slot, hslot⟩
      subst edge
      have hendpoint := (doubleCylinderEdgeVertexMatrix_eq_one_iff
          (transposePresentation P) z S vertex
            (Sum.inl (copy, subdivisionFaceBoundaryEdge
              (transposePresentation P) z S face slot))).1 hvertex
      let discharge (bits : Two × Two) (corner : Two)
          (hbits : localCornerVertex P z S (Sum.inl (copy, face)) bits = vertex)
          (hedge : localCornerEdge P z S (Sum.inl (copy, face))
              (bits, corner) = Sum.inl (copy, subdivisionFaceBoundaryEdge
                (transposePresentation P) z S face slot)) :
          ∃ preimage, localCornerToSharedEdge P z S
              (Sum.inl (copy, face)) vertex preimage =
            ⟨Sum.inl (copy, subdivisionFaceBoundaryEdge
              (transposePresentation P) z S face slot), hface, hvertex⟩ := by
        refine ⟨(⟨bits, hbits⟩, corner), ?_⟩
        apply Subtype.ext
        exact hedge
      rcases hendpoint with hstart | hend
      · rcases slot with ⟨kind, side⟩
        fin_cases kind <;> fin_cases side
        · apply discharge (0, 0) 0
          · have h := hstart.symm
            simp [subdivisionFaceBoundaryEdge, tannerDoubleCylinderEdgeStart] at h
            simp only [localCornerVertex, gridEndpoint, twoSelect]
            exact (congrArg (fun v => (copy, v))
              (subdivisionHorizontalEdge_start
                (transposePresentation P) z S face.1 face.2.1 _).symm).trans h
          · simp [localCornerEdge, gridEndpoint, twoSelect,
              subdivisionFaceBoundaryEdge]
            congr 3 <;> apply Fin.ext <;> rfl
        · apply discharge (0, 1) 0
          · have h := hstart.symm
            simp [subdivisionFaceBoundaryEdge, tannerDoubleCylinderEdgeStart] at h
            simp only [localCornerVertex, gridEndpoint, twoSelect]
            exact (congrArg (fun v => (copy, v))
              (subdivisionHorizontalEdge_start
                (transposePresentation P) z S face.1 face.2.1 _).symm).trans h
          · simp [localCornerEdge, gridEndpoint, twoSelect,
              subdivisionFaceBoundaryEdge]
            congr 3 <;> apply Fin.ext <;> rfl
        · apply discharge (0, 0) 1
          · have h := hstart.symm
            simp [subdivisionFaceBoundaryEdge, tannerDoubleCylinderEdgeStart] at h
            simp only [localCornerVertex, gridEndpoint, twoSelect]
            exact (congrArg (fun v => (copy, v))
              (subdivisionVerticalEdge_start
                (transposePresentation P) z S face.1 _ face.2.2).symm).trans h
          · simp [localCornerEdge, gridEndpoint, twoSelect,
              subdivisionFaceBoundaryEdge]
            congr 3 <;> apply Fin.ext <;> rfl
        · apply discharge (1, 0) 1
          · have h := hstart.symm
            simp [subdivisionFaceBoundaryEdge, tannerDoubleCylinderEdgeStart] at h
            simp only [localCornerVertex, gridEndpoint, twoSelect]
            exact (congrArg (fun v => (copy, v))
              (subdivisionVerticalEdge_start
                (transposePresentation P) z S face.1 _ face.2.2).symm).trans h
          · simp [localCornerEdge, gridEndpoint, twoSelect,
              subdivisionFaceBoundaryEdge]
            congr 3 <;> apply Fin.ext <;> rfl
      · rcases slot with ⟨kind, side⟩
        fin_cases kind <;> fin_cases side
        · apply discharge (1, 0) 0
          · have h := hend.symm
            simp [subdivisionFaceBoundaryEdge, tannerDoubleCylinderEdgeEnd] at h
            simp only [localCornerVertex, gridEndpoint, twoSelect]
            exact (congrArg (fun v => (copy, v))
              (subdivisionHorizontalEdge_end
                (transposePresentation P) z S face.1 face.2.1 _).symm).trans h
          · simp [localCornerEdge, gridEndpoint, twoSelect,
              subdivisionFaceBoundaryEdge]
            congr 3 <;> apply Fin.ext <;> rfl
        · apply discharge (1, 1) 0
          · have h := hend.symm
            simp [subdivisionFaceBoundaryEdge, tannerDoubleCylinderEdgeEnd] at h
            simp only [localCornerVertex, gridEndpoint, twoSelect]
            exact (congrArg (fun v => (copy, v))
              (subdivisionHorizontalEdge_end
                (transposePresentation P) z S face.1 face.2.1 _).symm).trans h
          · simp [localCornerEdge, gridEndpoint, twoSelect,
              subdivisionFaceBoundaryEdge]
            congr 3 <;> apply Fin.ext <;> rfl
        · apply discharge (0, 1) 1
          · have h := hend.symm
            simp [subdivisionFaceBoundaryEdge, tannerDoubleCylinderEdgeEnd] at h
            simp only [localCornerVertex, gridEndpoint, twoSelect]
            exact (congrArg (fun v => (copy, v))
              (subdivisionVerticalEdge_end
                (transposePresentation P) z S face.1 _ face.2.2).symm).trans h
          · simp [localCornerEdge, gridEndpoint, twoSelect,
              subdivisionFaceBoundaryEdge]
            congr 3 <;> apply Fin.ext <;> rfl
        · apply discharge (1, 1) 1
          · have h := hend.symm
            simp [subdivisionFaceBoundaryEdge, tannerDoubleCylinderEdgeEnd] at h
            simp only [localCornerVertex, gridEndpoint, twoSelect]
            exact (congrArg (fun v => (copy, v))
              (subdivisionVerticalEdge_end
                (transposePresentation P) z S face.1 _ face.2.2).symm).trans h
          · simp [localCornerEdge, gridEndpoint, twoSelect,
              subdivisionFaceBoundaryEdge]
            congr 3 <;> apply Fin.ext <;> rfl
    · simp [doubleCylinderFaceEdgeMatrix] at hface
  · rcases shared with ⟨edge, hface, hvertex⟩
    obtain ⟨slot, hslot⟩ :=
      (doubleCylinderFaceEdgeMatrix_rectangle_eq_one_iff
        (transposePresentation P) z S edge rectangle).1 hface
    subst edge
    have hendpoint := (doubleCylinderEdgeVertexMatrix_eq_one_iff
      (transposePresentation P) z S vertex
        (doubleCylinderRectangleBoundaryEdge
          (transposePresentation P) z S rectangle slot)).1 hvertex
    let discharge (bits : Two × Two) (corner : Two)
        (hbits : localCornerVertex P z S (Sum.inr rectangle) bits = vertex)
        (hedge : localCornerEdge P z S (Sum.inr rectangle) (bits, corner) =
          doubleCylinderRectangleBoundaryEdge
            (transposePresentation P) z S rectangle slot) :
        ∃ preimage, localCornerToSharedEdge P z S
            (Sum.inr rectangle) vertex preimage =
          ⟨doubleCylinderRectangleBoundaryEdge
            (transposePresentation P) z S rectangle slot, hface, hvertex⟩ := by
      refine ⟨(⟨bits, hbits⟩, corner), ?_⟩
      apply Subtype.ext
      exact hedge
    rcases hendpoint with hstart | hend
    · rcases slot with ⟨kind, side⟩
      fin_cases kind <;> fin_cases side
      · apply discharge (0, 0) 0
        · have h := hstart.symm
          simp [doubleCylinderRectangleBoundaryEdge, tannerDoubleCylinderEdgeStart] at h
          simp only [localCornerVertex, twoSelect, doubleCylinderRectangleCorner]
          exact (congrArg (fun v => ((0 : Two), v))
            (subdivisionBoundaryEdgeStart_value
              (transposePresentation P) z S rectangle)).trans h
        · simp [localCornerEdge, edgeEndpoint, twoSelect,
            doubleCylinderRectangleBoundaryEdge]
      · apply discharge (1, 0) 0
        · have h := hstart.symm
          simp [doubleCylinderRectangleBoundaryEdge, tannerDoubleCylinderEdgeStart] at h
          simp only [localCornerVertex, twoSelect, doubleCylinderRectangleCorner]
          exact (congrArg (fun v => ((1 : Two), v))
            (subdivisionBoundaryEdgeStart_value
              (transposePresentation P) z S rectangle)).trans h
        · simp [localCornerEdge, edgeEndpoint, twoSelect,
            doubleCylinderRectangleBoundaryEdge]
      · apply discharge (0, 0) 1
        · simpa [localCornerVertex, twoSelect,
            doubleCylinderRectangleCorner,
            doubleCylinderRectangleBoundaryEdge, tannerDoubleCylinderEdgeStart,
            subdivisionBoundaryEdgeStart_value] using hstart.symm
        · simp [localCornerEdge, edgeEndpoint, twoSelect,
            doubleCylinderRectangleBoundaryEdge]
      · apply discharge (0, 1) 1
        · simpa [localCornerVertex, twoSelect,
            doubleCylinderRectangleCorner,
            doubleCylinderRectangleBoundaryEdge, tannerDoubleCylinderEdgeStart,
            subdivisionBoundaryEdgeEnd_value] using hstart.symm
        · simp [localCornerEdge, edgeEndpoint, twoSelect,
            doubleCylinderRectangleBoundaryEdge]
    · rcases slot with ⟨kind, side⟩
      fin_cases kind <;> fin_cases side
      · apply discharge (0, 1) 0
        · have h := hend.symm
          simp [doubleCylinderRectangleBoundaryEdge, tannerDoubleCylinderEdgeEnd] at h
          simp only [localCornerVertex, twoSelect, doubleCylinderRectangleCorner]
          exact (congrArg (fun v => ((0 : Two), v))
            (subdivisionBoundaryEdgeEnd_value
              (transposePresentation P) z S rectangle)).trans h
        · simp [localCornerEdge, edgeEndpoint, twoSelect,
            doubleCylinderRectangleBoundaryEdge]
      · apply discharge (1, 1) 0
        · have h := hend.symm
          simp [doubleCylinderRectangleBoundaryEdge, tannerDoubleCylinderEdgeEnd] at h
          simp only [localCornerVertex, twoSelect, doubleCylinderRectangleCorner]
          exact (congrArg (fun v => ((1 : Two), v))
            (subdivisionBoundaryEdgeEnd_value
              (transposePresentation P) z S rectangle)).trans h
        · simp [localCornerEdge, edgeEndpoint, twoSelect,
            doubleCylinderRectangleBoundaryEdge]
      · apply discharge (1, 0) 1
        · simpa [localCornerVertex, twoSelect,
            doubleCylinderRectangleCorner,
            doubleCylinderRectangleBoundaryEdge, tannerDoubleCylinderEdgeEnd,
            subdivisionBoundaryEdgeStart_value] using hend.symm
        · simp [localCornerEdge, edgeEndpoint, twoSelect,
            doubleCylinderRectangleBoundaryEdge]
      · apply discharge (1, 1) 1
        · simpa [localCornerVertex, twoSelect,
            doubleCylinderRectangleCorner,
            doubleCylinderRectangleBoundaryEdge, tannerDoubleCylinderEdgeEnd,
            subdivisionBoundaryEdgeEnd_value] using hend.symm
        · simp [localCornerEdge, edgeEndpoint, twoSelect,
            doubleCylinderRectangleBoundaryEdge]

private theorem localCornerToSharedEdge_bijective
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale)
    (face : ZDoubleCylinderFace P z S)
    (vertex : ZDoubleCylinderVertex P z S) :
    Function.Bijective (localCornerToSharedEdge P z S face vertex) :=
  ⟨localCornerToSharedEdge_injective P z S face vertex,
    localCornerToSharedEdge_surjective P z S face vertex⟩

private noncomputable def glueCornerVertex
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (a : QZEdge P)
    (edge : QDoubleCylinderEdge (transposePresentation P) a.1.1 S) :
    Two → ZDoubleCylinderVertex P a.1.2 S := fun endpoint =>
  qToZDoubleCylinderVertex P A a.1.1 a.1.2 a.2 S
    (edgeEndpoint
      (qDoubleCylinderEdgeStart (transposePresentation P) a.1.1 S)
      (qDoubleCylinderEdgeEnd (transposePresentation P) a.1.1 S)
      edge endpoint)

private noncomputable def glueCornerQ
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (a : QZEdge P)
    (edge : QDoubleCylinderEdge (transposePresentation P) a.1.1 S) :
    Two × Two → RZQ P S
  | (endpoint, corner) =>
      if corner = 0 then
        Sum.inl ⟨a.1.2, qToZDoubleCylinderEdge P A a.1.1 a.1.2 a.2 S edge⟩
      else
        Sum.inr ⟨a.1.1,
          edgeEndpoint
            (qDoubleCylinderEdgeStart (transposePresentation P) a.1.1 S)
            (qDoubleCylinderEdgeEnd (transposePresentation P) a.1.1 S)
            edge endpoint⟩

private theorem qDoubleCylinderEdgeStart_ne_end
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (edge : QDoubleCylinderEdge P q S) :
    qDoubleCylinderEdgeStart P q S edge ≠
      qDoubleCylinderEdgeEnd P q S edge := by
  rcases edge with ⟨copy, edge, segment⟩ | endpoint
  · simp [qDoubleCylinderEdgeStart, qDoubleCylinderEdgeEnd,
      qSubdivisionEdgeStart, qSubdivisionEdgeEnd]
    by_cases hstart : segment.1 = 0
    · by_cases hend : segment.1 + 1 = S.half
      · have hhalf : S.half = 1 := by omega
        have hsegment : segment = ⟨0, S.half_pos⟩ := Fin.ext (by simpa using hstart)
        subst segment
        simp [hhalf, qStarEdgeStart, qStarEdgeEnd]
      · have hhalf : S.half ≠ 1 := by omega
        have hone : (1 : Nat) ≠ S.half := Ne.symm hhalf
        simp [hstart, hone, qStarEdgeStart, qStarEdgeEnd]
    · by_cases hend : segment.1 + 1 = S.half
      · simp [hstart, hend]
      · simp [hstart, hend, Fin.ext_iff]
        omega
  · simp [qDoubleCylinderEdgeStart, qDoubleCylinderEdgeEnd]

/-- A glue face's selected Z endpoint determines its endpoint bit once its
materialized Q-cylinder edge is fixed.  This is the `F_zqGlue_Z` part of
cellular regularity. -/
private theorem glueCornerVertex_injective
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (a : QZEdge P)
    (edge : QDoubleCylinderEdge (transposePresentation P) a.1.1 S) :
    Function.Injective (glueCornerVertex P A S a edge) := by
  intro firstEndpoint secondEndpoint hvertex
  have hselected := qToZDoubleCylinderVertex_injective
    P A a.1.1 a.1.2 a.2 S hvertex
  fin_cases firstEndpoint <;> fin_cases secondEndpoint <;> try rfl
  · exfalso
    exact qDoubleCylinderEdgeStart_ne_end
      (transposePresentation P) a.1.1 S edge (by
        simpa [glueCornerVertex, edgeEndpoint, twoSelect] using hselected)
  · exfalso
    exact qDoubleCylinderEdgeStart_ne_end
      (transposePresentation P) a.1.1 S edge (by
        simpa [glueCornerVertex, edgeEndpoint, twoSelect] using hselected.symm)

private theorem glueCornerPair_injective
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (a : QZEdge P)
    (edge : QDoubleCylinderEdge (transposePresentation P) a.1.1 S) :
    Function.Injective (fun ec : Two × Two =>
      (glueCornerVertex P A S a edge ec.1,
        glueCornerQ P A S a edge ec)) := by
  rintro ⟨firstEndpoint, firstCorner⟩ ⟨secondEndpoint, secondCorner⟩ h
  have hvertex := congrArg Prod.fst h
  have hq := congrArg Prod.snd h
  have hendpoint : firstEndpoint = secondEndpoint := by
    have hselected := qToZDoubleCylinderVertex_injective
      P A a.1.1 a.1.2 a.2 S hvertex
    fin_cases firstEndpoint <;> fin_cases secondEndpoint <;> try rfl
    · exfalso
      exact qDoubleCylinderEdgeStart_ne_end
        (transposePresentation P) a.1.1 S edge (by
          simpa [glueCornerVertex, edgeEndpoint, twoSelect] using hselected)
    · exfalso
      exact qDoubleCylinderEdgeStart_ne_end
        (transposePresentation P) a.1.1 S edge (by
          simpa [glueCornerVertex, edgeEndpoint, twoSelect] using hselected.symm)
  subst secondEndpoint
  have hcorner : firstCorner = secondCorner := by
    fin_cases firstCorner <;> fin_cases secondCorner <;> try rfl
    all_goals simp [glueCornerQ] at hq
  subst secondCorner
  rfl

/-- Recover the original Q label from the particular subdivision-edge shape
used by an old-X copy face.  The fallback makes this a total projection on the
whole successor Q carrier; it is definitionally irrelevant on old-X corners. -/
private def oldCornerQLabel
    (P : TannerSquarePresentation) (S : OddScale) (fallback : P.Q) :
    RZQ P S → P.Q
  | Sum.inr qVertex => qVertex.1
  | Sum.inl ⟨_, Sum.inl (_, Sum.inl (starEdge, _))⟩ =>
      match starEdge.1 with
      | Sum.inl xqEdge => xqEdge.1.2
      | Sum.inr qzEdge => qzEdge.1.1
  | _ => fallback

private theorem oldCornerPair_injective
    (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (z : P.Z) (copy : Two) :
    Function.Injective (fun fc : FaceOver P.data x z × Two =>
      (oldXFaceZ P S (fc.1.1, copy),
        oldXFaceQ P S fc.2 (fc.1.1, copy))) := by
  rintro ⟨firstFace, firstCorner⟩ ⟨secondFace, secondCorner⟩ h
  have hq := congrArg (fun pair : RZZ P S × RZQ P S => pair.2) h
  have hQ := congrArg
    (oldCornerQLabel P S (P.faceQ firstFace.1 firstCorner)) hq
  have hQ' : P.faceQ firstFace.1 firstCorner =
      P.faceQ secondFace.1 secondCorner := by
    simpa [oldXFaceQ, oldCornerQLabel] using hQ
  have hshared : faceCornerToShared P.data x z (firstFace, firstCorner) =
      faceCornerToShared P.data x z (secondFace, secondCorner) := by
    apply Subtype.ext
    exact hQ'
  exact (P.perfectPairing x z).1 hshared

/-- Raw finite RZ successor data.  Validity is deliberately not a field here;
`perfectPairing` remains a theorem obligation before packaging a presentation. -/
noncomputable def rzReplacementData (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) : TannerSquareData := by
  classical
  exact
    { X := RZX P S
      Q := RZQ P S
      Z := RZZ P S
      Face := RZFace P S
      xFintype := inferInstance
      qFintype := inferInstance
      zFintype := inferInstance
      faceFintype := inferInstance
      xDecidableEq := Classical.decEq _
      qDecidableEq := Classical.decEq _
      zDecidableEq := Classical.decEq _
      faceDecidableEq := Classical.decEq _
      xq := rzXQIncidence P A S
      qz := rzQZIncidence P A S
      faceX := rzFaceX P S
      faceZ := rzFaceZ P A S
      faceQ := rzFaceQ P A S
      faceQ_xq := by
        intro face corner
        rcases face with localFace | glueOrOld
        · rcases localFace with ⟨z, localCell, bits⟩
          rcases localCell with copyFace | rectangle
          · rcases copyFace with ⟨copy, smallFace⟩
            rcases bits with ⟨first, second⟩
            fin_cases first <;> fin_cases second <;> fin_cases corner
            all_goals
              simp only [rzFaceX, rzFaceQ, localFaceX, localFaceQ0,
                localFaceQ1, twoSelect, if_pos, if_false, rzXQIncidence]
              apply decide_eq_true
              refine ⟨rfl, ?_⟩
            all_goals
              first
              | have h := doubleCylinderEndFaceBoundaryEdge_matrix_eq_one
                  (transposePresentation P) z S copy smallFace (0, 0)
                simp [gridEndpoint, twoSelect, lowerGridIndex, upperGridIndex,
                  subdivisionFaceBoundaryEdge] at h ⊢
                exact h
              | have h := doubleCylinderEndFaceBoundaryEdge_matrix_eq_one
                  (transposePresentation P) z S copy smallFace (0, 1)
                simp [gridEndpoint, twoSelect, lowerGridIndex, upperGridIndex,
                  subdivisionFaceBoundaryEdge] at h ⊢
                exact h
              | have h := doubleCylinderEndFaceBoundaryEdge_matrix_eq_one
                  (transposePresentation P) z S copy smallFace (1, 0)
                simp [gridEndpoint, twoSelect, lowerGridIndex, upperGridIndex,
                  subdivisionFaceBoundaryEdge] at h ⊢
                exact h
              | have h := doubleCylinderEndFaceBoundaryEdge_matrix_eq_one
                  (transposePresentation P) z S copy smallFace (1, 1)
                simp [gridEndpoint, twoSelect, lowerGridIndex, upperGridIndex,
                  subdivisionFaceBoundaryEdge] at h ⊢
                exact h
          · rcases bits with ⟨copy, endpoint⟩
            fin_cases copy <;> fin_cases endpoint <;> fin_cases corner
            all_goals
              simp only [rzFaceX, rzFaceQ, localFaceX, localFaceQ0,
                localFaceQ1, twoSelect, if_pos, if_false, rzXQIncidence]
              apply decide_eq_true
              refine ⟨rfl, ?_⟩
            all_goals
              first
              | simpa [edgeEndpoint, twoSelect, doubleCylinderRectangleBoundaryEdge] using
                  doubleCylinderRectangleBoundaryEdge_matrix_eq_one
                    (transposePresentation P) z S rectangle (0, 0)
              | simpa [edgeEndpoint, twoSelect, doubleCylinderRectangleBoundaryEdge] using
                  doubleCylinderRectangleBoundaryEdge_matrix_eq_one
                    (transposePresentation P) z S rectangle (0, 1)
              | simpa [edgeEndpoint, twoSelect, doubleCylinderRectangleBoundaryEdge] using
                  doubleCylinderRectangleBoundaryEdge_matrix_eq_one
                    (transposePresentation P) z S rectangle (1, 0)
              | simpa [edgeEndpoint, twoSelect, doubleCylinderRectangleBoundaryEdge] using
                  doubleCylinderRectangleBoundaryEdge_matrix_eq_one
                    (transposePresentation P) z S rectangle (1, 1)
        · rcases glueOrOld with glueFace | oldFace
          · rcases glueFace with ⟨edge, qEdge, endpoint⟩
            fin_cases endpoint <;> fin_cases corner
            · simp only [rzFaceX, rzFaceQ, glueFaceX, glueFaceQ0,
                twoSelect, if_pos, rzXQIncidence]
              apply decide_eq_true
              exact ⟨edge.2, rfl⟩
            · simp only [rzFaceX, rzFaceQ, glueFaceX, glueFaceQ1,
                twoSelect, if_false, Fin.zero_eta, edgeEndpoint,
                rzXQIncidence]
              apply decide_eq_true
              exact ⟨rfl, Or.inl rfl⟩
            · simp only [rzFaceX, rzFaceQ, glueFaceX, glueFaceQ0,
                twoSelect, if_pos, rzXQIncidence]
              apply decide_eq_true
              exact ⟨edge.2, rfl⟩
            · simp only [rzFaceX, rzFaceQ, glueFaceX, glueFaceQ1,
                twoSelect, if_false, Fin.isValue, edgeEndpoint,
                rzXQIncidence]
              apply decide_eq_true
              exact ⟨rfl, Or.inr rfl⟩
          · rcases oldFace with ⟨face, copy⟩
            fin_cases corner
            all_goals
              simp only [rzFaceX, rzFaceQ, oldXFaceX, oldXFaceQ,
                rzXQIncidence]
              apply decide_eq_true
            · exact ⟨face, 0, rfl, rfl⟩
            · exact ⟨face, 1, rfl, rfl⟩
      faceQ_qz := by
        intro face corner
        rcases face with localFace | glueOrOld
        · rcases localFace with ⟨z, localCell, bits⟩
          rcases localCell with copyFace | rectangle
          · rcases copyFace with ⟨copy, smallFace⟩
            have h := localCornerEdge_vertexMatrix_eq_one
              P z S (Sum.inl (copy, smallFace)) bits corner
            rcases bits with ⟨first, second⟩
            fin_cases first <;> fin_cases second <;> fin_cases corner
            all_goals
              simp only [rzFaceQ, rzFaceZ, localFaceQ0, localFaceQ1,
                localFaceZ, twoSelect, if_pos, if_false, rzQZIncidence]
              apply decide_eq_true
              refine ⟨rfl, ?_⟩
              simp [localCornerVertex, localCornerEdge, gridEndpoint, twoSelect] at h
              exact h
          · rcases bits with ⟨copy, endpoint⟩
            fin_cases copy <;> fin_cases endpoint <;> fin_cases corner
            all_goals
              simp only [rzFaceQ, rzFaceZ, localFaceQ0, localFaceQ1,
                localFaceZ, twoSelect, if_pos, if_false, rzQZIncidence]
              apply decide_eq_true
              refine ⟨rfl, ?_⟩
            all_goals
              first
              | simpa [edgeEndpoint, twoSelect,
                  doubleCylinderEdgeVertexMatrix] using
                  subdivisionBoundaryEdge_vertexMatrix_start_eq_one
                    (transposePresentation P) z S rectangle
              | simpa [edgeEndpoint, twoSelect,
                  doubleCylinderEdgeVertexMatrix] using
                  subdivisionBoundaryEdge_vertexMatrix_end_eq_one
                    (transposePresentation P) z S rectangle
        · rcases glueOrOld with glueFace | oldFace
          · rcases glueFace with ⟨edge, qEdge, endpoint⟩
            fin_cases endpoint <;> fin_cases corner
            · simp only [rzFaceQ, rzFaceZ, glueFaceQ0, glueFaceZ,
                twoSelect, if_pos, edgeEndpoint, rzQZIncidence]
              apply decide_eq_true
              refine ⟨rfl, ?_⟩
              simpa [qToZDoubleCylinderEdge_start] using
                doubleCylinderEdgeVertexMatrix_start_eq_one
                  (transposePresentation P) edge.1.2 S
                  (qToZDoubleCylinderEdge P A edge.1.1 edge.1.2 edge.2 S qEdge)
            · simp only [rzFaceQ, rzFaceZ, glueFaceQ1, glueFaceZ,
                twoSelect, if_false, Fin.zero_eta, edgeEndpoint,
                rzQZIncidence]
              apply decide_eq_true
              exact ⟨edge.2, rfl⟩
            · simp only [rzFaceQ, rzFaceZ, glueFaceQ0, glueFaceZ,
                twoSelect, if_pos, edgeEndpoint, rzQZIncidence]
              apply decide_eq_true
              refine ⟨rfl, ?_⟩
              simpa [qToZDoubleCylinderEdge_end] using
                doubleCylinderEdgeVertexMatrix_end_eq_one
                  (transposePresentation P) edge.1.2 S
                  (qToZDoubleCylinderEdge P A edge.1.1 edge.1.2 edge.2 S qEdge)
            · simp only [rzFaceQ, rzFaceZ, glueFaceQ1, glueFaceZ,
                twoSelect, if_false, Fin.isValue, edgeEndpoint,
                rzQZIncidence]
              apply decide_eq_true
              exact ⟨edge.2, rfl⟩
          · rcases oldFace with ⟨face, copy⟩
            fin_cases corner
            all_goals
              simp only [rzFaceQ, rzFaceZ, oldXFaceQ, oldXFaceZ,
                rzQZIncidence]
              apply decide_eq_true
              refine ⟨P.data.faceQ_qz face _, ?_⟩
              exact oldXFaceQ_maps_to_faceZ P A S face copy _ }

private theorem localFaceZ_eq_corner
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z)
    (face : ZDoubleCylinderFace P z S) (bits : Two × Two) :
    localFaceZ P S ⟨z, face, bits⟩ =
      ⟨z, localCornerVertex P z S face bits⟩ := by
  rcases face with copyFace | rectangle
  · rfl
  · rcases bits with ⟨copy, endpoint⟩
    fin_cases endpoint <;>
      simp [localFaceZ, localCornerVertex, doubleCylinderRectangleCorner,
        edgeEndpoint, twoSelect, subdivisionBoundaryEdgeStart_value,
        subdivisionBoundaryEdgeEnd_value]

private theorem localFaceQ_eq_corner
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z)
    (face : ZDoubleCylinderFace P z S) (bits : Two × Two)
    (corner : Two) :
    twoSelect (localFaceQ0 P S ⟨z, face, bits⟩)
        (localFaceQ1 P S ⟨z, face, bits⟩) corner =
      Sum.inl ⟨z, localCornerEdge P z S face (bits, corner)⟩ := by
  rcases face with copyFace | rectangle <;> fin_cases corner <;>
    simp [localFaceQ0, localFaceQ1, localCornerEdge, twoSelect]

private theorem rzReplacementFaceCorner_injective
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (x : (rzReplacementData P A S).X)
    (z : (rzReplacementData P A S).Z) :
    Function.Injective
      (faceCornerToShared (rzReplacementData P A S) x z) := by
  classical
  rintro ⟨⟨firstFace, hfirstX, hfirstZ⟩, firstCorner⟩
    ⟨⟨secondFace, hsecondX, hsecondZ⟩, secondCorner⟩ hshared
  have hfaceX : rzFaceX P S firstFace = rzFaceX P S secondFace :=
    hfirstX.trans hsecondX.symm
  have hfaceZ : rzFaceZ P A S firstFace = rzFaceZ P A S secondFace :=
    hfirstZ.trans hsecondZ.symm
  have hq : rzFaceQ P A S firstFace firstCorner =
      rzFaceQ P A S secondFace secondCorner := by
    exact congrArg Subtype.val hshared
  rcases firstFace with ⟨firstLocalZ, firstLocalFace, firstBits⟩ |
      (⟨firstGlue, firstGlueEdge, firstEndpoint⟩ | ⟨firstOldFace, firstCopy⟩)
  · rcases secondFace with ⟨secondLocalZ, secondLocalFace, secondBits⟩ |
        (⟨secondGlue, secondGlueEdge, secondEndpoint⟩ |
          ⟨secondOldFace, secondCopy⟩)
    · have hlocalX :
          (⟨firstLocalZ, firstLocalFace⟩ :
              Sigma fun z : P.Z => ZDoubleCylinderFace P z S) =
            ⟨secondLocalZ, secondLocalFace⟩ := by
          simpa [rzFaceX, localFaceX] using hfaceX
      cases hlocalX
      have hvertex : localCornerVertex P firstLocalZ S firstLocalFace firstBits =
          localCornerVertex P firstLocalZ S firstLocalFace secondBits := by
        change localFaceZ P S
            ⟨firstLocalZ, firstLocalFace, firstBits⟩ =
          localFaceZ P S ⟨firstLocalZ, firstLocalFace, secondBits⟩ at hfaceZ
        rw [localFaceZ_eq_corner, localFaceZ_eq_corner] at hfaceZ
        exact eq_of_heq (Sigma.mk.inj_iff.mp hfaceZ).2
      have hedge :
          localCornerEdge P firstLocalZ S firstLocalFace
              (firstBits, firstCorner) =
            localCornerEdge P firstLocalZ S firstLocalFace
              (secondBits, secondCorner) := by
        rw [show rzFaceQ P A S
              (Sum.inl ⟨firstLocalZ, firstLocalFace, firstBits⟩)
                firstCorner =
              twoSelect
                (localFaceQ0 P S ⟨firstLocalZ, firstLocalFace, firstBits⟩)
                (localFaceQ1 P S ⟨firstLocalZ, firstLocalFace, firstBits⟩)
                firstCorner by rfl,
            show rzFaceQ P A S
              (Sum.inl ⟨firstLocalZ, firstLocalFace, secondBits⟩)
                secondCorner =
              twoSelect
                (localFaceQ0 P S ⟨firstLocalZ, firstLocalFace, secondBits⟩)
                (localFaceQ1 P S ⟨firstLocalZ, firstLocalFace, secondBits⟩)
                secondCorner by rfl,
            localFaceQ_eq_corner, localFaceQ_eq_corner] at hq
        exact eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inl.inj hq)).2
      have hpair := localCornerPair_injective P firstLocalZ S firstLocalFace
        (a₁ := (firstBits, firstCorner))
        (a₂ := (secondBits, secondCorner)) (Prod.ext hvertex hedge)
      cases hpair
      rfl
    · simp [rzFaceX, localFaceX, glueFaceX] at hfaceX
    · simp [rzFaceX, localFaceX, oldXFaceX] at hfaceX
  · rcases secondFace with ⟨secondLocalZ, secondLocalFace, secondBits⟩ |
        (⟨secondGlue, secondGlueEdge, secondEndpoint⟩ |
          ⟨secondOldFace, secondCopy⟩)
    · simp [rzFaceX, localFaceX, glueFaceX] at hfaceX
    · have hglueX :
          (⟨firstGlue.1.1, firstGlueEdge⟩ :
              Sigma fun q : P.Q =>
                QDoubleCylinderEdge (transposePresentation P) q S) =
            ⟨secondGlue.1.1, secondGlueEdge⟩ := by
          simpa [rzFaceX, glueFaceX] using hfaceX
      have hqtag : firstGlue.1.1 = secondGlue.1.1 :=
        congrArg Sigma.fst hglueX
      have hzsigma :
          (⟨firstGlue.1.2, glueCornerVertex P A S firstGlue firstGlueEdge
              firstEndpoint⟩ :
                Sigma fun z : P.Z => ZDoubleCylinderVertex P z S) =
            ⟨secondGlue.1.2, glueCornerVertex P A S secondGlue secondGlueEdge
              secondEndpoint⟩ := by
        simpa [rzFaceZ, glueFaceZ, glueCornerVertex] using hfaceZ
      have hztag : firstGlue.1.2 = secondGlue.1.2 :=
        congrArg Sigma.fst hzsigma
      have hglue : firstGlue = secondGlue := by
        apply Subtype.ext
        exact Prod.ext hqtag hztag
      subst secondGlue
      have hedge : firstGlueEdge = secondGlueEdge :=
        eq_of_heq (Sigma.mk.inj_iff.mp hglueX).2
      subst secondGlueEdge
      have hvertex :
          glueCornerVertex P A S firstGlue firstGlueEdge firstEndpoint =
            glueCornerVertex P A S firstGlue firstGlueEdge secondEndpoint :=
        eq_of_heq (Sigma.mk.inj_iff.mp hzsigma).2
      have hq' : glueCornerQ P A S firstGlue firstGlueEdge
            (firstEndpoint, firstCorner) =
          glueCornerQ P A S firstGlue firstGlueEdge
            (secondEndpoint, secondCorner) := by
        simpa [rzFaceQ, glueCornerQ, glueFaceQ0, glueFaceQ1, twoSelect] using hq
      have hpair := glueCornerPair_injective P A S firstGlue firstGlueEdge
        (a₁ := (firstEndpoint, firstCorner))
        (a₂ := (secondEndpoint, secondCorner)) (Prod.ext hvertex hq')
      cases hpair
      rfl
    · simp [rzFaceX, glueFaceX, oldXFaceX] at hfaceX
  · rcases secondFace with ⟨secondLocalZ, secondLocalFace, secondBits⟩ |
        (⟨secondGlue, secondGlueEdge, secondEndpoint⟩ |
          ⟨secondOldFace, secondCopy⟩)
    · simp [rzFaceX, localFaceX, oldXFaceX] at hfaceX
    · simp [rzFaceX, glueFaceX, oldXFaceX] at hfaceX
    · have hxcopy :
          (P.faceX firstOldFace, firstCopy) =
            (P.faceX secondOldFace, secondCopy) := by
          simpa [rzFaceX, oldXFaceX] using hfaceX
      have hx : P.faceX firstOldFace = P.faceX secondOldFace :=
        congrArg Prod.fst hxcopy
      have hcopy : firstCopy = secondCopy := congrArg Prod.snd hxcopy
      have hz : P.faceZ firstOldFace = P.faceZ secondOldFace := by
        have hsigma :
            (⟨P.faceZ firstOldFace,
                (firstCopy, Sum.inl (xStarFaceZVertex
                  (transposePresentation P) (P.faceZ firstOldFace)
                    (oldFaceInZStar P firstOldFace)))⟩ :
                  Sigma fun z : P.Z => ZDoubleCylinderVertex P z S) =
              ⟨P.faceZ secondOldFace,
                (secondCopy, Sum.inl (xStarFaceZVertex
                  (transposePresentation P) (P.faceZ secondOldFace)
                    (oldFaceInZStar P secondOldFace)))⟩ := by
          simpa [rzFaceZ, oldXFaceZ] using hfaceZ
        exact congrArg Sigma.fst hsigma
      subst secondCopy
      let firstOver : FaceOver P.data (P.faceX firstOldFace)
          (P.faceZ firstOldFace) := ⟨firstOldFace, rfl, rfl⟩
      let secondOver : FaceOver P.data (P.faceX firstOldFace)
          (P.faceZ firstOldFace) := ⟨secondOldFace, hx.symm, hz.symm⟩
      have hold := oldCornerPair_injective P S
        (P.faceX firstOldFace) (P.faceZ firstOldFace) firstCopy
        (a₁ := (firstOver, firstCorner))
        (a₂ := (secondOver, secondCorner)) (by
          apply Prod.ext
          · simpa [firstOver, secondOver, rzFaceZ] using hfaceZ
          · simpa [firstOver, secondOver, rzFaceQ] using hq)
      have hface : firstOldFace = secondOldFace :=
        congrArg (fun fc => fc.1.1) hold
      have hcorner : firstCorner = secondCorner :=
        congrArg (fun fc => fc.2) hold
      subst secondOldFace
      subst secondCorner
      rfl

private theorem rzReplacementFaceCorner_surjective
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (x : (rzReplacementData P A S).X)
    (z : (rzReplacementData P A S).Z) :
    Function.Surjective
      (faceCornerToShared (rzReplacementData P A S) x z) := by
  classical
  intro shared
  rcases x with (localX | glueX) | oldX
  · rcases localX with ⟨localZ, localFace⟩
    rcases z with ⟨targetZ, targetVertex⟩
    rcases shared with ⟨sharedQ, hshared⟩
    have hinc :=
      (Bool.and_eq_true_eq_eq_true_and_eq_true _ _).mp hshared
    rcases sharedQ with localEdge | qVertex
    · rcases localEdge with ⟨localEdgeZ, localEdge⟩
      have hxq : rzXQIncidence P A S
          (Sum.inl (Sum.inl ⟨localZ, localFace⟩))
          (Sum.inl ⟨localEdgeZ, localEdge⟩) = true := hinc.1
      have hqz : rzQZIncidence P A S (Sum.inl ⟨localEdgeZ, localEdge⟩)
          ⟨targetZ, targetVertex⟩ = true := hinc.2
      obtain ⟨hedgeTag, hface⟩ := of_decide_eq_true hxq
      obtain ⟨hvertexTag, hvertex⟩ := of_decide_eq_true hqz
      cases hedgeTag
      cases hvertexTag
      let localShared : LocalSharedEdge P localZ S localFace targetVertex :=
        ⟨localEdge, hface, hvertex⟩
      obtain ⟨preimage, hpreimage⟩ :=
        localCornerToSharedEdge_surjective P localZ S localFace
          targetVertex localShared
      rcases preimage with ⟨bits, corner⟩
      refine ⟨(⟨Sum.inl ⟨localZ, localFace, bits.1⟩, rfl, ?_⟩,
        corner), ?_⟩
      · change rzFaceZ P A S (Sum.inl ⟨localZ, localFace, bits.1⟩) =
          ⟨localZ, targetVertex⟩
        rw [show rzFaceZ P A S (Sum.inl ⟨localZ, localFace, bits.1⟩) =
            localFaceZ P S ⟨localZ, localFace, bits.1⟩ by rfl]
        rw [localFaceZ_eq_corner, bits.2]
      · apply Subtype.ext
        change rzFaceQ P A S (Sum.inl ⟨localZ, localFace, bits.1⟩) corner =
          Sum.inl ⟨localZ, localEdge⟩
        have hedge := congrArg Subtype.val hpreimage
        simpa [rzFaceQ, localFaceQ_eq_corner, localCornerToSharedEdge,
          localShared] using hedge
    · have hxq := hinc.1
      change false = true at hxq
      exact Bool.noConfusion hxq
  · rcases glueX with ⟨glueQ, glueEdge⟩
    rcases z with ⟨targetZ, targetVertex⟩
    rcases shared with ⟨sharedQ, hshared⟩
    have hinc :=
      (Bool.and_eq_true_eq_eq_true_and_eq_true _ _).mp hshared
    rcases sharedQ with localEdge | qVertex
    · rcases localEdge with ⟨localEdgeZ, localEdge⟩
      have hxq : rzXQIncidence P A S
          (Sum.inl (Sum.inr ⟨glueQ, glueEdge⟩))
          (Sum.inl ⟨localEdgeZ, localEdge⟩) = true := hinc.1
      have hqz : rzQZIncidence P A S (Sum.inl ⟨localEdgeZ, localEdge⟩)
          ⟨targetZ, targetVertex⟩ = true := hinc.2
      obtain ⟨hglueQZ, hedge⟩ := of_decide_eq_true hxq
      obtain ⟨hvertexTag, hvertex⟩ := of_decide_eq_true hqz
      cases hvertexTag
      change qToZDoubleCylinderEdge P A glueQ targetZ hglueQZ S glueEdge =
        localEdge at hedge
      let a : QZEdge P := ⟨(glueQ, targetZ), hglueQZ⟩
      have hendpoint := (doubleCylinderEdgeVertexMatrix_eq_one_iff
        (transposePresentation P) targetZ S targetVertex localEdge).1 hvertex
      rcases hendpoint with hstart | hend
      · refine ⟨(⟨Sum.inr (Sum.inl ⟨a, glueEdge, 0⟩), rfl, ?_⟩, 0), ?_⟩
        · change rzFaceZ P A S (Sum.inr (Sum.inl ⟨a, glueEdge, 0⟩)) =
            ⟨targetZ, targetVertex⟩
          rw [show rzFaceZ P A S (Sum.inr (Sum.inl ⟨a, glueEdge, 0⟩)) =
              glueFaceZ P A S ⟨a, glueEdge, 0⟩ by rfl]
          change
            (⟨targetZ,
              qToZDoubleCylinderVertex P A glueQ targetZ hglueQZ S
                (edgeEndpoint
                  (qDoubleCylinderEdgeStart (transposePresentation P) glueQ S)
                  (qDoubleCylinderEdgeEnd (transposePresentation P) glueQ S)
                  glueEdge 0)⟩ : RZZ P S) = ⟨targetZ, targetVertex⟩
          refine Sigma.eq rfl ?_
          change qToZDoubleCylinderVertex P A glueQ targetZ hglueQZ S
              (qDoubleCylinderEdgeStart (transposePresentation P) glueQ S glueEdge) =
            targetVertex
          rw [qToZDoubleCylinderEdge_start]
          rw [← hedge] at hstart
          exact hstart.symm
        · apply Subtype.ext
          change rzFaceQ P A S
              (Sum.inr (Sum.inl ⟨a, glueEdge, 0⟩)) 0 =
            Sum.inl ⟨targetZ, localEdge⟩
          rw [show rzFaceQ P A S
              (Sum.inr (Sum.inl ⟨a, glueEdge, 0⟩)) 0 =
                glueFaceQ0 P A S ⟨a, glueEdge, 0⟩ by rfl]
          apply congrArg Sum.inl
          change (⟨targetZ,
              qToZDoubleCylinderEdge P A glueQ targetZ hglueQZ S glueEdge⟩ :
                Sigma fun z : P.Z => ZDoubleCylinderEdge P z S) =
            ⟨targetZ, localEdge⟩
          exact Sigma.eq rfl hedge
      · refine ⟨(⟨Sum.inr (Sum.inl ⟨a, glueEdge, 1⟩), rfl, ?_⟩, 0), ?_⟩
        · change rzFaceZ P A S (Sum.inr (Sum.inl ⟨a, glueEdge, 1⟩)) =
            ⟨targetZ, targetVertex⟩
          rw [show rzFaceZ P A S (Sum.inr (Sum.inl ⟨a, glueEdge, 1⟩)) =
              glueFaceZ P A S ⟨a, glueEdge, 1⟩ by rfl]
          change
            (⟨targetZ,
              qToZDoubleCylinderVertex P A glueQ targetZ hglueQZ S
                (edgeEndpoint
                  (qDoubleCylinderEdgeStart (transposePresentation P) glueQ S)
                  (qDoubleCylinderEdgeEnd (transposePresentation P) glueQ S)
                  glueEdge 1)⟩ : RZZ P S) = ⟨targetZ, targetVertex⟩
          refine Sigma.eq rfl ?_
          change qToZDoubleCylinderVertex P A glueQ targetZ hglueQZ S
              (qDoubleCylinderEdgeEnd (transposePresentation P) glueQ S glueEdge) =
            targetVertex
          rw [qToZDoubleCylinderEdge_end]
          rw [← hedge] at hend
          exact hend.symm
        · apply Subtype.ext
          change rzFaceQ P A S
              (Sum.inr (Sum.inl ⟨a, glueEdge, 1⟩)) 0 =
            Sum.inl ⟨targetZ, localEdge⟩
          rw [show rzFaceQ P A S
              (Sum.inr (Sum.inl ⟨a, glueEdge, 1⟩)) 0 =
                glueFaceQ0 P A S ⟨a, glueEdge, 1⟩ by rfl]
          apply congrArg Sum.inl
          change (⟨targetZ,
              qToZDoubleCylinderEdge P A glueQ targetZ hglueQZ S glueEdge⟩ :
                Sigma fun z : P.Z => ZDoubleCylinderEdge P z S) =
            ⟨targetZ, localEdge⟩
          exact Sigma.eq rfl hedge
    · rcases qVertex with ⟨qVertexQ, qVertex⟩
      have hxq : rzXQIncidence P A S
          (Sum.inl (Sum.inr ⟨glueQ, glueEdge⟩))
          (Sum.inr ⟨qVertexQ, qVertex⟩) = true := hinc.1
      have hqz : rzQZIncidence P A S (Sum.inr ⟨qVertexQ, qVertex⟩)
          ⟨targetZ, targetVertex⟩ = true := hinc.2
      obtain ⟨hqtag, hendpoint⟩ := of_decide_eq_true hxq
      obtain ⟨hglueQZ, hvertex⟩ := of_decide_eq_true hqz
      cases hqtag
      let a : QZEdge P := ⟨(glueQ, targetZ), hglueQZ⟩
      rcases hendpoint with hstart | hend
      · refine ⟨(⟨Sum.inr (Sum.inl ⟨a, glueEdge, 0⟩), rfl, ?_⟩, 1), ?_⟩
        · change rzFaceZ P A S (Sum.inr (Sum.inl ⟨a, glueEdge, 0⟩)) =
            ⟨targetZ, targetVertex⟩
          rw [show rzFaceZ P A S (Sum.inr (Sum.inl ⟨a, glueEdge, 0⟩)) =
              glueFaceZ P A S ⟨a, glueEdge, 0⟩ by rfl]
          change
            (⟨targetZ,
              qToZDoubleCylinderVertex P A glueQ targetZ hglueQZ S
                (edgeEndpoint
                  (qDoubleCylinderEdgeStart (transposePresentation P) glueQ S)
                  (qDoubleCylinderEdgeEnd (transposePresentation P) glueQ S)
                  glueEdge 0)⟩ : RZZ P S) = ⟨targetZ, targetVertex⟩
          refine Sigma.eq rfl ?_
          change qToZDoubleCylinderVertex P A glueQ targetZ hglueQZ S
              (qDoubleCylinderEdgeStart (transposePresentation P) glueQ S glueEdge) =
            targetVertex
          rw [← hstart]
          exact hvertex
        · apply Subtype.ext
          change rzFaceQ P A S (Sum.inr (Sum.inl ⟨a, glueEdge, 0⟩)) 1 =
            Sum.inr ⟨glueQ, qVertex⟩
          simpa [rzFaceQ, glueFaceQ1, twoSelect, edgeEndpoint, a] using hstart.symm
      · refine ⟨(⟨Sum.inr (Sum.inl ⟨a, glueEdge, 1⟩), rfl, ?_⟩, 1), ?_⟩
        · change rzFaceZ P A S (Sum.inr (Sum.inl ⟨a, glueEdge, 1⟩)) =
            ⟨targetZ, targetVertex⟩
          rw [show rzFaceZ P A S (Sum.inr (Sum.inl ⟨a, glueEdge, 1⟩)) =
              glueFaceZ P A S ⟨a, glueEdge, 1⟩ by rfl]
          change
            (⟨targetZ,
              qToZDoubleCylinderVertex P A glueQ targetZ hglueQZ S
                (edgeEndpoint
                  (qDoubleCylinderEdgeStart (transposePresentation P) glueQ S)
                  (qDoubleCylinderEdgeEnd (transposePresentation P) glueQ S)
                  glueEdge 1)⟩ : RZZ P S) = ⟨targetZ, targetVertex⟩
          refine Sigma.eq rfl ?_
          change qToZDoubleCylinderVertex P A glueQ targetZ hglueQZ S
              (qDoubleCylinderEdgeEnd (transposePresentation P) glueQ S glueEdge) =
            targetVertex
          rw [← hend]
          exact hvertex
        · apply Subtype.ext
          change rzFaceQ P A S (Sum.inr (Sum.inl ⟨a, glueEdge, 1⟩)) 1 =
            Sum.inr ⟨glueQ, qVertex⟩
          simpa [rzFaceQ, glueFaceQ1, twoSelect, edgeEndpoint, a] using hend.symm
  · rcases oldX with ⟨oldVertex, copy⟩
    rcases z with ⟨targetZ, targetVertex⟩
    rcases shared with ⟨sharedQ, hshared⟩
    have hinc :=
      (Bool.and_eq_true_eq_eq_true_and_eq_true _ _).mp hshared
    rcases sharedQ with localEdge | qVertex
    · have hxq := hinc.1
      change false = true at hxq
      exact Bool.noConfusion hxq
    · rcases qVertex with ⟨qVertexQ, qVertex⟩
      have hxq : rzXQIncidence P A S (Sum.inr (oldVertex, copy))
          (Sum.inr ⟨qVertexQ, qVertex⟩) = true := hinc.1
      have hqz : rzQZIncidence P A S (Sum.inr ⟨qVertexQ, qVertex⟩)
          ⟨targetZ, targetVertex⟩ = true := hinc.2
      obtain ⟨oldFace, oldCorner, holdX, holdQ⟩ := of_decide_eq_true hxq
      obtain ⟨holdQZ, hvertex⟩ := of_decide_eq_true hqz
      have hqtag : P.faceQ oldFace oldCorner = qVertexQ := by
        exact congrArg (fun value : RZQ P S =>
          match value with
          | Sum.inl _ => P.faceQ oldFace oldCorner
          | Sum.inr tagged => tagged.1) holdQ
      let originalShared : SharedQ P.data oldVertex targetZ :=
        ⟨qVertexQ, by
          simpa [holdX, hqtag] using
            (And.intro (P.data.faceQ_xq oldFace oldCorner) holdQZ)⟩
      obtain ⟨originalCorner, horiginal⟩ :=
        (P.perfectPairing oldVertex targetZ).2 originalShared
      rcases originalCorner with ⟨faceOver, corner⟩
      rcases faceOver with ⟨faceOver, hfaceX, hfaceZ⟩
      have hQ : P.faceQ faceOver corner = qVertexQ :=
        congrArg Subtype.val horiginal
      have hcandidateQ : oldXFaceQ P S corner (faceOver, copy) =
          Sum.inr ⟨qVertexQ, qVertex⟩ := by
        rw [oldXFaceQ_congr P S faceOver oldFace corner oldCorner copy
          (hfaceX.trans holdX.symm) (hQ.trans hqtag.symm)]
        exact holdQ
      refine ⟨(⟨Sum.inr (Sum.inr (faceOver, copy)), ?_, ?_⟩,
        corner), ?_⟩
      · change rzFaceX P S (Sum.inr (Sum.inr (faceOver, copy))) =
          Sum.inr (oldVertex, copy)
        simpa [rzFaceX, oldXFaceX] using hfaceX
      · change rzFaceZ P A S (Sum.inr (Sum.inr (faceOver, copy))) =
          ⟨targetZ, targetVertex⟩
        rw [show rzFaceZ P A S (Sum.inr (Sum.inr (faceOver, copy))) =
            oldXFaceZ P S (faceOver, copy) by rfl]
        clear horiginal originalShared hshared hinc hxq hqz
        cases hfaceZ
        have hcandidateSigma :
            (⟨P.faceQ faceOver corner,
              (copy, Sum.inl (Sum.inr
                (⟨P.faceX faceOver,
                  P.data.faceQ_xq faceOver corner⟩ :
                  QStarEdge (transposePresentation P)
                    (P.faceQ faceOver corner))))⟩ :
              Sigma fun q : P.Q =>
                QDoubleCylinderVertex (transposePresentation P) q S) =
              (⟨qVertexQ, qVertex⟩ :
                Sigma fun q : P.Q =>
                  QDoubleCylinderVertex (transposePresentation P) q S) := by
          exact Sum.inr.inj hcandidateQ
        cases hcandidateSigma
        refine Sigma.eq rfl ?_
        rw [← hvertex]
        exact (oldXFaceQ_maps_to_faceZ P A S faceOver copy corner).symm
      · apply Subtype.ext
        exact hcandidateQ

theorem rzReplacementPerfectPairing
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (x : (rzReplacementData P A S).X)
    (z : (rzReplacementData P A S).Z) :
    Function.Bijective
      (faceCornerToShared (rzReplacementData P A S) x z) :=
  ⟨rzReplacementFaceCorner_injective P A S x z,
    rzReplacementFaceCorner_surjective P A S x z⟩

/-- The concrete quotient-free RZ successor presentation. -/
noncomputable def rzReplacementPresentation
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) : TannerSquarePresentation where
  data := rzReplacementData P A S
  perfectPairing := rzReplacementPerfectPairing P A S

/-- Cellular regularity of the concrete RZ successor.

The local and Q-Z glue families are constructor-injective.  Only the old-X
copy family consumes cellular regularity of the input presentation.  The V3
admissibility and cellular-regularity hypotheses remain separate: neither is
derived from the other. -/
theorem rzReplacementCellularRegular
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) :
    TannerSquareCellularRegular
      (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S) where
  faceXZ_injective := by
    classical
    let A : TannerSquareAdmissible P :=
      A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
    intro firstFace secondFace hpairs
    have hfaceX := congrArg Prod.fst hpairs
    have hfaceZ := congrArg Prod.snd hpairs
    change rzFaceX P S firstFace = rzFaceX P S secondFace at hfaceX
    change rzFaceZ P A S firstFace = rzFaceZ P A S secondFace at hfaceZ
    rcases firstFace with ⟨firstLocalZ, firstLocalFace, firstBits⟩ |
        (⟨firstGlue, firstGlueEdge, firstEndpoint⟩ |
          ⟨firstOldFace, firstCopy⟩)
    · rcases secondFace with ⟨secondLocalZ, secondLocalFace, secondBits⟩ |
          (⟨secondGlue, secondGlueEdge, secondEndpoint⟩ |
            ⟨secondOldFace, secondCopy⟩)
      · have hlocalX :
            (⟨firstLocalZ, firstLocalFace⟩ :
                Sigma fun z : P.Z => ZDoubleCylinderFace P z S) =
              ⟨secondLocalZ, secondLocalFace⟩ := by
            simpa [rzFaceX, localFaceX] using hfaceX
        cases hlocalX
        have hvertex :
            localCornerVertex P firstLocalZ S firstLocalFace firstBits =
              localCornerVertex P firstLocalZ S firstLocalFace secondBits := by
          change localFaceZ P S
              ⟨firstLocalZ, firstLocalFace, firstBits⟩ =
            localFaceZ P S
              ⟨firstLocalZ, firstLocalFace, secondBits⟩ at hfaceZ
          rw [localFaceZ_eq_corner, localFaceZ_eq_corner] at hfaceZ
          exact eq_of_heq (Sigma.mk.inj_iff.mp hfaceZ).2
        have hbits := localCornerVertex_injective
          P firstLocalZ S firstLocalFace hvertex
        cases hbits
        rfl
      · simp [rzFaceX, localFaceX, glueFaceX] at hfaceX
      · simp [rzFaceX, localFaceX, oldXFaceX] at hfaceX
    · rcases secondFace with ⟨secondLocalZ, secondLocalFace, secondBits⟩ |
          (⟨secondGlue, secondGlueEdge, secondEndpoint⟩ |
            ⟨secondOldFace, secondCopy⟩)
      · simp [rzFaceX, localFaceX, glueFaceX] at hfaceX
      · have hglueX :
            (⟨firstGlue.1.1, firstGlueEdge⟩ :
                Sigma fun q : P.Q =>
                  QDoubleCylinderEdge (transposePresentation P) q S) =
              ⟨secondGlue.1.1, secondGlueEdge⟩ := by
            simpa [rzFaceX, glueFaceX] using hfaceX
        have hqtag : firstGlue.1.1 = secondGlue.1.1 :=
          congrArg Sigma.fst hglueX
        have hzsigma :
            (⟨firstGlue.1.2,
                glueCornerVertex P A S firstGlue firstGlueEdge firstEndpoint⟩ :
                Sigma fun z : P.Z => ZDoubleCylinderVertex P z S) =
              ⟨secondGlue.1.2,
                glueCornerVertex P A S secondGlue secondGlueEdge secondEndpoint⟩ := by
            simpa [rzFaceZ, glueFaceZ, glueCornerVertex] using hfaceZ
        have hztag : firstGlue.1.2 = secondGlue.1.2 :=
          congrArg Sigma.fst hzsigma
        have hglue : firstGlue = secondGlue := by
          apply Subtype.ext
          exact Prod.ext hqtag hztag
        subst secondGlue
        have hedge : firstGlueEdge = secondGlueEdge :=
          eq_of_heq (Sigma.mk.inj_iff.mp hglueX).2
        subst secondGlueEdge
        have hvertex :
            glueCornerVertex P A S firstGlue firstGlueEdge firstEndpoint =
              glueCornerVertex P A S firstGlue firstGlueEdge secondEndpoint :=
          eq_of_heq (Sigma.mk.inj_iff.mp hzsigma).2
        have hendpoint := glueCornerVertex_injective
          P A S firstGlue firstGlueEdge hvertex
        cases hendpoint
        rfl
      · simp [rzFaceX, glueFaceX, oldXFaceX] at hfaceX
    · rcases secondFace with ⟨secondLocalZ, secondLocalFace, secondBits⟩ |
          (⟨secondGlue, secondGlueEdge, secondEndpoint⟩ |
            ⟨secondOldFace, secondCopy⟩)
      · simp [rzFaceX, localFaceX, oldXFaceX] at hfaceX
      · simp [rzFaceX, glueFaceX, oldXFaceX] at hfaceX
      · have hxcopy :
            (P.faceX firstOldFace, firstCopy) =
              (P.faceX secondOldFace, secondCopy) := by
            simpa [rzFaceX, oldXFaceX] using hfaceX
        have hx : P.faceX firstOldFace = P.faceX secondOldFace :=
          congrArg Prod.fst hxcopy
        have hcopy : firstCopy = secondCopy := congrArg Prod.snd hxcopy
        have hz : P.faceZ firstOldFace = P.faceZ secondOldFace := by
          have hsigma :
              (⟨P.faceZ firstOldFace,
                  (firstCopy, Sum.inl (xStarFaceZVertex
                    (transposePresentation P) (P.faceZ firstOldFace)
                      (oldFaceInZStar P firstOldFace)))⟩ :
                    Sigma fun z : P.Z => ZDoubleCylinderVertex P z S) =
                ⟨P.faceZ secondOldFace,
                  (secondCopy, Sum.inl (xStarFaceZVertex
                    (transposePresentation P) (P.faceZ secondOldFace)
                      (oldFaceInZStar P secondOldFace)))⟩ := by
            simpa [rzFaceZ, oldXFaceZ] using hfaceZ
          exact congrArg Sigma.fst hsigma
        have hface : firstOldFace = secondOldFace :=
          R.faceXZ_injective (Prod.ext hx hz)
        subst secondOldFace
        subst secondCopy
        rfl

/-! ## Constructed admissibility witnesses -/

/-- The zero grid coordinate in a positive half-scale. -/
private def rzRadialGridZero (S : OddScale) : Fin S.half :=
  ⟨0, S.half_pos⟩

private def rzTwoElim {motive : Two → Sort _}
    (zero : motive 0) (one : motive 1) (i : Two) : motive i := by
  rcases i with ⟨i, hi⟩
  rcases i with _ | i
  · exact zero
  · rcases i with _ | i
    · exact one
    · omega

/-- The input V3 radial owner supplies the small square adjacent to an X-Q
subdivision segment.  This is the acyclic root route approved by #908: it
uses only input data, never a successor root or successor admissibility
witness. -/
private noncomputable def radialSubdivisionFaceOwner
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (x : P.X) (S : OddScale) (edge : XQEdge P)
    (member : xStarEdgeMember P x (Sum.inl edge) = true)
    (segment : Fin S.half) :
    {face : SubdivisionFace P x S //
      subdivisionFaceEdgeMatrix P x S
        (Sum.inl (⟨Sum.inl edge, member⟩, segment)) face = 1} := by
  let owner := A3.xRadialFaceOwner x edge member
  refine rzTwoElim (motive := fun corner => owner.1.2 = corner →
      {face : SubdivisionFace P x S //
        subdivisionFaceEdgeMatrix P x S
          (Sum.inl (⟨Sum.inl edge, member⟩, segment)) face = 1}) ?_ ?_
      owner.1.2 rfl
  · intro hcorner
    refine ⟨(owner.1.1, segment, rzRadialGridZero S), ?_⟩
    apply (subdivisionFaceEdgeMatrix_eq_one_iff P x S _ _).2
    refine ⟨(0, 0), ?_⟩
    rw [subdivisionFaceBoundaryEdge_zero_zero]
    have hedge := owner.2
    rw [hcorner] at hedge
    change Sum.inl (xStarFaceXQEdge P x owner.1.1 0, segment) = _
    exact congrArg
      (fun starEdge : XStarEdge P x =>
        (Sum.inl (starEdge, segment) : SubdivisionEdge P x S)) hedge
  · intro hcorner
    refine ⟨(owner.1.1, rzRadialGridZero S, segment), ?_⟩
    apply (subdivisionFaceEdgeMatrix_eq_one_iff P x S _ _).2
    refine ⟨(1, 0), ?_⟩
    rw [subdivisionFaceBoundaryEdge_one_zero]
    have hedge := owner.2
    rw [hcorner] at hedge
    change Sum.inl (xStarFaceXQEdge P x owner.1.1 1, segment) = _
    exact congrArg
      (fun starEdge : XStarEdge P x =>
        (Sum.inl (starEdge, segment) : SubdivisionEdge P x S)) hedge

private def doubleCylinderFaceBoundaryEdge
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : DoubleCylinderFace P x S) (slot : Two × Two) :
    DoubleCylinderEdge P x S :=
  match face with
  | Sum.inl copyFace =>
      Sum.inl (copyFace.1,
        subdivisionFaceBoundaryEdge P x S copyFace.2 slot)
  | Sum.inr rectangle =>
      doubleCylinderRectangleBoundaryEdge P x S rectangle slot

private noncomputable def radialSubdivisionFaceSlotOwner
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (x : P.X) (S : OddScale) (edge : XQEdge P)
    (member : xStarEdgeMember P x (Sum.inl edge) = true)
    (segment : Fin S.half) :
    {owned : SubdivisionFace P x S × (Two × Two) //
      subdivisionFaceBoundaryEdge P x S owned.1 owned.2 =
        Sum.inl (⟨Sum.inl edge, member⟩, segment)} := by
  let owner := A3.xRadialFaceOwner x edge member
  by_cases hcorner : owner.1.2 = 0
  ·
    refine ⟨⟨(owner.1.1, segment, rzRadialGridZero S), (0, 0)⟩, ?_⟩
    rw [subdivisionFaceBoundaryEdge_zero_zero]
    have hedge := owner.2
    rw [hcorner] at hedge
    change Sum.inl (xStarFaceXQEdge P x owner.1.1 0, segment) = _
    exact congrArg
      (fun starEdge : XStarEdge P x =>
        (Sum.inl (starEdge, segment) : SubdivisionEdge P x S)) hedge
  · have hcornerOne : owner.1.2 = 1 := by
      apply Fin.ext
      have hval : owner.1.2.1 ≠ 0 := by
        intro hzero
        apply hcorner
        apply Fin.ext
        exact hzero
      have hlt := owner.1.2.2
      omega
    refine ⟨⟨(owner.1.1, rzRadialGridZero S, segment), (1, 0)⟩, ?_⟩
    rw [subdivisionFaceBoundaryEdge_one_zero]
    have hedge := owner.2
    rw [hcornerOne] at hedge
    change Sum.inl (xStarFaceXQEdge P x owner.1.1 1, segment) = _
    exact congrArg
      (fun starEdge : XStarEdge P x =>
        (Sum.inl (starEdge, segment) : SubdivisionEdge P x S)) hedge

private noncomputable def radialSubdivisionFaceSlotOwnerValue
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (x : P.X) (S : OddScale) (edge : XQEdge P)
    (member : xStarEdgeMember P x (Sum.inl edge) = true)
    (segment : Fin S.half) : SubdivisionFace P x S × (Two × Two) :=
  let owner := A3.xRadialFaceOwner x edge member
  if owner.1.2 = 0 then
    ((owner.1.1, segment, rzRadialGridZero S), (0, 0))
  else
    ((owner.1.1, rzRadialGridZero S, segment), (1, 0))

private theorem radialSubdivisionFaceSlotOwner_value
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (x : P.X) (S : OddScale) (edge : XQEdge P)
    (member : xStarEdgeMember P x (Sum.inl edge) = true)
    (segment : Fin S.half) :
    (radialSubdivisionFaceSlotOwner P A3 x S edge member segment).1 =
      radialSubdivisionFaceSlotOwnerValue P A3 x S edge member segment := by
  unfold radialSubdivisionFaceSlotOwner radialSubdivisionFaceSlotOwnerValue
  dsimp only
  split <;> rfl

private noncomputable def doubleCylinderEdgeFaceSlotOwner
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (x : P.X) (S : OddScale) (edge : DoubleCylinderEdge P x S) :
    {owned : DoubleCylinderFace P x S × (Two × Two) //
      doubleCylinderFaceBoundaryEdge P x S owned.1 owned.2 = edge} := by
  classical
  rcases edge with endEdge | vertical
  · rcases endEdge with ⟨copy, subdivisionEdge⟩
    rcases subdivisionEdge with boundarySegment | interior
    · rcases boundarySegment with ⟨starEdge, segment⟩
      rcases starEdge with ⟨rawEdge, member⟩
      rcases rawEdge with radial | boundary
      · let owner := radialSubdivisionFaceSlotOwner P A3 x S radial member segment
        refine ⟨⟨Sum.inl (copy, owner.1.1), owner.1.2⟩, ?_⟩
        exact congrArg (fun value => Sum.inl (copy, value)) owner.2
      · let boundaryEdge : XStarBoundaryEdge P x :=
          ⟨Sum.inr boundary, by
            simpa only [xStarBoundaryEdgeMember, xStarEdgeMember] using member⟩
        let rectangle := subdivisionOriginalBoundaryEdge P x S boundaryEdge segment
        refine ⟨⟨Sum.inr rectangle, (0, copy)⟩, ?_⟩
        rfl
    · rcases interior with horizontal | verticalEdge
      · rcases horizontal with ⟨face, i, j⟩
        let row : Fin S.half := ⟨j.1, by have := j.2; omega⟩
        let square : SubdivisionFace P x S := (face, i, row)
        refine ⟨⟨Sum.inl (copy, square), (0, 1)⟩, ?_⟩
        rw [show doubleCylinderFaceBoundaryEdge P x S
          (Sum.inl (copy, square)) (0, 1) =
            Sum.inl (copy, subdivisionFaceBoundaryEdge P x S square (0, 1)) by rfl]
        rw [subdivisionFaceBoundaryEdge_zero_one]
        simp only [subdivisionHorizontalEdge]
        split <;> rename_i hzero
        · have hvalue : row.1 + 1 = 0 := hzero
          omega
        · split <;> rename_i hlast
          · exfalso
            have hvalue : row.1 + 1 = S.half := hlast
            have hrow : row.1 = j.1 := rfl
            have hjlt : j.1 + 1 < S.half := by
              exact (Nat.lt_sub_iff_add_lt).1 j.2
            omega
          · congr 3
      · rcases verticalEdge with ⟨face, i, j⟩
        let column : Fin S.half := ⟨i.1, by have := i.2; omega⟩
        let square : SubdivisionFace P x S := (face, column, j)
        refine ⟨⟨Sum.inl (copy, square), (1, 1)⟩, ?_⟩
        rw [show doubleCylinderFaceBoundaryEdge P x S
          (Sum.inl (copy, square)) (1, 1) =
            Sum.inl (copy, subdivisionFaceBoundaryEdge P x S square (1, 1)) by rfl]
        rw [subdivisionFaceBoundaryEdge_one_one]
        simp only [subdivisionVerticalEdge]
        split <;> rename_i hzero
        · have hvalue : column.1 + 1 = 0 := hzero
          omega
        · split <;> rename_i hlast
          · exfalso
            have hvalue : column.1 + 1 = S.half := hlast
            have hcolumn : column.1 = i.1 := rfl
            have hilt : i.1 + 1 < S.half := by
              exact (Nat.lt_sub_iff_add_lt).1 i.2
            omega
          · congr 3
  · obtain ⟨⟨rectangle, endpoint⟩, hendpoint⟩ :=
      subdivisionBoundaryIncidentEdge P A3.toTannerSquareAdmissibleV2 x S vertical
    refine ⟨⟨Sum.inr rectangle, (1, endpoint)⟩, ?_⟩
    exact rzTwoElim (motive := fun endpoint =>
        BDL26TannerLocalRegularity.edgeEndpoint
            (subdivisionBoundaryEdgeStart P x S)
            (subdivisionBoundaryEdgeEnd P x S) rectangle endpoint = vertical →
          doubleCylinderFaceBoundaryEdge P x S (Sum.inr rectangle)
            (1, endpoint) = Sum.inr vertical)
      (fun h => by simpa [doubleCylinderFaceBoundaryEdge,
        doubleCylinderRectangleBoundaryEdge] using h)
      (fun h => by simpa [doubleCylinderFaceBoundaryEdge,
        doubleCylinderRectangleBoundaryEdge] using h) endpoint hendpoint

private noncomputable def localCornerAtBoundaryEndpoint
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale)
    (face : ZDoubleCylinderFace P z S) (slot : Two × Two)
    (endpoint : Two) :
    {owned : (Two × Two) × Two //
      localCornerEdge P z S face owned =
          doubleCylinderFaceBoundaryEdge (transposePresentation P) z S
            face slot ∧
        localCornerVertex P z S face owned.1 =
          BDL26TannerLocalRegularity.edgeEndpoint
            (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
            (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
            (doubleCylinderFaceBoundaryEdge (transposePresentation P) z S
              face slot) endpoint} := by
  rcases face with copyFace | rectangle
  · rcases copyFace with ⟨copy, face⟩
    rcases slot with ⟨kind, side⟩
    let bits : Two × Two :=
      if kind = 0 then (endpoint, side) else (side, endpoint)
    refine ⟨(bits, kind), ?_, ?_⟩
    · fin_cases kind <;> fin_cases side <;> fin_cases endpoint
      all_goals
        simp [bits, localCornerEdge, doubleCylinderFaceBoundaryEdge,
          gridEndpoint, twoSelect, subdivisionFaceBoundaryEdge]
        congr 3 <;> apply Fin.ext <;> rfl
    · fin_cases kind <;> fin_cases side <;> fin_cases endpoint
      all_goals
        simp [bits, localCornerVertex, doubleCylinderFaceBoundaryEdge,
          gridEndpoint, twoSelect, lowerGridIndex, upperGridIndex,
          subdivisionFaceBoundaryEdge,
          tannerDoubleCylinderEdgeStart, tannerDoubleCylinderEdgeEnd,
          subdivisionHorizontalEdge_start, subdivisionHorizontalEdge_end,
          subdivisionVerticalEdge_start, subdivisionVerticalEdge_end]
        first
        | exact (subdivisionHorizontalEdge_start
            (transposePresentation P) z S face.1 face.2.1 _).symm
        | exact (subdivisionHorizontalEdge_end
            (transposePresentation P) z S face.1 face.2.1 _).symm
        | exact (subdivisionVerticalEdge_start
            (transposePresentation P) z S face.1 _ face.2.2).symm
        | exact (subdivisionVerticalEdge_end
            (transposePresentation P) z S face.1 _ face.2.2).symm
  · rcases slot with ⟨kind, side⟩
    let bits : Two × Two :=
      if kind = 0 then (side, endpoint) else (endpoint, side)
    refine ⟨(bits, kind), ?_, ?_⟩
    · fin_cases kind <;> fin_cases side <;> fin_cases endpoint <;>
        simp [bits, localCornerEdge, doubleCylinderFaceBoundaryEdge,
          edgeEndpoint, twoSelect, doubleCylinderRectangleBoundaryEdge]
    · fin_cases kind <;> fin_cases side <;> fin_cases endpoint <;>
        simp [bits, localCornerVertex, doubleCylinderFaceBoundaryEdge,
          edgeEndpoint, twoSelect, doubleCylinderRectangleCorner,
          doubleCylinderRectangleBoundaryEdge, tannerDoubleCylinderEdgeStart,
          tannerDoubleCylinderEdgeEnd, subdivisionBoundaryEdgeStart_value,
          subdivisionBoundaryEdgeEnd_value]
      all_goals
        first
        | exact subdivisionBoundaryEdgeStart_value (transposePresentation P) z S rectangle
        | exact subdivisionBoundaryEdgeEnd_value (transposePresentation P) z S rectangle

/-- Every edge of a materialized double cylinder has an explicitly selected
incident face.  End-copy face-interior edges retain their face tag; boundary
segments use their rectangle; radial X-Q segments use the input V3 owner; and
vertical edges use the input V2 endpoint-tagged boundary owner. -/
private noncomputable def doubleCylinderEdgeFaceOwner
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (x : P.X) (S : OddScale) (edge : DoubleCylinderEdge P x S) :
    {face : DoubleCylinderFace P x S //
      doubleCylinderFaceEdgeMatrix P x S edge face = 1} := by
  classical
  rcases edge with endEdge | vertical
  · rcases endEdge with ⟨copy, subdivisionEdge⟩
    rcases subdivisionEdge with boundarySegment | interior
    · rcases boundarySegment with ⟨starEdge, segment⟩
      rcases starEdge with ⟨rawEdge, member⟩
      rcases rawEdge with radial | boundary
      · let owner := radialSubdivisionFaceOwner P A3 x S radial member segment
        refine ⟨Sum.inl (copy, owner.1), ?_⟩
        simpa using owner.2
      · let boundaryEdge : XStarBoundaryEdge P x :=
          ⟨Sum.inr boundary, by
            simpa only [xStarBoundaryEdgeMember, xStarEdgeMember] using member⟩
        let rectangle := subdivisionOriginalBoundaryEdge P x S boundaryEdge segment
        refine ⟨Sum.inr rectangle, ?_⟩
        change doubleCylinderFaceEdgeMatrix P x S
          (Sum.inl (copy, rectangle.1)) (Sum.inr rectangle) = 1
        exact doubleCylinder_rectangle_end_boundary P x S copy rectangle
    · rcases interior with horizontal | verticalEdge
      · rcases horizontal with ⟨face, i, j⟩
        let row : Fin S.half := ⟨j.1, by have := j.2; omega⟩
        let square : SubdivisionFace P x S := (face, i, row)
        refine ⟨Sum.inl (copy, square), ?_⟩
        rw [doubleCylinder_end_face_boundary]
        apply (subdivisionFaceEdgeMatrix_eq_one_iff P x S _ _).2
        refine ⟨(0, 1), ?_⟩
        rw [subdivisionFaceBoundaryEdge_zero_one]
        simp only [subdivisionHorizontalEdge]
        split <;> rename_i hzero
        · have hvalue : row.1 + 1 = 0 := hzero
          omega
        · split <;> rename_i hlast
          · exfalso
            have hvalue : row.1 + 1 = S.half := hlast
            have hrow : row.1 = j.1 := rfl
            have hjlt : j.1 + 1 < S.half := by
              exact (Nat.lt_sub_iff_add_lt).1 j.2
            omega
          · congr 3
      · rcases verticalEdge with ⟨face, i, j⟩
        let column : Fin S.half := ⟨i.1, by have := i.2; omega⟩
        let square : SubdivisionFace P x S := (face, column, j)
        refine ⟨Sum.inl (copy, square), ?_⟩
        rw [doubleCylinder_end_face_boundary]
        apply (subdivisionFaceEdgeMatrix_eq_one_iff P x S _ _).2
        refine ⟨(1, 1), ?_⟩
        rw [subdivisionFaceBoundaryEdge_one_one]
        simp only [subdivisionVerticalEdge]
        split <;> rename_i hzero
        · have hvalue : column.1 + 1 = 0 := hzero
          omega
        · split <;> rename_i hlast
          · exfalso
            have hvalue : column.1 + 1 = S.half := hlast
            have hcolumn : column.1 = i.1 := rfl
            have hilt : i.1 + 1 < S.half := by
              exact (Nat.lt_sub_iff_add_lt).1 i.2
            omega
          · congr 3
  · obtain ⟨⟨rectangle, endpoint⟩, hendpoint⟩ :=
      subdivisionBoundaryIncidentEdge P A3.toTannerSquareAdmissibleV2 x S vertical
    refine ⟨Sum.inr rectangle, ?_⟩
    apply (doubleCylinderFaceEdgeMatrix_rectangle_eq_one_iff P x S _ _).2
    refine rzTwoElim (motive := fun endpoint =>
        BDL26TannerLocalRegularity.edgeEndpoint
            (subdivisionBoundaryEdgeStart P x S)
            (subdivisionBoundaryEdgeEnd P x S) rectangle endpoint = vertical →
          ∃ slot : Two × Two,
            doubleCylinderRectangleBoundaryEdge P x S rectangle slot =
              Sum.inr vertical) ?_ ?_ endpoint hendpoint
    · intro h
      refine ⟨(1, 0), ?_⟩
      simpa [doubleCylinderRectangleBoundaryEdge] using h
    · intro h
      refine ⟨(1, 1), ?_⟩
      simpa [doubleCylinderRectangleBoundaryEdge] using h

/-- Convert a concrete old X-boundary edge into the radial edge carrying the
same Q tag.  Boundary membership excludes the impossible X-Q branch. -/
private noncomputable def xStarAnchorRadialEdgeFromBoundary
    (P : TannerSquarePresentation) (x : P.X)
    (boundary : XStarBoundaryEdge P x) :
    {edge : XStarEdge P x //
      (xStarEdgeStart P x edge).1 = Vertex.x x} := by
  rcases boundary with ⟨raw, member⟩
  rcases raw with impossible | qz
  · simp [xStarBoundaryEdgeMember] at member
  · have hxq : P.xq x qz.1.1 = true := by
      change decide (∃ face : P.Face,
        xStarFaceMember P x face = true ∧
          decide (qz = faceQZEdge P face 0 ∨
            qz = faceQZEdge P face 1) = true) = true at member
      obtain ⟨face, hface, huse⟩ := of_decide_eq_true member
      have hx : P.faceX face = x := by
        simpa [xStarFaceMember] using hface
      have hcorner : qz = faceQZEdge P face 0 ∨
          qz = faceQZEdge P face 1 := by
        exact of_decide_eq_true huse
      rcases hcorner with hcorner | hcorner
      · have hq := congrArg (fun edge : QZEdge P => edge.1.1) hcorner
        simp only [faceQZEdge] at hq
        simpa [hx, hq] using P.data.faceQ_xq face 0
      · have hq := congrArg (fun edge : QZEdge P => edge.1.1) hcorner
        simp only [faceQZEdge] at hq
        simpa [hx, hq] using P.data.faceQ_xq face 1
    let radial : XQEdge P := ⟨(x, qz.1.1), by simpa [hxq]⟩
    have radialMember : xStarEdgeMember P x (Sum.inl radial) = true := by
      change decide (∃ face : P.Face,
        xStarFaceMember P x face = true ∧
          decide (radial = faceXQEdge P face 0 ∨
            radial = faceXQEdge P face 1) = true) = true
      rw [decide_eq_true_eq]
      change decide (∃ face : P.Face,
        xStarFaceMember P x face = true ∧
          decide (qz = faceQZEdge P face 0 ∨
            qz = faceQZEdge P face 1) = true) = true at member
      obtain ⟨face, hface, huse⟩ := of_decide_eq_true member
      refine ⟨face, hface, ?_⟩
      rw [decide_eq_true_eq]
      rcases of_decide_eq_true huse with hcorner | hcorner
      · left
        apply Subtype.ext
        have hx : P.faceX face = x := by
          simpa [xStarFaceMember] using hface
        have hq := congrArg (fun edge : QZEdge P => edge.1.1) hcorner
        exact Prod.ext hx.symm hq
      · right
        apply Subtype.ext
        have hx : P.faceX face = x := by
          simpa [xStarFaceMember] using hface
        have hq := congrArg (fun edge : QZEdge P => edge.1.1) hcorner
        exact Prod.ext hx.symm hq
    refine ⟨⟨Sum.inl radial, radialMember⟩, ?_⟩
    rfl

/-- A deterministic radial edge from the old X corner.  The Q tag is read
from the input boundary root's V2-owned Q-Z edge; only its membership proof is
eliminated, and no face preimage is retained. -/
private noncomputable def xStarAnchorRadialEdge
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (x : P.X) :
    {edge : XStarEdge P x //
      (xStarEdgeStart P x edge).1 = Vertex.x x} :=
  xStarAnchorRadialEdgeFromBoundary P x
    (A3.xBoundaryIncidentEdge x
      (A3.toTannerSquareAdmissible.xBoundaryRoot x)).1.1

/-- Every subdivision vertex has a choice-free incident edge.  Original
boundary vertices use the approved V2 endpoint route, the old X corner uses
`xStarAnchorRadialEdge`, and both interior families retain their stored edge
coordinates. -/
private noncomputable def subdivisionVertexIncidentEdge
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (x : P.X) (S : OddScale) (vertex : SubdivisionVertex P x S) :
    {owned : SubdivisionEdge P x S × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S)
        owned.1 owned.2 = vertex} := by
  rcases vertex with original | interior
  · rcases original with ⟨value, member⟩
    rcases value with oldX | q | z
    · have hx : oldX = x := by
        simpa [xStarVertexMember] using member
      subst oldX
      let edge := (xStarAnchorRadialEdge P A3 x).1
      let first : Fin S.half := ⟨0, S.half_pos⟩
      refine ⟨⟨Sum.inl (edge, first), 0⟩, ?_⟩
      rw [BDL26TannerLocalRegularity.edgeEndpoint_zero]
      apply congrArg Sum.inl
      apply Subtype.ext
      simpa [subdivisionEdgeStart, subdivisionSegmentStart, first, edge] using
        (xStarAnchorRadialEdge P A3 x).2
    · let boundaryVertex : XStarBoundaryVertex P x :=
        ⟨Vertex.q q, by simpa [xStarBoundaryVertexMember,
          xStarVertexMember] using member⟩
      let subdivided := subdivisionOriginalBoundaryVertex P x S boundaryVertex
      obtain ⟨⟨edge, endpoint⟩, hendpoint⟩ :=
        subdivisionBoundaryIncidentEdge P A3.toTannerSquareAdmissibleV2
          x S subdivided
      refine ⟨⟨edge.1, endpoint⟩, ?_⟩
      exact rzTwoElim (motive := fun endpoint =>
          BDL26TannerLocalRegularity.edgeEndpoint
              (subdivisionBoundaryEdgeStart P x S)
              (subdivisionBoundaryEdgeEnd P x S) edge endpoint = subdivided →
            BDL26TannerLocalRegularity.edgeEndpoint
              (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S)
              edge.1 endpoint = Sum.inl ⟨Vertex.q q, member⟩)
        (fun h => by
          rw [BDL26TannerLocalRegularity.edgeEndpoint_zero] at h ⊢
          simpa [subdivisionBoundaryEdgeStart_value, subdivided,
            subdivisionOriginalBoundaryVertex, boundaryVertex,
            xStarBoundaryVertexToStar] using congrArg Subtype.val h)
        (fun h => by
          rw [BDL26TannerLocalRegularity.edgeEndpoint_one] at h ⊢
          simpa [subdivisionBoundaryEdgeEnd_value, subdivided,
            subdivisionOriginalBoundaryVertex, boundaryVertex,
            xStarBoundaryVertexToStar] using congrArg Subtype.val h) endpoint hendpoint
    · let boundaryVertex : XStarBoundaryVertex P x :=
        ⟨Vertex.z z, by simpa [xStarBoundaryVertexMember,
          xStarVertexMember] using member⟩
      let subdivided := subdivisionOriginalBoundaryVertex P x S boundaryVertex
      obtain ⟨⟨edge, endpoint⟩, hendpoint⟩ :=
        subdivisionBoundaryIncidentEdge P A3.toTannerSquareAdmissibleV2
          x S subdivided
      refine ⟨⟨edge.1, endpoint⟩, ?_⟩
      exact rzTwoElim (motive := fun endpoint =>
          BDL26TannerLocalRegularity.edgeEndpoint
              (subdivisionBoundaryEdgeStart P x S)
              (subdivisionBoundaryEdgeEnd P x S) edge endpoint = subdivided →
            BDL26TannerLocalRegularity.edgeEndpoint
              (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S)
              edge.1 endpoint = Sum.inl ⟨Vertex.z z, member⟩)
        (fun h => by
          rw [BDL26TannerLocalRegularity.edgeEndpoint_zero] at h ⊢
          simpa [subdivisionBoundaryEdgeStart_value, subdivided,
            subdivisionOriginalBoundaryVertex, boundaryVertex,
            xStarBoundaryVertexToStar] using congrArg Subtype.val h)
        (fun h => by
          rw [BDL26TannerLocalRegularity.edgeEndpoint_one] at h ⊢
          simpa [subdivisionBoundaryEdgeEnd_value, subdivided,
            subdivisionOriginalBoundaryVertex, boundaryVertex,
            xStarBoundaryVertexToStar] using congrArg Subtype.val h) endpoint hendpoint
  · rcases interior with edgeInterior | faceInterior
    · rcases edgeInterior with ⟨edge, index⟩
      let preceding : Fin S.half :=
        ⟨index.1, by have := index.2; omega⟩
      refine ⟨⟨Sum.inl (edge, preceding), 1⟩, ?_⟩
      rw [BDL26TannerLocalRegularity.edgeEndpoint_one]
      have hlt : index.1 + 1 < S.half :=
        (Nat.lt_sub_iff_add_lt).1 index.2
      have hnot : preceding.1 + 1 ≠ S.half := by
        dsimp [preceding]
        omega
      simp [subdivisionEdgeEnd, subdivisionSegmentEnd, preceding, hnot]
    · rcases faceInterior with ⟨face, i, j⟩
      let column : Fin S.half :=
        ⟨i.1, by have := i.2; omega⟩
      let row : Fin (S.half + 1) :=
        ⟨j.1 + 1, by
          have hjlt : j.1 + 1 < S.half :=
            (Nat.lt_sub_iff_add_lt).1 j.2
          omega⟩
      let targetColumn : Fin (S.half + 1) :=
        ⟨i.1 + 1, by omega⟩
      let edge : SubdivisionEdge P x S :=
        subdivisionHorizontalEdge P x S face column row
      refine ⟨⟨edge, 1⟩, ?_⟩
      rw [BDL26TannerLocalRegularity.edgeEndpoint_one]
      have hilt : i.1 + 1 < S.half :=
        (Nat.lt_sub_iff_add_lt).1 i.2
      have hjlt : j.1 + 1 < S.half :=
        (Nat.lt_sub_iff_add_lt).1 j.2
      have hend : subdivisionEdgeEnd P x S edge =
          subdivisionGridVertex P x S face targetColumn row := by
        dsimp [edge]
        rw [subdivisionHorizontalEdge_end]
        rfl
      rw [hend]
      simp [targetColumn, row, subdivisionGridVertex, hilt.ne, hjlt.ne]
      constructor
      · apply Fin.ext
        change (i.1 + 1) - 1 = i.1
        omega
      · apply Fin.ext
        change (j.1 + 1) - 1 = j.1
        omega

/-- Lift a subdivision incident edge to the selected end copy. -/
private noncomputable def doubleCylinderVertexIncidentEdge
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (x : P.X) (S : OddScale) (vertex : DoubleCylinderVertex P x S) :
    {owned : DoubleCylinderEdge P x S × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (tannerDoubleCylinderEdgeStart P x S)
        (tannerDoubleCylinderEdgeEnd P x S) owned.1 owned.2 = vertex} := by
  obtain ⟨⟨edge, endpoint⟩, hendpoint⟩ :=
    subdivisionVertexIncidentEdge P A3 x S vertex.2
  refine ⟨⟨Sum.inl (vertex.1, edge), endpoint⟩, ?_⟩
  exact rzTwoElim (motive := fun endpoint =>
      BDL26TannerLocalRegularity.edgeEndpoint
          (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S)
          edge endpoint = vertex.2 →
        BDL26TannerLocalRegularity.edgeEndpoint
          (tannerDoubleCylinderEdgeStart P x S)
          (tannerDoubleCylinderEdgeEnd P x S)
          (Sum.inl (vertex.1, edge)) endpoint = vertex)
    (fun h => by
      rw [BDL26TannerLocalRegularity.edgeEndpoint_zero]
      exact Prod.ext rfl h)
    (fun h => by
      rw [BDL26TannerLocalRegularity.edgeEndpoint_one]
      exact Prod.ext rfl h) endpoint hendpoint

private theorem localFaceZ_eq_localCornerVertex
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale)
    (face : ZDoubleCylinderFace P z S) (bits : Two × Two) :
    localFaceZ P S ⟨z, face, bits⟩ =
      ⟨z, localCornerVertex P z S face bits⟩ := by
  rcases face with copyFace | rectangle
  · rfl
  · rcases bits with ⟨copy, endpoint⟩
    fin_cases endpoint <;>
      simp [localFaceZ, localCornerVertex, edgeEndpoint, twoSelect,
        doubleCylinderRectangleCorner]

/-- Every successor Z tag has a constructor-level boundary X root.  The
incident edge owner retains its explicit boundary slot, so the actual local RZ
face and its corner are constructed directly without inverting pairing. -/
noncomputable def rzReplacementZBoundaryRoot
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale)
    (z : (rzReplacementPresentation P
      A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S).Z) :
    ZStarBoundaryVertex
      (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S) z := by
  let A := A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  obtain ⟨⟨edge, endpoint⟩, hendpoint⟩ :=
    doubleCylinderVertexIncidentEdge (transposePresentation P)
      (transposeTannerSquareAdmissibleV3 P A3) z.1 S z.2
  let owner := doubleCylinderEdgeFaceSlotOwner (transposePresentation P)
    (transposeTannerSquareAdmissibleV3 P A3) z.1 S edge
  let corner := localCornerAtBoundaryEndpoint P z.1 S
    owner.1.1 owner.1.2 endpoint
  let x : (rzReplacementPresentation P A S).X :=
    Sum.inl (Sum.inl ⟨z.1, owner.1.1⟩)
  let face : (rzReplacementPresentation P A S).Face :=
    Sum.inl ⟨z.1, owner.1.1, corner.1.1⟩
  have hvertex : localCornerVertex P z.1 S owner.1.1 corner.1.1 = z.2 := by
    calc
      localCornerVertex P z.1 S owner.1.1 corner.1.1 =
          BDL26TannerLocalRegularity.edgeEndpoint
            (tannerDoubleCylinderEdgeStart (transposePresentation P) z.1 S)
            (tannerDoubleCylinderEdgeEnd (transposePresentation P) z.1 S)
            (doubleCylinderFaceBoundaryEdge (transposePresentation P) z.1 S
              owner.1.1 owner.1.2) endpoint := corner.2.2
      _ = BDL26TannerLocalRegularity.edgeEndpoint
            (tannerDoubleCylinderEdgeStart (transposePresentation P) z.1 S)
            (tannerDoubleCylinderEdgeEnd (transposePresentation P) z.1 S)
            edge endpoint := congrArg
              (fun ownedEdge => BDL26TannerLocalRegularity.edgeEndpoint
                (tannerDoubleCylinderEdgeStart (transposePresentation P) z.1 S)
                (tannerDoubleCylinderEdgeEnd (transposePresentation P) z.1 S)
                ownedEdge endpoint) owner.2
      _ = z.2 := hendpoint
  refine ⟨Vertex.x x, ?_⟩
  change decide (∃ face : (rzReplacementPresentation P A S).Face,
    zStarFaceMember (rzReplacementPresentation P A S) z face = true ∧
      x = (rzReplacementPresentation P A S).faceX face) = true
  rw [decide_eq_true_eq]
  refine ⟨face, ?_, rfl⟩
  simp only [zStarFaceMember, decide_eq_true_eq]
  have hsigma : (⟨z.1,
      localCornerVertex P z.1 S owner.1.1 corner.1.1⟩ :
      Sigma fun oldZ : P.Z => ZDoubleCylinderVertex P oldZ S) = z := by
    exact Sigma.ext
      (x := (⟨z.1, localCornerVertex P z.1 S owner.1.1 corner.1.1⟩ :
        Sigma fun oldZ : P.Z => ZDoubleCylinderVertex P oldZ S))
      (y := z) rfl (heq_of_eq hvertex)
  change rzFaceZ P A S face = z
  rw [show rzFaceZ P A S face =
      localFaceZ P S ⟨z.1, owner.1.1, corner.1.1⟩ by rfl]
  rw [localFaceZ_eq_localCornerVertex]
  exact hsigma

/-- The concrete local successor face whose X endpoint is the deterministic
Z-boundary root.  It packages the already selected incident edge, face slot,
and matching corner without any new search. -/
private noncomputable def rzReplacementZBoundaryRootFace
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale)
    (z : (rzReplacementPresentation P
      A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S).Z) :
    ZStarFace
      (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S) z := by
  let A := A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  let incident := doubleCylinderVertexIncidentEdge (transposePresentation P)
    (transposeTannerSquareAdmissibleV3 P A3) z.1 S z.2
  let owner := doubleCylinderEdgeFaceSlotOwner (transposePresentation P)
    (transposeTannerSquareAdmissibleV3 P A3) z.1 S incident.1.1
  let corner := localCornerAtBoundaryEndpoint P z.1 S
    owner.1.1 owner.1.2 incident.1.2
  let face : (rzReplacementPresentation P A S).Face :=
    Sum.inl ⟨z.1, owner.1.1, corner.1.1⟩
  refine ⟨face, ?_⟩
  simp only [zStarFaceMember, decide_eq_true_eq]
  change localFaceZ P S ⟨z.1, owner.1.1, corner.1.1⟩ = z
  rw [localFaceZ_eq_localCornerVertex]
  apply Sigma.ext
    (x := (⟨z.1, localCornerVertex P z.1 S owner.1.1 corner.1.1⟩ :
      Sigma fun oldZ : P.Z => ZDoubleCylinderVertex P oldZ S))
    (y := z) rfl
  apply heq_of_eq
  exact calc
    localCornerVertex P z.1 S owner.1.1 corner.1.1 =
        BDL26TannerLocalRegularity.edgeEndpoint
          (tannerDoubleCylinderEdgeStart (transposePresentation P) z.1 S)
          (tannerDoubleCylinderEdgeEnd (transposePresentation P) z.1 S)
          (doubleCylinderFaceBoundaryEdge (transposePresentation P) z.1 S
            owner.1.1 owner.1.2) incident.1.2 := corner.2.2
    _ = BDL26TannerLocalRegularity.edgeEndpoint
          (tannerDoubleCylinderEdgeStart (transposePresentation P) z.1 S)
          (tannerDoubleCylinderEdgeEnd (transposePresentation P) z.1 S)
          incident.1.1 incident.1.2 := congrArg
            (fun ownedEdge => BDL26TannerLocalRegularity.edgeEndpoint
              (tannerDoubleCylinderEdgeStart (transposePresentation P) z.1 S)
              (tannerDoubleCylinderEdgeEnd (transposePresentation P) z.1 S)
              ownedEdge incident.1.2) owner.2
    _ = z.2 := incident.2

/-- The ordered Q corner of the packaged root face carried by the selected
incident edge. -/
private noncomputable def rzReplacementZBoundaryRootCorner
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale)
    (z : (rzReplacementPresentation P
      A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S).Z) : Two :=
  let incident := doubleCylinderVertexIncidentEdge (transposePresentation P)
    (transposeTannerSquareAdmissibleV3 P A3) z.1 S z.2
  let owner := doubleCylinderEdgeFaceSlotOwner (transposePresentation P)
    (transposeTannerSquareAdmissibleV3 P A3) z.1 S incident.1.1
  (localCornerAtBoundaryEndpoint P z.1 S
    owner.1.1 owner.1.2 incident.1.2).1.2

/-- The selected Q corner of the packaged root face is exactly the selected
incident local edge. -/
private theorem rzReplacementZBoundaryRootFaceQ_eq_incidentEdge
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale)
    (z : (rzReplacementPresentation P
      A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S).Z) :
    (rzReplacementPresentation P
      A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S).faceQ
        (rzReplacementZBoundaryRootFace P A3 S z).1
        (rzReplacementZBoundaryRootCorner P A3 S z) =
      Sum.inl ⟨z.1,
        (doubleCylinderVertexIncidentEdge (transposePresentation P)
          (transposeTannerSquareAdmissibleV3 P A3) z.1 S z.2).1.1⟩ := by
  let incident := doubleCylinderVertexIncidentEdge (transposePresentation P)
    (transposeTannerSquareAdmissibleV3 P A3) z.1 S z.2
  let owner := doubleCylinderEdgeFaceSlotOwner (transposePresentation P)
    (transposeTannerSquareAdmissibleV3 P A3) z.1 S incident.1.1
  let corner := localCornerAtBoundaryEndpoint P z.1 S
    owner.1.1 owner.1.2 incident.1.2
  change twoSelect
      (localFaceQ0 P S ⟨z.1, owner.1.1, corner.1.1⟩)
      (localFaceQ1 P S ⟨z.1, owner.1.1, corner.1.1⟩) corner.1.2 =
    Sum.inl ⟨z.1, incident.1.1⟩
  rw [localFaceQ_eq_corner]
  apply congrArg Sum.inl
  apply Sigma.ext
    (x := (⟨z.1, localCornerEdge P z.1 S owner.1.1 corner.1⟩ :
      Sigma fun oldZ : P.Z => ZDoubleCylinderEdge P oldZ S))
    (y := ⟨z.1, incident.1.1⟩) rfl
  apply heq_of_eq
  exact corner.2.1.trans owner.2

/-- The selected Q corner of any concrete face is an X-boundary vertex. -/
private def faceXBoundaryQVertex (P : TannerSquarePresentation)
    (face : P.Face) (corner : Two) :
    XStarBoundaryVertex P (P.faceX face) :=
  ⟨Vertex.q (P.faceQ face corner), by
    simp only [xStarBoundaryVertexMember, decide_eq_true_eq]
    refine ⟨face, ?_, ?_⟩
    · simp [xStarFaceMember]
    · exact rzTwoElim (motive := fun corner =>
        P.faceQ face corner = P.faceQ face 0 ∨
          P.faceQ face corner = P.faceQ face 1)
        (Or.inl rfl) (Or.inr rfl) corner⟩

/-- Historical successor X-boundary roots, selected from actual RZ faces.
Local and glue X tags retain their constructor face.  An old-X copy uses the
input V3 owner of the deterministic old radial anchor. -/
noncomputable def rzReplacementXBoundaryRoot
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale)
    (x : (rzReplacementPresentation P
      A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S).X) :
    XStarBoundaryVertex
      (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S) x := by
  let A := A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  rcases x with localOrGlue | oldX
  · rcases localOrGlue with localX | glue
    · let face : (rzReplacementPresentation P A S).Face :=
        Sum.inl ⟨localX.1, localX.2, (0, 0)⟩
      have hfaceX : (rzReplacementPresentation P A S).faceX face =
          Sum.inl (Sum.inl localX) := by rfl
      exact hfaceX ▸ faceXBoundaryQVertex
        (rzReplacementPresentation P A S) face 0
    · let endpoint : Two := 0
      let zroot := A.qzRoot glue.1
      let a : QZEdge P := ⟨(glue.1, zroot.1), zroot.2⟩
      let glueTag : Sigma fun edge : QZEdge P =>
          QDoubleCylinderEdge (transposePresentation P) edge.1.1 S × Two :=
        ⟨a, glue.2, endpoint⟩
      let face : (rzReplacementPresentation P A S).Face :=
        Sum.inr (Sum.inl glueTag)
      have hfaceX : (rzReplacementPresentation P A S).faceX face =
          Sum.inl (Sum.inr glue) := by
        apply congrArg (fun value => Sum.inl (Sum.inr value))
        apply Sigma.ext
        · rfl
        · rfl
      exact hfaceX ▸ faceXBoundaryQVertex
        (rzReplacementPresentation P A S) face 1
  · rcases oldX with ⟨oldX, copy⟩
    obtain ⟨⟨raw, member⟩, hstart⟩ := xStarAnchorRadialEdge P A3 oldX
    rcases raw with radial | impossible
    · let owner := A3.xRadialFaceOwner oldX radial member
      let face : (rzReplacementPresentation P A S).Face :=
        Sum.inr (Sum.inr (owner.1.1.1, copy))
      have hx : P.faceX owner.1.1.1 = oldX := by
        simpa [xStarFaceMember] using owner.1.1.2
      have hfaceX : (rzReplacementPresentation P A S).faceX face =
          Sum.inr (oldX, copy) := by
        change rzFaceX P S face = Sum.inr (oldX, copy)
        simp [face, rzFaceX, oldXFaceX, hx]
      exact hfaceX ▸ faceXBoundaryQVertex
        (rzReplacementPresentation P A S) face owner.1.2
    · change Vertex.q impossible.1.1 = Vertex.x oldX at hstart
      cases hstart

/-! ### Explicit within-face boundary paths -/

private def rzXStarFaceBoundaryEdge
    (P : TannerSquarePresentation) (x : P.X)
    (face : XStarFace P x) (corner : Two) : XStarBoundaryEdge P x := by
  let edge := xStarFaceQZEdge P x face corner
  refine ⟨edge.1, ?_⟩
  simpa [xStarBoundaryEdgeMember, xStarEdgeMember, edge, xStarFaceQZEdge]
    using edge.2

private noncomputable def rzZStarFaceBoundaryEdge
    (P : TannerSquarePresentation) (z : P.Z)
    (face : ZStarFace P z) (corner : Two) : ZStarBoundaryEdge P z :=
  transposeXStarBoundaryEdgeEquiv P z
    (rzXStarFaceBoundaryEdge (transposePresentation P) z
      ((transposeXStarFaceEquiv P z).symm face) corner)

private noncomputable def rzXStarFaceBoundaryPathToQ
    (P : TannerSquarePresentation) (x : P.X)
    (face : XStarFace P x) (corner : Two) :
    UndirectedPath (xBoundaryEdgeStart P x) (xBoundaryEdgeEnd P x)
      (xBoundaryEdgeStart P x (rzXStarFaceBoundaryEdge P x face 0))
      (xBoundaryEdgeStart P x (rzXStarFaceBoundaryEdge P x face corner)) :=
  rzTwoElim (motive := fun corner =>
      UndirectedPath (xBoundaryEdgeStart P x) (xBoundaryEdgeEnd P x)
        (xBoundaryEdgeStart P x (rzXStarFaceBoundaryEdge P x face 0))
        (xBoundaryEdgeStart P x
          (rzXStarFaceBoundaryEdge P x face corner)))
    .nil
    (.step
      (.step .nil (rzXStarFaceBoundaryEdge P x face 0)
        (Or.inl ⟨rfl, rfl⟩))
      (rzXStarFaceBoundaryEdge P x face 1)
      (Or.inr ⟨rfl, rfl⟩)) corner

private def rzXStarFaceBoundaryPathToZ
    (P : TannerSquarePresentation) (x : P.X)
    (face : XStarFace P x) :
    UndirectedPath (xBoundaryEdgeStart P x) (xBoundaryEdgeEnd P x)
      (xBoundaryEdgeStart P x (rzXStarFaceBoundaryEdge P x face 0))
      (xBoundaryEdgeEnd P x (rzXStarFaceBoundaryEdge P x face 0)) :=
  .step .nil (rzXStarFaceBoundaryEdge P x face 0)
    (Or.inl ⟨rfl, rfl⟩)

/-- One explicit X-boundary step from a face's Z vertex to either ordered Q
vertex. -/
private noncomputable def rzXStarFaceBoundaryPathFromZToQ
    (P : TannerSquarePresentation) (x : P.X)
    (face : XStarFace P x) (corner : Two) :
    UndirectedPath (xBoundaryEdgeStart P x) (xBoundaryEdgeEnd P x)
      (xBoundaryEdgeEnd P x (rzXStarFaceBoundaryEdge P x face corner))
      (xBoundaryEdgeStart P x (rzXStarFaceBoundaryEdge P x face corner)) :=
  .step .nil (rzXStarFaceBoundaryEdge P x face corner)
    (Or.inr ⟨rfl, rfl⟩)

/-- Regard one materialized corner of a fixed RZ local cell as a face in its
successor X-star. -/
private def rzLocalCellXStarFace
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (z : P.Z) (cell : ZDoubleCylinderFace P z S)
    (corner : Two × Two) :
    XStarFace (rzReplacementPresentation P A S)
      (Sum.inl (Sum.inl ⟨z, cell⟩)) :=
  ⟨Sum.inl ⟨z, cell, corner⟩, by
    simp only [xStarFaceMember, decide_eq_true_eq]
    rw [show (rzReplacementPresentation P A S).faceX = rzFaceX P S from rfl]
    rfl⟩

/-- Explicit four-corner link path around a fixed RZ local two-cell. -/
private noncomputable def rzLocalCellBoundaryPathToZCorner
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (z : P.Z) (cell : ZDoubleCylinderFace P z S)
    (corner : Two × Two) :
    UndirectedPath
      (xBoundaryEdgeStart (rzReplacementPresentation P A S)
        (Sum.inl (Sum.inl ⟨z, cell⟩)))
      (xBoundaryEdgeEnd (rzReplacementPresentation P A S)
        (Sum.inl (Sum.inl ⟨z, cell⟩)))
      (xBoundaryEdgeEnd (rzReplacementPresentation P A S)
        (Sum.inl (Sum.inl ⟨z, cell⟩))
        (rzXStarFaceBoundaryEdge (rzReplacementPresentation P A S)
          (Sum.inl (Sum.inl ⟨z, cell⟩))
          (rzLocalCellXStarFace P A S z cell (0, 0)) 0))
      (xBoundaryEdgeEnd (rzReplacementPresentation P A S)
        (Sum.inl (Sum.inl ⟨z, cell⟩))
        (rzXStarFaceBoundaryEdge (rzReplacementPresentation P A S)
          (Sum.inl (Sum.inl ⟨z, cell⟩))
          (rzLocalCellXStarFace P A S z cell corner) 0)) := by
  rcases cell with small | rectangle
  · rcases corner with ⟨first, second⟩
    exact rzTwoElim (motive := fun first =>
        ∀ second, UndirectedPath
          (xBoundaryEdgeStart (rzReplacementPresentation P A S)
            (Sum.inl (Sum.inl ⟨z, Sum.inl small⟩)))
          (xBoundaryEdgeEnd (rzReplacementPresentation P A S)
            (Sum.inl (Sum.inl ⟨z, Sum.inl small⟩)))
          (xBoundaryEdgeEnd (rzReplacementPresentation P A S)
            (Sum.inl (Sum.inl ⟨z, Sum.inl small⟩))
            (rzXStarFaceBoundaryEdge (rzReplacementPresentation P A S)
              (Sum.inl (Sum.inl ⟨z, Sum.inl small⟩))
              (rzLocalCellXStarFace P A S z (Sum.inl small) (0, 0)) 0))
          (xBoundaryEdgeEnd (rzReplacementPresentation P A S)
            (Sum.inl (Sum.inl ⟨z, Sum.inl small⟩))
            (rzXStarFaceBoundaryEdge (rzReplacementPresentation P A S)
              (Sum.inl (Sum.inl ⟨z, Sum.inl small⟩))
              (rzLocalCellXStarFace P A S z (Sum.inl small)
                (first, second)) 0)))
      (rzTwoElim
        .nil
        ((rzXStarFaceBoundaryPathFromZToQ _ _
            (rzLocalCellXStarFace P A S z (Sum.inl small) (0, 0)) 1).append
          (rzXStarFaceBoundaryPathFromZToQ _ _
            (rzLocalCellXStarFace P A S z (Sum.inl small) (0, 1)) 1).reverse))
      (rzTwoElim
        ((rzXStarFaceBoundaryPathFromZToQ _ _
            (rzLocalCellXStarFace P A S z (Sum.inl small) (0, 0)) 0).append
          (rzXStarFaceBoundaryPathFromZToQ _ _
            (rzLocalCellXStarFace P A S z (Sum.inl small) (1, 0)) 0).reverse)
        (((rzXStarFaceBoundaryPathFromZToQ _ _
            (rzLocalCellXStarFace P A S z (Sum.inl small) (0, 0)) 0).append
          (rzXStarFaceBoundaryPathFromZToQ _ _
            (rzLocalCellXStarFace P A S z (Sum.inl small) (1, 0)) 0).reverse).append
          ((rzXStarFaceBoundaryPathFromZToQ _ _
            (rzLocalCellXStarFace P A S z (Sum.inl small) (1, 0)) 1).append
          (rzXStarFaceBoundaryPathFromZToQ _ _
            (rzLocalCellXStarFace P A S z (Sum.inl small) (1, 1)) 1).reverse)))
      first second

  · rcases corner with ⟨first, second⟩
    exact rzTwoElim (motive := fun first =>
        ∀ second, UndirectedPath
          (xBoundaryEdgeStart (rzReplacementPresentation P A S)
            (Sum.inl (Sum.inl ⟨z, Sum.inr rectangle⟩)))
          (xBoundaryEdgeEnd (rzReplacementPresentation P A S)
            (Sum.inl (Sum.inl ⟨z, Sum.inr rectangle⟩)))
          (xBoundaryEdgeEnd (rzReplacementPresentation P A S)
            (Sum.inl (Sum.inl ⟨z, Sum.inr rectangle⟩))
            (rzXStarFaceBoundaryEdge (rzReplacementPresentation P A S)
              (Sum.inl (Sum.inl ⟨z, Sum.inr rectangle⟩))
              (rzLocalCellXStarFace P A S z (Sum.inr rectangle) (0, 0)) 0))
          (xBoundaryEdgeEnd (rzReplacementPresentation P A S)
            (Sum.inl (Sum.inl ⟨z, Sum.inr rectangle⟩))
            (rzXStarFaceBoundaryEdge (rzReplacementPresentation P A S)
              (Sum.inl (Sum.inl ⟨z, Sum.inr rectangle⟩))
              (rzLocalCellXStarFace P A S z (Sum.inr rectangle)
                (first, second)) 0)))
      (rzTwoElim
        .nil
        ((rzXStarFaceBoundaryPathFromZToQ _ _
            (rzLocalCellXStarFace P A S z (Sum.inr rectangle) (0, 0)) 0).append
          (rzXStarFaceBoundaryPathFromZToQ _ _
            (rzLocalCellXStarFace P A S z (Sum.inr rectangle) (0, 1)) 0).reverse))
      (rzTwoElim
        ((rzXStarFaceBoundaryPathFromZToQ _ _
            (rzLocalCellXStarFace P A S z (Sum.inr rectangle) (0, 0)) 1).append
          (rzXStarFaceBoundaryPathFromZToQ _ _
            (rzLocalCellXStarFace P A S z (Sum.inr rectangle) (1, 0)) 1).reverse)
        (((rzXStarFaceBoundaryPathFromZToQ _ _
            (rzLocalCellXStarFace P A S z (Sum.inr rectangle) (0, 0)) 1).append
          (rzXStarFaceBoundaryPathFromZToQ _ _
            (rzLocalCellXStarFace P A S z (Sum.inr rectangle) (1, 0)) 1).reverse).append
          ((rzXStarFaceBoundaryPathFromZToQ _ _
            (rzLocalCellXStarFace P A S z (Sum.inr rectangle) (1, 0)) 0).append
          (rzXStarFaceBoundaryPathFromZToQ _ _
            (rzLocalCellXStarFace P A S z (Sum.inr rectangle) (1, 1)) 0).reverse)))
      first second

/-! ### Local-cell X-star target normalization -/

private noncomputable def rzLocalCellZAt
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z)
    (cell : ZDoubleCylinderFace P z S) (corner : Two × Two) : RZZ P S :=
  localFaceZ P S ⟨z, cell, corner⟩

private noncomputable def rzLocalCellQAt
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (z : P.Z) (cell : ZDoubleCylinderFace P z S)
    (corner : Two × Two) (qCorner : Two) : RZQ P S :=
  rzFaceQ P A S (Sum.inl ⟨z, cell, corner⟩) qCorner

private theorem rzLocalCellBoundaryZ_cases
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (z : P.Z) (cell : ZDoubleCylinderFace P z S)
    (newZ : RZZ P S)
    (member : xStarBoundaryVertexMember (rzReplacementPresentation P A S)
      (Sum.inl (Sum.inl ⟨z, cell⟩)) (Vertex.z newZ) = true) :
    newZ = rzLocalCellZAt P S z cell (0, 0) ∨
      newZ = rzLocalCellZAt P S z cell (0, 1) ∨
      newZ = rzLocalCellZAt P S z cell (1, 0) ∨
      newZ = rzLocalCellZAt P S z cell (1, 1) := by
  classical
  simp only [xStarBoundaryVertexMember] at member
  rw [show (rzReplacementPresentation P A S).faceZ = rzFaceZ P A S from rfl]
    at member
  obtain ⟨face, hx, hz⟩ := of_decide_eq_true member
  simp only [xStarFaceMember, decide_eq_true_eq] at hx
  rw [show (rzReplacementPresentation P A S).faceX = rzFaceX P S from rfl] at hx
  rcases face with localFaceData | glueOrOld
  · rcases localFaceData with ⟨oldZ, localCell, corner⟩
    change (Sum.inl (Sum.inl (⟨oldZ, localCell⟩ :
      Sigma fun oldZ : P.Z => ZDoubleCylinderFace P oldZ S)) : RZX P S) =
        Sum.inl (Sum.inl ⟨z, cell⟩) at hx
    have howner : (⟨oldZ, localCell⟩ :
        Sigma fun oldZ : P.Z => ZDoubleCylinderFace P oldZ S) = ⟨z, cell⟩ :=
      Sum.inl.inj (Sum.inl.inj hx)
    cases howner
    rcases corner with ⟨first, second⟩
    exact rzTwoElim (motive := fun first =>
        ∀ second, newZ = rzLocalCellZAt P S z cell (first, second) →
          newZ = rzLocalCellZAt P S z cell (0, 0) ∨
          newZ = rzLocalCellZAt P S z cell (0, 1) ∨
          newZ = rzLocalCellZAt P S z cell (1, 0) ∨
          newZ = rzLocalCellZAt P S z cell (1, 1))
      (rzTwoElim (fun h => Or.inl h) (fun h => Or.inr (Or.inl h)))
      (rzTwoElim (fun h => Or.inr (Or.inr (Or.inl h)))
        (fun h => Or.inr (Or.inr (Or.inr h)))) first second hz
  · rcases glueOrOld with glue | old <;> cases hx

private theorem rzLocalCellBoundaryQ_cases
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (z : P.Z) (cell : ZDoubleCylinderFace P z S)
    (newQ : RZQ P S)
    (member : xStarBoundaryVertexMember (rzReplacementPresentation P A S)
      (Sum.inl (Sum.inl ⟨z, cell⟩)) (Vertex.q newQ) = true) :
    newQ = rzLocalCellQAt P A S z cell (0, 0) 0 ∨
      newQ = rzLocalCellQAt P A S z cell (0, 0) 1 ∨
      newQ = rzLocalCellQAt P A S z cell (0, 1) 0 ∨
      newQ = rzLocalCellQAt P A S z cell (0, 1) 1 ∨
      newQ = rzLocalCellQAt P A S z cell (1, 0) 0 ∨
      newQ = rzLocalCellQAt P A S z cell (1, 0) 1 ∨
      newQ = rzLocalCellQAt P A S z cell (1, 1) 0 ∨
      newQ = rzLocalCellQAt P A S z cell (1, 1) 1 := by
  classical
  simp only [xStarBoundaryVertexMember, decide_eq_true_eq] at member
  obtain ⟨face, hx, hq⟩ := member
  change newQ = rzFaceQ P A S face 0 ∨
    newQ = rzFaceQ P A S face 1 at hq
  simp only [xStarFaceMember, decide_eq_true_eq] at hx
  rw [show (rzReplacementPresentation P A S).faceX = rzFaceX P S from rfl] at hx
  rcases face with localFaceData | glueOrOld
  · rcases localFaceData with ⟨oldZ, localCell, corner⟩
    change (Sum.inl (Sum.inl (⟨oldZ, localCell⟩ :
      Sigma fun oldZ : P.Z => ZDoubleCylinderFace P oldZ S)) : RZX P S) =
        Sum.inl (Sum.inl ⟨z, cell⟩) at hx
    have howner : (⟨oldZ, localCell⟩ :
        Sigma fun oldZ : P.Z => ZDoubleCylinderFace P oldZ S) = ⟨z, cell⟩ :=
      Sum.inl.inj (Sum.inl.inj hx)
    cases howner
    rcases corner with ⟨first, second⟩
    have route : ∀ qCorner,
        newQ = rzLocalCellQAt P A S z cell (first, second) qCorner →
          newQ = rzLocalCellQAt P A S z cell (0, 0) 0 ∨
          newQ = rzLocalCellQAt P A S z cell (0, 0) 1 ∨
          newQ = rzLocalCellQAt P A S z cell (0, 1) 0 ∨
          newQ = rzLocalCellQAt P A S z cell (0, 1) 1 ∨
          newQ = rzLocalCellQAt P A S z cell (1, 0) 0 ∨
          newQ = rzLocalCellQAt P A S z cell (1, 0) 1 ∨
          newQ = rzLocalCellQAt P A S z cell (1, 1) 0 ∨
          newQ = rzLocalCellQAt P A S z cell (1, 1) 1 :=
      rzTwoElim (motive := fun first => ∀ second qCorner,
          newQ = rzLocalCellQAt P A S z cell (first, second) qCorner → _)
        (rzTwoElim
          (rzTwoElim (fun h => Or.inl h) (fun h => Or.inr (Or.inl h)))
          (rzTwoElim (fun h => Or.inr (Or.inr (Or.inl h)))
            (fun h => Or.inr (Or.inr (Or.inr (Or.inl h))))))
        (rzTwoElim
          (rzTwoElim (fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
            (fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
          (rzTwoElim
            (fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr (Or.inl h)))))))
            (fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr (Or.inr h))))))))) first second
    rcases hq with hq | hq
    · exact route 0 hq
    · exact route 1 hq
  · rcases glueOrOld with glue | old <;> cases hx

private noncomputable def rzLocalCellBoundaryPathToZTarget
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (z : P.Z) (cell : ZDoubleCylinderFace P z S)
    (corner : Two × Two) :
    UndirectedPath
      (xBoundaryEdgeStart (rzReplacementPresentation P A S)
        (Sum.inl (Sum.inl ⟨z, cell⟩)))
      (xBoundaryEdgeEnd (rzReplacementPresentation P A S)
        (Sum.inl (Sum.inl ⟨z, cell⟩)))
      (xBoundaryEdgeStart (rzReplacementPresentation P A S)
        (Sum.inl (Sum.inl ⟨z, cell⟩))
        (rzXStarFaceBoundaryEdge (rzReplacementPresentation P A S)
          (Sum.inl (Sum.inl ⟨z, cell⟩))
          (rzLocalCellXStarFace P A S z cell (0, 0)) 0))
      (xBoundaryEdgeEnd (rzReplacementPresentation P A S)
        (Sum.inl (Sum.inl ⟨z, cell⟩))
        (rzXStarFaceBoundaryEdge (rzReplacementPresentation P A S)
          (Sum.inl (Sum.inl ⟨z, cell⟩))
          (rzLocalCellXStarFace P A S z cell corner) 0)) :=
  (rzXStarFaceBoundaryPathToZ _ _
    (rzLocalCellXStarFace P A S z cell (0, 0))).append
  (rzLocalCellBoundaryPathToZCorner P A S z cell corner)

private noncomputable def rzLocalCellBoundaryPathToQCorner
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (z : P.Z) (cell : ZDoubleCylinderFace P z S)
    (corner : Two × Two) (qCorner : Two) :
    UndirectedPath
      (xBoundaryEdgeStart (rzReplacementPresentation P A S)
        (Sum.inl (Sum.inl ⟨z, cell⟩)))
      (xBoundaryEdgeEnd (rzReplacementPresentation P A S)
        (Sum.inl (Sum.inl ⟨z, cell⟩)))
      (xBoundaryEdgeStart (rzReplacementPresentation P A S)
        (Sum.inl (Sum.inl ⟨z, cell⟩))
        (rzXStarFaceBoundaryEdge (rzReplacementPresentation P A S)
          (Sum.inl (Sum.inl ⟨z, cell⟩))
          (rzLocalCellXStarFace P A S z cell (0, 0)) 0))
      (xBoundaryEdgeStart (rzReplacementPresentation P A S)
        (Sum.inl (Sum.inl ⟨z, cell⟩))
        (rzXStarFaceBoundaryEdge (rzReplacementPresentation P A S)
          (Sum.inl (Sum.inl ⟨z, cell⟩))
          (rzLocalCellXStarFace P A S z cell corner) qCorner)) :=
  (rzLocalCellBoundaryPathToZTarget P A S z cell corner).append
    (rzXStarFaceBoundaryPathFromZToQ _ _
      (rzLocalCellXStarFace P A S z cell corner) qCorner)

private theorem rzReplacementXBoundaryRoot_localCell
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (z : P.Z) (cell : ZDoubleCylinderFace P z S) :
    rzReplacementXBoundaryRoot P A3 S (Sum.inl (Sum.inl ⟨z, cell⟩)) =
      xBoundaryEdgeStart (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        (Sum.inl (Sum.inl ⟨z, cell⟩))
        (rzXStarFaceBoundaryEdge (rzReplacementPresentation P
          A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
          (Sum.inl (Sum.inl ⟨z, cell⟩))
          (rzLocalCellXStarFace P
            A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
            S z cell (0, 0)) 0) := by
  apply Subtype.ext
  rfl

private noncomputable def rzLocalCellBoundaryPathToZVertex
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (z : P.Z) (cell : ZDoubleCylinderFace P z S)
    (newZ : RZZ P S)
    (member : xStarBoundaryVertexMember (rzReplacementPresentation P
      A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
      (Sum.inl (Sum.inl ⟨z, cell⟩)) (Vertex.z newZ) = true) :
    UndirectedPath
      (xBoundaryEdgeStart (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        (Sum.inl (Sum.inl ⟨z, cell⟩)))
      (xBoundaryEdgeEnd (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        (Sum.inl (Sum.inl ⟨z, cell⟩)))
      (rzReplacementXBoundaryRoot P A3 S (Sum.inl (Sum.inl ⟨z, cell⟩)))
      ⟨Vertex.z newZ, member⟩ := by
  let A := A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  rw [rzReplacementXBoundaryRoot_localCell P A3 S z cell]
  by_cases h00 : newZ = rzLocalCellZAt P S z cell (0, 0)
  · let path := rzLocalCellBoundaryPathToZTarget P A S z cell (0, 0)
    have htarget : xBoundaryEdgeEnd (rzReplacementPresentation P A S)
        (Sum.inl (Sum.inl ⟨z, cell⟩))
        (rzXStarFaceBoundaryEdge (rzReplacementPresentation P A S)
          (Sum.inl (Sum.inl ⟨z, cell⟩))
          (rzLocalCellXStarFace P A S z cell (0, 0)) 0) =
        ⟨Vertex.z newZ, member⟩ := by
      apply Subtype.ext
      exact congrArg Vertex.z h00.symm
    exact htarget ▸ path
  · by_cases h01 : newZ = rzLocalCellZAt P S z cell (0, 1)
    · let path := rzLocalCellBoundaryPathToZTarget P A S z cell (0, 1)
      have htarget : xBoundaryEdgeEnd (rzReplacementPresentation P A S)
          (Sum.inl (Sum.inl ⟨z, cell⟩))
          (rzXStarFaceBoundaryEdge (rzReplacementPresentation P A S)
            (Sum.inl (Sum.inl ⟨z, cell⟩))
            (rzLocalCellXStarFace P A S z cell (0, 1)) 0) =
          ⟨Vertex.z newZ, member⟩ := by
        apply Subtype.ext
        exact congrArg Vertex.z h01.symm
      exact htarget ▸ path
    · by_cases h10 : newZ = rzLocalCellZAt P S z cell (1, 0)
      · let path := rzLocalCellBoundaryPathToZTarget P A S z cell (1, 0)
        have htarget : xBoundaryEdgeEnd (rzReplacementPresentation P A S)
            (Sum.inl (Sum.inl ⟨z, cell⟩))
            (rzXStarFaceBoundaryEdge (rzReplacementPresentation P A S)
              (Sum.inl (Sum.inl ⟨z, cell⟩))
              (rzLocalCellXStarFace P A S z cell (1, 0)) 0) =
            ⟨Vertex.z newZ, member⟩ := by
          apply Subtype.ext
          exact congrArg Vertex.z h10.symm
        exact htarget ▸ path
      · have remaining01 :=
          (rzLocalCellBoundaryZ_cases P A S z cell newZ member).resolve_left h00
        have remaining10 := remaining01.resolve_left h01
        have h11 := remaining10.resolve_left h10
        let path := rzLocalCellBoundaryPathToZTarget P A S z cell (1, 1)
        have htarget : xBoundaryEdgeEnd (rzReplacementPresentation P A S)
            (Sum.inl (Sum.inl ⟨z, cell⟩))
            (rzXStarFaceBoundaryEdge (rzReplacementPresentation P A S)
              (Sum.inl (Sum.inl ⟨z, cell⟩))
              (rzLocalCellXStarFace P A S z cell (1, 1)) 0) =
            ⟨Vertex.z newZ, member⟩ := by
          apply Subtype.ext
          exact congrArg Vertex.z h11.symm
        exact htarget ▸ path

private noncomputable def rzLocalCellBoundaryPathToQVertexAt
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (z : P.Z) (cell : ZDoubleCylinderFace P z S)
    (newQ : RZQ P S)
    (member : xStarBoundaryVertexMember (rzReplacementPresentation P
      A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
      (Sum.inl (Sum.inl ⟨z, cell⟩)) (Vertex.q newQ) = true)
    (corner : Two × Two) (qCorner : Two)
    (htarget : newQ = rzLocalCellQAt P
      A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
      S z cell corner qCorner) :
    UndirectedPath
      (xBoundaryEdgeStart (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        (Sum.inl (Sum.inl ⟨z, cell⟩)))
      (xBoundaryEdgeEnd (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        (Sum.inl (Sum.inl ⟨z, cell⟩)))
      (rzReplacementXBoundaryRoot P A3 S (Sum.inl (Sum.inl ⟨z, cell⟩)))
      ⟨Vertex.q newQ, member⟩ := by
  let A := A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  rw [rzReplacementXBoundaryRoot_localCell P A3 S z cell]
  let path := rzLocalCellBoundaryPathToQCorner P A S z cell corner qCorner
  have hend : xBoundaryEdgeStart (rzReplacementPresentation P A S)
      (Sum.inl (Sum.inl ⟨z, cell⟩))
      (rzXStarFaceBoundaryEdge (rzReplacementPresentation P A S)
        (Sum.inl (Sum.inl ⟨z, cell⟩))
        (rzLocalCellXStarFace P A S z cell corner) qCorner) =
      ⟨Vertex.q newQ, member⟩ := by
    apply Subtype.ext
    exact congrArg Vertex.q htarget.symm
  exact hend ▸ path

private noncomputable def rzLocalCellBoundaryPathToQVertex
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (z : P.Z) (cell : ZDoubleCylinderFace P z S)
    (newQ : RZQ P S)
    (member : xStarBoundaryVertexMember (rzReplacementPresentation P
      A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
      (Sum.inl (Sum.inl ⟨z, cell⟩)) (Vertex.q newQ) = true) :
    UndirectedPath
      (xBoundaryEdgeStart (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        (Sum.inl (Sum.inl ⟨z, cell⟩)))
      (xBoundaryEdgeEnd (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        (Sum.inl (Sum.inl ⟨z, cell⟩)))
      (rzReplacementXBoundaryRoot P A3 S (Sum.inl (Sum.inl ⟨z, cell⟩)))
      ⟨Vertex.q newQ, member⟩ := by
  let A := A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  have cases := rzLocalCellBoundaryQ_cases P A S z cell newQ member
  by_cases h000 : newQ = rzLocalCellQAt P A S z cell (0, 0) 0
  · exact rzLocalCellBoundaryPathToQVertexAt P A3 S z cell newQ member
      (0, 0) 0 h000
  · by_cases h001 : newQ = rzLocalCellQAt P A S z cell (0, 0) 1
    · exact rzLocalCellBoundaryPathToQVertexAt P A3 S z cell newQ member
        (0, 0) 1 h001
    · by_cases h010 : newQ = rzLocalCellQAt P A S z cell (0, 1) 0
      · exact rzLocalCellBoundaryPathToQVertexAt P A3 S z cell newQ member
          (0, 1) 0 h010
      · by_cases h011 : newQ = rzLocalCellQAt P A S z cell (0, 1) 1
        · exact rzLocalCellBoundaryPathToQVertexAt P A3 S z cell newQ member
            (0, 1) 1 h011
        · by_cases h100 : newQ = rzLocalCellQAt P A S z cell (1, 0) 0
          · exact rzLocalCellBoundaryPathToQVertexAt P A3 S z cell newQ member
              (1, 0) 0 h100
          · by_cases h101 : newQ = rzLocalCellQAt P A S z cell (1, 0) 1
            · exact rzLocalCellBoundaryPathToQVertexAt P A3 S z cell newQ member
                (1, 0) 1 h101
            · by_cases h110 : newQ = rzLocalCellQAt P A S z cell (1, 1) 0
              · exact rzLocalCellBoundaryPathToQVertexAt P A3 S z cell newQ
                  member (1, 1) 0 h110
              · have remaining001 := cases.resolve_left h000
                have remaining010 := remaining001.resolve_left h001
                have remaining011 := remaining010.resolve_left h010
                have remaining100 := remaining011.resolve_left h011
                have remaining101 := remaining100.resolve_left h100
                have remaining110 := remaining101.resolve_left h101
                have h111 := remaining110.resolve_left h110
                exact rzLocalCellBoundaryPathToQVertexAt P A3 S z cell newQ
                  member (1, 1) 1 h111

private noncomputable def rzLocalCellBoundaryPath
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (z : P.Z) (cell : ZDoubleCylinderFace P z S)
    (vertex : XStarBoundaryVertex (rzReplacementPresentation P
      A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
      (Sum.inl (Sum.inl ⟨z, cell⟩))) :
    UndirectedPath
      (xBoundaryEdgeStart (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        (Sum.inl (Sum.inl ⟨z, cell⟩)))
      (xBoundaryEdgeEnd (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        (Sum.inl (Sum.inl ⟨z, cell⟩)))
      (rzReplacementXBoundaryRoot P A3 S (Sum.inl (Sum.inl ⟨z, cell⟩)))
      vertex := by
  rcases vertex with ⟨value, member⟩
  rcases value with impossible | newQ | newZ
  · simp [xStarBoundaryVertexMember] at member
  · exact rzLocalCellBoundaryPathToQVertex P A3 S z cell newQ member
  · exact rzLocalCellBoundaryPathToZVertex P A3 S z cell newZ member

/-! ### Q-cylinder-edge X-star boundary data -/

/-- A successor Z vertex on the X-boundary of a fixed Q-cylinder edge retains
an old Q-Z incidence with that edge's old Q owner. -/
private theorem rzGlueXBoundaryZ_incidence
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale)
    (qEdge : Sigma fun q : P.Q =>
      QDoubleCylinderEdge (transposePresentation P) q S)
    (newZ : RZZ P S)
    (member : xStarBoundaryVertexMember (rzReplacementPresentation P A S)
      (Sum.inl (Sum.inr qEdge)) (Vertex.z newZ) = true) :
    P.qz qEdge.1 newZ.1 = true := by
  classical
  simp only [xStarBoundaryVertexMember] at member
  rw [show (rzReplacementPresentation P A S).faceZ = rzFaceZ P A S from rfl]
    at member
  obtain ⟨face, hx, hz⟩ := of_decide_eq_true member
  simp only [xStarFaceMember, decide_eq_true_eq] at hx
  rw [show (rzReplacementPresentation P A S).faceX = rzFaceX P S from rfl] at hx
  rcases face with localFace | glueOrOld
  · cases hx
  · rcases glueOrOld with glue | old
    · rcases glue with ⟨a, edge, endpoint⟩
      change (Sum.inl (Sum.inr
        (⟨a.1.1, edge⟩ : Sigma fun q : P.Q =>
          QDoubleCylinderEdge (transposePresentation P) q S)) : RZX P S) =
        Sum.inl (Sum.inr qEdge) at hx
      have howner : (⟨a.1.1, edge⟩ : Sigma fun q : P.Q =>
          QDoubleCylinderEdge (transposePresentation P) q S) = qEdge :=
        Sum.inr.inj (Sum.inl.inj hx)
      have hzowner : newZ.1 = a.1.2 := congrArg Sigma.fst hz
      have hqowner : a.1.1 = qEdge.1 := congrArg Sigma.fst howner
      simpa [hqowner, hzowner] using a.2
    · cases hx

/-- A Z boundary tag of a fixed glue X-star is the same-edge image of one of
the Q-cylinder edge's two oriented endpoints. -/
private theorem rzGlueXBoundaryZ_endpoints
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale)
    (qEdge : Sigma fun q : P.Q =>
      QDoubleCylinderEdge (transposePresentation P) q S)
    (newZ : RZZ P S)
    (member : xStarBoundaryVertexMember (rzReplacementPresentation P A S)
      (Sum.inl (Sum.inr qEdge)) (Vertex.z newZ) = true) :
    let hqz := rzGlueXBoundaryZ_incidence P A S qEdge newZ member
    newZ = ⟨newZ.1, qToZDoubleCylinderVertex P A qEdge.1 newZ.1 hqz S
        (qDoubleCylinderEdgeStart
          (transposePresentation P) qEdge.1 S qEdge.2)⟩ ∨
      newZ = ⟨newZ.1, qToZDoubleCylinderVertex P A qEdge.1 newZ.1 hqz S
        (qDoubleCylinderEdgeEnd
          (transposePresentation P) qEdge.1 S qEdge.2)⟩ := by
  classical
  dsimp only
  simp only [xStarBoundaryVertexMember] at member
  rw [show (rzReplacementPresentation P A S).faceZ = rzFaceZ P A S from rfl]
    at member
  obtain ⟨face, hx, hz⟩ := of_decide_eq_true member
  simp only [xStarFaceMember, decide_eq_true_eq] at hx
  rw [show (rzReplacementPresentation P A S).faceX = rzFaceX P S from rfl] at hx
  rcases face with localFace | glueOrOld
  · cases hx
  · rcases glueOrOld with glue | old
    · rcases glue with ⟨a, edge, endpoint⟩
      change (Sum.inl (Sum.inr
        (⟨a.1.1, edge⟩ : Sigma fun q : P.Q =>
          QDoubleCylinderEdge (transposePresentation P) q S)) : RZX P S) =
        Sum.inl (Sum.inr qEdge) at hx
      have howner : (⟨a.1.1, edge⟩ : Sigma fun q : P.Q =>
          QDoubleCylinderEdge (transposePresentation P) q S) = qEdge :=
        Sum.inr.inj (Sum.inl.inj hx)
      cases howner
      cases hz
      exact rzTwoElim (motive := fun endpoint =>
          (⟨a.1.2, glueCornerVertex P A S a edge endpoint⟩ : RZZ P S) =
              ⟨a.1.2, qToZDoubleCylinderVertex P A a.1.1 a.1.2
                (rzGlueXBoundaryZ_incidence P A S ⟨a.1.1, edge⟩
                  ⟨a.1.2, glueCornerVertex P A S a edge endpoint⟩
                  (by
                    simp only [xStarBoundaryVertexMember]
                    apply decide_eq_true
                    refine ⟨Sum.inr (Sum.inl ⟨a, edge, endpoint⟩), ?_, rfl⟩
                    simp only [xStarFaceMember, decide_eq_true_eq]
                    rw [show (rzReplacementPresentation P A S).faceX =
                      rzFaceX P S from rfl]
                    rfl)) S
                (qDoubleCylinderEdgeStart
                  (transposePresentation P) a.1.1 S edge)⟩ ∨
            (⟨a.1.2, glueCornerVertex P A S a edge endpoint⟩ : RZZ P S) =
              ⟨a.1.2, qToZDoubleCylinderVertex P A a.1.1 a.1.2
                (rzGlueXBoundaryZ_incidence P A S ⟨a.1.1, edge⟩
                  ⟨a.1.2, glueCornerVertex P A S a edge endpoint⟩
                  (by
                    simp only [xStarBoundaryVertexMember]
                    apply decide_eq_true
                    refine ⟨Sum.inr (Sum.inl ⟨a, edge, endpoint⟩), ?_, rfl⟩
                    simp only [xStarFaceMember, decide_eq_true_eq]
                    rw [show (rzReplacementPresentation P A S).faceX =
                      rzFaceX P S from rfl]
                    rfl)) S
                (qDoubleCylinderEdgeEnd
                  (transposePresentation P) a.1.1 S edge)⟩)
        (Or.inl (by simp [glueCornerVertex, edgeEndpoint, twoSelect]))
        (Or.inr (by simp [glueCornerVertex, edgeEndpoint, twoSelect])) endpoint
    · cases hx

/-- A local-edge Q boundary tag in a fixed glue X-star retains the old Q-Z
incidence of its local-edge owner. -/
private theorem rzGlueXBoundaryLocalQ_incidence
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale)
    (qEdge : Sigma fun q : P.Q =>
      QDoubleCylinderEdge (transposePresentation P) q S)
    (localEdge : Sigma fun z : P.Z => ZDoubleCylinderEdge P z S)
    (member : xStarBoundaryVertexMember (rzReplacementPresentation P A S)
      (Sum.inl (Sum.inr qEdge)) (Vertex.q (Sum.inl localEdge)) = true) :
    P.qz qEdge.1 localEdge.1 = true := by
  classical
  simp only [xStarBoundaryVertexMember, decide_eq_true_eq] at member
  obtain ⟨face, hx, hq⟩ := member
  change Sum.inl localEdge = rzFaceQ P A S face 0 ∨
    Sum.inl localEdge = rzFaceQ P A S face 1 at hq
  simp only [xStarFaceMember, decide_eq_true_eq] at hx
  rw [show (rzReplacementPresentation P A S).faceX = rzFaceX P S from rfl] at hx
  rcases face with localFace | glueOrOld
  · cases hx
  · rcases glueOrOld with glue | old
    · rcases glue with ⟨a, edge, endpoint⟩
      change (Sum.inl (Sum.inr
        (⟨a.1.1, edge⟩ : Sigma fun q : P.Q =>
          QDoubleCylinderEdge (transposePresentation P) q S)) : RZX P S) =
        Sum.inl (Sum.inr qEdge) at hx
      have howner : (⟨a.1.1, edge⟩ : Sigma fun q : P.Q =>
          QDoubleCylinderEdge (transposePresentation P) q S) = qEdge :=
        Sum.inr.inj (Sum.inl.inj hx)
      rcases hq with hq | hq
      · have hlocal := Sum.inl.inj hq
        have hzowner : localEdge.1 = a.1.2 := congrArg Sigma.fst hlocal
        have hqowner : a.1.1 = qEdge.1 := congrArg Sigma.fst howner
        rw [← hqowner, hzowner]
        exact a.2
      · cases hq
    · cases hx

/-- The local edge itself is the same-edge Z-boundary image of the fixed
Q-cylinder edge at its stored old Z owner. -/
private theorem rzGlueXBoundaryLocalQ_edge
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale)
    (qEdge : Sigma fun q : P.Q =>
      QDoubleCylinderEdge (transposePresentation P) q S)
    (localEdge : Sigma fun z : P.Z => ZDoubleCylinderEdge P z S)
    (member : xStarBoundaryVertexMember (rzReplacementPresentation P A S)
      (Sum.inl (Sum.inr qEdge)) (Vertex.q (Sum.inl localEdge)) = true) :
    localEdge.2 = qToZDoubleCylinderEdge P A qEdge.1 localEdge.1
      (rzGlueXBoundaryLocalQ_incidence P A S qEdge localEdge member)
      S qEdge.2 := by
  classical
  simp only [xStarBoundaryVertexMember, decide_eq_true_eq] at member
  obtain ⟨face, hx, hq⟩ := member
  change Sum.inl localEdge = rzFaceQ P A S face 0 ∨
    Sum.inl localEdge = rzFaceQ P A S face 1 at hq
  simp only [xStarFaceMember, decide_eq_true_eq] at hx
  rw [show (rzReplacementPresentation P A S).faceX = rzFaceX P S from rfl] at hx
  rcases face with localFace | glueOrOld
  · cases hx
  · rcases glueOrOld with glue | old
    · rcases glue with ⟨a, edge, endpoint⟩
      change (Sum.inl (Sum.inr
        (⟨a.1.1, edge⟩ : Sigma fun q : P.Q =>
          QDoubleCylinderEdge (transposePresentation P) q S)) : RZX P S) =
        Sum.inl (Sum.inr qEdge) at hx
      have howner : (⟨a.1.1, edge⟩ : Sigma fun q : P.Q =>
          QDoubleCylinderEdge (transposePresentation P) q S) = qEdge :=
        Sum.inr.inj (Sum.inl.inj hx)
      rcases hq with hq | hq
      · have hlocal := Sum.inl.inj hq
        cases howner
        cases hlocal
        rfl
      · cases hq
    · cases hx

/-- A Q-cylinder-vertex boundary tag of a fixed glue X-star is one of that
edge's two explicit endpoints.  The face existential is eliminated only in
this proposition-valued declaration. -/
private theorem rzGlueXBoundaryQVertex_endpoints
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale)
    (qEdge : Sigma fun q : P.Q =>
      QDoubleCylinderEdge (transposePresentation P) q S)
    (qVertex : Sigma fun q : P.Q =>
      QDoubleCylinderVertex (transposePresentation P) q S)
    (member : xStarBoundaryVertexMember (rzReplacementPresentation P A S)
      (Sum.inl (Sum.inr qEdge)) (Vertex.q (Sum.inr qVertex)) = true) :
    qVertex = ⟨qEdge.1, qDoubleCylinderEdgeStart
        (transposePresentation P) qEdge.1 S qEdge.2⟩ ∨
      qVertex = ⟨qEdge.1, qDoubleCylinderEdgeEnd
        (transposePresentation P) qEdge.1 S qEdge.2⟩ := by
  classical
  simp only [xStarBoundaryVertexMember, decide_eq_true_eq] at member
  obtain ⟨face, hx, hq⟩ := member
  change Sum.inr qVertex = rzFaceQ P A S face 0 ∨
    Sum.inr qVertex = rzFaceQ P A S face 1 at hq
  rcases face with localFace | glueOrOld
  · simp only [xStarFaceMember, decide_eq_true_eq] at hx
    change Sum.inl (Sum.inl (⟨localFace.1, localFace.2.1⟩ :
      Sigma fun z : P.Z => ZDoubleCylinderFace P z S)) =
      Sum.inl (Sum.inr qEdge) at hx
    cases Sum.inl.inj hx
  · rcases glueOrOld with glue | old
    · rcases glue with ⟨a, edge, endpoint⟩
      simp only [xStarFaceMember, decide_eq_true_eq] at hx
      change Sum.inl (Sum.inr ⟨a.1.1, edge⟩) =
        Sum.inl (Sum.inr qEdge) at hx
      have howner : (⟨a.1.1, edge⟩ : Sigma fun q : P.Q =>
          QDoubleCylinderEdge (transposePresentation P) q S) = qEdge :=
        Sum.inr.inj (Sum.inl.inj hx)
      rcases hq with hq | hq
      · change Sum.inr qVertex = glueFaceQ0 P A S ⟨a, edge, endpoint⟩
          at hq
        cases hq
      · change Sum.inr qVertex = glueFaceQ1 P S ⟨a, edge, endpoint⟩
          at hq
        have hvertex := Sum.inr.inj hq
        cases howner
        exact rzTwoElim (motive := fun endpoint =>
            qVertex = ⟨a.1.1, edgeEndpoint
              (qDoubleCylinderEdgeStart (transposePresentation P) a.1.1 S)
              (qDoubleCylinderEdgeEnd (transposePresentation P) a.1.1 S)
              edge endpoint⟩ →
              qVertex = ⟨a.1.1, qDoubleCylinderEdgeStart
                  (transposePresentation P) a.1.1 S edge⟩ ∨
                qVertex = ⟨a.1.1, qDoubleCylinderEdgeEnd
                  (transposePresentation P) a.1.1 S edge⟩)
          (fun h => Or.inl h) (fun h => Or.inr h) endpoint hvertex
    · simp only [xStarFaceMember, decide_eq_true_eq] at hx
      change Sum.inr (P.faceX old.1, old.2) =
        Sum.inl (Sum.inr qEdge) at hx
      cases hx

/-- Deterministically retain the orientation tag of a vertex already known
to be one of an edge's two endpoints. -/
private noncomputable def rzOrientedBoundaryEndpoint
    {Vertex Edge : Type} [DecidableEq Vertex]
    (start finish : Edge → Vertex) (edge : Edge) (vertex : Vertex) : Two :=
  if vertex = start edge then 0 else 1

private theorem rzOrientedBoundaryEndpoint_spec
    {Vertex Edge : Type} [DecidableEq Vertex]
    (start finish : Edge → Vertex) (edge : Edge) (vertex : Vertex)
    (hendpoint : vertex = start edge ∨ vertex = finish edge) :
    edgeEndpoint start finish edge
        (rzOrientedBoundaryEndpoint start finish edge vertex) = vertex := by
  by_cases hstart : vertex = start edge
  · simp [rzOrientedBoundaryEndpoint, hstart, edgeEndpoint, twoSelect]
  · have hfinish : vertex = finish edge := hendpoint.resolve_left hstart
    subst vertex
    simp [rzOrientedBoundaryEndpoint, hstart, edgeEndpoint, twoSelect]

/-- A concrete glue face of the fixed Q-cylinder-edge X-star. -/
private def rzGlueXStarFace
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale)
    (qEdge : Sigma fun q : P.Q =>
      QDoubleCylinderEdge (transposePresentation P) q S)
    (z : P.Z) (hqz : P.qz qEdge.1 z = true) (endpoint : Two) :
    XStarFace (rzReplacementPresentation P A S)
      (Sum.inl (Sum.inr qEdge)) :=
  ⟨Sum.inr (Sum.inl
      ⟨(⟨(qEdge.1, z), hqz⟩ : QZEdge P), qEdge.2, endpoint⟩), by
    simp only [xStarFaceMember, decide_eq_true_eq]
    rw [show (rzReplacementPresentation P A S).faceX = rzFaceX P S from rfl]
    rfl⟩

/-- The historical glue-X root reaches every Q-cylinder endpoint by two
within-face spans through the root glue face's common local Q vertex. -/
private noncomputable def rzGlueXBoundaryPathToQVertex
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale)
    (qEdge : Sigma fun q : P.Q =>
      QDoubleCylinderEdge (transposePresentation P) q S)
    (qVertex : Sigma fun q : P.Q =>
      QDoubleCylinderVertex (transposePresentation P) q S)
    (member : xStarBoundaryVertexMember
      (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
      (Sum.inl (Sum.inr qEdge)) (Vertex.q (Sum.inr qVertex)) = true) :
    UndirectedPath
      (xBoundaryEdgeStart (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
          (Sum.inl (Sum.inr qEdge)))
      (xBoundaryEdgeEnd (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
          (Sum.inl (Sum.inr qEdge)))
      (rzReplacementXBoundaryRoot P A3 S
        (Sum.inl (Sum.inr qEdge)))
      ⟨Vertex.q (Sum.inr qVertex), member⟩ := by
  let A := A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  have hdata := rzGlueXBoundaryQVertex_endpoints P A S qEdge qVertex member
  let startVertex : Sigma fun q : P.Q =>
      QDoubleCylinderVertex (transposePresentation P) q S :=
    ⟨qEdge.1, qDoubleCylinderEdgeStart
      (transposePresentation P) qEdge.1 S qEdge.2⟩
  let endVertex : Sigma fun q : P.Q =>
      QDoubleCylinderVertex (transposePresentation P) q S :=
    ⟨qEdge.1, qDoubleCylinderEdgeEnd
      (transposePresentation P) qEdge.1 S qEdge.2⟩
  let endpoint := rzOrientedBoundaryEndpoint
    (fun _ : Unit => startVertex) (fun _ : Unit => endVertex) () qVertex
  let root := A.qzRoot qEdge.1
  let rootFace := rzGlueXStarFace P A S qEdge root.1 root.2 0
  let targetFace := rzGlueXStarFace P A S qEdge root.1 root.2 endpoint
  let path :=
    (rzXStarFaceBoundaryPathToQ
      (rzReplacementPresentation P A S) (Sum.inl (Sum.inr qEdge))
      rootFace 1).reverse.append
    (rzXStarFaceBoundaryPathToQ
      (rzReplacementPresentation P A S) (Sum.inl (Sum.inr qEdge))
      targetFace 1)
  have hselected :
      (⟨qEdge.1, edgeEndpoint
        (qDoubleCylinderEdgeStart (transposePresentation P) qEdge.1 S)
        (qDoubleCylinderEdgeEnd (transposePresentation P) qEdge.1 S)
        qEdge.2 endpoint⟩ : Sigma fun q : P.Q =>
          QDoubleCylinderVertex (transposePresentation P) q S) = qVertex := by
    have hshape : edgeEndpoint
        (fun _ : Unit => startVertex) (fun _ : Unit => endVertex) () endpoint =
        (⟨qEdge.1, edgeEndpoint
          (qDoubleCylinderEdgeStart (transposePresentation P) qEdge.1 S)
          (qDoubleCylinderEdgeEnd (transposePresentation P) qEdge.1 S)
          qEdge.2 endpoint⟩ : Sigma fun q : P.Q =>
            QDoubleCylinderVertex (transposePresentation P) q S) :=
      rzTwoElim (motive := fun endpoint => edgeEndpoint
          (fun _ : Unit => startVertex) (fun _ : Unit => endVertex) () endpoint =
          (⟨qEdge.1, edgeEndpoint
            (qDoubleCylinderEdgeStart (transposePresentation P) qEdge.1 S)
            (qDoubleCylinderEdgeEnd (transposePresentation P) qEdge.1 S)
            qEdge.2 endpoint⟩ : Sigma fun q : P.Q =>
              QDoubleCylinderVertex (transposePresentation P) q S))
        rfl rfl endpoint
    exact hshape.symm.trans (rzOrientedBoundaryEndpoint_spec
      (fun _ : Unit => startVertex) (fun _ : Unit => endVertex)
      () qVertex hdata)
  have htarget : xBoundaryEdgeStart (rzReplacementPresentation P A S)
      (Sum.inl (Sum.inr qEdge))
      (rzXStarFaceBoundaryEdge (rzReplacementPresentation P A S)
        (Sum.inl (Sum.inr qEdge)) targetFace 1) =
      ⟨Vertex.q (Sum.inr qVertex), member⟩ := by
    apply Subtype.ext
    apply congrArg Vertex.q
    apply congrArg Sum.inr
    exact hselected
  have hroot : xBoundaryEdgeStart (rzReplacementPresentation P A S)
      (Sum.inl (Sum.inr qEdge))
      (rzXStarFaceBoundaryEdge (rzReplacementPresentation P A S)
        (Sum.inl (Sum.inr qEdge)) rootFace 1) =
      rzReplacementXBoundaryRoot P A3 S
        (Sum.inl (Sum.inr qEdge)) := by
    apply Subtype.ext
    rfl
  exact hroot ▸ htarget ▸ path

/-- The historical glue-X root reaches a local-edge Q target directly through
the endpoint-zero glue face at that edge's stored old Z owner. -/
private noncomputable def rzGlueXBoundaryPathToLocalQ
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale)
    (qEdge : Sigma fun q : P.Q =>
      QDoubleCylinderEdge (transposePresentation P) q S)
    (localEdge : Sigma fun z : P.Z => ZDoubleCylinderEdge P z S)
    (member : xStarBoundaryVertexMember
      (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
      (Sum.inl (Sum.inr qEdge)) (Vertex.q (Sum.inl localEdge)) = true) :
    UndirectedPath
      (xBoundaryEdgeStart (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
          (Sum.inl (Sum.inr qEdge)))
      (xBoundaryEdgeEnd (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
          (Sum.inl (Sum.inr qEdge)))
      (rzReplacementXBoundaryRoot P A3 S
        (Sum.inl (Sum.inr qEdge)))
      ⟨Vertex.q (Sum.inl localEdge), member⟩ := by
  let A := A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  let hqz := rzGlueXBoundaryLocalQ_incidence P A S qEdge localEdge member
  let targetFace := rzGlueXStarFace P A S qEdge localEdge.1 hqz 0
  let path := (rzXStarFaceBoundaryPathToQ
    (rzReplacementPresentation P A S) (Sum.inl (Sum.inr qEdge))
    targetFace 1).reverse
  have htarget : xBoundaryEdgeStart (rzReplacementPresentation P A S)
      (Sum.inl (Sum.inr qEdge))
      (rzXStarFaceBoundaryEdge (rzReplacementPresentation P A S)
        (Sum.inl (Sum.inr qEdge)) targetFace 0) =
      ⟨Vertex.q (Sum.inl localEdge), member⟩ := by
    apply Subtype.ext
    apply congrArg Vertex.q
    apply congrArg Sum.inl
    refine Sigma.ext (x := (⟨localEdge.1,
      qToZDoubleCylinderEdge P A qEdge.1 localEdge.1 hqz S qEdge.2⟩ :
        Sigma fun z : P.Z => ZDoubleCylinderEdge P z S))
      (y := localEdge) rfl ?_
    exact heq_of_eq
      (rzGlueXBoundaryLocalQ_edge P A S qEdge localEdge member).symm
  have hroot : xBoundaryEdgeStart (rzReplacementPresentation P A S)
      (Sum.inl (Sum.inr qEdge))
      (rzXStarFaceBoundaryEdge (rzReplacementPresentation P A S)
        (Sum.inl (Sum.inr qEdge)) targetFace 1) =
      rzReplacementXBoundaryRoot P A3 S
        (Sum.inl (Sum.inr qEdge)) := by
    apply Subtype.ext
    rfl
  exact hroot ▸ htarget ▸ path

/-- The historical glue-X root reaches a Z target through the endpoint-zero
face at its old Z owner and then the explicitly oriented target face. -/
private noncomputable def rzGlueXBoundaryPathToZ
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale)
    (qEdge : Sigma fun q : P.Q =>
      QDoubleCylinderEdge (transposePresentation P) q S)
    (newZ : RZZ P S)
    (member : xStarBoundaryVertexMember
      (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
      (Sum.inl (Sum.inr qEdge)) (Vertex.z newZ) = true) :
    UndirectedPath
      (xBoundaryEdgeStart (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
          (Sum.inl (Sum.inr qEdge)))
      (xBoundaryEdgeEnd (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
          (Sum.inl (Sum.inr qEdge)))
      (rzReplacementXBoundaryRoot P A3 S
        (Sum.inl (Sum.inr qEdge)))
      ⟨Vertex.z newZ, member⟩ := by
  classical
  let A := A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  let hqz := rzGlueXBoundaryZ_incidence P A S qEdge newZ member
  have hdata := rzGlueXBoundaryZ_endpoints P A S qEdge newZ member
  let startZ : RZZ P S := ⟨newZ.1,
    qToZDoubleCylinderVertex P A qEdge.1 newZ.1 hqz S
      (qDoubleCylinderEdgeStart
        (transposePresentation P) qEdge.1 S qEdge.2)⟩
  let endZ : RZZ P S := ⟨newZ.1,
    qToZDoubleCylinderVertex P A qEdge.1 newZ.1 hqz S
      (qDoubleCylinderEdgeEnd
        (transposePresentation P) qEdge.1 S qEdge.2)⟩
  let endpoint := rzOrientedBoundaryEndpoint
    (fun _ : Unit => startZ) (fun _ : Unit => endZ) () newZ
  let rootFace := rzGlueXStarFace P A S qEdge newZ.1 hqz 0
  let targetFace := rzGlueXStarFace P A S qEdge newZ.1 hqz endpoint
  let path :=
    (rzXStarFaceBoundaryPathToQ
      (rzReplacementPresentation P A S) (Sum.inl (Sum.inr qEdge))
      rootFace 1).reverse.append
    (rzXStarFaceBoundaryPathToZ
      (rzReplacementPresentation P A S) (Sum.inl (Sum.inr qEdge))
      targetFace)
  have hselected : edgeEndpoint
      (fun _ : Unit => startZ) (fun _ : Unit => endZ) () endpoint = newZ :=
    rzOrientedBoundaryEndpoint_spec _ _ _ _ hdata
  have hshape : edgeEndpoint
      (fun _ : Unit => startZ) (fun _ : Unit => endZ) () endpoint =
      ⟨newZ.1, qToZDoubleCylinderVertex P A qEdge.1 newZ.1 hqz S
        (edgeEndpoint
          (qDoubleCylinderEdgeStart (transposePresentation P) qEdge.1 S)
          (qDoubleCylinderEdgeEnd (transposePresentation P) qEdge.1 S)
          qEdge.2 endpoint)⟩ :=
    rzTwoElim (motive := fun endpoint => edgeEndpoint
        (fun _ : Unit => startZ) (fun _ : Unit => endZ) () endpoint =
        ⟨newZ.1, qToZDoubleCylinderVertex P A qEdge.1 newZ.1 hqz S
          (edgeEndpoint
            (qDoubleCylinderEdgeStart (transposePresentation P) qEdge.1 S)
            (qDoubleCylinderEdgeEnd (transposePresentation P) qEdge.1 S)
            qEdge.2 endpoint)⟩)
      rfl rfl endpoint
  have htarget : xBoundaryEdgeEnd (rzReplacementPresentation P A S)
      (Sum.inl (Sum.inr qEdge))
      (rzXStarFaceBoundaryEdge (rzReplacementPresentation P A S)
        (Sum.inl (Sum.inr qEdge)) targetFace 0) =
      ⟨Vertex.z newZ, member⟩ := by
    apply Subtype.ext
    apply congrArg Vertex.z
    exact hshape.symm.trans hselected
  have hroot : xBoundaryEdgeStart (rzReplacementPresentation P A S)
      (Sum.inl (Sum.inr qEdge))
      (rzXStarFaceBoundaryEdge (rzReplacementPresentation P A S)
        (Sum.inl (Sum.inr qEdge)) rootFace 1) =
      rzReplacementXBoundaryRoot P A3 S
        (Sum.inl (Sum.inr qEdge)) := by
    apply Subtype.ext
    rfl
  exact hroot ▸ htarget ▸ path

/-- Complete historical boundary routing for a fixed glue X tag. -/
private noncomputable def rzGlueXBoundaryPath
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale)
    (qEdge : Sigma fun q : P.Q =>
      QDoubleCylinderEdge (transposePresentation P) q S)
    (vertex : XStarBoundaryVertex
      (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
      (Sum.inl (Sum.inr qEdge))) :
    UndirectedPath
      (xBoundaryEdgeStart (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
          (Sum.inl (Sum.inr qEdge)))
      (xBoundaryEdgeEnd (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
          (Sum.inl (Sum.inr qEdge)))
      (rzReplacementXBoundaryRoot P A3 S
        (Sum.inl (Sum.inr qEdge))) vertex := by
  rcases vertex with ⟨value, member⟩
  rcases value with successorX | successorQ | successorZ
  · simp [xStarBoundaryVertexMember] at member
  · rcases successorQ with localEdge | qVertex
    · exact rzGlueXBoundaryPathToLocalQ P A3 S qEdge localEdge member
    · exact rzGlueXBoundaryPathToQVertex P A3 S qEdge qVertex member
  · exact rzGlueXBoundaryPathToZ P A3 S qEdge successorZ member

private noncomputable def rzZStarFaceBoundaryPathToQ
    (P : TannerSquarePresentation) (z : P.Z)
    (face : ZStarFace P z) (corner : Two) :
    UndirectedPath (zBoundaryEdgeStart P z) (zBoundaryEdgeEnd P z)
      (zBoundaryEdgeEnd P z (rzZStarFaceBoundaryEdge P z face 0))
      (zBoundaryEdgeEnd P z (rzZStarFaceBoundaryEdge P z face corner)) :=
  rzTwoElim (motive := fun corner =>
      UndirectedPath (zBoundaryEdgeStart P z) (zBoundaryEdgeEnd P z)
        (zBoundaryEdgeEnd P z (rzZStarFaceBoundaryEdge P z face 0))
        (zBoundaryEdgeEnd P z
          (rzZStarFaceBoundaryEdge P z face corner)))
    .nil
    (.step
      (.step .nil (rzZStarFaceBoundaryEdge P z face 0)
        (Or.inr ⟨rfl, rfl⟩))
      (rzZStarFaceBoundaryEdge P z face 1)
      (Or.inl ⟨rfl, rfl⟩)) corner

private noncomputable def rzZStarFaceBoundaryPathToX
    (P : TannerSquarePresentation) (z : P.Z)
    (face : ZStarFace P z) :
    UndirectedPath (zBoundaryEdgeStart P z) (zBoundaryEdgeEnd P z)
      (zBoundaryEdgeEnd P z (rzZStarFaceBoundaryEdge P z face 0))
      (zBoundaryEdgeStart P z (rzZStarFaceBoundaryEdge P z face 0)) :=
  .step .nil (rzZStarFaceBoundaryEdge P z face 0)
    (Or.inr ⟨rfl, rfl⟩)

private noncomputable def oldXBoundaryVertexLift
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (x : P.X) (copy : Two) :
    XStarBoundaryVertex P x →
      XStarBoundaryVertex (rzReplacementPresentation P A S)
        (Sum.inr (x, copy)) := by
  intro vertex
  rcases vertex with ⟨value, hvalue⟩
  rcases value with oldX | q | z
  · simp [xStarBoundaryVertexMember] at hvalue
  · have hxq : P.xq x q = true := by
      simp only [xStarBoundaryVertexMember, decide_eq_true_eq] at hvalue
      obtain ⟨face, hface, hcorner⟩ := hvalue
      have hx : P.faceX face = x := by
        simpa [xStarFaceMember] using hface
      rcases hcorner with hcorner | hcorner
      · simpa [hx, hcorner] using P.data.faceQ_xq face 0
      · simpa [hx, hcorner] using P.data.faceQ_xq face 1
    let radial : QStarEdge (transposePresentation P) q := ⟨x, hxq⟩
    let liftedQ : (rzReplacementPresentation P A S).Q :=
      Sum.inr ⟨q, (copy, Sum.inl (Sum.inr radial))⟩
    refine ⟨Vertex.q liftedQ, ?_⟩
    simp only [xStarBoundaryVertexMember, decide_eq_true_eq]
    simp only [xStarBoundaryVertexMember, decide_eq_true_eq] at hvalue
    obtain ⟨face, hface, hcorner⟩ := hvalue
    refine ⟨Sum.inr (Sum.inr (face, copy)), ?_, ?_⟩
    · have hx : P.faceX face = x := by
        simpa [xStarFaceMember] using hface
      simp only [xStarFaceMember, decide_eq_true_eq]
      change Sum.inr (P.faceX face, copy) =
        (Sum.inr (x, copy) : RZX P S)
      exact congrArg (fun oldX => Sum.inr (oldX, copy)) hx
    · rcases hcorner with hcorner | hcorner
      · left
        have hx : P.faceX face = x := by
          simpa [xStarFaceMember] using hface
        subst q
        subst x
        change liftedQ = oldXFaceQ P S 0 (face, copy)
        rfl
      · right
        have hx : P.faceX face = x := by
          simpa [xStarFaceMember] using hface
        subst q
        subst x
        change liftedQ = oldXFaceQ P S 1 (face, copy)
        rfl
  · have hxz : ∃ face : P.Face,
        xStarFaceMember P x face = true ∧ z = P.faceZ face := by
      simpa only [xStarBoundaryVertexMember, decide_eq_true_eq] using hvalue
    let oldXInZStar : XStarVertex (transposePresentation P) z :=
      ⟨Vertex.z x, by
        simp only [xStarVertexMember, decide_eq_true_eq]
        obtain ⟨face, hface, hz⟩ := hxz
        refine ⟨face, ?_, ?_⟩
        · simp only [xStarFaceMember, decide_eq_true_eq]
          exact hz.symm
        · have hx : P.faceX face = x := by
            simpa [xStarFaceMember] using hface
          exact hx.symm⟩
    let liftedZ : (rzReplacementPresentation P A S).Z :=
      ⟨z, (copy, Sum.inl oldXInZStar)⟩
    refine ⟨Vertex.z liftedZ, ?_⟩
    simp only [xStarBoundaryVertexMember, decide_eq_true_eq]
    obtain ⟨face, hface, hz⟩ := hxz
    refine ⟨Sum.inr (Sum.inr (face, copy)), ?_, ?_⟩
    · have hx : P.faceX face = x := by
        simpa [xStarFaceMember] using hface
      simp only [xStarFaceMember, decide_eq_true_eq]
      change Sum.inr (P.faceX face, copy) =
        (Sum.inr (x, copy) : RZX P S)
      exact congrArg (fun oldX => Sum.inr (oldX, copy)) hx
    · have hx : P.faceX face = x := by
        simpa [xStarFaceMember] using hface
      subst z
      subst x
      apply Sigma.ext rfl
      apply heq_of_eq
      apply Prod.ext
      · rfl
      · apply congrArg Sum.inl
        apply Subtype.ext
        rfl

private noncomputable def oldXBoundaryEdgeLift
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (x : P.X) (copy : Two) :
    XStarBoundaryEdge P x →
      XStarBoundaryEdge (rzReplacementPresentation P A S)
        (Sum.inr (x, copy)) := by
  classical
  intro edge
  rcases edge with ⟨raw, hraw⟩
  rcases raw with impossible | qz
  · simp [xStarBoundaryEdgeMember] at hraw
  · rcases qz with ⟨⟨q, z⟩, hqz⟩
    have hmember : ∃ face : P.Face,
        xStarFaceMember P x face = true ∧
          decide ((⟨(q, z), hqz⟩ : QZEdge P) = faceQZEdge P face 0 ∨
            (⟨(q, z), hqz⟩ : QZEdge P) = faceQZEdge P face 1) = true := by
      simp only [xStarBoundaryEdgeMember, decide_eq_true_eq] at hraw
      obtain ⟨face, hface, huse⟩ := hraw
      refine ⟨face, hface, ?_⟩
      change decide ((⟨(q, z), hqz⟩ : QZEdge P) =
        faceQZEdge P face 0 ∨
        (⟨(q, z), hqz⟩ : QZEdge P) = faceQZEdge P face 1) = true at huse
      exact huse
    have hxq : P.xq x q = true := by
      obtain ⟨face, hface, huse⟩ := hmember
      have hx : P.faceX face = x := by
        simpa [xStarFaceMember] using hface
      have hcorner : (⟨(q, z), hqz⟩ : QZEdge P) =
          faceQZEdge P face 0 ∨
          (⟨(q, z), hqz⟩ : QZEdge P) = faceQZEdge P face 1 := by
        exact of_decide_eq_true huse
      rcases hcorner with hcorner | hcorner
      · have hq := congrArg (fun value : QZEdge P => value.1.1) hcorner
        have hq' : q = P.faceQ face 0 := by
          simpa [faceQZEdge] using hq
        exact (congrArg₂ P.xq hx.symm hq').trans
          (P.data.faceQ_xq face 0)
      · have hq := congrArg (fun value : QZEdge P => value.1.1) hcorner
        have hq' : q = P.faceQ face 1 := by
          simpa [faceQZEdge] using hq
        exact (congrArg₂ P.xq hx.symm hq').trans
          (P.data.faceQ_xq face 1)
    let radial : QStarEdge (transposePresentation P) q := ⟨x, hxq⟩
    let liftedQ : (rzReplacementPresentation P A S).Q :=
      Sum.inr ⟨q, (copy, Sum.inl (Sum.inr radial))⟩
    let oldXInZStar : XStarVertex (transposePresentation P) z :=
      ⟨Vertex.z x, by
        simp only [xStarVertexMember, decide_eq_true_eq]
        obtain ⟨face, hface, huse⟩ := hmember
        have hcorner : (⟨(q, z), hqz⟩ : QZEdge P) =
            faceQZEdge P face 0 ∨
            (⟨(q, z), hqz⟩ : QZEdge P) = faceQZEdge P face 1 := by
          exact of_decide_eq_true huse
        have hz : P.faceZ face = z := by
          rcases hcorner with hcorner | hcorner
          · exact (congrArg (fun value : QZEdge P => value.1.2) hcorner).symm
          · exact (congrArg (fun value : QZEdge P => value.1.2) hcorner).symm
        refine ⟨face, ?_, ?_⟩
        · simp only [xStarFaceMember, decide_eq_true_eq]
          exact hz
        · have hx : P.faceX face = x := by
            simpa [xStarFaceMember] using hface
          exact hx.symm⟩
    let liftedZ : (rzReplacementPresentation P A S).Z :=
      ⟨z, (copy, Sum.inl oldXInZStar)⟩
    have hliftedQZ : (rzReplacementPresentation P A S).qz liftedQ liftedZ = true := by
      simp only [rzReplacementPresentation, rzReplacementData, rzQZIncidence]
      apply decide_eq_true
      refine ⟨hqz, ?_⟩
      obtain ⟨face, hface, huse⟩ := hmember
      have hcorner : (⟨(q, z), hqz⟩ : QZEdge P) =
          faceQZEdge P face 0 ∨
          (⟨(q, z), hqz⟩ : QZEdge P) = faceQZEdge P face 1 := by
        exact of_decide_eq_true huse
      have hx : P.faceX face = x := by
        simpa [xStarFaceMember] using hface
      rcases hcorner with hcorner | hcorner
      · have hq := congrArg (fun value : QZEdge P => value.1.1) hcorner
        have hz := congrArg (fun value : QZEdge P => value.1.2) hcorner
        have hq' : q = P.faceQ face 0 := by
          simpa [faceQZEdge] using hq
        have hz' : z = P.faceZ face := by
          simpa [faceQZEdge] using hz
        subst q
        subst z
        subst x
        exact oldXFaceQ_maps_to_faceZ P A S face copy 0
      · have hq := congrArg (fun value : QZEdge P => value.1.1) hcorner
        have hz := congrArg (fun value : QZEdge P => value.1.2) hcorner
        have hq' : q = P.faceQ face 1 := by
          simpa [faceQZEdge] using hq
        have hz' : z = P.faceZ face := by
          simpa [faceQZEdge] using hz
        subst q
        subst z
        subst x
        exact oldXFaceQ_maps_to_faceZ P A S face copy 1
    refine ⟨Sum.inr ⟨(liftedQ, liftedZ), hliftedQZ⟩, ?_⟩
    simp only [xStarBoundaryEdgeMember, decide_eq_true_eq]
    obtain ⟨face, hface, huse⟩ := hmember
    have hcorner : (⟨(q, z), hqz⟩ : QZEdge P) =
        faceQZEdge P face 0 ∨
        (⟨(q, z), hqz⟩ : QZEdge P) = faceQZEdge P face 1 := by
      exact of_decide_eq_true huse
    refine ⟨Sum.inr (Sum.inr (face, copy)), ?_, ?_⟩
    · have hx : P.faceX face = x := by
        simpa [xStarFaceMember] using hface
      simp only [xStarFaceMember, decide_eq_true_eq]
      change Sum.inr (P.faceX face, copy) =
        (Sum.inr (x, copy) : RZX P S)
      exact congrArg (fun oldX => Sum.inr (oldX, copy)) hx
    · change decide ((⟨(liftedQ, liftedZ), hliftedQZ⟩ :
          QZEdge (rzReplacementPresentation P A S)) =
            faceQZEdge (rzReplacementPresentation P A S)
              (Sum.inr (Sum.inr (face, copy))) 0 ∨
          (⟨(liftedQ, liftedZ), hliftedQZ⟩ :
            QZEdge (rzReplacementPresentation P A S)) =
              faceQZEdge (rzReplacementPresentation P A S)
                (Sum.inr (Sum.inr (face, copy))) 1) = true
      rw [decide_eq_true_eq]
      rcases hcorner with hcorner | hcorner
      · left
        apply Subtype.ext
        apply Prod.ext
        · change liftedQ = oldXFaceQ P S 0 (face, copy)
          have hq := congrArg (fun value : QZEdge P => value.1.1) hcorner
          have hx : P.faceX face = x := by
            simpa [xStarFaceMember] using hface
          have hq' : q = P.faceQ face 0 := by
            simpa [faceQZEdge] using hq
          subst q
          subst x
          rfl
        · change liftedZ = oldXFaceZ P S (face, copy)
          have hz := congrArg (fun value : QZEdge P => value.1.2) hcorner
          have hx : P.faceX face = x := by
            simpa [xStarFaceMember] using hface
          have hz' : z = P.faceZ face := by
            simpa [faceQZEdge] using hz
          subst z
          subst x
          apply Sigma.ext rfl
          apply heq_of_eq
          apply Prod.ext
          · rfl
          · apply congrArg Sum.inl
            apply Subtype.ext
            rfl

      · right
        apply Subtype.ext
        apply Prod.ext
        · change liftedQ = oldXFaceQ P S 1 (face, copy)
          have hq := congrArg (fun value : QZEdge P => value.1.1) hcorner
          have hx : P.faceX face = x := by
            simpa [xStarFaceMember] using hface
          have hq' : q = P.faceQ face 1 := by
            simpa [faceQZEdge] using hq
          subst q
          subst x
          rfl
        · change liftedZ = oldXFaceZ P S (face, copy)
          have hz := congrArg (fun value : QZEdge P => value.1.2) hcorner
          have hx : P.faceX face = x := by
            simpa [xStarFaceMember] using hface
          have hz' : z = P.faceZ face := by
            simpa [faceQZEdge] using hz
          subst z
          subst x
          apply Sigma.ext rfl
          apply heq_of_eq
          apply Prod.ext
          · rfl
          · apply congrArg Sum.inl
            apply Subtype.ext
            rfl

private theorem oldXBoundaryEdgeLift_start
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : XStarBoundaryEdge P x) :
    xBoundaryEdgeStart (rzReplacementPresentation P A S)
        (Sum.inr (x, copy)) (oldXBoundaryEdgeLift P A S x copy edge) =
      oldXBoundaryVertexLift P A S x copy (xBoundaryEdgeStart P x edge) := by
  rcases edge with ⟨raw, hraw⟩
  rcases raw with impossible | qz
  · simp [xStarBoundaryEdgeMember] at hraw
  · rcases qz with ⟨⟨q, z⟩, hqz⟩
    apply Subtype.ext
    rfl

private theorem oldXBoundaryEdgeLift_end
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : XStarBoundaryEdge P x) :
    xBoundaryEdgeEnd (rzReplacementPresentation P A S)
        (Sum.inr (x, copy)) (oldXBoundaryEdgeLift P A S x copy edge) =
      oldXBoundaryVertexLift P A S x copy (xBoundaryEdgeEnd P x edge) := by
  rcases edge with ⟨raw, hraw⟩
  rcases raw with impossible | qz
  · simp [xStarBoundaryEdgeMember] at hraw
  · rcases qz with ⟨⟨q, z⟩, hqz⟩
    apply Subtype.ext
    rfl

private noncomputable def oldXBoundaryPathLift
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (x : P.X) (copy : Two)
    (vertex : XStarBoundaryVertex P x) :
    UndirectedPath
      (xBoundaryEdgeStart (rzReplacementPresentation P A S)
        (Sum.inr (x, copy)))
      (xBoundaryEdgeEnd (rzReplacementPresentation P A S)
        (Sum.inr (x, copy)))
      (oldXBoundaryVertexLift P A S x copy (A.xBoundaryRoot x))
      (oldXBoundaryVertexLift P A S x copy vertex) :=
  UndirectedPath.map
    (oldXBoundaryVertexLift P A S x copy)
    (oldXBoundaryEdgeLift P A S x copy)
    (oldXBoundaryEdgeLift_start P A S x copy)
    (oldXBoundaryEdgeLift_end P A S x copy)
    (A.xBoundaryPath x vertex)

private noncomputable def oldXBoundaryVertexProject
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (x : P.X) (copy : Two)
    (vertex : XStarBoundaryVertex (rzReplacementPresentation P A S)
      (Sum.inr (x, copy))) : XStarBoundaryVertex P x := by
  rcases vertex with ⟨value, hvalue⟩
  rcases value with successorX | successorQ | successorZ
  · simp [xStarBoundaryVertexMember] at hvalue
  · rcases successorQ with localEdge | qVertex
    · have himpossible : False := by
        simp only [xStarBoundaryVertexMember, decide_eq_true_eq] at hvalue
        obtain ⟨face, hface, hcorner⟩ := hvalue
        rcases face with localFace | glueOrOld
        · have hx := (show
              (rzReplacementPresentation P A S).faceX (Sum.inl localFace) =
                Sum.inr (x, copy) by
            simpa [xStarFaceMember] using hface)
          change Sum.inl (Sum.inl ⟨localFace.1, localFace.2.1⟩) =
            (Sum.inr (x, copy) : RZX P S) at hx
          cases hx
        · rcases glueOrOld with glueFace | oldFace
          · have hx := (show
                (rzReplacementPresentation P A S).faceX
                    (Sum.inr (Sum.inl glueFace)) = Sum.inr (x, copy) by
              simpa [xStarFaceMember] using hface)
            change Sum.inl (Sum.inr ⟨glueFace.1.1.1, glueFace.2.1⟩) =
              (Sum.inr (x, copy) : RZX P S) at hx
            cases hx
          · rcases oldFace with ⟨face, faceCopy⟩
            rcases hcorner with hcorner | hcorner
            · change Sum.inl localEdge = oldXFaceQ P S 0 (face, faceCopy)
                at hcorner
              cases hcorner
            · change Sum.inl localEdge = oldXFaceQ P S 1 (face, faceCopy)
                at hcorner
              cases hcorner
      exact himpossible.elim
    · refine ⟨Vertex.q qVertex.1, ?_⟩
      simp only [xStarBoundaryVertexMember, decide_eq_true_eq]
      simp only [xStarBoundaryVertexMember, decide_eq_true_eq] at hvalue
      obtain ⟨face, hface, hcorner⟩ := hvalue
      rcases face with localFace | glueOrOld
      · have hx := (show
            (rzReplacementPresentation P A S).faceX (Sum.inl localFace) =
              Sum.inr (x, copy) by simpa [xStarFaceMember] using hface)
        change Sum.inl (Sum.inl ⟨localFace.1, localFace.2.1⟩) =
          (Sum.inr (x, copy) : RZX P S) at hx
        cases hx
      · rcases glueOrOld with glueFace | oldFace
        · have hx := (show
              (rzReplacementPresentation P A S).faceX
                  (Sum.inr (Sum.inl glueFace)) = Sum.inr (x, copy) by
            simpa [xStarFaceMember] using hface)
          change Sum.inl (Sum.inr ⟨glueFace.1.1.1, glueFace.2.1⟩) =
            (Sum.inr (x, copy) : RZX P S) at hx
          cases hx
        · rcases oldFace with ⟨face, faceCopy⟩
          have hxsum := (show
              (rzReplacementPresentation P A S).faceX
                  (Sum.inr (Sum.inr (face, faceCopy))) = Sum.inr (x, copy) by
            simpa [xStarFaceMember] using hface)
          change Sum.inr (P.faceX face, faceCopy) =
            (Sum.inr (x, copy) : RZX P S) at hxsum
          have hxcopy : (P.faceX face, faceCopy) = (x, copy) :=
            Sum.inr.inj hxsum
          have hx : P.faceX face = x := congrArg Prod.fst hxcopy
          refine ⟨face, by simpa [xStarFaceMember] using hx, ?_⟩
          rcases hcorner with hcorner | hcorner
          · left
            exact congrArg (fun value : (rzReplacementPresentation P A S).Q =>
              match value with
              | Sum.inl _ => qVertex.1
              | Sum.inr tagged => tagged.1) hcorner
          · right
            exact congrArg (fun value : (rzReplacementPresentation P A S).Q =>
              match value with
              | Sum.inl _ => qVertex.1
              | Sum.inr tagged => tagged.1) hcorner
  · refine ⟨Vertex.z successorZ.1, ?_⟩
    simp only [xStarBoundaryVertexMember, decide_eq_true_eq]
    simp only [xStarBoundaryVertexMember, decide_eq_true_eq] at hvalue
    obtain ⟨face, hface, hz⟩ := hvalue
    rcases face with localFace | glueOrOld
    · have hx := (show
          (rzReplacementPresentation P A S).faceX (Sum.inl localFace) =
            Sum.inr (x, copy) by simpa [xStarFaceMember] using hface)
      change Sum.inl (Sum.inl ⟨localFace.1, localFace.2.1⟩) =
        (Sum.inr (x, copy) : RZX P S) at hx
      cases hx
    · rcases glueOrOld with glueFace | oldFace
      · have hx := (show
            (rzReplacementPresentation P A S).faceX
                (Sum.inr (Sum.inl glueFace)) = Sum.inr (x, copy) by
          simpa [xStarFaceMember] using hface)
        change Sum.inl (Sum.inr ⟨glueFace.1.1.1, glueFace.2.1⟩) =
          (Sum.inr (x, copy) : RZX P S) at hx
        cases hx
      · rcases oldFace with ⟨face, faceCopy⟩
        have hxsum := (show
            (rzReplacementPresentation P A S).faceX
                (Sum.inr (Sum.inr (face, faceCopy))) = Sum.inr (x, copy) by
          simpa [xStarFaceMember] using hface)
        change Sum.inr (P.faceX face, faceCopy) =
          (Sum.inr (x, copy) : RZX P S) at hxsum
        have hxcopy : (P.faceX face, faceCopy) = (x, copy) :=
          Sum.inr.inj hxsum
        have hx : P.faceX face = x := congrArg Prod.fst hxcopy
        refine ⟨face, by simpa [xStarFaceMember] using hx, ?_⟩
        exact congrArg (fun value : (rzReplacementPresentation P A S).Z =>
          value.1) hz

private theorem oldXBoundaryVertexLift_project
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (x : P.X) (copy : Two)
    (vertex : XStarBoundaryVertex (rzReplacementPresentation P A S)
      (Sum.inr (x, copy))) :
    oldXBoundaryVertexLift P A S x copy
        (oldXBoundaryVertexProject P A S x copy vertex) = vertex := by
  rcases vertex with ⟨value, hvalue⟩
  rcases value with successorX | successorQ | successorZ
  · simp [xStarBoundaryVertexMember] at hvalue
  · rcases successorQ with localEdge | qVertex
    · have himpossible : False := by
        simp only [xStarBoundaryVertexMember, decide_eq_true_eq] at hvalue
        obtain ⟨face, hface, hcorner⟩ := hvalue
        rcases face with localFace | glueOrOld
        · have hx := (show
              (rzReplacementPresentation P A S).faceX (Sum.inl localFace) =
                Sum.inr (x, copy) by simpa [xStarFaceMember] using hface)
          change Sum.inl (Sum.inl ⟨localFace.1, localFace.2.1⟩) =
            (Sum.inr (x, copy) : RZX P S) at hx
          cases hx
        · rcases glueOrOld with glueFace | oldFace
          · have hx := (show
                (rzReplacementPresentation P A S).faceX
                    (Sum.inr (Sum.inl glueFace)) = Sum.inr (x, copy) by
              simpa [xStarFaceMember] using hface)
            change Sum.inl (Sum.inr ⟨glueFace.1.1.1, glueFace.2.1⟩) =
              (Sum.inr (x, copy) : RZX P S) at hx
            cases hx
          · rcases oldFace with ⟨face, faceCopy⟩
            rcases hcorner with hcorner | hcorner
            · change Sum.inl localEdge = oldXFaceQ P S 0 (face, faceCopy)
                at hcorner
              cases hcorner
            · change Sum.inl localEdge = oldXFaceQ P S 1 (face, faceCopy)
                at hcorner
              cases hcorner
      exact himpossible.elim
    · rcases qVertex with ⟨qVertex, qValue⟩
      apply Subtype.ext
      simp only [oldXBoundaryVertexProject, oldXBoundaryVertexLift]
      simp only [xStarBoundaryVertexMember, decide_eq_true_eq] at hvalue
      obtain ⟨face, hface, hcorner⟩ := hvalue
      rcases face with localFace | glueOrOld
      · have hx := (show
            (rzReplacementPresentation P A S).faceX (Sum.inl localFace) =
              Sum.inr (x, copy) by simpa [xStarFaceMember] using hface)
        change Sum.inl (Sum.inl ⟨localFace.1, localFace.2.1⟩) =
          (Sum.inr (x, copy) : RZX P S) at hx
        cases hx
      · rcases glueOrOld with glueFace | oldFace
        · have hx := (show
              (rzReplacementPresentation P A S).faceX
                  (Sum.inr (Sum.inl glueFace)) = Sum.inr (x, copy) by
            simpa [xStarFaceMember] using hface)
          change Sum.inl (Sum.inr ⟨glueFace.1.1.1, glueFace.2.1⟩) =
            (Sum.inr (x, copy) : RZX P S) at hx
          cases hx
        · rcases oldFace with ⟨face, faceCopy⟩
          have hxsum := (show
              (rzReplacementPresentation P A S).faceX
                  (Sum.inr (Sum.inr (face, faceCopy))) = Sum.inr (x, copy) by
            simpa [xStarFaceMember] using hface)
          change Sum.inr (P.faceX face, faceCopy) =
            (Sum.inr (x, copy) : RZX P S) at hxsum
          have hxcopy := Sum.inr.inj hxsum
          have hx : P.faceX face = x := congrArg Prod.fst hxcopy
          have hcopy : faceCopy = copy := congrArg Prod.snd hxcopy
          rcases hcorner with hcorner | hcorner
          · change Sum.inr ⟨qVertex, qValue⟩ =
                oldXFaceQ P S 0 (face, faceCopy)
              at hcorner
            subst faceCopy
            subst x
            have hq : qVertex = P.faceQ face 0 :=
              congrArg (fun value : (rzReplacementPresentation P A S).Q =>
                match value with
                | Sum.inl _ => qVertex
                | Sum.inr tagged => tagged.1) hcorner
            have hxq : (transposePresentation P).qz qVertex
                (P.faceX face) = true := by
              rw [hq]
              exact P.data.faceQ_xq face 0
            apply congrArg Vertex.q
            calc
              Sum.inr ⟨qVertex,
                  (copy, Sum.inl (Sum.inr ⟨P.faceX face, hxq⟩))⟩ =
                  oldXFaceQ P S 0 (face, copy) := by
                apply congrArg Sum.inr
                apply Sigma.ext hq
                subst qVertex
                rfl
              _ = Sum.inr ⟨qVertex, qValue⟩ := hcorner.symm
          · change Sum.inr ⟨qVertex, qValue⟩ =
                oldXFaceQ P S 1 (face, faceCopy)
              at hcorner
            subst faceCopy
            subst x
            have hq : qVertex = P.faceQ face 1 :=
              congrArg (fun value : (rzReplacementPresentation P A S).Q =>
                match value with
                | Sum.inl _ => qVertex
                | Sum.inr tagged => tagged.1) hcorner
            have hxq : (transposePresentation P).qz qVertex
                (P.faceX face) = true := by
              rw [hq]
              exact P.data.faceQ_xq face 1
            apply congrArg Vertex.q
            calc
              Sum.inr ⟨qVertex,
                  (copy, Sum.inl (Sum.inr ⟨P.faceX face, hxq⟩))⟩ =
                  oldXFaceQ P S 1 (face, copy) := by
                apply congrArg Sum.inr
                apply Sigma.ext hq
                subst qVertex
                rfl
              _ = Sum.inr ⟨qVertex, qValue⟩ := hcorner.symm
  · rcases successorZ with ⟨successorZ, zValue⟩
    apply Subtype.ext
    simp only [oldXBoundaryVertexProject, oldXBoundaryVertexLift]
    simp only [xStarBoundaryVertexMember, decide_eq_true_eq] at hvalue
    obtain ⟨face, hface, hz⟩ := hvalue
    rcases face with localFace | glueOrOld
    · have hx := (show
          (rzReplacementPresentation P A S).faceX (Sum.inl localFace) =
            Sum.inr (x, copy) by simpa [xStarFaceMember] using hface)
      change Sum.inl (Sum.inl ⟨localFace.1, localFace.2.1⟩) =
        (Sum.inr (x, copy) : RZX P S) at hx
      cases hx
    · rcases glueOrOld with glueFace | oldFace
      · have hx := (show
            (rzReplacementPresentation P A S).faceX
                (Sum.inr (Sum.inl glueFace)) = Sum.inr (x, copy) by
          simpa [xStarFaceMember] using hface)
        change Sum.inl (Sum.inr ⟨glueFace.1.1.1, glueFace.2.1⟩) =
          (Sum.inr (x, copy) : RZX P S) at hx
        cases hx
      · rcases oldFace with ⟨face, faceCopy⟩
        have hxsum := (show
            (rzReplacementPresentation P A S).faceX
                (Sum.inr (Sum.inr (face, faceCopy))) = Sum.inr (x, copy) by
          simpa [xStarFaceMember] using hface)
        change Sum.inr (P.faceX face, faceCopy) =
          (Sum.inr (x, copy) : RZX P S) at hxsum
        have hxcopy := Sum.inr.inj hxsum
        have hx : P.faceX face = x := congrArg Prod.fst hxcopy
        have hcopy : faceCopy = copy := congrArg Prod.snd hxcopy
        subst faceCopy
        subst x
        have hzTag : successorZ = P.faceZ face :=
          congrArg (fun value : (rzReplacementPresentation P A S).Z =>
            value.1) hz
        have hstar : xStarVertexMember (transposePresentation P) successorZ
            (Vertex.z (P.faceX face)) = true := by
          simp only [xStarVertexMember, decide_eq_true_eq]
          refine ⟨face, ?_, rfl⟩
          simp only [xStarFaceMember, decide_eq_true_eq]
          exact hzTag.symm
        apply congrArg Vertex.z
        calc
          ⟨successorZ,
              (copy, Sum.inl (⟨Vertex.z (P.faceX face), hstar⟩ :
                XStarVertex (transposePresentation P) successorZ))⟩ =
              oldXFaceZ P S (face, copy) := by
            apply Sigma.ext hzTag
            subst successorZ
            apply heq_of_eq
            apply Prod.ext
            · rfl
            · apply congrArg Sum.inl
              apply Subtype.ext
              rfl
          _ = ⟨successorZ, zValue⟩ := hz.symm

private noncomputable def oldXBoundaryPath
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (x : P.X) (copy : Two)
    (vertex : XStarBoundaryVertex (rzReplacementPresentation P A S)
      (Sum.inr (x, copy))) :
    UndirectedPath
      (xBoundaryEdgeStart (rzReplacementPresentation P A S)
        (Sum.inr (x, copy)))
      (xBoundaryEdgeEnd (rzReplacementPresentation P A S)
        (Sum.inr (x, copy)))
      (oldXBoundaryVertexLift P A S x copy (A.xBoundaryRoot x)) vertex := by
  let projected := oldXBoundaryVertexProject P A S x copy vertex
  let path := oldXBoundaryPathLift P A S x copy projected
  exact oldXBoundaryVertexLift_project P A S x copy vertex ▸ path

private noncomputable def rzReplacementHistoricalXBoundaryRoot
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale)
    (x : (rzReplacementPresentation P
      A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S).X) :
    XStarBoundaryVertex
      (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S) x := by
  let A := A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  rcases x with localOrGlue | oldX
  · exact rzReplacementXBoundaryRoot P A3 S (Sum.inl localOrGlue)
  · exact oldXBoundaryVertexLift P A S oldX.1 oldX.2
      (A.xBoundaryRoot oldX.1)

private noncomputable def rzReplacementHistoricalXBoundaryPath
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale)
    (x : (rzReplacementPresentation P
      A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S).X)
    (vertex : XStarBoundaryVertex (rzReplacementPresentation P
      A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S) x) :
    UndirectedPath
      (xBoundaryEdgeStart (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S) x)
      (xBoundaryEdgeEnd (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S) x)
      (rzReplacementHistoricalXBoundaryRoot P A3 S x) vertex := by
  let A := A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  rcases x with localOrGlue | oldX
  · rcases localOrGlue with localCell | qEdge
    · exact rzLocalCellBoundaryPath P A3 S localCell.1 localCell.2 vertex
    · exact rzGlueXBoundaryPath P A3 S qEdge vertex
  · exact oldXBoundaryPath P A S oldX.1 oldX.2 vertex

/-! ### Input V4 owner for the original-central Z sector -/

/-- A historical Z-boundary edge is definitionally in the X-Q summand.  This
constructor projection is total because the Q-Z summand cannot carry the
boundary membership proof. -/
private def rzInputZBoundaryXQEdge
    (P : TannerSquarePresentation) (z : P.Z)
    (edge : ZStarBoundaryEdge P z) : XQEdge P := by
  rcases edge with ⟨raw, member⟩
  rcases raw with xq | qz
  · exact xq
  · simp [zStarBoundaryEdgeMember] at member

/-- The raw X-Q edge retained above is still a member of the closed Z-star.
No face witness is selected here. -/
private theorem rzInputZBoundaryXQEdge_member
    (P : TannerSquarePresentation) (z : P.Z)
    (edge : ZStarBoundaryEdge P z) :
    zStarEdgeMember P z (Sum.inl (rzInputZBoundaryXQEdge P z edge)) = true := by
  rcases edge with ⟨raw, member⟩
  rcases raw with xq | qz
  · simp only [rzInputZBoundaryXQEdge, zStarBoundaryEdgeMember,
      zStarEdgeMember, decide_eq_true_eq] at member ⊢
    exact decide_eq_true member
  · simp [zStarBoundaryEdgeMember] at member

private theorem rzInputZBoundaryEdge_start_value
    (P : TannerSquarePresentation) (z : P.Z)
    (edge : ZStarBoundaryEdge P z) :
    (zBoundaryEdgeStart P z edge).1 =
      Vertex.x (rzInputZBoundaryXQEdge P z edge).1.1 := by
  rcases edge with ⟨raw, member⟩
  rcases raw with xq | qz
  · rfl
  · simp [zStarBoundaryEdgeMember] at member

private theorem rzInputZBoundaryEdge_end_value
    (P : TannerSquarePresentation) (z : P.Z)
    (edge : ZStarBoundaryEdge P z) :
    (zBoundaryEdgeEnd P z edge).1 =
      Vertex.q (rzInputZBoundaryXQEdge P z edge).1.2 := by
  rcases edge with ⟨raw, member⟩
  rcases raw with xq | qz
  · rfl
  · simp [zStarBoundaryEdgeMember] at member

/-- Consume exactly the new V4 Z-boundary face owner.  This is the only input
selector used by the RZ historical original-central sector. -/
private noncomputable def rzInputZBoundaryFaceOwner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (z : P.Z) (edge : ZStarBoundaryEdge P z) :
    {owner : ZStarFace P z × Two //
      zStarFaceXQEdge P z owner.1 owner.2 =
        ⟨Sum.inl (rzInputZBoundaryXQEdge P z edge),
          rzInputZBoundaryXQEdge_member P z edge⟩} :=
  A4.zBoundaryFaceOwner z (rzInputZBoundaryXQEdge P z edge)
    (rzInputZBoundaryXQEdge_member P z edge)

/-- The V4 owner equality retains the exact historical raw X-Q edge. -/
private theorem rzInputZBoundaryXQEdge_eq_ownerFaceEdge
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (z : P.Z) (edge : ZStarBoundaryEdge P z) :
    rzInputZBoundaryXQEdge P z edge =
      faceXQEdge P (rzInputZBoundaryFaceOwner P A4 z edge).1.1.1
        (rzInputZBoundaryFaceOwner P A4 z edge).1.2 := by
  have h := congrArg
    (fun owned : ZStarEdge P z => owned.1)
    (rzInputZBoundaryFaceOwner P A4 z edge).2
  change Sum.inl (faceXQEdge P
      (rzInputZBoundaryFaceOwner P A4 z edge).1.1.1
      (rzInputZBoundaryFaceOwner P A4 z edge).1.2) =
    Sum.inl (rzInputZBoundaryXQEdge P z edge) at h
  exact (Sum.inl.inj h).symm

private theorem rzInputZBoundaryOwner_faceX
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (z : P.Z) (edge : ZStarBoundaryEdge P z) :
    P.faceX (rzInputZBoundaryFaceOwner P A4 z edge).1.1.1 =
      (rzInputZBoundaryXQEdge P z edge).1.1 := by
  have h := congrArg (fun owned : XQEdge P => owned.1.1)
    (rzInputZBoundaryXQEdge_eq_ownerFaceEdge P A4 z edge)
  simpa [faceXQEdge] using h.symm

private theorem rzInputZBoundaryOwner_faceQ
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (z : P.Z) (edge : ZStarBoundaryEdge P z) :
    P.faceQ (rzInputZBoundaryFaceOwner P A4 z edge).1.1.1
        (rzInputZBoundaryFaceOwner P A4 z edge).1.2 =
      (rzInputZBoundaryXQEdge P z edge).1.2 := by
  have h := congrArg (fun owned : XQEdge P => owned.1.2)
    (rzInputZBoundaryXQEdge_eq_ownerFaceEdge P A4 z edge)
  simpa [faceXQEdge] using h.symm

/-- Cellular regularity makes the supplied V4 owner agree with every concrete
old face over the same X/Z pair.  Regularity supplies only this equality; the
Type-valued owner itself comes from V4. -/
private theorem rzInputZBoundaryOwnerFace_eq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (z : P.Z)
    (edge : ZStarBoundaryEdge P z) (face : ZStarFace P z)
    (hfaceX : P.faceX face.1 = (rzInputZBoundaryXQEdge P z edge).1.1) :
    (rzInputZBoundaryFaceOwner P A4 z edge).1.1.1 = face.1 := by
  apply R.faceXZ_injective
  apply Prod.ext
  · have hownerX :
        (rzInputZBoundaryXQEdge P z edge).1.1 =
          P.faceX (rzInputZBoundaryFaceOwner P A4 z edge).1.1.1 := by
      have h := congrArg (fun owned : XQEdge P => owned.1.1)
        (rzInputZBoundaryXQEdge_eq_ownerFaceEdge P A4 z edge)
      simpa [faceXQEdge] using h
    exact hownerX.symm.trans hfaceX.symm
  · have hownerZ :
        P.faceZ (rzInputZBoundaryFaceOwner P A4 z edge).1.1.1 = z := by
      simpa [zStarFaceMember] using
        (rzInputZBoundaryFaceOwner P A4 z edge).1.1.2
    have hfaceZ : P.faceZ face.1 = z := by
      simpa [zStarFaceMember] using face.2
    exact hownerZ.trans hfaceZ.symm

/-- The copy-tagged original central vertex of the transposed old Z-star. -/
private def rzOriginalCentralZVertex
    (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) (copy : Two) : RZZ P S :=
  ⟨z, (copy, Sum.inl ⟨Vertex.x z, by
    simp only [xStarVertexMember, decide_eq_true_eq]
    rfl⟩)⟩

/-- The first small square of a transposed old Z-star face at the original
central vertex in one cylinder copy. -/
private def rzOriginalCentralCell
    (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) (copy : Two)
    (face : XStarFace (transposePresentation P) z) :
    ZDoubleCylinderFace P z S :=
  Sum.inl (copy, (face, rzRadialGridZero S, rzRadialGridZero S))

/-- The materialized successor face at that original-central corner. -/
private def rzOriginalCentralFace
    (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) (copy : Two)
    (face : XStarFace (transposePresentation P) z) : RZFace P S :=
  Sum.inl ⟨z, rzOriginalCentralCell P S z copy face, (0, 0)⟩

@[simp] private theorem rzOriginalCentralFace_z
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (face : XStarFace (transposePresentation P) z) :
    rzFaceZ P A S (rzOriginalCentralFace P S z copy face) =
      rzOriginalCentralZVertex P S z copy := by
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    change (copy, subdivisionGridVertex (transposePresentation P) z S
      face 0 0) =
      (copy, Sum.inl ⟨Vertex.x z, by
        simp only [xStarVertexMember, decide_eq_true_eq]
        rfl⟩)
    apply Prod.ext
    · rfl
    · have hx : (transposePresentation P).faceX face.1 = z := by
        simpa [xStarFaceMember] using face.2
      simp [subdivisionGridVertex, xStarFaceXVertex, hx]

/-- A face-grid vertex equal to the original transposed X corner has zero
grid coordinates and retains that owner. -/
private theorem rzSubdivisionGridVertex_eq_originalX_coordinates
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z)
    (face : XStarFace (transposePresentation P) z)
    (a b : Fin (S.half + 1))
    (h : subdivisionGridVertex (transposePresentation P) z S face a b =
      Sum.inl ⟨Vertex.x z, by
        simp only [xStarVertexMember, decide_eq_true_eq]
        rfl⟩) :
    a.1 = 0 ∧ b.1 = 0 ∧
      (transposePresentation P).faceX face.1 = z := by
  simp only [subdivisionGridVertex] at h
  split at h <;> rename_i ha0
  · split at h <;> rename_i hb0
    · refine ⟨ha0, hb0, ?_⟩
      have raw := congrArg Subtype.val (Sum.inl.inj h)
      exact Vertex.x.inj raw
    · split at h <;> rename_i hblast
      · have raw := congrArg Subtype.val (Sum.inl.inj h)
        cases raw
      · cases h
  · split at h <;> rename_i halast
    · split at h <;> rename_i hb0
      · have raw := congrArg Subtype.val (Sum.inl.inj h)
        cases raw
      · split at h <;> rename_i hblast
        · have raw := congrArg Subtype.val (Sum.inl.inj h)
          cases raw
        · cases h
    · split at h <;> rename_i hb0
      · cases h
      · split at h <;> rename_i hblast <;> cases h

/-- An original Q boundary vertex occurs at exactly one of the two Q corners
of the stored transposed face grid. -/
private theorem rzSubdivisionGridVertex_eq_originalQ_coordinates
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z)
    (face : XStarFace (transposePresentation P) z)
    (a b : Fin (S.half + 1)) (q : P.Q)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true)
    (h : subdivisionGridVertex (transposePresentation P) z S face a b =
      Sum.inl ⟨Vertex.q q, member⟩) :
    ((transposePresentation P).faceQ face.1 0 = q ∧
        a.1 = S.half ∧ b.1 = 0) ∨
      ((transposePresentation P).faceQ face.1 1 = q ∧
        a.1 = 0 ∧ b.1 = S.half) := by
  simp only [subdivisionGridVertex] at h
  split at h <;> rename_i ha0
  · split at h <;> rename_i hb0
    · have raw := congrArg Subtype.val (Sum.inl.inj h)
      cases raw
    · split at h <;> rename_i hblast
      · right
        refine ⟨?_, ha0, hblast⟩
        exact Vertex.q.inj (congrArg Subtype.val (Sum.inl.inj h))
      · cases h
  · split at h <;> rename_i halast
    · split at h <;> rename_i hb0
      · left
        refine ⟨?_, halast, hb0⟩
        exact Vertex.q.inj (congrArg Subtype.val (Sum.inl.inj h))
      · split at h <;> rename_i hblast
        · have raw := congrArg Subtype.val (Sum.inl.inj h)
          cases raw
        · cases h
    · split at h <;> rename_i hb0
      · cases h
      · split at h <;> rename_i hblast <;> cases h

/-- The original Z boundary vertex of a transposed face is its unique outer
grid corner. -/
private theorem rzSubdivisionGridVertex_eq_originalZ_coordinates
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z)
    (face : XStarFace (transposePresentation P) z)
    (a b : Fin (S.half + 1)) (x : P.X)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.z x) = true)
    (h : subdivisionGridVertex (transposePresentation P) z S face a b =
      Sum.inl ⟨Vertex.z x, member⟩) :
    (transposePresentation P).faceZ face.1 = x ∧
      a.1 = S.half ∧ b.1 = S.half := by
  simp only [subdivisionGridVertex] at h
  split at h <;> rename_i ha0
  · split at h <;> rename_i hb0
    · have raw := congrArg Subtype.val (Sum.inl.inj h)
      cases raw
    · split at h <;> rename_i hblast
      · have raw := congrArg Subtype.val (Sum.inl.inj h)
        cases raw
      · cases h
  · split at h <;> rename_i halast
    · split at h <;> rename_i hb0
      · have raw := congrArg Subtype.val (Sum.inl.inj h)
        cases raw
      · split at h <;> rename_i hblast
        · refine ⟨?_, halast, hblast⟩
          exact Vertex.z.inj (congrArg Subtype.val (Sum.inl.inj h))
        · cases h
    · split at h <;> rename_i hb0
      · cases h
      · split at h <;> rename_i hblast <;> cases h

/-! ### Original boundary endpoints of a successor Z cylinder -/

/-- The copy-tagged original Q endpoint in a transposed old Z-star. -/
private def rzOriginalQZVertex
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z)
    (copy : Two) (q : P.Q)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true) : RZZ P S :=
  ⟨z, (copy, Sum.inl ⟨Vertex.q q, member⟩)⟩

/-- The same original Q endpoint, viewed on the historical input Z-boundary. -/
private def rzOriginalQHistoricalBoundaryVertex
    (P : TannerSquarePresentation) (z : P.Z) (q : P.Q)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true) : ZStarBoundaryVertex P z :=
  ⟨Vertex.q q, by
    simp only [xStarVertexMember, zStarBoundaryVertexMember,
      decide_eq_true_eq] at member ⊢
    obtain ⟨face, hface, hq⟩ := member
    refine ⟨face, ?_, hq⟩
    simp only [xStarFaceMember, decide_eq_true_eq] at hface
    simp only [zStarFaceMember, decide_eq_true_eq]
    exact hface⟩

/-- The input V2 edge/endpoint retained at an original Q endpoint. -/
private noncomputable def rzOriginalQIncident
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (z : P.Z) (q : P.Q)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true) :=
  (A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2).zBoundaryIncidentEdge z
    (rzOriginalQHistoricalBoundaryVertex P z q member)

/-- Oriented old Z-boundary edges end, rather than start, at a Q endpoint. -/
private theorem rzOriginalQIncident_bit
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (z : P.Z) (q : P.Q)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true) :
    (rzOriginalQIncident P A4 z q member).1.2 = 1 := by
  generalize hincident : rzOriginalQIncident P A4 z q member = incident
  rcases incident with ⟨⟨edge, endpoint⟩, hendpoint⟩
  exact rzTwoElim (motive := fun endpoint =>
      BDL26TannerLocalRegularity.edgeEndpoint
          (zBoundaryEdgeStart P z) (zBoundaryEdgeEnd P z) edge endpoint =
        rzOriginalQHistoricalBoundaryVertex P z q member → endpoint = 1)
    (fun h => by
      rw [BDL26TannerLocalRegularity.edgeEndpoint_zero] at h
      have hvalue := congrArg Subtype.val h
      rw [rzInputZBoundaryEdge_start_value] at hvalue
      cases hvalue)
    (fun _ => rfl) endpoint hendpoint

/-- The raw X-Q edge retained by V2 has the requested original Q endpoint. -/
private theorem rzOriginalQIncident_q
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (z : P.Z) (q : P.Q)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true) :
    (rzInputZBoundaryXQEdge P z
      (rzOriginalQIncident P A4 z q member).1.1).1.2 = q := by
  have hbit := rzOriginalQIncident_bit P A4 z q member
  have hendpoint := (rzOriginalQIncident P A4 z q member).2
  rw [hbit] at hendpoint
  rw [BDL26TannerLocalRegularity.edgeEndpoint_one] at hendpoint
  have hvalue := congrArg Subtype.val hendpoint
  rw [rzInputZBoundaryEdge_end_value] at hvalue
  exact Vertex.q.inj hvalue

/-- The original Q endpoint as an input boundary vertex of the transposed
Z-star. -/
private def rzOriginalQTransposedBoundaryVertex
    (P : TannerSquarePresentation) (z : P.Z) (q : P.Q)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true) :
    XStarBoundaryVertex (transposePresentation P) z :=
  ⟨Vertex.q q, by
    simpa [xStarBoundaryVertexMember, xStarVertexMember] using member⟩

private theorem rzOriginalQTransposedBoundaryVertex_map
    (P : TannerSquarePresentation) (z : P.Z) (q : P.Q)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true) :
    transposeXStarBoundaryVertexEquiv P z
        (rzOriginalQTransposedBoundaryVertex P z q member) =
      rzOriginalQHistoricalBoundaryVertex P z q member := by
  apply Subtype.ext
  rfl

/-- Transposition flips the historical endpoint-one tag to endpoint zero. -/
private theorem rzOriginalQTransposeIncident_bit
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (z : P.Z) (q : P.Q)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true) :
    ((transposeTannerSquareAdmissibleV2 P
      A4.toTannerSquareAdmissibleV2).xBoundaryIncidentEdge z
        (rzOriginalQTransposedBoundaryVertex P z q member)).1.2 = 0 := by
  generalize hincident :
    (transposeTannerSquareAdmissibleV2 P
      A4.toTannerSquareAdmissibleV2).xBoundaryIncidentEdge z
        (rzOriginalQTransposedBoundaryVertex P z q member) = incident
  rcases incident with ⟨⟨edge, endpoint⟩, hendpoint⟩
  change endpoint = 0
  exact rzTwoElim (motive := fun endpoint =>
      BDL26TannerLocalRegularity.edgeEndpoint
          (xBoundaryEdgeStart (transposePresentation P) z)
          (xBoundaryEdgeEnd (transposePresentation P) z) edge endpoint =
        rzOriginalQTransposedBoundaryVertex P z q member → endpoint = 0)
    (fun _ => rfl)
    (fun h => by
      rw [BDL26TannerLocalRegularity.edgeEndpoint_one] at h
      have hvalue := congrArg Subtype.val h
      rcases edge with ⟨raw, boundaryMember⟩
      rcases raw with xq | qz
      · simp [xStarBoundaryEdgeMember] at boundaryMember
      · change @Vertex.z (transposePresentation P) qz.1.2 =
          @Vertex.q (transposePresentation P) q at hvalue
        cases hvalue)
    endpoint hendpoint

/-- The Q-Z value carried by a transposed X-boundary edge. -/
private def rzTransposedXBoundaryQZEdge
    (P : TannerSquarePresentation) (z : P.Z)
    (edge : XStarBoundaryEdge (transposePresentation P) z) :
    QZEdge (transposePresentation P) := by
  rcases edge with ⟨raw, boundaryMember⟩
  rcases raw with xq | qz
  · simp [xStarBoundaryEdgeMember] at boundaryMember
  · exact qz

private theorem rzTransposedXBoundaryQZEdge_member
    (P : TannerSquarePresentation) (z : P.Z)
    (edge : XStarBoundaryEdge (transposePresentation P) z) :
    xStarEdgeMember (transposePresentation P) z
      (Sum.inr (rzTransposedXBoundaryQZEdge P z edge)) = true := by
  rcases edge with ⟨raw, boundaryMember⟩
  rcases raw with xq | qz
  · simp [xStarBoundaryEdgeMember] at boundaryMember
  · simp only [rzTransposedXBoundaryQZEdge, xStarBoundaryEdgeMember,
      xStarEdgeMember, decide_eq_true_eq] at boundaryMember ⊢
    exact decide_eq_true boundaryMember

private theorem rzTransposedXBoundaryEdgeToStar_eq
    (P : TannerSquarePresentation) (z : P.Z)
    (edge : XStarBoundaryEdge (transposePresentation P) z) :
    xStarBoundaryEdgeToStar (transposePresentation P) z edge =
      ⟨Sum.inr (rzTransposedXBoundaryQZEdge P z edge),
        rzTransposedXBoundaryQZEdge_member P z edge⟩ := by
  apply Subtype.ext
  rcases edge with ⟨raw, boundaryMember⟩
  rcases raw with xq | qz
  · simp [xStarBoundaryEdgeMember] at boundaryMember
  · rfl

/-- The transposed V4 boundary owner of the deterministic original-Q edge. -/
private noncomputable def rzOriginalQTransposedBoundaryOwner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (z : P.Z) (q : P.Q)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true) :=
  let edge := ((transposeTannerSquareAdmissibleV2 P
    A4.toTannerSquareAdmissibleV2).xBoundaryIncidentEdge z
      (rzOriginalQTransposedBoundaryVertex P z q member)).1.1
  (transposeTannerSquareAdmissibleV4 P A4).xBoundaryFaceOwner z
    (rzTransposedXBoundaryQZEdge P z edge)
    (rzTransposedXBoundaryQZEdge_member P z edge)

/-- The transposed V4 owner face at an original Q endpoint. -/
private noncomputable def rzOriginalQOwnerFace
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (z : P.Z) (q : P.Q)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true) : XStarFace (transposePresentation P) z :=
  (rzOriginalQTransposedBoundaryOwner P A4 z q member).1.1

private noncomputable def rzOriginalQOwnerCorner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (z : P.Z) (q : P.Q)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true) : Two :=
  (rzOriginalQTransposedBoundaryOwner P A4 z q member).1.2

/-- The transposed V2 edge is exactly the boundary edge of the V4 owner face. -/
private theorem rzOriginalQTransposeIncident_edge
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (z : P.Z) (q : P.Q)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true) :
    xStarBoundaryEdgeToStar (transposePresentation P) z
      ((transposeTannerSquareAdmissibleV2 P
        A4.toTannerSquareAdmissibleV2).xBoundaryIncidentEdge z
          (rzOriginalQTransposedBoundaryVertex P z q member)).1.1 =
      xStarFaceQZEdge (transposePresentation P) z
        (rzOriginalQOwnerFace P A4 z q member)
        (rzOriginalQOwnerCorner P A4 z q member) := by
  let edge := ((transposeTannerSquareAdmissibleV2 P
    A4.toTannerSquareAdmissibleV2).xBoundaryIncidentEdge z
      (rzOriginalQTransposedBoundaryVertex P z q member)).1.1
  have howner := (rzOriginalQTransposedBoundaryOwner
    P A4 z q member).2
  calc
    xStarBoundaryEdgeToStar (transposePresentation P) z edge =
        ⟨Sum.inr (rzTransposedXBoundaryQZEdge P z edge),
          rzTransposedXBoundaryQZEdge_member P z edge⟩ :=
      rzTransposedXBoundaryEdgeToStar_eq P z edge
    _ = xStarFaceQZEdge (transposePresentation P) z
        (rzOriginalQOwnerFace P A4 z q member)
        (rzOriginalQOwnerCorner P A4 z q member) := by
      simpa [edge, rzOriginalQOwnerFace, rzOriginalQOwnerCorner,
        rzOriginalQTransposedBoundaryOwner] using howner.symm

private theorem rzOriginalQTransposeIncident_bit_of_boundary
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (z : P.Z) (q : P.Q)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true)
    (boundaryMember : xStarBoundaryVertexMember
      (transposePresentation P) z (Vertex.q q) = true) :
    ((transposeTannerSquareAdmissibleV2 P
      A4.toTannerSquareAdmissibleV2).xBoundaryIncidentEdge z
        ⟨Vertex.q q, boundaryMember⟩).1.2 = 0 := by
  have hvertex : (⟨Vertex.q q, boundaryMember⟩ :
      XStarBoundaryVertex (transposePresentation P) z) =
      rzOriginalQTransposedBoundaryVertex P z q member := by
    apply Subtype.ext
    rfl
  rw [hvertex]
  exact rzOriginalQTransposeIncident_bit P A4 z q member

private theorem rzOriginalQTransposeIncident_edge_of_boundary
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (z : P.Z) (q : P.Q)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true)
    (boundaryMember : xStarBoundaryVertexMember
      (transposePresentation P) z (Vertex.q q) = true) :
    xStarBoundaryEdgeToStar (transposePresentation P) z
      ((transposeTannerSquareAdmissibleV2 P
        A4.toTannerSquareAdmissibleV2).xBoundaryIncidentEdge z
          ⟨Vertex.q q, boundaryMember⟩).1.1 =
      xStarFaceQZEdge (transposePresentation P) z
        (rzOriginalQOwnerFace P A4 z q member)
        (rzOriginalQOwnerCorner P A4 z q member) := by
  have hvertex : (⟨Vertex.q q, boundaryMember⟩ :
      XStarBoundaryVertex (transposePresentation P) z) =
      rzOriginalQTransposedBoundaryVertex P z q member := by
    apply Subtype.ext
    rfl
  rw [hvertex]
  exact rzOriginalQTransposeIncident_edge P A4 z q member

private theorem rzOriginalQTransposeIncident_bit_of_value
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (z : P.Z) (q : P.Q)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true)
    (vertex : XStarBoundaryVertex (transposePresentation P) z)
    (hvalue : vertex.1 = @Vertex.q (transposePresentation P) q) :
    ((transposeTannerSquareAdmissibleV2 P
      A4.toTannerSquareAdmissibleV2).xBoundaryIncidentEdge z vertex).1.2 = 0 := by
  have hvertex : vertex = rzOriginalQTransposedBoundaryVertex P z q member := by
    apply Subtype.ext
    exact hvalue
  rw [hvertex]
  exact rzOriginalQTransposeIncident_bit P A4 z q member

private theorem rzOriginalQTransposeIncident_edge_of_value
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (z : P.Z) (q : P.Q)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true)
    (vertex : XStarBoundaryVertex (transposePresentation P) z)
    (hvalue : vertex.1 = @Vertex.q (transposePresentation P) q) :
    xStarBoundaryEdgeToStar (transposePresentation P) z
      ((transposeTannerSquareAdmissibleV2 P
        A4.toTannerSquareAdmissibleV2).xBoundaryIncidentEdge z vertex).1.1 =
      xStarFaceQZEdge (transposePresentation P) z
        (rzOriginalQOwnerFace P A4 z q member)
        (rzOriginalQOwnerCorner P A4 z q member) := by
  have hvertex : vertex = rzOriginalQTransposedBoundaryVertex P z q member := by
    apply Subtype.ext
    exact hvalue
  rw [hvertex]
  exact rzOriginalQTransposeIncident_edge P A4 z q member

/-- The transposed original-Q boundary owner selects its first subdivision
segment at endpoint zero. -/
private theorem rzOriginalQSubdivisionBoundaryIncidentEdge_eq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (q : P.Q)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true) :
    (subdivisionBoundaryIncidentEdge (transposePresentation P)
      (transposeTannerSquareAdmissibleV2 P
        A4.toTannerSquareAdmissibleV2) z S
      (subdivisionOriginalBoundaryVertex (transposePresentation P) z S
        (rzOriginalQTransposedBoundaryVertex P z q member))).1 =
      (subdivisionOriginalBoundaryEdge (transposePresentation P) z S
        ((transposeTannerSquareAdmissibleV2 P
          A4.toTannerSquareAdmissibleV2).xBoundaryIncidentEdge z
            (rzOriginalQTransposedBoundaryVertex P z q member)).1.1
        (rzRadialGridZero S), 0) := by
  simpa [rzRadialGridZero] using
    subdivisionBoundaryIncidentEdge_original_zero
      (transposePresentation P)
      (transposeTannerSquareAdmissibleV2 P
        A4.toTannerSquareAdmissibleV2) z S
      (rzOriginalQTransposedBoundaryVertex P z q member)
      (rzOriginalQTransposeIncident_bit P A4 z q member)

/-- The lifted double-cylinder incident edge is the first segment of the
transposed V4 owner boundary edge in the selected copy. -/
private theorem rzOriginalQRootIncidentEdge_eq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two) (q : P.Q)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true) :
    (doubleCylinderVertexIncidentEdge (transposePresentation P)
      (transposeTannerSquareAdmissibleV3 P
        A4.toTannerSquareAdmissibleV3) z S
      (rzOriginalQZVertex P S z copy q member).2).1.1 =
      Sum.inl (copy, Sum.inl
        (xStarFaceQZEdge (transposePresentation P) z
          (rzOriginalQOwnerFace P A4 z q member)
          (rzOriginalQOwnerCorner P A4 z q member),
        rzRadialGridZero S)) := by
  simp only [doubleCylinderVertexIncidentEdge, subdivisionVertexIncidentEdge,
    rzOriginalQZVertex]
  change
    Sum.inl (copy, (subdivisionBoundaryIncidentEdge (transposePresentation P)
      (transposeTannerSquareAdmissibleV2 P
        A4.toTannerSquareAdmissibleV2) z S
      (subdivisionOriginalBoundaryVertex (transposePresentation P) z S
        (rzOriginalQTransposedBoundaryVertex P z q member))).1.1.1) = _
  rw [rzOriginalQSubdivisionBoundaryIncidentEdge_eq]
  change Sum.inl (copy, Sum.inl
    (xStarBoundaryEdgeToStar (transposePresentation P) z
      ((transposeTannerSquareAdmissibleV2 P
        A4.toTannerSquareAdmissibleV2).xBoundaryIncidentEdge z
          (rzOriginalQTransposedBoundaryVertex P z q member)).1.1,
      rzRadialGridZero S)) = _
  rw [rzOriginalQTransposeIncident_edge]

/-- The end-copy owner cell incident to the selected original Q corner. -/
private noncomputable def rzOriginalQOwnerCell
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two) (q : P.Q)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true) : ZDoubleCylinderFace P z S :=
  twoSelect
    (Sum.inl (copy, rzOriginalQOwnerFace P A4 z q member,
      lastHalfSegment S, rzRadialGridZero S))
    (Sum.inl (copy, rzOriginalQOwnerFace P A4 z q member,
      rzRadialGridZero S, lastHalfSegment S))
    (rzOriginalQOwnerCorner P A4 z q member)

private noncomputable def rzOriginalQOwnerBits
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (z : P.Z) (q : P.Q)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true) : Two × Two :=
  twoSelect (1, 0) (0, 1)
    (rzOriginalQOwnerCorner P A4 z q member)

private noncomputable def rzOriginalQBoundaryCorner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (z : P.Z) (q : P.Q)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true) : Two :=
  twoSelect 1 0 (rzOriginalQOwnerCorner P A4 z q member)

/-- The V4 owner cell materializes the requested original Q fixed-Z tag. -/
private theorem rzOriginalQOwnerFace_z
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two) (q : P.Q)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true) :
    localFaceZ P S ⟨z, rzOriginalQOwnerCell P A4 S z copy q member,
        rzOriginalQOwnerBits P A4 z q member⟩ =
      rzOriginalQZVertex P S z copy q member := by
  have hownerQ : (transposePresentation P).faceQ
      (rzOriginalQOwnerFace P A4 z q member).1
      (rzOriginalQOwnerCorner P A4 z q member) = q := by
    let incident := (transposeTannerSquareAdmissibleV2 P
      A4.toTannerSquareAdmissibleV2).xBoundaryIncidentEdge z
        (rzOriginalQTransposedBoundaryVertex P z q member)
    have hbit := rzOriginalQTransposeIncident_bit P A4 z q member
    have hendpoint := incident.2
    change incident.1.2 = 0 at hbit
    rw [hbit, BDL26TannerLocalRegularity.edgeEndpoint_zero] at hendpoint
    have hstart := congrArg
      (xStarBoundaryVertexToStar (transposePresentation P) z) hendpoint
    have hstart :=
      (xBoundaryEdgeStart_toStar (transposePresentation P) z incident.1.1).symm.trans
        hstart
    have hedge := rzOriginalQTransposeIncident_edge P A4 z q member
    change xStarBoundaryEdgeToStar (transposePresentation P) z
      incident.1.1 = _ at hedge
    rw [hedge] at hstart
    have hvalue := congrArg Subtype.val hstart
    exact Vertex.q.inj hvalue
  have hlast : (lastHalfSegment S).1 + 1 = S.half := by
    dsimp [lastHalfSegment]
    have := S.half_pos
    omega
  have hlast' : S.half - 1 + 1 = S.half := by
    have := S.half_pos
    omega
  rw [localFaceZ_eq_localCornerVertex]
  generalize hcorner : rzOriginalQOwnerCorner P A4 z q member = corner at hownerQ ⊢
  fin_cases corner
  · apply Sigma.ext
      (x := ⟨z, localCornerVertex P z S
        (rzOriginalQOwnerCell P A4 S z copy q member)
        (rzOriginalQOwnerBits P A4 z q member)⟩)
      (y := rzOriginalQZVertex P S z copy q member) (by
        simp [rzOriginalQZVertex])
    apply heq_of_eq
    simp [rzOriginalQOwnerCell, rzOriginalQOwnerBits, localFaceZ,
      localCornerVertex, gridEndpoint, twoSelect, subdivisionGridVertex,
      lastHalfSegment, rzRadialGridZero, lowerGridIndex, upperGridIndex,
      hlast, hlast', S.half_pos.ne', hcorner, hownerQ,
      xStarFaceQVertex, rzOriginalQZVertex]
    exact congrArg Vertex.q hownerQ
  · apply Sigma.ext
      (x := ⟨z, localCornerVertex P z S
        (rzOriginalQOwnerCell P A4 S z copy q member)
        (rzOriginalQOwnerBits P A4 z q member)⟩)
      (y := rzOriginalQZVertex P S z copy q member) (by
        simp [rzOriginalQZVertex])
    apply heq_of_eq
    simp [rzOriginalQOwnerCell, rzOriginalQOwnerBits, localFaceZ,
      localCornerVertex, gridEndpoint, twoSelect, subdivisionGridVertex,
      lastHalfSegment, rzRadialGridZero, lowerGridIndex, upperGridIndex,
      hlast, hlast', S.half_pos.ne', hcorner, hownerQ,
      xStarFaceQVertex, rzOriginalQZVertex]
    exact congrArg Vertex.q hownerQ

private noncomputable def rzOriginalQOwnerZStarFace
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two) (q : P.Q)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true) :
    ZStarFace (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
      (rzOriginalQZVertex P S z copy q member) :=
  ⟨Sum.inl ⟨z, rzOriginalQOwnerCell P A4 S z copy q member,
      rzOriginalQOwnerBits P A4 z q member⟩, by
    simp only [zStarFaceMember, decide_eq_true_eq]
    exact rzOriginalQOwnerFace_z P A4 S z copy q member⟩

/-- The deterministic root's selected local edge is the owner cell's
original-boundary edge. -/
private theorem rzOriginalQRootFaceQ_eq_ownerBoundaryQ
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two) (q : P.Q)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true) :
    (rzReplacementPresentation P A4.toTannerSquareAdmissible S).faceQ
        (rzReplacementZBoundaryRootFace P
          A4.toTannerSquareAdmissibleV3 S
          (rzOriginalQZVertex P S z copy q member)).1
        (rzReplacementZBoundaryRootCorner P
          A4.toTannerSquareAdmissibleV3 S
          (rzOriginalQZVertex P S z copy q member)) =
      (rzReplacementPresentation P A4.toTannerSquareAdmissible S).faceQ
        (rzOriginalQOwnerZStarFace P A4 S z copy q member).1
        (rzOriginalQBoundaryCorner P A4 z q member) := by
  refine (rzReplacementZBoundaryRootFaceQ_eq_incidentEdge P
    A4.toTannerSquareAdmissibleV3 S
    (rzOriginalQZVertex P S z copy q member)).trans ?_
  change Sum.inl (⟨z,
      (doubleCylinderVertexIncidentEdge (transposePresentation P)
        (transposeTannerSquareAdmissibleV3 P
          A4.toTannerSquareAdmissibleV3) z S
        (rzOriginalQZVertex P S z copy q member).2).1.1⟩ :
      Sigma fun oldZ : P.Z => ZDoubleCylinderEdge P oldZ S) = _
  rw [rzOriginalQRootIncidentEdge_eq]
  change Sum.inl (⟨z, Sum.inl (copy, Sum.inl
      (xStarFaceQZEdge (transposePresentation P) z
        (rzOriginalQOwnerFace P A4 z q member)
        (rzOriginalQOwnerCorner P A4 z q member),
      rzRadialGridZero S))⟩ :
      Sigma fun oldZ : P.Z => ZDoubleCylinderEdge P oldZ S) =
    twoSelect
      (localFaceQ0 P S ⟨z,
        rzOriginalQOwnerCell P A4 S z copy q member,
        rzOriginalQOwnerBits P A4 z q member⟩)
      (localFaceQ1 P S ⟨z,
        rzOriginalQOwnerCell P A4 S z copy q member,
        rzOriginalQOwnerBits P A4 z q member⟩)
      (rzOriginalQBoundaryCorner P A4 z q member)
  have hlast : (lastHalfSegment S).1 + 1 = S.half := by
    dsimp [lastHalfSegment]
    have := S.half_pos
    omega
  have hlast' : S.half - 1 + 1 = S.half := by
    have := S.half_pos
    omega
  generalize hcorner : rzOriginalQOwnerCorner P A4 z q member = corner
  fin_cases corner
  · simp [rzOriginalQOwnerZStarFace, rzOriginalQOwnerCell,
      rzOriginalQOwnerBits, rzOriginalQBoundaryCorner, hcorner,
      rzReplacementPresentation, rzReplacementData, rzFaceQ,
      localFaceQ1, lastHalfSegment, rzRadialGridZero,
      subdivisionOriginalBoundaryEdge, twoSelect, gridEndpoint,
      lowerGridIndex, upperGridIndex, subdivisionVerticalEdge,
      subdivisionHorizontalEdge, hlast, hlast', S.half_pos.ne']
  · simp [rzOriginalQOwnerZStarFace, rzOriginalQOwnerCell,
      rzOriginalQOwnerBits, rzOriginalQBoundaryCorner, hcorner,
      rzReplacementPresentation, rzReplacementData, rzFaceQ,
      localFaceQ0, lastHalfSegment, rzRadialGridZero,
      subdivisionOriginalBoundaryEdge, twoSelect, gridEndpoint,
      lowerGridIndex, upperGridIndex, subdivisionVerticalEdge,
      subdivisionHorizontalEdge, hlast, hlast', S.half_pos.ne']

/-! ### Original Z endpoints of a successor Z cylinder -/

private def rzOriginalZZVertex
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z)
    (copy : Two) (x : P.X)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.z x) = true) : RZZ P S :=
  ⟨z, (copy, Sum.inl ⟨Vertex.z x, member⟩)⟩

private def rzOriginalZHistoricalBoundaryVertex
    (P : TannerSquarePresentation) (z : P.Z) (x : P.X)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.z x) = true) : ZStarBoundaryVertex P z :=
  ⟨Vertex.x x, by
    simp only [xStarVertexMember, zStarBoundaryVertexMember,
      decide_eq_true_eq] at member ⊢
    obtain ⟨face, hface, hx⟩ := member
    refine ⟨face, ?_, hx⟩
    simp only [xStarFaceMember, decide_eq_true_eq] at hface
    simp only [zStarFaceMember, decide_eq_true_eq]
    exact hface⟩

private noncomputable def rzOriginalZIncident
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (z : P.Z) (x : P.X)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.z x) = true) :=
  A4.toTannerSquareAdmissibleV2.zBoundaryIncidentEdge z
    (rzOriginalZHistoricalBoundaryVertex P z x member)

private theorem rzOriginalZIncident_bit
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (z : P.Z) (x : P.X)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.z x) = true) :
    (rzOriginalZIncident P A4 z x member).1.2 = 0 := by
  generalize hincident : rzOriginalZIncident P A4 z x member = incident
  rcases incident with ⟨⟨edge, endpoint⟩, hendpoint⟩
  exact rzTwoElim (motive := fun endpoint =>
      BDL26TannerLocalRegularity.edgeEndpoint
          (zBoundaryEdgeStart P z) (zBoundaryEdgeEnd P z) edge endpoint =
        rzOriginalZHistoricalBoundaryVertex P z x member → endpoint = 0)
    (fun _ => rfl)
    (fun h => by
      rw [BDL26TannerLocalRegularity.edgeEndpoint_one] at h
      have hvalue := congrArg Subtype.val h
      rw [rzInputZBoundaryEdge_end_value] at hvalue
      cases hvalue)
    endpoint hendpoint

private theorem rzOriginalZIncident_x
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (z : P.Z) (x : P.X)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.z x) = true) :
    (rzInputZBoundaryXQEdge P z
      (rzOriginalZIncident P A4 z x member).1.1).1.1 = x := by
  have hbit := rzOriginalZIncident_bit P A4 z x member
  have hendpoint := (rzOriginalZIncident P A4 z x member).2
  rw [hbit, BDL26TannerLocalRegularity.edgeEndpoint_zero] at hendpoint
  have hvalue := congrArg Subtype.val hendpoint
  rw [rzInputZBoundaryEdge_start_value] at hvalue
  exact Vertex.x.inj hvalue

private def rzOriginalZTransposedBoundaryVertex
    (P : TannerSquarePresentation) (z : P.Z) (x : P.X)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.z x) = true) :
    XStarBoundaryVertex (transposePresentation P) z :=
  ⟨Vertex.z x, by
    simpa [xStarBoundaryVertexMember, xStarVertexMember] using member⟩

private theorem rzOriginalZTransposeIncident_bit
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (z : P.Z) (x : P.X)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.z x) = true) :
    ((transposeTannerSquareAdmissibleV2 P
      A4.toTannerSquareAdmissibleV2).xBoundaryIncidentEdge z
        (rzOriginalZTransposedBoundaryVertex P z x member)).1.2 = 1 := by
  generalize hincident :
    (transposeTannerSquareAdmissibleV2 P
      A4.toTannerSquareAdmissibleV2).xBoundaryIncidentEdge z
        (rzOriginalZTransposedBoundaryVertex P z x member) = incident
  rcases incident with ⟨⟨edge, endpoint⟩, hendpoint⟩
  exact rzTwoElim (motive := fun endpoint =>
      BDL26TannerLocalRegularity.edgeEndpoint
          (xBoundaryEdgeStart (transposePresentation P) z)
          (xBoundaryEdgeEnd (transposePresentation P) z) edge endpoint =
        rzOriginalZTransposedBoundaryVertex P z x member → endpoint = 1)
    (fun h => by
      rw [BDL26TannerLocalRegularity.edgeEndpoint_zero] at h
      have hvalue := congrArg Subtype.val h
      rcases edge with ⟨raw, boundaryMember⟩
      rcases raw with xq | qz
      · simp [xStarBoundaryEdgeMember] at boundaryMember
      · change @Vertex.q (transposePresentation P) qz.1.1 =
          @Vertex.z (transposePresentation P) x at hvalue
        cases hvalue)
    (fun _ => rfl) endpoint hendpoint

private noncomputable def rzOriginalZTransposedBoundaryOwner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (z : P.Z) (x : P.X)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.z x) = true) :=
  let edge := ((transposeTannerSquareAdmissibleV2 P
    A4.toTannerSquareAdmissibleV2).xBoundaryIncidentEdge z
      (rzOriginalZTransposedBoundaryVertex P z x member)).1.1
  (transposeTannerSquareAdmissibleV4 P A4).xBoundaryFaceOwner z
    (rzTransposedXBoundaryQZEdge P z edge)
    (rzTransposedXBoundaryQZEdge_member P z edge)

private noncomputable def rzOriginalZOwnerFace
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (z : P.Z) (x : P.X)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.z x) = true) : XStarFace (transposePresentation P) z :=
  (rzOriginalZTransposedBoundaryOwner P A4 z x member).1.1

private noncomputable def rzOriginalZOwnerCorner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (z : P.Z) (x : P.X)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.z x) = true) : Two :=
  (rzOriginalZTransposedBoundaryOwner P A4 z x member).1.2

private theorem rzOriginalZTransposeIncident_edge
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (z : P.Z) (x : P.X)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.z x) = true) :
    xStarBoundaryEdgeToStar (transposePresentation P) z
      ((transposeTannerSquareAdmissibleV2 P
        A4.toTannerSquareAdmissibleV2).xBoundaryIncidentEdge z
          (rzOriginalZTransposedBoundaryVertex P z x member)).1.1 =
      xStarFaceQZEdge (transposePresentation P) z
        (rzOriginalZOwnerFace P A4 z x member)
        (rzOriginalZOwnerCorner P A4 z x member) := by
  let edge := ((transposeTannerSquareAdmissibleV2 P
    A4.toTannerSquareAdmissibleV2).xBoundaryIncidentEdge z
      (rzOriginalZTransposedBoundaryVertex P z x member)).1.1
  have howner := (rzOriginalZTransposedBoundaryOwner P A4 z x member).2
  calc
    xStarBoundaryEdgeToStar (transposePresentation P) z edge =
        ⟨Sum.inr (rzTransposedXBoundaryQZEdge P z edge),
          rzTransposedXBoundaryQZEdge_member P z edge⟩ :=
      rzTransposedXBoundaryEdgeToStar_eq P z edge
    _ = xStarFaceQZEdge (transposePresentation P) z
        (rzOriginalZOwnerFace P A4 z x member)
        (rzOriginalZOwnerCorner P A4 z x member) := by
      simpa [edge, rzOriginalZOwnerFace, rzOriginalZOwnerCorner,
        rzOriginalZTransposedBoundaryOwner] using howner.symm

private theorem rzOriginalZSubdivisionBoundaryIncidentEdge_eq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (x : P.X)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.z x) = true) :
    (subdivisionBoundaryIncidentEdge (transposePresentation P)
      (transposeTannerSquareAdmissibleV2 P A4.toTannerSquareAdmissibleV2)
      z S (subdivisionOriginalBoundaryVertex (transposePresentation P) z S
        (rzOriginalZTransposedBoundaryVertex P z x member))).1 =
      (subdivisionOriginalBoundaryEdge (transposePresentation P) z S
        ((transposeTannerSquareAdmissibleV2 P
          A4.toTannerSquareAdmissibleV2).xBoundaryIncidentEdge z
            (rzOriginalZTransposedBoundaryVertex P z x member)).1.1
        (lastHalfSegment S), 1) := by
  simpa [lastHalfSegment] using
    subdivisionBoundaryIncidentEdge_original_one
      (transposePresentation P)
      (transposeTannerSquareAdmissibleV2 P A4.toTannerSquareAdmissibleV2)
      z S (rzOriginalZTransposedBoundaryVertex P z x member)
      (rzOriginalZTransposeIncident_bit P A4 z x member)

private theorem rzOriginalZRootIncidentEdge_eq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two) (x : P.X)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.z x) = true) :
    (doubleCylinderVertexIncidentEdge (transposePresentation P)
      (transposeTannerSquareAdmissibleV3 P A4.toTannerSquareAdmissibleV3)
      z S (rzOriginalZZVertex P S z copy x member).2).1.1 =
      Sum.inl (copy, Sum.inl
        (xStarFaceQZEdge (transposePresentation P) z
          (rzOriginalZOwnerFace P A4 z x member)
          (rzOriginalZOwnerCorner P A4 z x member), lastHalfSegment S)) := by
  simp only [doubleCylinderVertexIncidentEdge, subdivisionVertexIncidentEdge,
    rzOriginalZZVertex]
  change Sum.inl (copy, (subdivisionBoundaryIncidentEdge
    (transposePresentation P) (transposeTannerSquareAdmissibleV2 P
      A4.toTannerSquareAdmissibleV2) z S
    (subdivisionOriginalBoundaryVertex (transposePresentation P) z S
      (rzOriginalZTransposedBoundaryVertex P z x member))).1.1.1) = _
  rw [rzOriginalZSubdivisionBoundaryIncidentEdge_eq]
  change Sum.inl (copy, Sum.inl
    (xStarBoundaryEdgeToStar (transposePresentation P) z
      ((transposeTannerSquareAdmissibleV2 P
        A4.toTannerSquareAdmissibleV2).xBoundaryIncidentEdge z
          (rzOriginalZTransposedBoundaryVertex P z x member)).1.1,
      lastHalfSegment S)) = _
  rw [rzOriginalZTransposeIncident_edge]

private noncomputable def rzOriginalZOwnerCell
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two) (x : P.X)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.z x) = true) : ZDoubleCylinderFace P z S :=
  Sum.inl (copy, rzOriginalZOwnerFace P A4 z x member,
    lastHalfSegment S, lastHalfSegment S)

private theorem rzOriginalZOwnerFace_z
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two) (x : P.X)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.z x) = true) :
    localFaceZ P S ⟨z, rzOriginalZOwnerCell P A4 S z copy x member,
      (1, 1)⟩ = rzOriginalZZVertex P S z copy x member := by
  have hownerZ : (transposePresentation P).faceZ
      (rzOriginalZOwnerFace P A4 z x member).1 = x := by
    let incident := (transposeTannerSquareAdmissibleV2 P
      A4.toTannerSquareAdmissibleV2).xBoundaryIncidentEdge z
        (rzOriginalZTransposedBoundaryVertex P z x member)
    have hbit := rzOriginalZTransposeIncident_bit P A4 z x member
    have hendpoint := incident.2
    change incident.1.2 = 1 at hbit
    rw [hbit, BDL26TannerLocalRegularity.edgeEndpoint_one] at hendpoint
    have hend := congrArg
      (xStarBoundaryVertexToStar (transposePresentation P) z) hendpoint
    have hend :=
      (xBoundaryEdgeEnd_toStar (transposePresentation P) z incident.1.1).symm.trans
        hend
    have hedge := rzOriginalZTransposeIncident_edge P A4 z x member
    change xStarBoundaryEdgeToStar (transposePresentation P) z
      incident.1.1 = _ at hedge
    rw [hedge] at hend
    exact Vertex.z.inj (congrArg Subtype.val hend)
  have hlast : S.half - 1 + 1 = S.half := by
    have := S.half_pos
    omega
  rw [localFaceZ_eq_localCornerVertex]
  apply Sigma.ext
    (x := ⟨z, localCornerVertex P z S
      (rzOriginalZOwnerCell P A4 S z copy x member) (1, 1)⟩)
    (y := rzOriginalZZVertex P S z copy x member) rfl
  apply heq_of_eq
  simp [rzOriginalZOwnerCell, localCornerVertex, gridEndpoint, twoSelect,
    lowerGridIndex, upperGridIndex, subdivisionGridVertex,
    lastHalfSegment, rzRadialGridZero, xStarFaceZVertex,
    rzOriginalZZVertex, hownerZ, hlast, S.half_pos.ne']

private noncomputable def rzOriginalZOwnerZStarFace
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two) (x : P.X)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.z x) = true) :
    ZStarFace (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
      (rzOriginalZZVertex P S z copy x member) :=
  ⟨Sum.inl ⟨z, rzOriginalZOwnerCell P A4 S z copy x member, (1, 1)⟩,
    by
      simp only [zStarFaceMember, decide_eq_true_eq]
      exact rzOriginalZOwnerFace_z P A4 S z copy x member⟩

/-- Every successor face incident to an original-central Z coordinate is the
zeroth small cell of a retained transposed old Z-star face. -/
private theorem rzOriginalCentralFace_cases
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (candidate : RZFace P S)
    (hz : rzFaceZ P A S candidate =
      rzOriginalCentralZVertex P S z copy) :
    ∃ face : XStarFace (transposePresentation P) z,
      candidate = rzOriginalCentralFace P S z copy face := by
  classical
  rcases candidate with candidateLocal | glue | old
  · rcases candidateLocal with ⟨oldZ, localCell, material⟩
    rcases localCell with copyFace | rectangle
    · rcases copyFace with ⟨candidateCopy, small⟩
      rcases small with ⟨candidateFace, column, row⟩
      rcases material with ⟨first, second⟩
      have howner : oldZ = z := congrArg Sigma.fst hz
      subst oldZ
      have hvertex :
          (candidateCopy,
            subdivisionGridVertex (transposePresentation P) z S candidateFace
              (gridEndpoint column first) (gridEndpoint row second)) =
            (copy, Sum.inl ⟨Vertex.x z, by
              simp only [xStarVertexMember, decide_eq_true_eq]
              rfl⟩) :=
        eq_of_heq (Sigma.mk.inj_iff.mp hz).2
      have hcopy : candidateCopy = copy := congrArg Prod.fst hvertex
      subst candidateCopy
      have hgrid := congrArg Prod.snd hvertex
      have coordinates := rzSubdivisionGridVertex_eq_originalX_coordinates
        P S z candidateFace (gridEndpoint column first)
          (gridEndpoint row second) hgrid
      fin_cases first <;> fin_cases second
      · have hcolumn : column = rzRadialGridZero S := by
          apply Fin.ext
          simpa [gridEndpoint, twoSelect, lowerGridIndex, rzRadialGridZero] using
            coordinates.1
        have hrow : row = rzRadialGridZero S := by
          apply Fin.ext
          simpa [gridEndpoint, twoSelect, lowerGridIndex, rzRadialGridZero] using
            coordinates.2.1
        let face : XStarFace (transposePresentation P) z :=
          ⟨candidateFace, candidateFace.2⟩
        refine ⟨face, ?_⟩
        rw [hcolumn, hrow]
        rfl
      · have := coordinates.2.1
        simp [gridEndpoint, twoSelect, upperGridIndex] at this
      · have := coordinates.1
        simp [gridEndpoint, twoSelect, upperGridIndex] at this
      · have := coordinates.1
        simp [gridEndpoint, twoSelect, upperGridIndex] at this
    · rcases material with ⟨materialCopy, endpoint⟩
      have howner : oldZ = z := congrArg Sigma.fst hz
      subst oldZ
      have hvertex : (materialCopy,
          (edgeEndpoint
            (subdivisionBoundaryEdgeStart (transposePresentation P) z S)
            (subdivisionBoundaryEdgeEnd (transposePresentation P) z S)
            rectangle endpoint).1) =
          (copy, Sum.inl ⟨Vertex.x z, by
            simp only [xStarVertexMember, decide_eq_true_eq]
            rfl⟩) :=
        eq_of_heq (Sigma.mk.inj_iff.mp hz).2
      have hsubdivision := congrArg Prod.snd hvertex
      fin_cases endpoint
      · have hmember :=
          (subdivisionBoundaryEdgeStart
            (transposePresentation P) z S rectangle).2
        have hmember := (congrArg
          (subdivisionBoundaryVertexMember (transposePresentation P) z S)
          (subdivisionBoundaryEdgeStart_value (transposePresentation P) z S
            rectangle)).symm.trans hmember
        have himpossible : subdivisionEdgeStart (transposePresentation P) z S
            rectangle.1 = Sum.inl ⟨Vertex.x z, by
              simp only [xStarVertexMember, decide_eq_true_eq]
              rfl⟩ := by
          simp only [edgeEndpoint, twoSelect] at hsubdivision
          exact (subdivisionBoundaryEdgeStart_value
            (transposePresentation P) z S rectangle).symm.trans hsubdivision
        rw [himpossible] at hmember
        simp [subdivisionBoundaryVertexMember, xStarBoundaryVertexMember]
          at hmember
      · have hmember :=
          (subdivisionBoundaryEdgeEnd
            (transposePresentation P) z S rectangle).2
        have hmember := (congrArg
          (subdivisionBoundaryVertexMember (transposePresentation P) z S)
          (subdivisionBoundaryEdgeEnd_value (transposePresentation P) z S
            rectangle)).symm.trans hmember
        have himpossible : subdivisionEdgeEnd (transposePresentation P) z S
            rectangle.1 = Sum.inl ⟨Vertex.x z, by
              simp only [xStarVertexMember, decide_eq_true_eq]
              rfl⟩ := by
          simp only [edgeEndpoint, twoSelect] at hsubdivision
          exact (subdivisionBoundaryEdgeEnd_value
            (transposePresentation P) z S rectangle).symm.trans hsubdivision
        rw [himpossible] at hmember
        simp [subdivisionBoundaryVertexMember, xStarBoundaryVertexMember]
          at hmember
  · rcases glue with ⟨a, edge, endpoint⟩
    have howner : a.1.2 = z := congrArg Sigma.fst hz
    subst z
    have hvertex : qToZDoubleCylinderVertex P A a.1.1 a.1.2 a.2 S
        (edgeEndpoint
          (qDoubleCylinderEdgeStart (transposePresentation P) a.1.1 S)
          (qDoubleCylinderEdgeEnd (transposePresentation P) a.1.1 S)
          edge endpoint) =
        (copy, Sum.inl ⟨Vertex.x a.1.2, by
          simp only [xStarVertexMember, decide_eq_true_eq]
          rfl⟩) :=
      eq_of_heq (Sigma.mk.inj_iff.mp hz).2
    generalize hselected : edgeEndpoint
      (qDoubleCylinderEdgeStart (transposePresentation P) a.1.1 S)
      (qDoubleCylinderEdgeEnd (transposePresentation P) a.1.1 S)
      edge endpoint = selected at hvertex
    rcases selected with ⟨selectedCopy, selected⟩
    rcases selected with original | interior
    · rcases original with center | oldX
      · have hstar := Sum.inl.inj (congrArg Prod.snd hvertex)
        have hraw := congrArg Subtype.val hstar
        change (@Vertex.q (transposePresentation P) a.1.1) =
          @Vertex.x (transposePresentation P) a.1.2 at hraw
        cases hraw
      · have hstar := Sum.inl.inj (congrArg Prod.snd hvertex)
        have hraw := congrArg Subtype.val hstar
        change (@Vertex.z (transposePresentation P) oldX.1) =
          @Vertex.x (transposePresentation P) a.1.2 at hraw
        cases hraw
    · have hsum := congrArg Prod.snd hvertex
      cases hsum
  · rcases old with ⟨oldFace, oldCopy⟩
    have howner : P.faceZ oldFace = z := congrArg Sigma.fst hz
    subst z
    have hvertex :
        (oldCopy, Sum.inl (xStarFaceZVertex (transposePresentation P)
          (P.faceZ oldFace) (oldFaceInZStar P oldFace))) =
        (copy, Sum.inl ⟨Vertex.x (P.faceZ oldFace), by
          simp only [xStarVertexMember, decide_eq_true_eq]
          rfl⟩) :=
      eq_of_heq (Sigma.mk.inj_iff.mp hz).2
    have hstar := Sum.inl.inj (congrArg Prod.snd hvertex)
    have raw := congrArg Subtype.val hstar
    cases raw

/-- Package the concrete original-central small cell as a face in the fixed
successor Z star. -/
private noncomputable def rzOriginalCentralZStarFace
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (face : XStarFace (transposePresentation P) z) :
    ZStarFace (rzReplacementPresentation P A S)
      (rzOriginalCentralZVertex P S z copy) :=
  ⟨rzOriginalCentralFace P S z copy face, by
    simp only [zStarFaceMember, decide_eq_true_eq]
    exact rzOriginalCentralFace_z P A S z copy face⟩

/-- The end-copy small square at the original central Z corner selected by
the V4 owner face. -/
private noncomputable def rzOriginalCentralOwnerCell
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (edge : ZStarBoundaryEdge P z) : ZDoubleCylinderFace P z S :=
  Sum.inl (copy,
    ((transposeXStarFaceEquiv P z).symm
      (rzInputZBoundaryFaceOwner P A4 z edge).1.1,
      rzRadialGridZero S, rzRadialGridZero S))

/-- The owner-selected local face at the original central Z vertex. -/
private noncomputable def rzOriginalCentralOwnerLocalZStarFace
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (edge : ZStarBoundaryEdge P z) :
    ZStarFace (rzReplacementPresentation P
      A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
      (rzOriginalCentralZVertex P S z copy) := by
  let A := A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  let cell := rzOriginalCentralOwnerCell P A4 S z copy edge
  let face : (rzReplacementPresentation P A S).Face :=
    Sum.inl ⟨z, cell, (0, 0)⟩
  refine ⟨face, ?_⟩
  simp only [zStarFaceMember, decide_eq_true_eq]
  change localFaceZ P S ⟨z, cell, (0, 0)⟩ = _
  simp [cell, rzOriginalCentralOwnerCell, localFaceZ, gridEndpoint,
    twoSelect, lowerGridIndex, subdivisionGridVertex, rzRadialGridZero,
    rzOriginalCentralZVertex, xStarFaceXVertex]
  apply congrArg Vertex.x
  simpa only [xStarFaceMember, decide_eq_true_eq] using
    ((transposeXStarFaceEquiv P z).symm
      (rzInputZBoundaryFaceOwner P A4 z edge).1.1).2

/-- The owner-selected end-copy cell gives the canonical one-edge historical
X-to-Q route for the old Z-boundary edge.  The face-local detour is explicit:
from the local X corner to corner zero, then within the same face to the
owner's ordered corner. -/
private noncomputable def rzOriginalCentralBoundaryEdgePath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (edge : ZStarBoundaryEdge P z) :
    UndirectedPath
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        (rzOriginalCentralZVertex P S z copy))
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        (rzOriginalCentralZVertex P S z copy))
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        (rzOriginalCentralZVertex P S z copy)
        (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
          A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
          (rzOriginalCentralZVertex P S z copy)
          (rzOriginalCentralOwnerLocalZStarFace P A4 S z copy edge) 0))
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        (rzOriginalCentralZVertex P S z copy)
        (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
          A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
          (rzOriginalCentralZVertex P S z copy)
          (rzOriginalCentralOwnerLocalZStarFace P A4 S z copy edge)
          (rzInputZBoundaryFaceOwner P A4 z edge).1.2)) :=
  (rzZStarFaceBoundaryPathToX
      (rzReplacementPresentation P
        A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
      (rzOriginalCentralZVertex P S z copy)
      (rzOriginalCentralOwnerLocalZStarFace P A4 S z copy edge)).reverse.append
    (rzZStarFaceBoundaryPathToQ
      (rzReplacementPresentation P
        A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
      (rzOriginalCentralZVertex P S z copy)
      (rzOriginalCentralOwnerLocalZStarFace P A4 S z copy edge)
      (rzInputZBoundaryFaceOwner P A4 z edge).1.2)

/-- Canonical successor boundary vertex attached to one oriented endpoint of
an old Z-boundary edge.  Endpoint zero is the owner-cell X tag; endpoint one
is the owner's matching radial local-Q tag. -/
private noncomputable def rzOriginalCentralBoundaryEdgeVertex
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (edge : ZStarBoundaryEdge P z) (endpoint : Two) :
    ZStarBoundaryVertex (rzReplacementPresentation P
      A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
      (rzOriginalCentralZVertex P S z copy) :=
  rzTwoElim (motive := fun _ =>
      ZStarBoundaryVertex (rzReplacementPresentation P
        A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        (rzOriginalCentralZVertex P S z copy))
    (zBoundaryEdgeStart (rzReplacementPresentation P
        A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
      (rzOriginalCentralZVertex P S z copy)
      (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
          A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        (rzOriginalCentralZVertex P S z copy)
        (rzOriginalCentralOwnerLocalZStarFace P A4 S z copy edge) 0))
    (zBoundaryEdgeEnd (rzReplacementPresentation P
        A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
      (rzOriginalCentralZVertex P S z copy)
      (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
          A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        (rzOriginalCentralZVertex P S z copy)
        (rzOriginalCentralOwnerLocalZStarFace P A4 S z copy edge)
        (rzInputZBoundaryFaceOwner P A4 z edge).1.2)) endpoint

/-- The canonical local-face path, truncated at either oriented input
endpoint. -/
private noncomputable def rzOriginalCentralBoundaryEdgePathToEndpoint
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (edge : ZStarBoundaryEdge P z) (endpoint : Two) :
    UndirectedPath
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        (rzOriginalCentralZVertex P S z copy))
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        (rzOriginalCentralZVertex P S z copy))
      (rzOriginalCentralBoundaryEdgeVertex P A4 S z copy edge 0)
      (rzOriginalCentralBoundaryEdgeVertex P A4 S z copy edge endpoint) :=
  rzTwoElim (motive := fun endpoint =>
      UndirectedPath
        (zBoundaryEdgeStart (rzReplacementPresentation P
          A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
          (rzOriginalCentralZVertex P S z copy))
        (zBoundaryEdgeEnd (rzReplacementPresentation P
          A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
          (rzOriginalCentralZVertex P S z copy))
        (rzOriginalCentralBoundaryEdgeVertex P A4 S z copy edge 0)
        (rzOriginalCentralBoundaryEdgeVertex P A4 S z copy edge endpoint))
    .nil (rzOriginalCentralBoundaryEdgePath P A4 S z copy edge) endpoint

/-- Lift an old Z-boundary vertex through its V2-owned incident edge and the
V4-owned face of that edge.  Independence from the selected incident edge is
proved separately using cellular regularity. -/
private noncomputable def rzOriginalCentralBoundaryVertexLift
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (vertex : ZStarBoundaryVertex P z) :
    ZStarBoundaryVertex (rzReplacementPresentation P
      A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
      (rzOriginalCentralZVertex P S z copy) := by
  let owned := A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2
    |>.zBoundaryIncidentEdge z vertex
  exact rzOriginalCentralBoundaryEdgeVertex P A4 S z copy owned.1.1 owned.1.2

/-- At the original central Z corner, two V4 owner corners with the same old Q
endpoint determine the same transposed radial star edge. -/
private theorem rzOriginalCentralOwnerRadialEdge_eq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (z : P.Z) (first second : ZStarBoundaryEdge P z)
    (hq : (rzInputZBoundaryXQEdge P z first).1.2 =
      (rzInputZBoundaryXQEdge P z second).1.2) :
    xStarFaceXQEdge (transposePresentation P) z
        ((transposeXStarFaceEquiv P z).symm
          (rzInputZBoundaryFaceOwner P A4 z first).1.1)
        (rzInputZBoundaryFaceOwner P A4 z first).1.2 =
      xStarFaceXQEdge (transposePresentation P) z
        ((transposeXStarFaceEquiv P z).symm
          (rzInputZBoundaryFaceOwner P A4 z second).1.1)
        (rzInputZBoundaryFaceOwner P A4 z second).1.2 := by
  apply Subtype.ext
  apply congrArg Sum.inl
  apply Subtype.ext
  apply Prod.ext
  · have hfirst : (transposePresentation P).faceX
        ((transposeXStarFaceEquiv P z).symm
          (rzInputZBoundaryFaceOwner P A4 z first).1.1).1 = z := by
      simpa [xStarFaceMember] using
        ((transposeXStarFaceEquiv P z).symm
          (rzInputZBoundaryFaceOwner P A4 z first).1.1).2
    have hsecond : (transposePresentation P).faceX
        ((transposeXStarFaceEquiv P z).symm
          (rzInputZBoundaryFaceOwner P A4 z second).1.1).1 = z := by
      simpa [xStarFaceMember] using
        ((transposeXStarFaceEquiv P z).symm
          (rzInputZBoundaryFaceOwner P A4 z second).1.1).2
    exact hfirst.trans hsecond.symm
  · exact (rzInputZBoundaryOwner_faceQ P A4 z first).trans
      (hq.trans (rzInputZBoundaryOwner_faceQ P A4 z second).symm)

/-! ### Fixed-Z face-interior link -/

/-- Embed a face-interior vertex index into the adjacent lower small-square
index. -/
private def rzInteriorLowerFaceIndex (S : OddScale)
    (i : Fin (S.half - 1)) : Fin S.half :=
  ⟨i.1, by have := i.2; omega⟩

/-- Embed a face-interior vertex index into the adjacent upper small-square
index. -/
private def rzInteriorUpperFaceIndex (S : OddScale)
    (i : Fin (S.half - 1)) : Fin S.half :=
  ⟨i.1 + 1, by have := i.2; omega⟩

/-- A grid vertex equal to a stored face-interior tag retains the old face
and has the unique interior grid coordinates.  This is a constructor
inversion theorem in `Prop`; it does not select a face or a path. -/
private theorem subdivisionGridVertex_eq_faceInterior
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale)
    (candidate target : XStarFace (transposePresentation P) z)
    (u v : Fin (S.half + 1)) (i j : Fin (S.half - 1))
    (h : subdivisionGridVertex (transposePresentation P) z S candidate u v =
      Sum.inr (Sum.inr (target, i, j))) :
    candidate = target ∧ u.1 = i.1 + 1 ∧ v.1 = j.1 + 1 := by
  simp only [subdivisionGridVertex] at h
  split at h <;> rename_i hu0
  · split at h <;> rename_i hv0
    · cases h
    · split at h <;> cases h
  · split at h <;> rename_i hulast
    · split at h <;> rename_i hv0
      · cases h
      · split at h <;> cases h
    · split at h <;> rename_i hv0
      · cases h
      · split at h <;> rename_i hvlast
        · cases h
        · have hpayload := Sum.inr.inj (Sum.inr.inj h)
          have hface : candidate = target := congrArg Prod.fst hpayload
          have hi :=
            congrArg Fin.val (congrArg (fun payload => payload.2.1) hpayload)
          have hj :=
            congrArg Fin.val (congrArg (fun payload => payload.2.2) hpayload)
          change u.1 - 1 = i.1 at hi
          change v.1 - 1 = j.1 at hj
          refine ⟨hface, ?_, ?_⟩
          · omega
          · omega

/-- The four small cells incident to a stored Z-star face-interior subdivision
vertex, in southwest/southeast/northwest/northeast order. -/
private noncomputable def rzFaceInteriorLocalFaceSW
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z)
    (copy : Two) (face : XStarFace (transposePresentation P) z)
    (i j : Fin (S.half - 1)) : RZLocalFace P S :=
  ⟨z, Sum.inl (copy,
    (face, rzInteriorLowerFaceIndex S i, rzInteriorLowerFaceIndex S j)),
    (1, 1)⟩

private noncomputable def rzFaceInteriorLocalFaceSE
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z)
    (copy : Two) (face : XStarFace (transposePresentation P) z)
    (i j : Fin (S.half - 1)) : RZLocalFace P S :=
  ⟨z, Sum.inl (copy,
    (face, rzInteriorUpperFaceIndex S i, rzInteriorLowerFaceIndex S j)),
    (0, 1)⟩

private noncomputable def rzFaceInteriorLocalFaceNW
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z)
    (copy : Two) (face : XStarFace (transposePresentation P) z)
    (i j : Fin (S.half - 1)) : RZLocalFace P S :=
  ⟨z, Sum.inl (copy,
    (face, rzInteriorLowerFaceIndex S i, rzInteriorUpperFaceIndex S j)),
    (1, 0)⟩

private noncomputable def rzFaceInteriorLocalFaceNE
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z)
    (copy : Two) (face : XStarFace (transposePresentation P) z)
    (i j : Fin (S.half - 1)) : RZLocalFace P S :=
  ⟨z, Sum.inl (copy,
    (face, rzInteriorUpperFaceIndex S i, rzInteriorUpperFaceIndex S j)),
    (0, 0)⟩

/-- The four and only end-copy squares having the stored face-interior vertex
as a corner. -/
private theorem rzFaceInteriorLocalCell_cases
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z)
    (copy : Two) (face : XStarFace (transposePresentation P) z)
    (i j : Fin (S.half - 1)) (cell : ZDoubleCylinderFace P z S)
    (bits : Two × Two)
    (h : localCornerVertex P z S cell bits =
      (copy, Sum.inr (Sum.inr (face, i, j)))) :
    (⟨z, cell, bits⟩ : RZLocalFace P S) =
        rzFaceInteriorLocalFaceSW P S z copy face i j ∨
      (⟨z, cell, bits⟩ : RZLocalFace P S) =
        rzFaceInteriorLocalFaceSE P S z copy face i j ∨
      (⟨z, cell, bits⟩ : RZLocalFace P S) =
        rzFaceInteriorLocalFaceNW P S z copy face i j ∨
      (⟨z, cell, bits⟩ : RZLocalFace P S) =
        rzFaceInteriorLocalFaceNE P S z copy face i j := by
  rcases cell with copyFace | rectangle
  · rcases copyFace with ⟨candidateCopy, candidate, a, b⟩
    have hcopy : candidateCopy = copy := congrArg Prod.fst h
    have hvertex : subdivisionGridVertex (transposePresentation P) z S
        candidate (gridEndpoint a bits.1) (gridEndpoint b bits.2) =
          Sum.inr (Sum.inr (face, i, j)) := congrArg Prod.snd h
    obtain ⟨hface, hu, hv⟩ := subdivisionGridVertex_eq_faceInterior
      P z S candidate face (gridEndpoint a bits.1) (gridEndpoint b bits.2)
        i j hvertex
    subst candidateCopy
    subst candidate
    rcases bits with ⟨first, second⟩
    fin_cases first <;> fin_cases second
    · right; right; right
      change a.1 = i.1 + 1 at hu
      change b.1 = j.1 + 1 at hv
      congr 6
      · apply Fin.ext
        exact hu
      · apply Fin.ext
        exact hv
    · right; left
      change a.1 = i.1 + 1 at hu
      change b.1 + 1 = j.1 + 1 at hv
      congr 6
      · apply Fin.ext
        exact hu
      · apply Fin.ext
        change b.1 = j.1
        omega
    · right; right; left
      change a.1 + 1 = i.1 + 1 at hu
      change b.1 = j.1 + 1 at hv
      congr 6
      · apply Fin.ext
        change a.1 = i.1
        omega
      · apply Fin.ext
        exact hv
    · left
      change a.1 + 1 = i.1 + 1 at hu
      change b.1 + 1 = j.1 + 1 at hv
      congr 6
      · apply Fin.ext
        change a.1 = i.1
        omega
      · apply Fin.ext
        change b.1 = j.1
        omega
  · simp only [localCornerVertex] at h
    have hsnd := congrArg Prod.snd h
    rcases bits with ⟨bitCopy, endpoint⟩
    have himpossible : False := by
      fin_cases endpoint
      · have hb := (subdivisionBoundaryEdgeStart
          (transposePresentation P) z S rectangle).2
        have heq : (subdivisionBoundaryEdgeStart
            (transposePresentation P) z S rectangle).1 =
            Sum.inr (Sum.inr (face, i, j)) := by
          simpa [doubleCylinderRectangleCorner] using hsnd
        rw [heq] at hb
        simp [subdivisionBoundaryVertexMember] at hb
      · have hb := (subdivisionBoundaryEdgeEnd
          (transposePresentation P) z S rectangle).2
        have heq : (subdivisionBoundaryEdgeEnd
            (transposePresentation P) z S rectangle).1 =
            Sum.inr (Sum.inr (face, i, j)) := by
          simpa [doubleCylinderRectangleCorner] using hsnd
        rw [heq] at hb
        simp [subdivisionBoundaryVertexMember] at hb
    exact himpossible.elim

/-- The one-dimensional Q-side embedding lands only on original-star or
edge-interior subdivision vertices, never on a stored square-interior tag. -/
private theorem qToZDoubleCylinderVertex_ne_faceInterior
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale)
    (vertex : QDoubleCylinderVertex (transposePresentation P) q S)
    (copy : Two) (face : XStarFace (transposePresentation P) z)
    (i j : Fin (S.half - 1)) :
    qToZDoubleCylinderVertex P A q z hqz S vertex ≠
      (copy, Sum.inr (Sum.inr (face, i, j))) := by
  rcases vertex with ⟨vertexCopy, vertex⟩
  rcases vertex with original | interior
  · simp [qToZDoubleCylinderVertex, qToZSubdivisionVertex]
  · simp [qToZDoubleCylinderVertex, qToZSubdivisionVertex]

/-- Each adjacent small cell has the stored face-interior vertex as its
selected successor Z corner. -/
private theorem rzFaceInteriorLocalFaceZ_eq
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z)
    (copy : Two) (face : XStarFace (transposePresentation P) z)
    (i j : Fin (S.half - 1)) :
    localFaceZ P S (rzFaceInteriorLocalFaceSW P S z copy face i j) =
        ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩ ∧
      localFaceZ P S (rzFaceInteriorLocalFaceSE P S z copy face i j) =
        ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩ ∧
      localFaceZ P S (rzFaceInteriorLocalFaceNW P S z copy face i j) =
        ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩ ∧
      localFaceZ P S (rzFaceInteriorLocalFaceNE P S z copy face i j) =
        ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩ := by
  have hi : i.1 + 1 < S.half := (Nat.lt_sub_iff_add_lt).1 i.2
  have hj : j.1 + 1 < S.half := (Nat.lt_sub_iff_add_lt).1 j.2
  constructor
  · simp [rzFaceInteriorLocalFaceSW, localFaceZ, gridEndpoint, twoSelect,
      rzInteriorLowerFaceIndex, subdivisionGridVertex, lowerGridIndex,
      upperGridIndex, hi.ne, hj.ne]
    constructor
    · apply Fin.ext
      change (i.1 + 1) - 1 = i.1
      omega
    · apply Fin.ext
      change (j.1 + 1) - 1 = j.1
      omega
  constructor
  · simp [rzFaceInteriorLocalFaceSE, localFaceZ, gridEndpoint, twoSelect,
      rzInteriorLowerFaceIndex, rzInteriorUpperFaceIndex,
      subdivisionGridVertex, lowerGridIndex, upperGridIndex, hi.ne, hj.ne]
    constructor
    · apply Fin.ext
      change (i.1 + 1) - 1 = i.1
      omega
    · apply Fin.ext
      change (j.1 + 1) - 1 = j.1
      omega
  constructor
  · simp [rzFaceInteriorLocalFaceNW, localFaceZ, gridEndpoint, twoSelect,
      rzInteriorLowerFaceIndex, rzInteriorUpperFaceIndex,
      subdivisionGridVertex, lowerGridIndex, upperGridIndex, hi.ne, hj.ne]
    constructor
    · apply Fin.ext
      change (i.1 + 1) - 1 = i.1
      omega
    · apply Fin.ext
      change (j.1 + 1) - 1 = j.1
      omega
  · simp [rzFaceInteriorLocalFaceNE, localFaceZ, gridEndpoint, twoSelect,
      rzInteriorUpperFaceIndex, subdivisionGridVertex, lowerGridIndex,
      upperGridIndex, hi.ne, hj.ne]
    constructor
    · apply Fin.ext
      change (i.1 + 1) - 1 = i.1
      omega
    · apply Fin.ext
      change (j.1 + 1) - 1 = j.1
      omega

/-- Materialize the four adjacent local faces in the fixed successor Z-star. -/
private noncomputable def rzFaceInteriorZStarFaceSW
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (face : XStarFace (transposePresentation P) z)
    (i j : Fin (S.half - 1)) :
    ZStarFace (rzReplacementPresentation P A S)
      ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩ :=
  ⟨Sum.inl (rzFaceInteriorLocalFaceSW P S z copy face i j), by
    simp only [zStarFaceMember, decide_eq_true_eq]
    rw [show (rzReplacementPresentation P A S).faceZ = rzFaceZ P A S from rfl]
    exact (rzFaceInteriorLocalFaceZ_eq P S z copy face i j).1⟩

private noncomputable def rzFaceInteriorZStarFaceSE
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (face : XStarFace (transposePresentation P) z)
    (i j : Fin (S.half - 1)) :
    ZStarFace (rzReplacementPresentation P A S)
      ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩ :=
  ⟨Sum.inl (rzFaceInteriorLocalFaceSE P S z copy face i j), by
    simp only [zStarFaceMember, decide_eq_true_eq]
    rw [show (rzReplacementPresentation P A S).faceZ = rzFaceZ P A S from rfl]
    exact (rzFaceInteriorLocalFaceZ_eq P S z copy face i j).2.1⟩

private noncomputable def rzFaceInteriorZStarFaceNW
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (face : XStarFace (transposePresentation P) z)
    (i j : Fin (S.half - 1)) :
    ZStarFace (rzReplacementPresentation P A S)
      ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩ :=
  ⟨Sum.inl (rzFaceInteriorLocalFaceNW P S z copy face i j), by
    simp only [zStarFaceMember, decide_eq_true_eq]
    rw [show (rzReplacementPresentation P A S).faceZ = rzFaceZ P A S from rfl]
    exact (rzFaceInteriorLocalFaceZ_eq P S z copy face i j).2.2.1⟩

private noncomputable def rzFaceInteriorZStarFaceNE
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (face : XStarFace (transposePresentation P) z)
    (i j : Fin (S.half - 1)) :
    ZStarFace (rzReplacementPresentation P A S)
      ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩ :=
  ⟨Sum.inl (rzFaceInteriorLocalFaceNE P S z copy face i j), by
    simp only [zStarFaceMember, decide_eq_true_eq]
    rw [show (rzReplacementPresentation P A S).faceZ = rzFaceZ P A S from rfl]
    exact (rzFaceInteriorLocalFaceZ_eq P S z copy face i j).2.2.2⟩

/-- The start of the selected Z-star boundary edge is the X endpoint of its
concrete face. -/
private theorem rzZStarFaceBoundaryEdge_start_value
    (P : TannerSquarePresentation) (z : P.Z)
    (face : ZStarFace P z) (corner : Two) :
    (zBoundaryEdgeStart P z
      (rzZStarFaceBoundaryEdge P z face corner)).1 =
        Vertex.x (P.faceX face.1) := by
  let transposedFace := (transposeXStarFaceEquiv P z).symm face
  let edge := rzXStarFaceBoundaryEdge (transposePresentation P) z
    transposedFace corner
  have hend := congrArg Subtype.val (transpose_xBoundaryEdgeEnd P z edge)
  change (zBoundaryEdgeStart P z
    (transposeXStarBoundaryEdgeEquiv P z edge)).1 = _
  rw [← hend]
  change Vertex.x (P.faceX face.1) = Vertex.x (P.faceX face.1)
  rfl

/-- The end of the selected Z-star boundary edge is its ordered Q corner. -/
private theorem rzZStarFaceBoundaryEdge_end_value
    (P : TannerSquarePresentation) (z : P.Z)
    (face : ZStarFace P z) (corner : Two) :
    (zBoundaryEdgeEnd P z
      (rzZStarFaceBoundaryEdge P z face corner)).1 =
        Vertex.q (P.faceQ face.1 corner) := by
  let transposedFace := (transposeXStarFaceEquiv P z).symm face
  let edge := rzXStarFaceBoundaryEdge (transposePresentation P) z
    transposedFace corner
  have hstart := congrArg Subtype.val (transpose_xBoundaryEdgeStart P z edge)
  change (zBoundaryEdgeEnd P z
    (transposeXStarBoundaryEdgeEquiv P z edge)).1 = _
  rw [← hstart]
  change Vertex.q (P.faceQ face.1 corner) =
    Vertex.q (P.faceQ face.1 corner)
  rfl

/-- The V4 owner of a boundary edge cut from a retained face is that same
old face; regularity is used only for this face identity. -/
private theorem rzOriginalCentralFace_owner_eq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (z : P.Z)
    (face : XStarFace (transposePresentation P) z) (corner : Two) :
    (rzInputZBoundaryFaceOwner P A4 z
      (rzZStarFaceBoundaryEdge P z
        (transposeXStarFaceEquiv P z face) corner)).1.1 =
      transposeXStarFaceEquiv P z face := by
  let oldFace := transposeXStarFaceEquiv P z face
  let edge := rzZStarFaceBoundaryEdge P z oldFace corner
  have hinput := rzInputZBoundaryEdge_start_value P z edge
  have hface := rzZStarFaceBoundaryEdge_start_value P z oldFace corner
  have hx : P.faceX oldFace.1 =
      (rzInputZBoundaryXQEdge P z edge).1.1 := by
    exact (Vertex.x.inj (hface.symm.trans hinput)).symm
  apply Subtype.ext
  simpa [oldFace, edge] using
    rzInputZBoundaryOwnerFace_eq P A4 R z edge oldFace hx

/-- The X corner of a retained central small cell is the endpoint-zero lift
of either old boundary edge cut from that face. -/
private theorem rzOriginalCentralFace_xCoordinate
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (z : P.Z) (copy : Two)
    (face : XStarFace (transposePresentation P) z) (corner : Two) :
    rzOriginalCentralBoundaryEdgeVertex P A4 S z copy
        (rzZStarFaceBoundaryEdge P z
          (transposeXStarFaceEquiv P z face) corner) 0 =
      zBoundaryEdgeStart (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S)
        (rzOriginalCentralZVertex P S z copy)
        (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S)
          (rzOriginalCentralZVertex P S z copy)
          (rzOriginalCentralZStarFace P A4.toTannerSquareAdmissible
            S z copy face) 0) := by
  apply Subtype.ext
  change (zBoundaryEdgeStart (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S)
    (rzOriginalCentralZVertex P S z copy)
    (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
      (rzOriginalCentralZVertex P S z copy)
      (rzOriginalCentralOwnerLocalZStarFace P A4 S z copy
        (rzZStarFaceBoundaryEdge P z
          (transposeXStarFaceEquiv P z face) corner)) 0)).1 = _
  refine (rzZStarFaceBoundaryEdge_start_value
    (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
    (rzOriginalCentralZVertex P S z copy)
    (rzOriginalCentralOwnerLocalZStarFace P A4 S z copy
      (rzZStarFaceBoundaryEdge P z (transposeXStarFaceEquiv P z face) corner))
    0).trans ?_
  refine Eq.trans ?_ (rzZStarFaceBoundaryEdge_start_value
    (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
    (rzOriginalCentralZVertex P S z copy)
    (rzOriginalCentralZStarFace P A4.toTannerSquareAdmissible S z copy face)
    0).symm
  apply congrArg Vertex.x
  simp only [rzReplacementPresentation, rzReplacementData,
    rzOriginalCentralOwnerLocalZStarFace, rzOriginalCentralZStarFace,
    rzOriginalCentralFace, localFaceX]
  apply congrArg (fun cell : ZDoubleCylinderFace P z S =>
    (Sum.inl (Sum.inl ⟨z, cell⟩) : RZX P S))
  simp only [rzOriginalCentralOwnerCell, rzOriginalCentralCell]
  rw [rzOriginalCentralFace_owner_eq P A4 R z face corner]
  rw [Equiv.symm_apply_apply]

/-- Either Q corner of a retained central small cell is the endpoint-one lift
of the corresponding old boundary edge. -/
private theorem rzOriginalCentralFace_qCoordinate
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (z : P.Z) (copy : Two)
    (face : XStarFace (transposePresentation P) z) (corner : Two) :
    rzOriginalCentralBoundaryEdgeVertex P A4 S z copy
        (rzZStarFaceBoundaryEdge P z
          (transposeXStarFaceEquiv P z face) corner) 1 =
      zBoundaryEdgeEnd (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S)
        (rzOriginalCentralZVertex P S z copy)
        (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S)
          (rzOriginalCentralZVertex P S z copy)
          (rzOriginalCentralZStarFace P A4.toTannerSquareAdmissible
            S z copy face) corner) := by
  let oldFace := transposeXStarFaceEquiv P z face
  let edge := rzZStarFaceBoundaryEdge P z oldFace corner
  let owner := rzInputZBoundaryFaceOwner P A4 z edge
  have hface : owner.1.1 = oldFace := by
    simpa [owner, edge, oldFace] using
      rzOriginalCentralFace_owner_eq P A4 R z face corner
  have hinput := rzInputZBoundaryEdge_end_value P z edge
  have hold := rzZStarFaceBoundaryEdge_end_value P z oldFace corner
  have hq : (rzInputZBoundaryXQEdge P z edge).1.2 =
      P.faceQ oldFace.1 corner :=
    Vertex.q.inj (hinput.symm.trans hold)
  have hownerQ := rzInputZBoundaryOwner_faceQ P A4 z edge
  have hradial :
      xStarFaceXQEdge (transposePresentation P) z
          ((transposeXStarFaceEquiv P z).symm owner.1.1) owner.1.2 =
        xStarFaceXQEdge (transposePresentation P) z face corner := by
    apply Subtype.ext
    apply congrArg Sum.inl
    apply Subtype.ext
    apply Prod.ext
    · simp [hface, oldFace, faceXQEdge]
    · change P.faceQ owner.1.1.1 owner.1.2 =
        P.faceQ oldFace.1 corner
      exact hownerQ.trans hq
  apply Subtype.ext
  change (zBoundaryEdgeEnd (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S)
    (rzOriginalCentralZVertex P S z copy)
    (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
      (rzOriginalCentralZVertex P S z copy)
      (rzOriginalCentralOwnerLocalZStarFace P A4 S z copy edge)
      owner.1.2)).1 = _
  refine (rzZStarFaceBoundaryEdge_end_value
    (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
    (rzOriginalCentralZVertex P S z copy)
    (rzOriginalCentralOwnerLocalZStarFace P A4 S z copy edge)
    owner.1.2).trans ?_
  refine Eq.trans ?_ (rzZStarFaceBoundaryEdge_end_value
    (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
    (rzOriginalCentralZVertex P S z copy)
    (rzOriginalCentralZStarFace P A4.toTannerSquareAdmissible S z copy face)
    corner).symm
  apply congrArg Vertex.q
  simp only [rzReplacementPresentation, rzReplacementData,
    rzOriginalCentralOwnerLocalZStarFace, rzOriginalCentralZStarFace,
    rzOriginalCentralFace]
  change twoSelect
      (localFaceQ0 P S ⟨z,
        rzOriginalCentralOwnerCell P A4 S z copy edge, (0, 0)⟩)
      (localFaceQ1 P S ⟨z,
        rzOriginalCentralOwnerCell P A4 S z copy edge, (0, 0)⟩)
      owner.1.2 =
    twoSelect
      (localFaceQ0 P S ⟨z,
        rzOriginalCentralCell P S z copy face, (0, 0)⟩)
      (localFaceQ1 P S ⟨z,
        rzOriginalCentralCell P S z copy face, (0, 0)⟩) corner
  rw [localFaceQ_eq_corner, localFaceQ_eq_corner]
  apply congrArg Sum.inl
  refine Sigma.ext
    (x := (⟨z, localCornerEdge P z S
      (rzOriginalCentralOwnerCell P A4 S z copy edge)
      ((0, 0), owner.1.2)⟩ :
        Sigma fun oldZ : P.Z => ZDoubleCylinderEdge P oldZ S))
    (y := (⟨z, localCornerEdge P z S
      (rzOriginalCentralCell P S z copy face)
      ((0, 0), corner)⟩ :
        Sigma fun oldZ : P.Z => ZDoubleCylinderEdge P oldZ S)) rfl ?_
  apply heq_of_eq
  have htransposedFace :
      (transposeXStarFaceEquiv P z).symm owner.1.1 = face := by
    rw [hface]
    exact Equiv.symm_apply_apply _ _
  simp only [rzOriginalCentralOwnerCell, rzOriginalCentralCell]
  rw [htransposedFace]
  rw [htransposedFace] at hradial
  generalize hownerCorner : owner.1.2 = ownerCorner at hradial ⊢
  have hgridZero : lowerGridIndex (rzRadialGridZero S) =
      (0 : Fin (S.half + 1)) := by
    apply Fin.ext
    rfl
  fin_cases ownerCorner <;> fin_cases corner <;>
    simpa [localCornerEdge, gridEndpoint, twoSelect,
      subdivisionHorizontalEdge, subdivisionVerticalEdge,
      hgridZero] using congrArg
        (fun selected : XStarEdge (transposePresentation P) z =>
          (Sum.inl (copy,
            (Sum.inl (selected, rzRadialGridZero S) :
              SubdivisionEdge (transposePresentation P) z S)) :
            ZDoubleCylinderEdge P z S)) hradial

/-- Cellular regularity makes the endpoint-zero local-X lift independent of
which incident old Z-boundary edge V2 selected. -/
private theorem rzOriginalCentralBoundaryEdgeVertex_zero_eq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (z : P.Z) (copy : Two) (first second : ZStarBoundaryEdge P z)
    (hx : (rzInputZBoundaryXQEdge P z first).1.1 =
      (rzInputZBoundaryXQEdge P z second).1.1) :
    rzOriginalCentralBoundaryEdgeVertex P A4 S z copy first 0 =
      rzOriginalCentralBoundaryEdgeVertex P A4 S z copy second 0 := by
  have hfaceX :
      P.faceX (rzInputZBoundaryFaceOwner P A4 z second).1.1.1 =
        (rzInputZBoundaryXQEdge P z first).1.1 :=
    (rzInputZBoundaryOwner_faceX P A4 z second).trans hx.symm
  have hface := rzInputZBoundaryOwnerFace_eq
    P A4 R z first (rzInputZBoundaryFaceOwner P A4 z second).1.1 hfaceX
  have htransposedFace :
      (transposeXStarFaceEquiv P z).symm
          (rzInputZBoundaryFaceOwner P A4 z first).1.1 =
        (transposeXStarFaceEquiv P z).symm
          (rzInputZBoundaryFaceOwner P A4 z second).1.1 := by
    apply Subtype.ext
    exact hface
  have hcell : rzOriginalCentralOwnerCell P A4 S z copy first =
      rzOriginalCentralOwnerCell P A4 S z copy second := by
    simp [rzOriginalCentralOwnerCell, htransposedFace]
  apply Subtype.ext
  change (zBoundaryEdgeStart
      (rzReplacementPresentation P
        A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
      (rzOriginalCentralZVertex P S z copy)
      (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
          A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        (rzOriginalCentralZVertex P S z copy)
        (rzOriginalCentralOwnerLocalZStarFace P A4 S z copy first) 0)).1 =
    (zBoundaryEdgeStart
      (rzReplacementPresentation P
        A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
      (rzOriginalCentralZVertex P S z copy)
      (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
          A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        (rzOriginalCentralZVertex P S z copy)
        (rzOriginalCentralOwnerLocalZStarFace P A4 S z copy second) 0)).1
  refine (rzZStarFaceBoundaryEdge_start_value
    (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
    (rzOriginalCentralZVertex P S z copy)
    (rzOriginalCentralOwnerLocalZStarFace P A4 S z copy first)
    0).trans ?_
  refine Eq.trans ?_ (rzZStarFaceBoundaryEdge_start_value
    (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
    (rzOriginalCentralZVertex P S z copy)
    (rzOriginalCentralOwnerLocalZStarFace P A4 S z copy second)
    0).symm
  apply congrArg Vertex.x
  exact congrArg (fun cell : ZDoubleCylinderFace P z S =>
    (Sum.inl (Sum.inl ⟨z, cell⟩) : RZX P S)) hcell

/-- Cellular regularity makes the endpoint-one radial local-Q lift independent
of which incident old Z-boundary edge V2 selected. -/
private theorem rzOriginalCentralBoundaryEdgeVertex_one_eq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (z : P.Z) (copy : Two) (first second : ZStarBoundaryEdge P z)
    (hq : (rzInputZBoundaryXQEdge P z first).1.2 =
      (rzInputZBoundaryXQEdge P z second).1.2) :
    rzOriginalCentralBoundaryEdgeVertex P A4 S z copy first 1 =
      rzOriginalCentralBoundaryEdgeVertex P A4 S z copy second 1 := by
  have hradial := rzOriginalCentralOwnerRadialEdge_eq P A4 z first second hq
  apply Subtype.ext
  change (zBoundaryEdgeEnd
      (rzReplacementPresentation P
        A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
      (rzOriginalCentralZVertex P S z copy)
      (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
          A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        (rzOriginalCentralZVertex P S z copy)
        (rzOriginalCentralOwnerLocalZStarFace P A4 S z copy first)
        (rzInputZBoundaryFaceOwner P A4 z first).1.2)).1 =
    (zBoundaryEdgeEnd
      (rzReplacementPresentation P
        A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
      (rzOriginalCentralZVertex P S z copy)
      (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
          A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        (rzOriginalCentralZVertex P S z copy)
        (rzOriginalCentralOwnerLocalZStarFace P A4 S z copy second)
        (rzInputZBoundaryFaceOwner P A4 z second).1.2)).1
  refine (rzZStarFaceBoundaryEdge_end_value
    (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
    (rzOriginalCentralZVertex P S z copy)
    (rzOriginalCentralOwnerLocalZStarFace P A4 S z copy first)
    (rzInputZBoundaryFaceOwner P A4 z first).1.2).trans ?_
  refine Eq.trans ?_ (rzZStarFaceBoundaryEdge_end_value
    (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
    (rzOriginalCentralZVertex P S z copy)
    (rzOriginalCentralOwnerLocalZStarFace P A4 S z copy second)
    (rzInputZBoundaryFaceOwner P A4 z second).1.2).symm
  apply congrArg Vertex.q
  simp only [rzReplacementPresentation, rzReplacementData,
    rzOriginalCentralOwnerLocalZStarFace]
  change twoSelect
      (localFaceQ0 P S ⟨z,
        rzOriginalCentralOwnerCell P A4 S z copy first, (0, 0)⟩)
      (localFaceQ1 P S ⟨z,
        rzOriginalCentralOwnerCell P A4 S z copy first, (0, 0)⟩)
      (rzInputZBoundaryFaceOwner P A4 z first).1.2 =
    twoSelect
      (localFaceQ0 P S ⟨z,
        rzOriginalCentralOwnerCell P A4 S z copy second, (0, 0)⟩)
      (localFaceQ1 P S ⟨z,
        rzOriginalCentralOwnerCell P A4 S z copy second, (0, 0)⟩)
      (rzInputZBoundaryFaceOwner P A4 z second).1.2
  rw [localFaceQ_eq_corner, localFaceQ_eq_corner]
  change (Sum.inl ⟨z, localCornerEdge P z S
      (rzOriginalCentralOwnerCell P A4 S z copy first)
      ((0, 0), (rzInputZBoundaryFaceOwner P A4 z first).1.2)⟩ : RZQ P S) =
    (Sum.inl ⟨z, localCornerEdge P z S
      (rzOriginalCentralOwnerCell P A4 S z copy second)
      ((0, 0), (rzInputZBoundaryFaceOwner P A4 z second).1.2)⟩ : RZQ P S)
  apply congrArg (fun edge : ZDoubleCylinderEdge P z S =>
    (Sum.inl ⟨z, edge⟩ : RZQ P S))
  generalize hfirstCorner : (rzInputZBoundaryFaceOwner P A4 z first).1.2 = firstCorner at hradial ⊢
  generalize hsecondCorner : (rzInputZBoundaryFaceOwner P A4 z second).1.2 = secondCorner at hradial ⊢
  have hgridZero : lowerGridIndex (rzRadialGridZero S) =
      (0 : Fin (S.half + 1)) := by
    apply Fin.ext
    rfl
  fin_cases firstCorner <;> fin_cases secondCorner <;>
    simpa [rzOriginalCentralOwnerCell, localCornerEdge, gridEndpoint, twoSelect,
      subdivisionHorizontalEdge, subdivisionVerticalEdge, hgridZero] using
        congrArg (fun edge =>
          (Sum.inl (copy,
            (Sum.inl (edge, rzRadialGridZero S) :
              SubdivisionEdge (transposePresentation P) z S)) :
            ZDoubleCylinderEdge P z S)) hradial

/-- The V2-selected incident edge computes the same canonical successor
vertex as any explicitly supplied old edge endpoint equal to the input
boundary vertex. -/
private theorem rzOriginalCentralBoundaryVertexLift_eq_edgeVertex
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (z : P.Z) (copy : Two) (vertex : ZStarBoundaryVertex P z)
    (edge : ZStarBoundaryEdge P z) (endpoint : Two)
    (hendpoint : BDL26TannerLocalRegularity.edgeEndpoint
      (zBoundaryEdgeStart P z) (zBoundaryEdgeEnd P z) edge endpoint = vertex) :
    rzOriginalCentralBoundaryVertexLift P A4 S z copy vertex =
      rzOriginalCentralBoundaryEdgeVertex P A4 S z copy edge endpoint := by
  unfold rzOriginalCentralBoundaryVertexLift
  generalize howned :
      A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.zBoundaryIncidentEdge
        z vertex = owned
  rcases owned with ⟨⟨selectedEdge, selectedEndpoint⟩, hselected⟩
  dsimp only
  have hsameEndpoint := hselected.trans hendpoint.symm
  fin_cases selectedEndpoint <;> fin_cases endpoint
  · apply rzOriginalCentralBoundaryEdgeVertex_zero_eq P A4 R S z copy
    change BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart P z) (zBoundaryEdgeEnd P z) selectedEdge 0 =
      BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart P z) (zBoundaryEdgeEnd P z) edge 0 at hsameEndpoint
    have hvalue := congrArg Subtype.val hsameEndpoint
    simp only [BDL26TannerLocalRegularity.edgeEndpoint_zero] at hvalue
    rw [rzInputZBoundaryEdge_start_value,
      rzInputZBoundaryEdge_start_value] at hvalue
    exact Vertex.x.inj hvalue
  · change BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart P z) (zBoundaryEdgeEnd P z) selectedEdge 0 =
      BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart P z) (zBoundaryEdgeEnd P z) edge 1 at hsameEndpoint
    have hvalue := congrArg Subtype.val hsameEndpoint
    simp only [BDL26TannerLocalRegularity.edgeEndpoint_zero,
      BDL26TannerLocalRegularity.edgeEndpoint_one] at hvalue
    rw [rzInputZBoundaryEdge_start_value,
      rzInputZBoundaryEdge_end_value] at hvalue
    cases hvalue
  · change BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart P z) (zBoundaryEdgeEnd P z) selectedEdge 1 =
      BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart P z) (zBoundaryEdgeEnd P z) edge 0 at hsameEndpoint
    have hvalue := congrArg Subtype.val hsameEndpoint
    simp only [BDL26TannerLocalRegularity.edgeEndpoint_one,
      BDL26TannerLocalRegularity.edgeEndpoint_zero] at hvalue
    rw [rzInputZBoundaryEdge_end_value,
      rzInputZBoundaryEdge_start_value] at hvalue
    cases hvalue
  · apply rzOriginalCentralBoundaryEdgeVertex_one_eq P A4 R S z copy
    change BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart P z) (zBoundaryEdgeEnd P z) selectedEdge 1 =
      BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart P z) (zBoundaryEdgeEnd P z) edge 1 at hsameEndpoint
    have hvalue := congrArg Subtype.val hsameEndpoint
    simp only [BDL26TannerLocalRegularity.edgeEndpoint_one] at hvalue
    rw [rzInputZBoundaryEdge_end_value,
      rzInputZBoundaryEdge_end_value] at hvalue
    exact Vertex.q.inj hvalue

/-- Every successor boundary vertex at an original-central Z coordinate is
the canonical lift of an old Z-boundary vertex.  This is proposition-level
surjectivity only; no inverse or representative selector is retained. -/
private theorem rzOriginalCentralBoundaryVertexLift_surjective
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (z : P.Z) (copy : Two) :
    Function.Surjective
      (rzOriginalCentralBoundaryVertexLift P A4 S z copy) := by
  classical
  rintro ⟨value, member⟩
  rcases value with newX | newQ | impossible
  · have hmember := member
    simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at hmember
    obtain ⟨candidate, hzMember, hx⟩ := hmember
    have hz : rzFaceZ P A4.toTannerSquareAdmissible S candidate =
        rzOriginalCentralZVertex P S z copy := by
      simp only [zStarFaceMember, decide_eq_true_eq] at hzMember
      exact hzMember
    obtain ⟨face, hface⟩ := rzOriginalCentralFace_cases P
      A4.toTannerSquareAdmissible S z copy candidate hz
    subst candidate
    let oldFace := transposeXStarFaceEquiv P z face
    let edge := rzZStarFaceBoundaryEdge P z oldFace 0
    let oldVertex := zBoundaryEdgeStart P z edge
    refine ⟨oldVertex, ?_⟩
    have hlift := rzOriginalCentralBoundaryVertexLift_eq_edgeVertex
      P A4 R S z copy oldVertex edge 0 (by
        rw [BDL26TannerLocalRegularity.edgeEndpoint_zero])
    have hcoordinate := rzOriginalCentralFace_xCoordinate
      P A4 R S z copy face 0
    have htarget :
        zBoundaryEdgeStart (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S)
          (rzOriginalCentralZVertex P S z copy)
          (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
              A4.toTannerSquareAdmissible S)
            (rzOriginalCentralZVertex P S z copy)
            (rzOriginalCentralZStarFace P A4.toTannerSquareAdmissible
              S z copy face) 0) =
          (⟨Vertex.x newX, member⟩ : ZStarBoundaryVertex
            (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
            (rzOriginalCentralZVertex P S z copy)) := by
      apply Subtype.ext
      exact (rzZStarFaceBoundaryEdge_start_value
        (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
        (rzOriginalCentralZVertex P S z copy)
        (rzOriginalCentralZStarFace P A4.toTannerSquareAdmissible
          S z copy face) 0).trans (congrArg Vertex.x hx.symm)
    exact hlift.trans (hcoordinate.trans htarget)
  · have hmember := member
    simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at hmember
    obtain ⟨candidate, hzMember, hq⟩ := hmember
    have hz : rzFaceZ P A4.toTannerSquareAdmissible S candidate =
        rzOriginalCentralZVertex P S z copy := by
      simp only [zStarFaceMember, decide_eq_true_eq] at hzMember
      exact hzMember
    obtain ⟨face, hface⟩ := rzOriginalCentralFace_cases P
      A4.toTannerSquareAdmissible S z copy candidate hz
    subst candidate
    rcases hq with hq | hq
    · let oldFace := transposeXStarFaceEquiv P z face
      let edge := rzZStarFaceBoundaryEdge P z oldFace 0
      let oldVertex := zBoundaryEdgeEnd P z edge
      refine ⟨oldVertex, ?_⟩
      have hlift := rzOriginalCentralBoundaryVertexLift_eq_edgeVertex
        P A4 R S z copy oldVertex edge 1 (by
          rw [BDL26TannerLocalRegularity.edgeEndpoint_one])
      have hcoordinate := rzOriginalCentralFace_qCoordinate
        P A4 R S z copy face 0
      have htarget :
          zBoundaryEdgeEnd (rzReplacementPresentation P
              A4.toTannerSquareAdmissible S)
            (rzOriginalCentralZVertex P S z copy)
            (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
                A4.toTannerSquareAdmissible S)
              (rzOriginalCentralZVertex P S z copy)
              (rzOriginalCentralZStarFace P A4.toTannerSquareAdmissible
                S z copy face) 0) =
            (⟨Vertex.q newQ, member⟩ : ZStarBoundaryVertex
              (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
              (rzOriginalCentralZVertex P S z copy)) := by
        apply Subtype.ext
        exact (rzZStarFaceBoundaryEdge_end_value
          (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
          (rzOriginalCentralZVertex P S z copy)
          (rzOriginalCentralZStarFace P A4.toTannerSquareAdmissible
            S z copy face) 0).trans (congrArg Vertex.q hq.symm)
      exact hlift.trans (hcoordinate.trans htarget)
    · let oldFace := transposeXStarFaceEquiv P z face
      let edge := rzZStarFaceBoundaryEdge P z oldFace 1
      let oldVertex := zBoundaryEdgeEnd P z edge
      refine ⟨oldVertex, ?_⟩
      have hlift := rzOriginalCentralBoundaryVertexLift_eq_edgeVertex
        P A4 R S z copy oldVertex edge 1 (by
          rw [BDL26TannerLocalRegularity.edgeEndpoint_one])
      have hcoordinate := rzOriginalCentralFace_qCoordinate
        P A4 R S z copy face 1
      have htarget :
          zBoundaryEdgeEnd (rzReplacementPresentation P
              A4.toTannerSquareAdmissible S)
            (rzOriginalCentralZVertex P S z copy)
            (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
                A4.toTannerSquareAdmissible S)
              (rzOriginalCentralZVertex P S z copy)
              (rzOriginalCentralZStarFace P A4.toTannerSquareAdmissible
                S z copy face) 1) =
            (⟨Vertex.q newQ, member⟩ : ZStarBoundaryVertex
              (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
              (rzOriginalCentralZVertex P S z copy)) := by
        apply Subtype.ext
        exact (rzZStarFaceBoundaryEdge_end_value
          (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
          (rzOriginalCentralZVertex P S z copy)
          (rzOriginalCentralZStarFace P A4.toTannerSquareAdmissible
            S z copy face) 1).trans (congrArg Vertex.q hq.symm)
      exact hlift.trans (hcoordinate.trans htarget)
  · simp [zStarBoundaryVertexMember] at member

/-- Structurally decode the retained old X tag from the only successor X
constructor that can occur at an original-central Z coordinate. -/
private def rzOriginalCentralXTag
    (P : TannerSquarePresentation) (S : OddScale) : RZX P S → Option P.X
  | Sum.inl (Sum.inl localCell) =>
      match localCell.2 with
      | Sum.inl copyFace => some (P.faceX copyFace.2.1.1)
      | Sum.inr _ => none
  | _ => none

/-- Structurally decode the retained old Q tag from the segment-zero radial
local-edge constructor at an original-central Z coordinate. -/
private def rzOriginalCentralQTag
    (P : TannerSquarePresentation) (S : OddScale) : RZQ P S → Option P.Q
  | Sum.inl localEdge =>
      match localEdge.2 with
      | Sum.inl copyEdge =>
          match copyEdge.2 with
          | Sum.inl starSegment =>
              match starSegment.1.1 with
              | Sum.inl radial => some radial.1.2
              | Sum.inr _ => none
          | Sum.inr _ => none
      | Sum.inr _ => none
  | _ => none

private def rzOriginalCentralBoundaryXTag
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) : Vertex (rzReplacementPresentation P A S) → Option P.X
  | Vertex.x coordinate => rzOriginalCentralXTag P S coordinate
  | _ => none

private def rzOriginalCentralBoundaryQTag
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) : Vertex (rzReplacementPresentation P A S) → Option P.Q
  | Vertex.q coordinate => rzOriginalCentralQTag P S coordinate
  | _ => none

/-- The structural X decoder is a left inverse on lifted old X vertices. -/
private theorem rzOriginalCentralXTag_lift
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two) (x : P.X)
    (member : zStarBoundaryVertexMember P z (Vertex.x x) = true) :
    rzOriginalCentralBoundaryXTag P A4.toTannerSquareAdmissible S
      (rzOriginalCentralBoundaryVertexLift P A4 S z copy
        ⟨Vertex.x x, member⟩).1 = some x := by
  unfold rzOriginalCentralBoundaryVertexLift
  generalize howned :
      A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.zBoundaryIncidentEdge
        z ⟨Vertex.x x, member⟩ = owned
  rcases owned with ⟨⟨edge, endpoint⟩, hendpoint⟩
  dsimp only
  fin_cases endpoint
  · change BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart P z) (zBoundaryEdgeEnd P z) edge 0 =
      ⟨Vertex.x x, member⟩ at hendpoint
    have hvalue := congrArg Subtype.val hendpoint
    simp only [BDL26TannerLocalRegularity.edgeEndpoint_zero] at hvalue
    rw [rzInputZBoundaryEdge_start_value] at hvalue
    have hx := Vertex.x.inj hvalue
    have howner := rzInputZBoundaryOwner_faceX P A4 z edge
    change rzOriginalCentralBoundaryXTag P A4.toTannerSquareAdmissible S
      (zBoundaryEdgeStart (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S)
        (rzOriginalCentralZVertex P S z copy)
        (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S)
          (rzOriginalCentralZVertex P S z copy)
          (rzOriginalCentralOwnerLocalZStarFace P A4 S z copy edge) 0)).1 =
      some x
    refine (congrArg (rzOriginalCentralBoundaryXTag P
      A4.toTannerSquareAdmissible S)
      (rzZStarFaceBoundaryEdge_start_value
        (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
        (rzOriginalCentralZVertex P S z copy)
        (rzOriginalCentralOwnerLocalZStarFace P A4 S z copy edge) 0)).trans ?_
    change rzOriginalCentralXTag P S
      (rzFaceX P S
        (rzOriginalCentralOwnerLocalZStarFace P A4 S z copy edge).1) = some x
    simp only [rzOriginalCentralXTag, rzFaceX, localFaceX,
      rzOriginalCentralOwnerLocalZStarFace, rzOriginalCentralOwnerCell]
    have hface := congrArg Subtype.val
      (Equiv.apply_symm_apply (transposeXStarFaceEquiv P z)
        (rzInputZBoundaryFaceOwner P A4 z edge).1.1)
    change ((transposeXStarFaceEquiv P z).symm
      (rzInputZBoundaryFaceOwner P A4 z edge).1.1).1 =
        (rzInputZBoundaryFaceOwner P A4 z edge).1.1.1 at hface
    rw [hface, howner, hx]
  · change BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart P z) (zBoundaryEdgeEnd P z) edge 1 =
      ⟨Vertex.x x, member⟩ at hendpoint
    have hvalue := congrArg Subtype.val hendpoint
    simp only [BDL26TannerLocalRegularity.edgeEndpoint_one] at hvalue
    rw [rzInputZBoundaryEdge_end_value] at hvalue
    cases hvalue

/-- A lifted old Q vertex remains in the successor Q constructor, so the X
decoder returns none. -/
private theorem rzOriginalCentralXTag_lift_q
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two) (q : P.Q)
    (member : zStarBoundaryVertexMember P z (Vertex.q q) = true) :
    rzOriginalCentralBoundaryXTag P A4.toTannerSquareAdmissible S
      (rzOriginalCentralBoundaryVertexLift P A4 S z copy
        ⟨Vertex.q q, member⟩).1 = none := by
  unfold rzOriginalCentralBoundaryVertexLift
  generalize howned :
      A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.zBoundaryIncidentEdge
        z ⟨Vertex.q q, member⟩ = owned
  rcases owned with ⟨⟨edge, endpoint⟩, hendpoint⟩
  dsimp only
  fin_cases endpoint
  · change BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart P z) (zBoundaryEdgeEnd P z) edge 0 =
      ⟨Vertex.q q, member⟩ at hendpoint
    have hvalue := congrArg Subtype.val hendpoint
    simp only [BDL26TannerLocalRegularity.edgeEndpoint_zero] at hvalue
    rw [rzInputZBoundaryEdge_start_value] at hvalue
    cases hvalue
  · change rzOriginalCentralBoundaryXTag P
      A4.toTannerSquareAdmissible S
      (rzOriginalCentralBoundaryEdgeVertex P A4 S z copy edge 1).1 = none
    change rzOriginalCentralBoundaryXTag P A4.toTannerSquareAdmissible S
      (zBoundaryEdgeEnd (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S)
        (rzOriginalCentralZVertex P S z copy)
        (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S)
          (rzOriginalCentralZVertex P S z copy)
          (rzOriginalCentralOwnerLocalZStarFace P A4 S z copy edge)
          (rzInputZBoundaryFaceOwner P A4 z edge).1.2)).1 = none
    exact congrArg (rzOriginalCentralBoundaryXTag P
      A4.toTannerSquareAdmissible S)
      (rzZStarFaceBoundaryEdge_end_value
        (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
        (rzOriginalCentralZVertex P S z copy)
        (rzOriginalCentralOwnerLocalZStarFace P A4 S z copy edge)
        (rzInputZBoundaryFaceOwner P A4 z edge).1.2)

/-- The structural Q decoder is a left inverse on lifted old Q vertices. -/
private theorem rzOriginalCentralQTag_lift
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two) (q : P.Q)
    (member : zStarBoundaryVertexMember P z (Vertex.q q) = true) :
    rzOriginalCentralBoundaryQTag P A4.toTannerSquareAdmissible S
      (rzOriginalCentralBoundaryVertexLift P A4 S z copy
        ⟨Vertex.q q, member⟩).1 = some q := by
  unfold rzOriginalCentralBoundaryVertexLift
  generalize howned :
      A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.zBoundaryIncidentEdge
        z ⟨Vertex.q q, member⟩ = owned
  rcases owned with ⟨⟨edge, endpoint⟩, hendpoint⟩
  dsimp only
  fin_cases endpoint
  · change BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart P z) (zBoundaryEdgeEnd P z) edge 0 =
      ⟨Vertex.q q, member⟩ at hendpoint
    have hvalue := congrArg Subtype.val hendpoint
    simp only [BDL26TannerLocalRegularity.edgeEndpoint_zero] at hvalue
    rw [rzInputZBoundaryEdge_start_value] at hvalue
    cases hvalue
  · change BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart P z) (zBoundaryEdgeEnd P z) edge 1 =
      ⟨Vertex.q q, member⟩ at hendpoint
    have hvalue := congrArg Subtype.val hendpoint
    simp only [BDL26TannerLocalRegularity.edgeEndpoint_one] at hvalue
    rw [rzInputZBoundaryEdge_end_value] at hvalue
    have hq := Vertex.q.inj hvalue
    change rzOriginalCentralBoundaryQTag P A4.toTannerSquareAdmissible S
      (rzOriginalCentralBoundaryEdgeVertex P A4 S z copy edge 1).1 = some q
    change rzOriginalCentralBoundaryQTag P A4.toTannerSquareAdmissible S
      (zBoundaryEdgeEnd (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S)
        (rzOriginalCentralZVertex P S z copy)
        (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S)
          (rzOriginalCentralZVertex P S z copy)
          (rzOriginalCentralOwnerLocalZStarFace P A4 S z copy edge)
          (rzInputZBoundaryFaceOwner P A4 z edge).1.2)).1 = some q
    refine (congrArg (rzOriginalCentralBoundaryQTag P
      A4.toTannerSquareAdmissible S)
      (rzZStarFaceBoundaryEdge_end_value
        (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
        (rzOriginalCentralZVertex P S z copy)
        (rzOriginalCentralOwnerLocalZStarFace P A4 S z copy edge)
        (rzInputZBoundaryFaceOwner P A4 z edge).1.2)).trans ?_
    change rzOriginalCentralQTag P S
      (rzFaceQ P A4.toTannerSquareAdmissible S
        (rzOriginalCentralOwnerLocalZStarFace P A4 S z copy edge).1
        (rzInputZBoundaryFaceOwner P A4 z edge).1.2) = some q
    have hgridZero : lowerGridIndex (rzRadialGridZero S) =
        (0 : Fin (S.half + 1)) := by
      apply Fin.ext
      rfl
    have hownerQ := rzInputZBoundaryOwner_faceQ P A4 z edge
    have hface := congrArg Subtype.val
      (Equiv.apply_symm_apply (transposeXStarFaceEquiv P z)
        (rzInputZBoundaryFaceOwner P A4 z edge).1.1)
    change ((transposeXStarFaceEquiv P z).symm
      (rzInputZBoundaryFaceOwner P A4 z edge).1.1).1 =
        (rzInputZBoundaryFaceOwner P A4 z edge).1.1.1 at hface
    generalize hcorner :
      (rzInputZBoundaryFaceOwner P A4 z edge).1.2 = corner at hownerQ ⊢
    fin_cases corner <;>
      simp [rzOriginalCentralQTag, rzFaceQ, localFaceQ0, localFaceQ1,
        rzOriginalCentralOwnerLocalZStarFace, rzOriginalCentralOwnerCell,
        subdivisionHorizontalEdge, subdivisionVerticalEdge, gridEndpoint,
        hgridZero, twoSelect, xStarFaceXQEdge, faceXQEdge,
        transposePresentation, transposeTannerSquareData,
        hface, hownerQ, hq]
    all_goals
      change P.faceQ ((transposeXStarFaceEquiv P z).symm
        (rzInputZBoundaryFaceOwner P A4 z edge).1.1).1 _ = q
      rw [hface]
      exact hownerQ.trans hq

/-- A lifted old X vertex remains in the successor X constructor, so the Q
decoder returns none. -/
private theorem rzOriginalCentralQTag_lift_x
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two) (x : P.X)
    (member : zStarBoundaryVertexMember P z (Vertex.x x) = true) :
    rzOriginalCentralBoundaryQTag P A4.toTannerSquareAdmissible S
      (rzOriginalCentralBoundaryVertexLift P A4 S z copy
        ⟨Vertex.x x, member⟩).1 = none := by
  unfold rzOriginalCentralBoundaryVertexLift
  generalize howned :
      A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.zBoundaryIncidentEdge
        z ⟨Vertex.x x, member⟩ = owned
  rcases owned with ⟨⟨edge, endpoint⟩, hendpoint⟩
  dsimp only
  fin_cases endpoint
  · change rzOriginalCentralBoundaryQTag P A4.toTannerSquareAdmissible S
      (rzOriginalCentralBoundaryEdgeVertex P A4 S z copy edge 0).1 = none
    change rzOriginalCentralBoundaryQTag P A4.toTannerSquareAdmissible S
      (zBoundaryEdgeStart (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S)
        (rzOriginalCentralZVertex P S z copy)
        (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S)
          (rzOriginalCentralZVertex P S z copy)
          (rzOriginalCentralOwnerLocalZStarFace P A4 S z copy edge) 0)).1 = none
    exact congrArg (rzOriginalCentralBoundaryQTag P
      A4.toTannerSquareAdmissible S)
      (rzZStarFaceBoundaryEdge_start_value
        (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
        (rzOriginalCentralZVertex P S z copy)
        (rzOriginalCentralOwnerLocalZStarFace P A4 S z copy edge) 0)
  · change BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart P z) (zBoundaryEdgeEnd P z) edge 1 =
      ⟨Vertex.x x, member⟩ at hendpoint
    have hvalue := congrArg Subtype.val hendpoint
    simp only [BDL26TannerLocalRegularity.edgeEndpoint_one] at hvalue
    rw [rzInputZBoundaryEdge_end_value] at hvalue
    cases hvalue

/-- A structurally decoded central successor X tag is an old Z-boundary X. -/
private theorem rzOriginalCentralXTag_member
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (z : P.Z) (copy : Two) (newX : RZX P S)
    (member : zStarBoundaryVertexMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S)
      (rzOriginalCentralZVertex P S z copy) (Vertex.x newX) = true)
    (x : P.X) (htag : rzOriginalCentralXTag P S newX = some x) :
    zStarBoundaryVertexMember P z (Vertex.x x) = true := by
  obtain ⟨oldVertex, himage⟩ :=
    rzOriginalCentralBoundaryVertexLift_surjective P A4 R S z copy
      ⟨Vertex.x newX, member⟩
  rcases oldVertex with ⟨oldValue, oldMember⟩
  rcases oldValue with oldX | oldQ | impossible
  · have hraw := congrArg Subtype.val himage
    have hbase := congrArg
      (rzOriginalCentralBoundaryXTag P A4.toTannerSquareAdmissible S) hraw
    change _ = rzOriginalCentralXTag P S newX at hbase
    rw [htag] at hbase
    rw [rzOriginalCentralXTag_lift P A4 S z copy oldX oldMember] at hbase
    exact (Option.some.inj hbase) ▸ oldMember
  · have hraw := congrArg Subtype.val himage
    have hbase := congrArg
      (rzOriginalCentralBoundaryXTag P A4.toTannerSquareAdmissible S) hraw
    change _ = rzOriginalCentralXTag P S newX at hbase
    rw [htag] at hbase
    rw [rzOriginalCentralXTag_lift_q P A4 S z copy oldQ oldMember] at hbase
    cases hbase
  · simp [zStarBoundaryVertexMember] at oldMember

/-- A structurally decoded central successor Q tag is an old Z-boundary Q. -/
private theorem rzOriginalCentralQTag_member
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (z : P.Z) (copy : Two) (newQ : RZQ P S)
    (member : zStarBoundaryVertexMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S)
      (rzOriginalCentralZVertex P S z copy) (Vertex.q newQ) = true)
    (q : P.Q) (htag : rzOriginalCentralQTag P S newQ = some q) :
    zStarBoundaryVertexMember P z (Vertex.q q) = true := by
  obtain ⟨oldVertex, himage⟩ :=
    rzOriginalCentralBoundaryVertexLift_surjective P A4 R S z copy
      ⟨Vertex.q newQ, member⟩
  rcases oldVertex with ⟨oldValue, oldMember⟩
  rcases oldValue with oldX | oldQ | impossible
  · have hraw := congrArg Subtype.val himage
    have hbase := congrArg
      (rzOriginalCentralBoundaryQTag P A4.toTannerSquareAdmissible S) hraw
    change _ = rzOriginalCentralQTag P S newQ at hbase
    rw [htag] at hbase
    rw [rzOriginalCentralQTag_lift_x P A4 S z copy oldX oldMember] at hbase
    cases hbase
  · have hraw := congrArg Subtype.val himage
    have hbase := congrArg
      (rzOriginalCentralBoundaryQTag P A4.toTannerSquareAdmissible S) hraw
    change _ = rzOriginalCentralQTag P S newQ at hbase
    rw [htag] at hbase
    rw [rzOriginalCentralQTag_lift P A4 S z copy oldQ oldMember] at hbase
    exact (Option.some.inj hbase) ▸ oldMember
  · simp [zStarBoundaryVertexMember] at oldMember

/-- Re-embedding a structurally decoded central X tag returns the supplied
successor boundary vertex. -/
private theorem rzOriginalCentralXTag_image
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (z : P.Z) (copy : Two) (newX : RZX P S)
    (member : zStarBoundaryVertexMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S)
      (rzOriginalCentralZVertex P S z copy) (Vertex.x newX) = true)
    (x : P.X) (htag : rzOriginalCentralXTag P S newX = some x)
    (xMember : zStarBoundaryVertexMember P z (Vertex.x x) = true) :
    rzOriginalCentralBoundaryVertexLift P A4 S z copy
        ⟨Vertex.x x, xMember⟩ = ⟨Vertex.x newX, member⟩ := by
  obtain ⟨oldVertex, himage⟩ :=
    rzOriginalCentralBoundaryVertexLift_surjective P A4 R S z copy
      ⟨Vertex.x newX, member⟩
  rcases oldVertex with ⟨oldValue, oldMember⟩
  rcases oldValue with oldX | oldQ | impossible
  · have hraw := congrArg Subtype.val himage
    have hbase := congrArg
      (rzOriginalCentralBoundaryXTag P A4.toTannerSquareAdmissible S) hraw
    change _ = rzOriginalCentralXTag P S newX at hbase
    rw [htag] at hbase
    rw [rzOriginalCentralXTag_lift P A4 S z copy oldX oldMember] at hbase
    have holdX : oldX = x := Option.some.inj hbase
    subst oldX
    have hold : (⟨Vertex.x x, oldMember⟩ : ZStarBoundaryVertex P z) =
        ⟨Vertex.x x, xMember⟩ := by
      rfl
    exact hold ▸ himage
  · have hraw := congrArg Subtype.val himage
    have hbase := congrArg
      (rzOriginalCentralBoundaryXTag P A4.toTannerSquareAdmissible S) hraw
    change _ = rzOriginalCentralXTag P S newX at hbase
    rw [htag] at hbase
    rw [rzOriginalCentralXTag_lift_q P A4 S z copy oldQ oldMember] at hbase
    cases hbase
  · simp [zStarBoundaryVertexMember] at oldMember

/-- Re-embedding a structurally decoded central Q tag returns the supplied
successor boundary vertex. -/
private theorem rzOriginalCentralQTag_image
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (z : P.Z) (copy : Two) (newQ : RZQ P S)
    (member : zStarBoundaryVertexMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S)
      (rzOriginalCentralZVertex P S z copy) (Vertex.q newQ) = true)
    (q : P.Q) (htag : rzOriginalCentralQTag P S newQ = some q)
    (qMember : zStarBoundaryVertexMember P z (Vertex.q q) = true) :
    rzOriginalCentralBoundaryVertexLift P A4 S z copy
        ⟨Vertex.q q, qMember⟩ = ⟨Vertex.q newQ, member⟩ := by
  obtain ⟨oldVertex, himage⟩ :=
    rzOriginalCentralBoundaryVertexLift_surjective P A4 R S z copy
      ⟨Vertex.q newQ, member⟩
  rcases oldVertex with ⟨oldValue, oldMember⟩
  rcases oldValue with oldX | oldQ | impossible
  · have hraw := congrArg Subtype.val himage
    have hbase := congrArg
      (rzOriginalCentralBoundaryQTag P A4.toTannerSquareAdmissible S) hraw
    change _ = rzOriginalCentralQTag P S newQ at hbase
    rw [htag] at hbase
    rw [rzOriginalCentralQTag_lift_x P A4 S z copy oldX oldMember] at hbase
    cases hbase
  · have hraw := congrArg Subtype.val himage
    have hbase := congrArg
      (rzOriginalCentralBoundaryQTag P A4.toTannerSquareAdmissible S) hraw
    change _ = rzOriginalCentralQTag P S newQ at hbase
    rw [htag] at hbase
    rw [rzOriginalCentralQTag_lift P A4 S z copy oldQ oldMember] at hbase
    have holdQ : oldQ = q := Option.some.inj hbase
    subst oldQ
    have hold : (⟨Vertex.q q, oldMember⟩ : ZStarBoundaryVertex P z) =
        ⟨Vertex.q q, qMember⟩ := by
      rfl
    exact hold ▸ himage
  · simp [zStarBoundaryVertexMember] at oldMember

/-- Every successor X boundary constructor at the original center carries an
old X tag.  This uses surjectivity only propositionally. -/
private theorem rzOriginalCentralXTag_ne_none
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (z : P.Z) (copy : Two) (newX : RZX P S)
    (member : zStarBoundaryVertexMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S)
      (rzOriginalCentralZVertex P S z copy) (Vertex.x newX) = true) :
    rzOriginalCentralXTag P S newX ≠ none := by
  intro hnone
  obtain ⟨oldVertex, himage⟩ :=
    rzOriginalCentralBoundaryVertexLift_surjective P A4 R S z copy
      ⟨Vertex.x newX, member⟩
  rcases oldVertex with ⟨oldValue, oldMember⟩
  rcases oldValue with oldX | oldQ | impossible
  · have hraw := congrArg Subtype.val himage
    have hbase := congrArg
      (rzOriginalCentralBoundaryXTag P A4.toTannerSquareAdmissible S) hraw
    change _ = rzOriginalCentralXTag P S newX at hbase
    rw [hnone] at hbase
    rw [rzOriginalCentralXTag_lift P A4 S z copy oldX oldMember] at hbase
    cases hbase
  · have hraw := congrArg Subtype.val himage
    have hbase := congrArg
      (rzOriginalCentralBoundaryQTag P A4.toTannerSquareAdmissible S) hraw
    change _ = none at hbase
    rw [rzOriginalCentralQTag_lift P A4 S z copy oldQ oldMember] at hbase
    cases hbase
  · simp [zStarBoundaryVertexMember] at oldMember

/-- Every successor Q boundary constructor at the original center carries an
old Q tag.  This uses surjectivity only propositionally. -/
private theorem rzOriginalCentralQTag_ne_none
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (z : P.Z) (copy : Two) (newQ : RZQ P S)
    (member : zStarBoundaryVertexMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S)
      (rzOriginalCentralZVertex P S z copy) (Vertex.q newQ) = true) :
    rzOriginalCentralQTag P S newQ ≠ none := by
  intro hnone
  obtain ⟨oldVertex, himage⟩ :=
    rzOriginalCentralBoundaryVertexLift_surjective P A4 R S z copy
      ⟨Vertex.q newQ, member⟩
  rcases oldVertex with ⟨oldValue, oldMember⟩
  rcases oldValue with oldX | oldQ | impossible
  · have hraw := congrArg Subtype.val himage
    have hbase := congrArg
      (rzOriginalCentralBoundaryXTag P A4.toTannerSquareAdmissible S) hraw
    change _ = none at hbase
    rw [rzOriginalCentralXTag_lift P A4 S z copy oldX oldMember] at hbase
    cases hbase
  · have hraw := congrArg Subtype.val himage
    have hbase := congrArg
      (rzOriginalCentralBoundaryQTag P A4.toTannerSquareAdmissible S) hraw
    change _ = rzOriginalCentralQTag P S newQ at hbase
    rw [hnone] at hbase
    rw [rzOriginalCentralQTag_lift P A4 S z copy oldQ oldMember] at hbase
    cases hbase
  · simp [zStarBoundaryVertexMember] at oldMember

/-- Replace every old Z-boundary edge in a historical path by its explicit
owner-face path in the original-central successor sector. -/
private noncomputable def rzOriginalCentralBoundaryPathLift
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (z : P.Z) (copy : Two) {root target : ZStarBoundaryVertex P z}
    (path : UndirectedPath (zBoundaryEdgeStart P z) (zBoundaryEdgeEnd P z)
      root target) :
    UndirectedPath
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        (rzOriginalCentralZVertex P S z copy))
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        (rzOriginalCentralZVertex P S z copy))
      (rzOriginalCentralBoundaryVertexLift P A4 S z copy root)
      (rzOriginalCentralBoundaryVertexLift P A4 S z copy target) := by
  induction path with
  | nil => exact .nil
  | @step u v oldPath edge connects ih =>
      let edgePath := rzOriginalCentralBoundaryEdgePath P A4 S z copy edge
      by_cases hforward : zBoundaryEdgeStart P z edge = u
      · have hend : zBoundaryEdgeEnd P z edge = v := by
          rcases connects with connects | connects
          · exact connects.2
          · have huv : u = v := hforward.symm.trans connects.1
            exact connects.2.trans huv
        have hu := rzOriginalCentralBoundaryVertexLift_eq_edgeVertex
          P A4 R S z copy u edge 0 (by
            simpa only [BDL26TannerLocalRegularity.edgeEndpoint_zero] using
              hforward)
        have hv := rzOriginalCentralBoundaryVertexLift_eq_edgeVertex
          P A4 R S z copy v edge 1 (by
            simpa only [BDL26TannerLocalRegularity.edgeEndpoint_one] using
              hend)
        exact (hu ▸ ih).append (hv.symm ▸ edgePath)
      · have hreverse : zBoundaryEdgeStart P z edge = v ∧
            zBoundaryEdgeEnd P z edge = u := by
          rcases connects with connects | connects
          · exact False.elim (hforward connects.1)
          · exact connects
        have hu := rzOriginalCentralBoundaryVertexLift_eq_edgeVertex
          P A4 R S z copy u edge 1 (by
            simpa only [BDL26TannerLocalRegularity.edgeEndpoint_one] using
              hreverse.2)
        have hv := rzOriginalCentralBoundaryVertexLift_eq_edgeVertex
          P A4 R S z copy v edge 0 (by
            simpa only [BDL26TannerLocalRegularity.edgeEndpoint_zero] using
              hreverse.1)
        exact (hu ▸ ih).append (hv.symm ▸ edgePath.reverse)

/-- Historical input connectedness, lifted edge-by-edge to one copy of the
original-central successor Z sector. -/
private noncomputable def rzOriginalCentralHistoricalBoundaryPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (z : P.Z) (copy : Two) (vertex : ZStarBoundaryVertex P z) :
    UndirectedPath
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        (rzOriginalCentralZVertex P S z copy))
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        (rzOriginalCentralZVertex P S z copy))
      (rzOriginalCentralBoundaryVertexLift P A4 S z copy
        (A4.toTannerSquareAdmissible.zBoundaryRoot z))
      (rzOriginalCentralBoundaryVertexLift P A4 S z copy vertex) :=
  rzOriginalCentralBoundaryPathLift P A4 R S z copy
    (A4.toTannerSquareAdmissible.zBoundaryPath z vertex)

/-- The transposed input V2 incident edge selected at the transposed
historical boundary root. -/
private noncomputable def rzOriginalCentralAnchorIncident
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (z : P.Z) :
    {owned : XStarBoundaryEdge (transposePresentation P) z × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (xBoundaryEdgeStart (transposePresentation P) z)
        (xBoundaryEdgeEnd (transposePresentation P) z)
        owned.1 owned.2 =
          (transposeTannerSquareAdmissible P
            A4.toTannerSquareAdmissible).xBoundaryRoot z} :=
  (transposeTannerSquareAdmissibleV3 P
    A4.toTannerSquareAdmissibleV3).xBoundaryIncidentEdge z
      ((transposeTannerSquareAdmissibleV3 P
        A4.toTannerSquareAdmissibleV3).xBoundaryRoot z)

/-- The transposed radial anchor retains exactly the Q endpoint of the input
boundary edge selected at the historical Z root. -/
private theorem rzOriginalCentralAnchorRadialEdge_end_value
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (z : P.Z) :
    (xStarEdgeEnd (transposePresentation P) z
      (xStarAnchorRadialEdge (transposePresentation P)
        (transposeTannerSquareAdmissibleV3 P
          A4.toTannerSquareAdmissibleV3) z).1).1 =
      (xBoundaryEdgeStart (transposePresentation P) z
        (rzOriginalCentralAnchorIncident P A4 z).1.1).1 := by
  unfold xStarAnchorRadialEdge rzOriginalCentralAnchorIncident
  generalize hinput :
      (transposeTannerSquareAdmissibleV3 P
        A4.toTannerSquareAdmissibleV3).toTannerSquareAdmissibleV2.2 z
          ((transposeTannerSquareAdmissibleV3 P
            A4.toTannerSquareAdmissibleV3).xBoundaryRoot z) = input
  rcases input with ⟨⟨boundary, endpoint⟩, hendpoint⟩
  rcases boundary with ⟨raw, member⟩
  rcases raw with impossible | qz
  · simp [xStarBoundaryEdgeMember] at member
  · simp [xStarAnchorRadialEdgeFromBoundary, xStarEdgeEnd,
      xBoundaryEdgeStart]

/-- The historical old Z-boundary edge corresponding to the transposed V2
incident edge at the anchor root. -/
private noncomputable def rzOriginalCentralAnchorBoundaryEdge
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (z : P.Z) : ZStarBoundaryEdge P z :=
  transposeXStarBoundaryEdgeEquiv P z
    (rzOriginalCentralAnchorIncident P A4 z).1.1

/-- Transposition preserves the Q tag shared by the historical boundary edge
and the radial anchor constructed from it. -/
private theorem rzOriginalCentralAnchorQ_eq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (z : P.Z) :
    (xStarEdgeEnd (transposePresentation P) z
      (xStarAnchorRadialEdge (transposePresentation P)
        (transposeTannerSquareAdmissibleV3 P
          A4.toTannerSquareAdmissibleV3) z).1).1 =
      (transposeVertexEquiv P).symm
        (Vertex.q (rzInputZBoundaryXQEdge P z
          (rzOriginalCentralAnchorBoundaryEdge P A4 z)).1.2) := by
  have hanchor := rzOriginalCentralAnchorRadialEdge_end_value P A4 z
  have htranspose := congrArg Subtype.val
    (transpose_xBoundaryEdgeStart P z
      (rzOriginalCentralAnchorIncident P A4 z).1.1)
  have hend := rzInputZBoundaryEdge_end_value P z
    (rzOriginalCentralAnchorBoundaryEdge P A4 z)
  have htranspose' :
      (xBoundaryEdgeStart (transposePresentation P) z
        (rzOriginalCentralAnchorIncident P A4 z).1.1).1 =
      (transposeVertexEquiv P).symm
        (zBoundaryEdgeEnd P z
          (rzOriginalCentralAnchorBoundaryEdge P A4 z)).1 := by
    apply (transposeVertexEquiv P).injective
    rw [Equiv.apply_symm_apply]
    exact htranspose
  exact hanchor.trans (htranspose'.trans
    (congrArg (transposeVertexEquiv P).symm hend))

/-- The V4 owner of the historical anchor boundary edge selects the same
transposed radial edge as the deterministic successor-root anchor. -/
private theorem rzOriginalCentralAnchorOwnerRadialEdge_eq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (z : P.Z) :
    xStarFaceXQEdge (transposePresentation P) z
        ((transposeXStarFaceEquiv P z).symm
          (rzInputZBoundaryFaceOwner P A4 z
            (rzOriginalCentralAnchorBoundaryEdge P A4 z)).1.1)
        (rzInputZBoundaryFaceOwner P A4 z
          (rzOriginalCentralAnchorBoundaryEdge P A4 z)).1.2 =
      (xStarAnchorRadialEdge (transposePresentation P)
        (transposeTannerSquareAdmissibleV3 P
          A4.toTannerSquareAdmissibleV3) z).1 := by
  generalize hanchor : xStarAnchorRadialEdge (transposePresentation P)
    (transposeTannerSquareAdmissibleV3 P
      A4.toTannerSquareAdmissibleV3) z = anchor
  rcases anchor with ⟨⟨radial | impossible, member⟩, hstart⟩
  · apply Subtype.ext
    apply congrArg Sum.inl
    apply Subtype.ext
    apply Prod.ext
    · have hfaceX :
          (transposePresentation P).faceX
            ((transposeXStarFaceEquiv P z).symm
              (rzInputZBoundaryFaceOwner P A4 z
                (rzOriginalCentralAnchorBoundaryEdge P A4 z)).1.1).1 = z := by
        simpa [xStarFaceMember] using
          ((transposeXStarFaceEquiv P z).symm
            (rzInputZBoundaryFaceOwner P A4 z
              (rzOriginalCentralAnchorBoundaryEdge P A4 z)).1.1).2
      have hradialX : radial.1.1 = z := by
        simpa [xStarEdgeStart] using Vertex.x.inj hstart
      exact hfaceX.trans hradialX.symm
    · have hq := rzOriginalCentralAnchorQ_eq P A4 z
      rw [hanchor] at hq
      have hradialQ : radial.1.2 =
          (rzInputZBoundaryXQEdge P z
            (rzOriginalCentralAnchorBoundaryEdge P A4 z)).1.2 := by
        simpa [xStarEdgeEnd, transposeVertexEquiv] using Vertex.q.inj hq
      have howner :
          (transposePresentation P).faceQ
            ((transposeXStarFaceEquiv P z).symm
              (rzInputZBoundaryFaceOwner P A4 z
                (rzOriginalCentralAnchorBoundaryEdge P A4 z)).1.1).1
            (rzInputZBoundaryFaceOwner P A4 z
              (rzOriginalCentralAnchorBoundaryEdge P A4 z)).1.2 =
          (rzInputZBoundaryXQEdge P z
            (rzOriginalCentralAnchorBoundaryEdge P A4 z)).1.2 := by
        exact rzInputZBoundaryOwner_faceQ P A4 z
          (rzOriginalCentralAnchorBoundaryEdge P A4 z)
      exact howner.trans hradialQ.symm
  · change Vertex.q impossible.1.1 = Vertex.x z at hstart
    cases hstart

/-- At an original-central successor Z vertex, the deterministic incident edge
is the first segment of the transposed historical anchor radial edge. -/
private theorem rzOriginalCentralRootIncidentEdge_eq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two) :
    (doubleCylinderVertexIncidentEdge (transposePresentation P)
      (transposeTannerSquareAdmissibleV3 P
        A4.toTannerSquareAdmissibleV3) z S
      (rzOriginalCentralZVertex P S z copy).2).1.1 =
      Sum.inl (copy, Sum.inl
        ((xStarAnchorRadialEdge (transposePresentation P)
          (transposeTannerSquareAdmissibleV3 P
            A4.toTannerSquareAdmissibleV3) z).1,
          rzRadialGridZero S)) := by
  simp [doubleCylinderVertexIncidentEdge, subdivisionVertexIncidentEdge,
    rzOriginalCentralZVertex]
  apply Fin.ext
  rfl

/-- The underlying value of the deterministic successor Z-boundary root is
the local-face X tag retained by the explicitly selected incident-edge owner. -/
private theorem rzReplacementZBoundaryRoot_value
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (z : P.Z) (vertex : ZDoubleCylinderVertex P z S) :
    (rzReplacementZBoundaryRoot P A3 S ⟨z, vertex⟩).1 =
      Vertex.x (Sum.inl (Sum.inl ⟨z,
        (doubleCylinderEdgeFaceSlotOwner (transposePresentation P)
          (transposeTannerSquareAdmissibleV3 P A3) z S
          (doubleCylinderVertexIncidentEdge (transposePresentation P)
            (transposeTannerSquareAdmissibleV3 P A3) z S vertex).1.1).1.1⟩)) := by
  classical
  generalize hincident : doubleCylinderVertexIncidentEdge
    (transposePresentation P) (transposeTannerSquareAdmissibleV3 P A3)
    z S vertex = incident
  rcases incident with ⟨⟨edge, endpoint⟩, hendpoint⟩
  generalize howner : doubleCylinderEdgeFaceSlotOwner
    (transposePresentation P) (transposeTannerSquareAdmissibleV3 P A3)
    z S edge = owner
  rcases owner with ⟨⟨face, slot⟩, hedge⟩
  simp only [rzReplacementZBoundaryRoot]
  rw [hincident, howner]

/-- The deterministic root is exactly the X endpoint of its packaged local
root face. -/
private theorem rzReplacementZBoundaryRoot_eq_rootFaceX
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale)
    (z : (rzReplacementPresentation P
      A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S).Z) :
    rzReplacementZBoundaryRoot P A3 S z =
      zBoundaryEdgeStart
        (rzReplacementPresentation P
          A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S) z
        (rzZStarFaceBoundaryEdge
          (rzReplacementPresentation P
            A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S) z
          (rzReplacementZBoundaryRootFace P A3 S z) 0) := by
  rcases z with ⟨z, vertex⟩
  apply Subtype.ext
  erw [rzReplacementZBoundaryRoot_value]

/-- Reach either ordered Q corner of the packaged deterministic root face. -/
private noncomputable def rzReplacementZBoundaryRootPathToQ
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale)
    (z : (rzReplacementPresentation P
      A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S).Z)
    (corner : Two) :
    UndirectedPath
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S) z)
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S) z)
      (rzReplacementZBoundaryRoot P A3 S z)
      (zBoundaryEdgeEnd (rzReplacementPresentation P
          A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S) z
        (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
            A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S) z
          (rzReplacementZBoundaryRootFace P A3 S z) corner)) := by
  rw [rzReplacementZBoundaryRoot_eq_rootFaceX]
  exact (rzZStarFaceBoundaryPathToX
      (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S) z
      (rzReplacementZBoundaryRootFace P A3 S z)).reverse.append
    (rzZStarFaceBoundaryPathToQ
      (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S) z
      (rzReplacementZBoundaryRootFace P A3 S z) corner)

/-- The selected root Q vertex is the boundary Q corner of the V4 owner cell. -/
private theorem rzOriginalQRootQ_eq_ownerBoundaryQ
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two) (q : P.Q)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true) :
    zBoundaryEdgeEnd (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
      (rzOriginalQZVertex P S z copy q member)
      (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S)
        (rzOriginalQZVertex P S z copy q member)
        (rzReplacementZBoundaryRootFace P
          A4.toTannerSquareAdmissibleV3 S
          (rzOriginalQZVertex P S z copy q member))
        (rzReplacementZBoundaryRootCorner P
          A4.toTannerSquareAdmissibleV3 S
          (rzOriginalQZVertex P S z copy q member))) =
      zBoundaryEdgeEnd (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S)
        (rzOriginalQZVertex P S z copy q member)
        (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S)
          (rzOriginalQZVertex P S z copy q member)
          (rzOriginalQOwnerZStarFace P A4 S z copy q member)
          (rzOriginalQBoundaryCorner P A4 z q member)) := by
  apply Subtype.ext
  erw [rzZStarFaceBoundaryEdge_end_value,
    rzZStarFaceBoundaryEdge_end_value]
  exact congrArg Vertex.q
    (rzOriginalQRootFaceQ_eq_ownerBoundaryQ P A4 S z copy q member)

/-- Reach the common radial Q hub of the original-Q owner sector from the
deterministic successor Z-boundary root. -/
private noncomputable def rzOriginalQRootToOwnerHubPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two) (q : P.Q)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true) :
    UndirectedPath
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalQZVertex P S z copy q member))
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalQZVertex P S z copy q member))
      (rzReplacementZBoundaryRoot P A4.toTannerSquareAdmissibleV3 S
        (rzOriginalQZVertex P S z copy q member))
      (zBoundaryEdgeEnd (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S)
        (rzOriginalQZVertex P S z copy q member)
        (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S)
          (rzOriginalQZVertex P S z copy q member)
          (rzOriginalQOwnerZStarFace P A4 S z copy q member)
          (rzOriginalQOwnerCorner P A4 z q member))) := by
  let fixedZ := rzOriginalQZVertex P S z copy q member
  let successor := rzReplacementPresentation P
    A4.toTannerSquareAdmissible S
  let ownerFace := rzOriginalQOwnerZStarFace P A4 S z copy q member
  let rootToQ := rzReplacementZBoundaryRootPathToQ P
    A4.toTannerSquareAdmissibleV3 S fixedZ
    (rzReplacementZBoundaryRootCorner P
      A4.toTannerSquareAdmissibleV3 S fixedZ)
  let ownerBridge :=
    (rzZStarFaceBoundaryPathToQ successor fixedZ ownerFace
      (rzOriginalQBoundaryCorner P A4 z q member)).reverse.append
    (rzZStarFaceBoundaryPathToQ successor fixedZ ownerFace
      (rzOriginalQOwnerCorner P A4 z q member))
  have hrootQ := rzOriginalQRootQ_eq_ownerBoundaryQ
    P A4 S z copy q member
  exact rootToQ.append (hrootQ.symm ▸ ownerBridge)

private noncomputable def rzOriginalZBoundaryCorner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (z : P.Z) (x : P.X)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.z x) = true) : Two :=
  twoSelect 1 0 (rzOriginalZOwnerCorner P A4 z x member)

/-- The endpoint-one root segment is the selected boundary edge of the
outer owner cell. -/
private theorem rzOriginalZRootFaceQ_eq_ownerBoundaryQ
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two) (x : P.X)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.z x) = true) :
    (rzReplacementPresentation P A4.toTannerSquareAdmissible S).faceQ
        (rzReplacementZBoundaryRootFace P
          A4.toTannerSquareAdmissibleV3 S
          (rzOriginalZZVertex P S z copy x member)).1
        (rzReplacementZBoundaryRootCorner P
          A4.toTannerSquareAdmissibleV3 S
          (rzOriginalZZVertex P S z copy x member)) =
      (rzReplacementPresentation P A4.toTannerSquareAdmissible S).faceQ
        (rzOriginalZOwnerZStarFace P A4 S z copy x member).1
        (rzOriginalZBoundaryCorner P A4 z x member) := by
  erw [rzReplacementZBoundaryRootFaceQ_eq_incidentEdge]
  change Sum.inl (⟨z,
      (doubleCylinderVertexIncidentEdge (transposePresentation P)
        (transposeTannerSquareAdmissibleV3 P
          A4.toTannerSquareAdmissibleV3) z S
        (rzOriginalZZVertex P S z copy x member).2).1.1⟩ :
      Sigma fun oldZ : P.Z => ZDoubleCylinderEdge P oldZ S) = _
  rw [rzOriginalZRootIncidentEdge_eq]
  change Sum.inl (⟨z, Sum.inl (copy, Sum.inl
      (xStarFaceQZEdge (transposePresentation P) z
        (rzOriginalZOwnerFace P A4 z x member)
        (rzOriginalZOwnerCorner P A4 z x member), lastHalfSegment S))⟩ :
      Sigma fun oldZ : P.Z => ZDoubleCylinderEdge P oldZ S) =
    twoSelect
      (localFaceQ0 P S ⟨z,
        rzOriginalZOwnerCell P A4 S z copy x member, (1, 1)⟩)
      (localFaceQ1 P S ⟨z,
        rzOriginalZOwnerCell P A4 S z copy x member, (1, 1)⟩)
      (rzOriginalZBoundaryCorner P A4 z x member)
  have hlast : S.half - 1 + 1 = S.half := by
    have := S.half_pos
    omega
  generalize hc : rzOriginalZOwnerCorner P A4 z x member = c
  fin_cases c <;>
    simp [rzOriginalZOwnerZStarFace, rzOriginalZOwnerCell,
      rzOriginalZBoundaryCorner, hc, rzReplacementPresentation,
      rzReplacementData, rzFaceQ, localFaceQ0, localFaceQ1,
      lastHalfSegment, rzRadialGridZero, subdivisionOriginalBoundaryEdge,
      twoSelect, gridEndpoint, lowerGridIndex, upperGridIndex,
      subdivisionVerticalEdge, subdivisionHorizontalEdge,
      hlast, S.half_pos.ne']

private theorem rzOriginalZRootQ_eq_ownerBoundaryQ
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two) (x : P.X)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.z x) = true) :
    zBoundaryEdgeEnd (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
      (rzOriginalZZVertex P S z copy x member)
      (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S)
        (rzOriginalZZVertex P S z copy x member)
        (rzReplacementZBoundaryRootFace P A4.toTannerSquareAdmissibleV3 S
          (rzOriginalZZVertex P S z copy x member))
        (rzReplacementZBoundaryRootCorner P A4.toTannerSquareAdmissibleV3 S
          (rzOriginalZZVertex P S z copy x member))) =
      zBoundaryEdgeEnd (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S)
        (rzOriginalZZVertex P S z copy x member)
        (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S)
          (rzOriginalZZVertex P S z copy x member)
          (rzOriginalZOwnerZStarFace P A4 S z copy x member)
          (rzOriginalZBoundaryCorner P A4 z x member)) := by
  apply Subtype.ext
  erw [rzZStarFaceBoundaryEdge_end_value,
    rzZStarFaceBoundaryEdge_end_value]
  exact congrArg Vertex.q
    (rzOriginalZRootFaceQ_eq_ownerBoundaryQ P A4 S z copy x member)

/-- Reach the X tag of the canonical outer owner cell from the deterministic
endpoint-one root. -/
private noncomputable def rzOriginalZRootToOwnerXPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two) (x : P.X)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.z x) = true) :
    UndirectedPath
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalZZVertex P S z copy x member))
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalZZVertex P S z copy x member))
      (rzReplacementZBoundaryRoot P A4.toTannerSquareAdmissibleV3 S
        (rzOriginalZZVertex P S z copy x member))
      (zBoundaryEdgeStart (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S)
        (rzOriginalZZVertex P S z copy x member)
        (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S)
          (rzOriginalZZVertex P S z copy x member)
          (rzOriginalZOwnerZStarFace P A4 S z copy x member) 0)) := by
  let successor := rzReplacementPresentation P A4.toTannerSquareAdmissible S
  let fixedZ := rzOriginalZZVertex P S z copy x member
  let ownerFace := rzOriginalZOwnerZStarFace P A4 S z copy x member
  let rootToQ := rzReplacementZBoundaryRootPathToQ P
    A4.toTannerSquareAdmissibleV3 S fixedZ
    (rzReplacementZBoundaryRootCorner P A4.toTannerSquareAdmissibleV3 S
      fixedZ)
  let last := (rzZStarFaceBoundaryPathToQ successor fixedZ ownerFace
      (rzOriginalZBoundaryCorner P A4 z x member)).reverse.append
    (rzZStarFaceBoundaryPathToX successor fixedZ ownerFace)
  have hrootQ := rzOriginalZRootQ_eq_ownerBoundaryQ
    P A4 S z copy x member
  exact rootToQ.append (hrootQ.symm ▸ last)

private theorem rzOriginalZOwnerFace_x
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (z : P.Z) (x : P.X)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.z x) = true) :
    (transposePresentation P).faceZ
      (rzOriginalZOwnerFace P A4 z x member).1 = x := by
  let incident := (transposeTannerSquareAdmissibleV2 P
    A4.toTannerSquareAdmissibleV2).xBoundaryIncidentEdge z
      (rzOriginalZTransposedBoundaryVertex P z x member)
  have hbit := rzOriginalZTransposeIncident_bit P A4 z x member
  have hendpoint := incident.2
  change incident.1.2 = 1 at hbit
  rw [hbit, BDL26TannerLocalRegularity.edgeEndpoint_one] at hendpoint
  have hend := congrArg
    (xStarBoundaryVertexToStar (transposePresentation P) z) hendpoint
  erw [xBoundaryEdgeEnd_toStar] at hend
  have hedge := rzOriginalZTransposeIncident_edge P A4 z x member
  change xStarBoundaryEdgeToStar (transposePresentation P) z
    incident.1.1 = _ at hedge
  rw [hedge] at hend
  exact Vertex.z.inj (congrArg Subtype.val hend)

/-- Cellular regularity identifies every transposed face over the same
original X/Z pair with the deterministic original-Z owner face. -/
private theorem rzOriginalZFace_eq_owner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (z : P.Z) (x : P.X)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.z x) = true)
    (face : XStarFace (transposePresentation P) z)
    (hfaceX : (transposePresentation P).faceZ face.1 = x) :
    face = rzOriginalZOwnerFace P A4 z x member := by
  apply Subtype.ext
  apply R.faceXZ_injective
  apply Prod.ext
  · exact hfaceX.trans (rzOriginalZOwnerFace_x P A4 z x member).symm
  · have hzFace : (transposePresentation P).faceX face.1 = z := by
      simpa [xStarFaceMember] using face.2
    have hzOwner : (transposePresentation P).faceX
        (rzOriginalZOwnerFace P A4 z x member).1 = z := by
      simpa [xStarFaceMember] using
        (rzOriginalZOwnerFace P A4 z x member).2
    exact hzFace.trans hzOwner.symm

private noncomputable def rzOriginalZTargetZStarFace
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two) (x : P.X)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.z x) = true)
    (cell : ZDoubleCylinderFace P z S) (bits : Two × Two)
    (hcorner : localCornerVertex P z S cell bits =
      (copy, Sum.inl ⟨Vertex.z x, member⟩)) :
    ZStarFace (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
      (rzOriginalZZVertex P S z copy x member) :=
  ⟨Sum.inl ⟨z, cell, bits⟩, by
    simp only [zStarFaceMember, decide_eq_true_eq]
    change localFaceZ P S ⟨z, cell, bits⟩ =
      rzOriginalZZVertex P S z copy x member
    rw [localFaceZ_eq_corner]
    exact Sigma.ext rfl (heq_of_eq hcorner)⟩

private theorem rzOriginalZCopyFace_eq_owner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (z : P.Z) (copy : Two) (x : P.X)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.z x) = true)
    (candidateCopy : Two) (face : XStarFace (transposePresentation P) z)
    (a b : Fin S.half) (bits : Two × Two)
    (hcorner : localCornerVertex P z S
      (Sum.inl (candidateCopy, face, a, b)) bits =
        (copy, Sum.inl ⟨Vertex.z x, member⟩)) :
    Sum.inl (candidateCopy, face, a, b) =
        rzOriginalZOwnerCell P A4 S z copy x member ∧ bits = (1, 1) := by
  have hcopy : candidateCopy = copy := congrArg Prod.fst hcorner
  have hgrid : subdivisionGridVertex (transposePresentation P) z S face
      (gridEndpoint a bits.1) (gridEndpoint b bits.2) =
        Sum.inl ⟨Vertex.z x, member⟩ := congrArg Prod.snd hcorner
  obtain ⟨hfaceX, hu, hv⟩ := rzSubdivisionGridVertex_eq_originalZ_coordinates
    P S z face (gridEndpoint a bits.1) (gridEndpoint b bits.2)
      x member hgrid
  have hface := rzOriginalZFace_eq_owner P A4 R z x member face hfaceX
  rcases bits with ⟨first, second⟩
  fin_cases first <;> fin_cases second
  all_goals simp [gridEndpoint, twoSelect, lowerGridIndex,
    upperGridIndex] at hu hv
  all_goals try omega
  · have ha : a = lastHalfSegment S := by
      apply Fin.ext
      dsimp [lastHalfSegment]
      omega
    have hb : b = lastHalfSegment S := by
      apply Fin.ext
      dsimp [lastHalfSegment]
      omega
    subst candidateCopy
    subst face
    subst a
    subst b
    exact ⟨rfl, rfl⟩

/-- Every end-copy local X target at the original-Z coordinate is the
canonical owner-cell X tag. -/
private noncomputable def rzOriginalZBoundaryPathToCopyX
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (z : P.Z) (copy : Two) (x : P.X)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.z x) = true)
    (candidateCopy : Two) (face : XStarFace (transposePresentation P) z)
    (a b : Fin S.half) (bits : Two × Two)
    (hcorner : localCornerVertex P z S
      (Sum.inl (candidateCopy, face, a, b)) bits =
        (copy, Sum.inl ⟨Vertex.z x, member⟩)) :
    UndirectedPath
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalZZVertex P S z copy x member))
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalZZVertex P S z copy x member))
      (rzReplacementZBoundaryRoot P A4.toTannerSquareAdmissibleV3 S
        (rzOriginalZZVertex P S z copy x member))
      (zBoundaryEdgeStart (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S)
        (rzOriginalZZVertex P S z copy x member)
        (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S)
          (rzOriginalZZVertex P S z copy x member)
          (rzOriginalZTargetZStarFace P A4 S z copy x member
            (Sum.inl (candidateCopy, face, a, b)) bits hcorner) 0)) := by
  by_cases hcell : Sum.inl (candidateCopy, face, a, b) =
      rzOriginalZOwnerCell P A4 S z copy x member
  · by_cases hbits : bits = (1, 1)
    · subst bits
      let successor := rzReplacementPresentation P
        A4.toTannerSquareAdmissible S
      let fixedZ := rzOriginalZZVertex P S z copy x member
      let targetFace := rzOriginalZTargetZStarFace P A4 S z copy x member
        (Sum.inl (candidateCopy, face, a, b)) (1, 1) hcorner
      let ownerFace := rzOriginalZOwnerZStarFace P A4 S z copy x member
      let path := rzOriginalZRootToOwnerXPath P A4 S z copy x member
      have htarget : zBoundaryEdgeStart successor fixedZ
            (rzZStarFaceBoundaryEdge successor fixedZ ownerFace 0) =
          zBoundaryEdgeStart successor fixedZ
            (rzZStarFaceBoundaryEdge successor fixedZ targetFace 0) := by
        apply Subtype.ext
        erw [rzZStarFaceBoundaryEdge_start_value,
          rzZStarFaceBoundaryEdge_start_value]
        apply congrArg Vertex.x
        change Sum.inl (Sum.inl (⟨z,
            rzOriginalZOwnerCell P A4 S z copy x member⟩ :
              Sigma fun oldZ : P.Z => ZDoubleCylinderFace P oldZ S)) =
          Sum.inl (Sum.inl (⟨z,
            Sum.inl (candidateCopy, face, a, b)⟩ :
              Sigma fun oldZ : P.Z => ZDoubleCylinderFace P oldZ S))
        exact congrArg (fun cell : ZDoubleCylinderFace P z S =>
          (Sum.inl (Sum.inl ⟨z, cell⟩) : RZX P S)) hcell.symm
      exact htarget ▸ path
    · exact False.elim (hbits (rzOriginalZCopyFace_eq_owner
        P A4 R S z copy x member candidateCopy face a b bits hcorner).2)
  · exact False.elim (hcell (rzOriginalZCopyFace_eq_owner
      P A4 R S z copy x member candidateCopy face a b bits hcorner).1)

/-- Reach a boundary-rectangle X tag at the original-Z endpoint through the
unique outer owner cell over the same original X/Z pair. -/
private noncomputable def rzOriginalZBoundaryPathToRectangleX
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (z : P.Z) (copy : Two) (x : P.X)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.z x) = true)
    (rectangle : ZSubdivisionBoundaryEdge P z S) (bits : Two × Two)
    (hcorner : localCornerVertex P z S (Sum.inr rectangle) bits =
      (copy, Sum.inl ⟨Vertex.z x, member⟩)) :
    UndirectedPath
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalZZVertex P S z copy x member))
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalZZVertex P S z copy x member))
      (rzReplacementZBoundaryRoot P A4.toTannerSquareAdmissibleV3 S
        (rzOriginalZZVertex P S z copy x member))
      (zBoundaryEdgeStart (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S)
        (rzOriginalZZVertex P S z copy x member)
        (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S)
          (rzOriginalZZVertex P S z copy x member)
          (rzOriginalZTargetZStarFace P A4 S z copy x member
            (Sum.inr rectangle) bits hcorner) 0)) := by
  rcases rectangle with ⟨rawEdge, boundaryMember⟩
  rcases rawEdge with boundarySegment | interior
  · rcases boundarySegment with ⟨starEdge, segment⟩
    rcases starEdge with ⟨rawStar, starMember⟩
    rcases rawStar with radial | boundary
    · simp [subdivisionBoundaryEdgeMember, xStarBoundaryEdgeMember]
        at boundaryMember
    · let boundaryEdge : XStarBoundaryEdge (transposePresentation P) z :=
        ⟨Sum.inr boundary, by
          simpa [xStarBoundaryEdgeMember, xStarEdgeMember] using starMember⟩
      rcases bits with ⟨candidateCopy, endpoint⟩
      have hcopy : candidateCopy = copy := congrArg Prod.fst hcorner
      by_cases hendpoint : endpoint = 1
      · subst endpoint
        have hvertex :
            (subdivisionBoundaryEdgeEnd (transposePresentation P) z S
              ⟨Sum.inl (⟨Sum.inr boundary, starMember⟩, segment),
                boundaryMember⟩).1 =
              Sum.inl ⟨Vertex.z x, member⟩ := by
          simpa [localCornerVertex, doubleCylinderRectangleCorner] using
            congrArg Prod.snd hcorner
        erw [subdivisionBoundaryEdgeEnd_value] at hvertex
        simp only [subdivisionEdgeEnd, subdivisionSegmentEnd] at hvertex
        by_cases hlast : segment.1 + 1 = S.half
        · simp [hlast, xStarEdgeEnd] at hvertex
          have hx : boundary.1.2 = x := Vertex.z.inj hvertex
          have hsegment : segment = lastHalfSegment S := by
            apply Fin.ext
            dsimp [lastHalfSegment]
            omega
          subst candidateCopy
          subst segment
          let owner := (transposeTannerSquareAdmissibleV4 P A4)
            |>.xBoundaryFaceOwner z boundary starMember
          let boundaryOwnerFace : XStarFace (transposePresentation P) z :=
            owner.1.1
          let boundaryOwnerCorner : Two := owner.1.2
          have hboundaryOwnerX : (transposePresentation P).faceZ
              boundaryOwnerFace.1 = x := by
            have howner := owner.2
            have hend := congrArg (fun edge : XStarEdge
                (transposePresentation P) z =>
              (xStarEdgeEnd (transposePresentation P) z edge).1) howner
            have hend' : (transposePresentation P).faceZ
                boundaryOwnerFace.1 = boundary.1.2 := by
              exact Vertex.z.inj hend
            exact hend'.trans hx
          have hownerFace : boundaryOwnerFace =
              rzOriginalZOwnerFace P A4 z x member :=
            rzOriginalZFace_eq_owner P A4 R z x member
              boundaryOwnerFace hboundaryOwnerX
          let successor := rzReplacementPresentation P
            A4.toTannerSquareAdmissible S
          let fixedZ := rzOriginalZZVertex P S z copy x member
          let ownerFace := rzOriginalZOwnerZStarFace P A4 S z copy x member
          let targetFace := rzOriginalZTargetZStarFace P A4 S z copy x member
            (Sum.inr ⟨Sum.inl
              (⟨Sum.inr boundary, starMember⟩, lastHalfSegment S),
                boundaryMember⟩) (copy, 1) (by simpa using hcorner)
          have hboundaryQ : successor.faceQ ownerFace.1
                (twoSelect 1 0 boundaryOwnerCorner) =
              successor.faceQ targetFace.1 0 := by
            have howner := owner.2
            have howner' : xStarFaceQZEdge (transposePresentation P) z
                (rzOriginalZOwnerFace P A4 z x member)
                boundaryOwnerCorner =
              xStarBoundaryEdgeToStar (transposePresentation P) z
                boundaryEdge := by
              rw [← hownerFace]
              exact howner
            have hlast' : S.half - 1 + 1 = S.half := by
              have := S.half_pos
              omega
            generalize hc : boundaryOwnerCorner = c at howner' ⊢
            change rzFaceQ P A4.toTannerSquareAdmissible S
                (Sum.inl ⟨z, rzOriginalZOwnerCell P A4 S z copy x member,
                  (1, 1)⟩) (twoSelect 1 0 c) =
              rzFaceQ P A4.toTannerSquareAdmissible S
                (Sum.inl ⟨z, Sum.inr
                  (subdivisionOriginalBoundaryEdge (transposePresentation P)
                    z S boundaryEdge (lastHalfSegment S)), (copy, 1)⟩) 0
            fin_cases c <;>
              simp [rzOriginalZOwnerCell, rzOriginalZBoundaryCorner,
                rzFaceQ, localFaceQ0, localFaceQ1, twoSelect, gridEndpoint,
                lowerGridIndex, upperGridIndex, lastHalfSegment,
                subdivisionHorizontalEdge, subdivisionVerticalEdge,
                subdivisionOriginalBoundaryEdge, hlast', S.half_pos.ne', hc] <;>
              exact howner'
          let first := rzOriginalZRootToOwnerXPath P A4 S z copy x member
          let middle :=
            (rzZStarFaceBoundaryPathToX successor fixedZ ownerFace).reverse.append
            (rzZStarFaceBoundaryPathToQ successor fixedZ ownerFace
              (twoSelect 1 0 boundaryOwnerCorner))
          let last :=
            (rzZStarFaceBoundaryPathToQ successor fixedZ targetFace 0).reverse.append
            (rzZStarFaceBoundaryPathToX successor fixedZ targetFace)
          have hbridge : zBoundaryEdgeEnd successor fixedZ
                (rzZStarFaceBoundaryEdge successor fixedZ ownerFace
                  (twoSelect 1 0 boundaryOwnerCorner)) =
              zBoundaryEdgeEnd successor fixedZ
                (rzZStarFaceBoundaryEdge successor fixedZ targetFace 0) := by
            apply Subtype.ext
            erw [rzZStarFaceBoundaryEdge_end_value,
              rzZStarFaceBoundaryEdge_end_value]
            exact congrArg Vertex.q hboundaryQ
          exact first.append (middle.append (hbridge ▸ last))
        · simp [hlast] at hvertex
      · have hendpointZero : endpoint = 0 := by
          apply Fin.ext
          have hne : endpoint.1 ≠ 1 := by
            intro hone
            apply hendpoint
            apply Fin.ext
            exact hone
          omega
        subst endpoint
        have hvertex :
            (subdivisionBoundaryEdgeStart (transposePresentation P) z S
              ⟨Sum.inl (⟨Sum.inr boundary, starMember⟩, segment),
                boundaryMember⟩).1 =
              Sum.inl ⟨Vertex.z x, member⟩ := by
          simpa [localCornerVertex, doubleCylinderRectangleCorner] using
            congrArg Prod.snd hcorner
        erw [subdivisionBoundaryEdgeStart_value] at hvertex
        simp only [subdivisionEdgeStart, subdivisionSegmentStart] at hvertex
        split at hvertex <;> cases hvertex
  · simp [subdivisionBoundaryEdgeMember] at boundaryMember

/-- Constructor-complete route to the X of a concrete local face at the
fixed original-Z coordinate. -/
private noncomputable def rzOriginalZBoundaryPathToMaterializedX
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (z : P.Z) (copy : Two) (x : P.X)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.z x) = true)
    (cell : ZDoubleCylinderFace P z S) (bits : Two × Two)
    (hcorner : localCornerVertex P z S cell bits =
      (copy, Sum.inl ⟨Vertex.z x, member⟩)) :
    UndirectedPath
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalZZVertex P S z copy x member))
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalZZVertex P S z copy x member))
      (rzReplacementZBoundaryRoot P A4.toTannerSquareAdmissibleV3 S
        (rzOriginalZZVertex P S z copy x member))
      (zBoundaryEdgeStart (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S)
        (rzOriginalZZVertex P S z copy x member)
        (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S)
          (rzOriginalZZVertex P S z copy x member)
          (rzOriginalZTargetZStarFace P A4 S z copy x member
            cell bits hcorner) 0)) := by
  rcases cell with copyFace | rectangle
  · rcases copyFace with ⟨candidateCopy, face, a, b⟩
    exact rzOriginalZBoundaryPathToCopyX P A4 R S z copy x member
      candidateCopy face a b bits hcorner
  · exact rzOriginalZBoundaryPathToRectangleX P A4 R S z copy x member
      rectangle bits hcorner

/-- Route to any local-face X tag on the original-Z fixed-Z boundary. -/
private noncomputable def rzOriginalZBoundaryPathToLocalX
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (z : P.Z) (copy : Two) (x : P.X)
    (originalMember : xStarVertexMember (transposePresentation P) z
      (Vertex.z x) = true)
    (localX : Sigma fun oldZ : P.Z => ZDoubleCylinderFace P oldZ S)
    (member : zStarBoundaryVertexMember
      (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
      (rzOriginalZZVertex P S z copy x originalMember)
      (Vertex.x (Sum.inl (Sum.inl localX))) = true) :
    UndirectedPath
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalZZVertex P S z copy x originalMember))
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalZZVertex P S z copy x originalMember))
      (rzReplacementZBoundaryRoot P A4.toTannerSquareAdmissibleV3 S
        (rzOriginalZZVertex P S z copy x originalMember))
      ⟨Vertex.x (Sum.inl (Sum.inl localX)), member⟩ := by
  let successor := rzReplacementPresentation P A4.toTannerSquareAdmissible S
  let fixedVertex : ZDoubleCylinderVertex P z S :=
    (copy, Sum.inl ⟨Vertex.z x, originalMember⟩)
  let fixedZ : successor.Z := rzOriginalZZVertex P S z copy x originalMember
  rcases localX with ⟨targetZ, cell⟩
  by_cases htargetZ : targetZ = z
  · subst targetZ
    let build (bits : Two × Two)
        (hcorner : localCornerVertex P z S cell bits = fixedVertex) :
        UndirectedPath
          (zBoundaryEdgeStart successor fixedZ)
          (zBoundaryEdgeEnd successor fixedZ)
          (rzReplacementZBoundaryRoot P A4.toTannerSquareAdmissibleV3 S fixedZ)
          ⟨Vertex.x (Sum.inl (Sum.inl ⟨z, cell⟩)), member⟩ := by
      let face := rzOriginalZTargetZStarFace P A4 S z copy x
        originalMember cell bits hcorner
      let path := rzOriginalZBoundaryPathToMaterializedX P A4 R S z copy x
        originalMember cell bits hcorner
      have htarget : zBoundaryEdgeStart successor fixedZ
            (rzZStarFaceBoundaryEdge successor fixedZ face 0) =
          (⟨Vertex.x (Sum.inl (Sum.inl ⟨z, cell⟩)), member⟩ :
            ZStarBoundaryVertex successor fixedZ) := by
        apply Subtype.ext
        rw [rzZStarFaceBoundaryEdge_start_value]
        rfl
      exact htarget ▸ path
    by_cases h00 : localCornerVertex P z S cell (0, 0) = fixedVertex
    · exact build (0, 0) h00
    · by_cases h01 : localCornerVertex P z S cell (0, 1) = fixedVertex
      · exact build (0, 1) h01
      · by_cases h10 : localCornerVertex P z S cell (1, 0) = fixedVertex
        · exact build (1, 0) h10
        · by_cases h11 : localCornerVertex P z S cell (1, 1) = fixedVertex
          · exact build (1, 1) h11
          · exact False.elim (by
              simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
              obtain ⟨successorFace, hfaceZ, hfaceX⟩ := member
              simp only [zStarFaceMember, decide_eq_true_eq] at hfaceZ
              rcases successorFace with localFace | glueOrOld
              · rcases localFace with ⟨ownerZ, ownerCell, bits⟩
                change Sum.inl (Sum.inl (⟨z, cell⟩ :
                    Sigma fun oldZ : P.Z => ZDoubleCylinderFace P oldZ S)) =
                  Sum.inl (Sum.inl (⟨ownerZ, ownerCell⟩ :
                    Sigma fun oldZ : P.Z => ZDoubleCylinderFace P oldZ S))
                    at hfaceX
                have howner := Sum.inl.inj (Sum.inl.inj hfaceX)
                cases howner
                change localFaceZ P S ⟨z, cell, bits⟩ = fixedZ at hfaceZ
                rw [localFaceZ_eq_corner] at hfaceZ
                have hbits : localCornerVertex P z S cell bits = fixedVertex :=
                  eq_of_heq (Sigma.mk.inj_iff.mp hfaceZ).2
                rcases bits with ⟨firstBit, secondBit⟩
                fin_cases firstBit <;> fin_cases secondBit
                · exact h00 hbits
                · exact h01 hbits
                · exact h10 hbits
                · exact h11 hbits
              · rcases glueOrOld with glueFace | oldFace
                · change Sum.inl (Sum.inl _) = Sum.inl (Sum.inr _) at hfaceX
                  cases Sum.inl.inj hfaceX
                · change Sum.inl (Sum.inl _) = Sum.inr _ at hfaceX
                  cases hfaceX)
  · exact False.elim (by
      simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
      obtain ⟨successorFace, hfaceZ, hfaceX⟩ := member
      simp only [zStarFaceMember, decide_eq_true_eq] at hfaceZ
      rcases successorFace with localFace | glueOrOld
      · rcases localFace with ⟨ownerZ, ownerCell, bits⟩
        change Sum.inl (Sum.inl (⟨targetZ, cell⟩ :
            Sigma fun oldZ : P.Z => ZDoubleCylinderFace P oldZ S)) =
          Sum.inl (Sum.inl (⟨ownerZ, ownerCell⟩ :
            Sigma fun oldZ : P.Z => ZDoubleCylinderFace P oldZ S)) at hfaceX
        have howner := Sum.inl.inj (Sum.inl.inj hfaceX)
        have hz : targetZ = ownerZ := congrArg Sigma.fst howner
        have hownerZ : ownerZ = z := by
          change localFaceZ P S ⟨ownerZ, ownerCell, bits⟩ = fixedZ at hfaceZ
          rw [localFaceZ_eq_corner] at hfaceZ
          exact congrArg Sigma.fst hfaceZ
        exact htargetZ (hz.trans hownerZ)
      · rcases glueOrOld with glueFace | oldFace
        · change Sum.inl (Sum.inl _) = Sum.inl (Sum.inr _) at hfaceX
          cases Sum.inl.inj hfaceX
        · change Sum.inl (Sum.inl _) = Sum.inr _ at hfaceX
          cases hfaceX)

/-- Route to any local-edge Q tag on the original-Z fixed-Z boundary. -/
private noncomputable def rzOriginalZBoundaryPathToLocalQ
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (z : P.Z) (copy : Two) (x : P.X)
    (originalMember : xStarVertexMember (transposePresentation P) z
      (Vertex.z x) = true)
    (localQ : Sigma fun oldZ : P.Z => ZDoubleCylinderEdge P oldZ S)
    (member : zStarBoundaryVertexMember
      (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
      (rzOriginalZZVertex P S z copy x originalMember)
      (Vertex.q (Sum.inl localQ)) = true) :
    UndirectedPath
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalZZVertex P S z copy x originalMember))
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalZZVertex P S z copy x originalMember))
      (rzReplacementZBoundaryRoot P A4.toTannerSquareAdmissibleV3 S
        (rzOriginalZZVertex P S z copy x originalMember))
      ⟨Vertex.q (Sum.inl localQ), member⟩ := by
  let A := A4.toTannerSquareAdmissible
  let successor := rzReplacementPresentation P A S
  let fixedVertex : ZDoubleCylinderVertex P z S :=
    (copy, Sum.inl ⟨Vertex.z x, originalMember⟩)
  let fixedZ : successor.Z := rzOriginalZZVertex P S z copy x originalMember
  have hqz : successor.qz (Sum.inl localQ) fixedZ = true := by
    simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
    obtain ⟨successorFace, hfaceZ, hfaceQ⟩ := member
    rcases hfaceQ with hfaceQ | hfaceQ
    · have h := successor.data.faceQ_qz successorFace 0
      change successor.qz (successor.faceQ successorFace 0)
        (successor.faceZ successorFace) = true at h
      change Sum.inl localQ = successor.faceQ successorFace 0 at hfaceQ
      have hz : successor.faceZ successorFace = fixedZ := by
        simpa [zStarFaceMember] using hfaceZ
      rw [← hfaceQ, hz] at h
      exact h
    · have h := successor.data.faceQ_qz successorFace 1
      change successor.qz (successor.faceQ successorFace 1)
        (successor.faceZ successorFace) = true at h
      change Sum.inl localQ = successor.faceQ successorFace 1 at hfaceQ
      have hz : successor.faceZ successorFace = fixedZ := by
        simpa [zStarFaceMember] using hfaceZ
      rw [← hfaceQ, hz] at h
      exact h
  rcases localQ with ⟨targetZ, edge⟩
  change successor.qz (Sum.inl ⟨targetZ, edge⟩) fixedZ = true at hqz
  by_cases htargetZ : z = targetZ
  · subst targetZ
    have hmatrix : doubleCylinderEdgeVertexMatrix (transposePresentation P) z S
        fixedVertex edge = 1 := by
      change decide (∃ h : z = z,
        doubleCylinderEdgeVertexMatrix (transposePresentation P) z S
          (h ▸ fixedVertex) edge = 1) = true at hqz
      obtain ⟨h, hmatrix⟩ := of_decide_eq_true hqz
      simpa only [Subsingleton.elim h rfl] using hmatrix
    let build (endpoint : Two)
        (hendpoint : BDL26TannerLocalRegularity.edgeEndpoint
          (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
          (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
          edge endpoint = fixedVertex) :
        UndirectedPath
          (zBoundaryEdgeStart successor fixedZ)
          (zBoundaryEdgeEnd successor fixedZ)
          (rzReplacementZBoundaryRoot P A4.toTannerSquareAdmissibleV3 S fixedZ)
          ⟨Vertex.q (Sum.inl ⟨z, edge⟩), member⟩ := by
      let owner := doubleCylinderEdgeFaceSlotOwner
        (transposePresentation P) (transposeTannerSquareAdmissibleV3 P
          A4.toTannerSquareAdmissibleV3) z S edge
      let corner := localCornerAtBoundaryEndpoint P z S
        owner.1.1 owner.1.2 endpoint
      have hcorner : localCornerVertex P z S owner.1.1 corner.1.1 =
          fixedVertex := by
        calc
          localCornerVertex P z S owner.1.1 corner.1.1 =
              BDL26TannerLocalRegularity.edgeEndpoint
                (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
                (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
                (doubleCylinderFaceBoundaryEdge (transposePresentation P) z S
                  owner.1.1 owner.1.2) endpoint := corner.2.2
          _ = BDL26TannerLocalRegularity.edgeEndpoint
                (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
                (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
                edge endpoint := by rw [owner.2]
          _ = fixedVertex := hendpoint
      let face := rzOriginalZTargetZStarFace P A4 S z copy x
        originalMember owner.1.1 corner.1.1 hcorner
      let first := rzOriginalZBoundaryPathToMaterializedX P A4 R S z copy x
        originalMember owner.1.1 corner.1.1 hcorner
      let last := (rzZStarFaceBoundaryPathToX successor fixedZ face).reverse.append
        (rzZStarFaceBoundaryPathToQ successor fixedZ face corner.1.2)
      have htarget : zBoundaryEdgeEnd successor fixedZ
            (rzZStarFaceBoundaryEdge successor fixedZ face corner.1.2) =
          (⟨Vertex.q (Sum.inl ⟨z, edge⟩), member⟩ :
            ZStarBoundaryVertex successor fixedZ) := by
        apply Subtype.ext
        rw [rzZStarFaceBoundaryEdge_end_value]
        apply congrArg Vertex.q
        change twoSelect
            (localFaceQ0 P S ⟨z, owner.1.1, corner.1.1⟩)
            (localFaceQ1 P S ⟨z, owner.1.1, corner.1.1⟩)
            corner.1.2 = Sum.inl ⟨z, edge⟩
        rw [localFaceQ_eq_corner]
        apply congrArg Sum.inl
        exact Sigma.ext
          (x := (⟨z, localCornerEdge P z S owner.1.1
            (corner.1.1, corner.1.2)⟩ :
              Sigma fun oldZ : P.Z => ZDoubleCylinderEdge P oldZ S))
          (y := ⟨z, edge⟩) rfl
          (heq_of_eq (corner.2.1.trans owner.2))
      exact first.append (htarget.symm ▸ last)
    by_cases hstart :
        tannerDoubleCylinderEdgeStart (transposePresentation P) z S edge =
          fixedVertex
    · exact build 0 hstart
    · by_cases hend :
          tannerDoubleCylinderEdgeEnd (transposePresentation P) z S edge =
            fixedVertex
      · exact build 1 hend
      · exact False.elim (by
          rcases (doubleCylinderEdgeVertexMatrix_eq_one_iff
            (transposePresentation P) z S fixedVertex edge).1 hmatrix with h | h
          · exact hstart h.symm
          · exact hend h.symm)
  · exact False.elim (by
      change decide (∃ h : z = targetZ,
        doubleCylinderEdgeVertexMatrix (transposePresentation P) targetZ S
          (h ▸ fixedVertex) edge = 1) = true at hqz
      obtain ⟨h, _⟩ := of_decide_eq_true hqz
      exact htargetZ h)


/-- The common radial local-Q edge of the original-Q owner sector. -/
private noncomputable def rzOriginalQHubLocalQ
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two) (q : P.Q)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true) :
    Sigma fun oldZ : P.Z => ZDoubleCylinderEdge P oldZ S :=
  ⟨z, Sum.inl (copy, Sum.inl
    (xStarFaceXQEdge (transposePresentation P) z
      (rzOriginalQOwnerFace P A4 z q member)
      (rzOriginalQOwnerCorner P A4 z q member),
    lastHalfSegment S))⟩

/-- The selected owner-face Q corner is the explicit common radial local-Q
tag. -/
private theorem rzOriginalQOwnerFaceQ_eq_localQ
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two) (q : P.Q)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true) :
    (rzReplacementPresentation P A4.toTannerSquareAdmissible S).faceQ
        (rzOriginalQOwnerZStarFace P A4 S z copy q member).1
        (rzOriginalQOwnerCorner P A4 z q member) =
      Sum.inl (rzOriginalQHubLocalQ P A4 S z copy q member) := by
  have hgridZero : lowerGridIndex (rzRadialGridZero S) =
      (0 : Fin (S.half + 1)) := by
    apply Fin.ext
    rfl
  generalize hcorner : rzOriginalQOwnerCorner P A4 z q member = corner
  change rzFaceQ P A4.toTannerSquareAdmissible S
      (rzOriginalQOwnerZStarFace P A4 S z copy q member).1 corner = _
  fin_cases corner <;>
    simp [rzOriginalQOwnerZStarFace, rzOriginalQOwnerCell,
      rzOriginalQOwnerBits, rzOriginalQHubLocalQ, hcorner,
      rzReplacementPresentation, rzReplacementData, rzFaceQ,
      localFaceQ0, localFaceQ1, twoSelect, gridEndpoint,
      lastHalfSegment, rzRadialGridZero, lowerGridIndex, upperGridIndex,
      hgridZero,
      subdivisionHorizontalEdge, subdivisionVerticalEdge,
      xStarFaceXQEdge, faceXQEdge, transposePresentation,
      transposeTannerSquareData]
  all_goals rfl

/-- The owner-sector hub endpoint is the explicit common radial local-Q tag. -/
private theorem rzOriginalQOwnerHub_eq_localQ
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two) (q : P.Q)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true) :
    zBoundaryEdgeEnd (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
      (rzOriginalQZVertex P S z copy q member)
      (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S)
        (rzOriginalQZVertex P S z copy q member)
        (rzOriginalQOwnerZStarFace P A4 S z copy q member)
        (rzOriginalQOwnerCorner P A4 z q member)) =
      ⟨Vertex.q (Sum.inl
        (rzOriginalQHubLocalQ P A4 S z copy q member)), by
        simp only [zStarBoundaryVertexMember, decide_eq_true_eq]
        refine ⟨(rzOriginalQOwnerZStarFace P A4 S z copy q member).1,
          (rzOriginalQOwnerZStarFace P A4 S z copy q member).2, ?_⟩
        generalize hcorner : rzOriginalQOwnerCorner P A4 z q member = corner
        fin_cases corner
        · left
          simpa [hcorner] using
            (rzOriginalQOwnerFaceQ_eq_localQ P A4 S z copy q member).symm
        · right
          simpa [hcorner] using
            (rzOriginalQOwnerFaceQ_eq_localQ P A4 S z copy q member).symm⟩ := by
  apply Subtype.ext
  erw [rzZStarFaceBoundaryEdge_end_value]
  exact congrArg Vertex.q
    (rzOriginalQOwnerFaceQ_eq_localQ P A4 S z copy q member)

/-- The V4 owner face retains the requested Q value at its selected corner. -/
private theorem rzOriginalQOwnerFace_q
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (z : P.Z) (q : P.Q)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true) :
    (transposePresentation P).faceQ
        (rzOriginalQOwnerFace P A4 z q member).1
        (rzOriginalQOwnerCorner P A4 z q member) = q := by
  let incident := (transposeTannerSquareAdmissibleV2 P
    A4.toTannerSquareAdmissibleV2).xBoundaryIncidentEdge z
      (rzOriginalQTransposedBoundaryVertex P z q member)
  have hbit := rzOriginalQTransposeIncident_bit P A4 z q member
  have hendpoint := incident.2
  change incident.1.2 = 0 at hbit
  rw [hbit, BDL26TannerLocalRegularity.edgeEndpoint_zero] at hendpoint
  have hstart := congrArg
    (xStarBoundaryVertexToStar (transposePresentation P) z) hendpoint
  erw [xBoundaryEdgeStart_toStar] at hstart
  have hedge := rzOriginalQTransposeIncident_edge P A4 z q member
  change xStarBoundaryEdgeToStar (transposePresentation P) z
    incident.1.1 = _ at hedge
  rw [hedge] at hstart
  have hvalue := congrArg Subtype.val hstart
  exact Vertex.q.inj hvalue

/-- Any transposed face corner carrying the same original Q value has the
same raw radial X-Q edge as the canonical owner hub. -/
private theorem rzOriginalQFaceRadialEdge_eq_owner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (z : P.Z) (q : P.Q)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true)
    (face : XStarFace (transposePresentation P) z) (corner : Two)
    (hq : (transposePresentation P).faceQ face.1 corner = q) :
    xStarFaceXQEdge (transposePresentation P) z face corner =
      xStarFaceXQEdge (transposePresentation P) z
        (rzOriginalQOwnerFace P A4 z q member)
        (rzOriginalQOwnerCorner P A4 z q member) := by
  apply Subtype.ext
  apply congrArg Sum.inl
  apply Subtype.ext
  apply Prod.ext
  · have hfaceX : (transposePresentation P).faceX face.1 = z := by
      simpa [xStarFaceMember] using face.2
    have hownerX : (transposePresentation P).faceX
        (rzOriginalQOwnerFace P A4 z q member).1 = z := by
      simpa [xStarFaceMember] using
        (rzOriginalQOwnerFace P A4 z q member).2
    exact hfaceX.trans hownerX.symm
  · exact hq.trans (rzOriginalQOwnerFace_q P A4 z q member).symm

/-- Package any concrete local face whose selected corner is the fixed
original-Q successor Z tag. -/
private noncomputable def rzOriginalQTargetZStarFace
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two) (q : P.Q)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true)
    (cell : ZDoubleCylinderFace P z S) (bits : Two × Two)
    (hcorner : localCornerVertex P z S cell bits =
      (copy, Sum.inl ⟨Vertex.q q, member⟩)) :
    ZStarFace (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S)
      (rzOriginalQZVertex P S z copy q member) :=
  ⟨Sum.inl ⟨z, cell, bits⟩, by
    simp only [zStarFaceMember, decide_eq_true_eq]
    change localFaceZ P S ⟨z, cell, bits⟩ =
      rzOriginalQZVertex P S z copy q member
    rw [localFaceZ_eq_corner]
    exact Sigma.ext rfl (heq_of_eq hcorner)⟩

/-- A copy-face corner carrying the fixed original Q value has one ordered
radial Q edge equal to the canonical owner hub. -/
private theorem rzOriginalQCopyFaceRadialQ_cases
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two) (q : P.Q)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true)
    (candidateCopy : Two) (face : XStarFace (transposePresentation P) z)
    (a b : Fin S.half) (bits : Two × Two)
    (hcorner : localCornerVertex P z S
      (Sum.inl (candidateCopy, face, a, b)) bits =
        (copy, Sum.inl ⟨Vertex.q q, member⟩)) :
    localFaceQ0 P S
        ⟨z, Sum.inl (candidateCopy, face, a, b), bits⟩ =
          Sum.inl (rzOriginalQHubLocalQ P A4 S z copy q member) ∨
      localFaceQ1 P S
        ⟨z, Sum.inl (candidateCopy, face, a, b), bits⟩ =
          Sum.inl (rzOriginalQHubLocalQ P A4 S z copy q member) := by
  have hcopy : candidateCopy = copy := congrArg Prod.fst hcorner
  have hgrid : subdivisionGridVertex (transposePresentation P) z S face
      (gridEndpoint a bits.1) (gridEndpoint b bits.2) =
        Sum.inl ⟨Vertex.q q, member⟩ := congrArg Prod.snd hcorner
  obtain hzero | hone := rzSubdivisionGridVertex_eq_originalQ_coordinates
    P S z face (gridEndpoint a bits.1) (gridEndpoint b bits.2)
      q member hgrid
  · rcases hzero with ⟨hq, hu, hv⟩
    have hradial := rzOriginalQFaceRadialEdge_eq_owner
      P A4 z q member face 0 hq
    rcases bits with ⟨first, second⟩
    fin_cases first <;> fin_cases second
    all_goals simp [gridEndpoint, twoSelect, lowerGridIndex,
      upperGridIndex] at hu hv
    all_goals try omega
    · left
      subst candidateCopy
      have ha : a = lastHalfSegment S := by
        apply Fin.ext
        dsimp [lastHalfSegment]
        omega
      subst a
      simp [localFaceQ0, gridEndpoint, twoSelect, lowerGridIndex,
        rzRadialGridZero, lastHalfSegment, subdivisionHorizontalEdge,
        rzOriginalQHubLocalQ, hv]
      exact hradial

  · rcases hone with ⟨hq, hu, hv⟩
    have hradial := rzOriginalQFaceRadialEdge_eq_owner
      P A4 z q member face 1 hq
    rcases bits with ⟨first, second⟩
    fin_cases first <;> fin_cases second
    all_goals simp [gridEndpoint, twoSelect, lowerGridIndex,
      upperGridIndex] at hu hv
    all_goals try omega
    · right
      subst candidateCopy
      have hb : b = lastHalfSegment S := by
        apply Fin.ext
        dsimp [lastHalfSegment]
        omega
      subst b
      simp [localFaceQ1, gridEndpoint, twoSelect, lowerGridIndex,
        rzRadialGridZero, lastHalfSegment, subdivisionVerticalEdge,
        rzOriginalQHubLocalQ, hu]
      exact hradial

/-- Reach the X tag of any end-copy cell whose selected corner is the fixed
original Q value. -/
private noncomputable def rzOriginalQBoundaryPathToCopyX
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two) (q : P.Q)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true)
    (candidateCopy : Two) (face : XStarFace (transposePresentation P) z)
    (a b : Fin S.half) (bits : Two × Two)
    (hcorner : localCornerVertex P z S
      (Sum.inl (candidateCopy, face, a, b)) bits =
        (copy, Sum.inl ⟨Vertex.q q, member⟩)) :
    UndirectedPath
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalQZVertex P S z copy q member))
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalQZVertex P S z copy q member))
      (rzReplacementZBoundaryRoot P A4.toTannerSquareAdmissibleV3 S
        (rzOriginalQZVertex P S z copy q member))
      (zBoundaryEdgeStart (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S)
        (rzOriginalQZVertex P S z copy q member)
        (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S)
          (rzOriginalQZVertex P S z copy q member)
          (rzOriginalQTargetZStarFace P A4 S z copy q member
            (Sum.inl (candidateCopy, face, a, b)) bits hcorner) 0)) := by
  let successor := rzReplacementPresentation P
    A4.toTannerSquareAdmissible S
  let fixedZ := rzOriginalQZVertex P S z copy q member
  let targetFace := rzOriginalQTargetZStarFace P A4 S z copy q member
    (Sum.inl (candidateCopy, face, a, b)) bits hcorner
  let first := rzOriginalQRootToOwnerHubPath P A4 S z copy q member
  by_cases hzero : localFaceQ0 P S
      ⟨z, Sum.inl (candidateCopy, face, a, b), bits⟩ =
        Sum.inl (rzOriginalQHubLocalQ P A4 S z copy q member)
  · let last := (rzZStarFaceBoundaryPathToQ successor fixedZ
        targetFace 0).reverse.append
      (rzZStarFaceBoundaryPathToX successor fixedZ targetFace)
    have hbridge :
        zBoundaryEdgeEnd successor fixedZ
            (rzZStarFaceBoundaryEdge successor fixedZ
              (rzOriginalQOwnerZStarFace P A4 S z copy q member)
              (rzOriginalQOwnerCorner P A4 z q member)) =
          zBoundaryEdgeEnd successor fixedZ
            (rzZStarFaceBoundaryEdge successor fixedZ targetFace 0) := by
      apply Subtype.ext
      erw [rzZStarFaceBoundaryEdge_end_value,
        rzZStarFaceBoundaryEdge_end_value]
      apply congrArg Vertex.q
      change (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S).faceQ
            (rzOriginalQOwnerZStarFace P A4 S z copy q member).1
            (rzOriginalQOwnerCorner P A4 z q member) =
        localFaceQ0 P S
          ⟨z, Sum.inl (candidateCopy, face, a, b), bits⟩
      rw [rzOriginalQOwnerFaceQ_eq_localQ]
      exact hzero.symm
    exact first.append (hbridge ▸ last)
  · by_cases hone : localFaceQ1 P S
        ⟨z, Sum.inl (candidateCopy, face, a, b), bits⟩ =
          Sum.inl (rzOriginalQHubLocalQ P A4 S z copy q member)
    · let last := (rzZStarFaceBoundaryPathToQ successor fixedZ
        targetFace 1).reverse.append
        (rzZStarFaceBoundaryPathToX successor fixedZ targetFace)
      have hbridge :
          zBoundaryEdgeEnd successor fixedZ
              (rzZStarFaceBoundaryEdge successor fixedZ
                (rzOriginalQOwnerZStarFace P A4 S z copy q member)
                (rzOriginalQOwnerCorner P A4 z q member)) =
            zBoundaryEdgeEnd successor fixedZ
              (rzZStarFaceBoundaryEdge successor fixedZ targetFace 1) := by
        apply Subtype.ext
        erw [rzZStarFaceBoundaryEdge_end_value,
          rzZStarFaceBoundaryEdge_end_value]
        apply congrArg Vertex.q
        change (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S).faceQ
              (rzOriginalQOwnerZStarFace P A4 S z copy q member).1
              (rzOriginalQOwnerCorner P A4 z q member) =
          localFaceQ1 P S
            ⟨z, Sum.inl (candidateCopy, face, a, b), bits⟩
        rw [rzOriginalQOwnerFaceQ_eq_localQ]
        exact hone.symm
      exact first.append (hbridge ▸ last)
    · exact False.elim (by
        rcases rzOriginalQCopyFaceRadialQ_cases
            P A4 S z copy q member candidateCopy face a b bits hcorner with
          h | h
        · exact hzero h
        · exact hone h)

/-- Reach the X tag of a boundary rectangle at the fixed original-Q corner.
The rectangle's own boundary edge supplies its V4 owner cell, whose radial
Q edge is the common owner hub. -/
private noncomputable def rzOriginalQBoundaryPathToRectangleX
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two) (q : P.Q)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true)
    (rectangle : ZSubdivisionBoundaryEdge P z S) (bits : Two × Two)
    (hcorner : localCornerVertex P z S (Sum.inr rectangle) bits =
      (copy, Sum.inl ⟨Vertex.q q, member⟩)) :
    UndirectedPath
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalQZVertex P S z copy q member))
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalQZVertex P S z copy q member))
      (rzReplacementZBoundaryRoot P A4.toTannerSquareAdmissibleV3 S
        (rzOriginalQZVertex P S z copy q member))
      (zBoundaryEdgeStart (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S)
        (rzOriginalQZVertex P S z copy q member)
        (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S)
          (rzOriginalQZVertex P S z copy q member)
          (rzOriginalQTargetZStarFace P A4 S z copy q member
            (Sum.inr rectangle) bits hcorner) 0)) := by
  rcases rectangle with ⟨rawEdge, boundaryMember⟩
  rcases rawEdge with boundarySegment | interior
  · rcases boundarySegment with ⟨starEdge, segment⟩
    rcases starEdge with ⟨rawStar, starMember⟩
    rcases rawStar with radial | boundary
    · simp [subdivisionBoundaryEdgeMember, xStarBoundaryEdgeMember] at boundaryMember
    · let boundaryEdge : XStarBoundaryEdge (transposePresentation P) z :=
        ⟨Sum.inr boundary, by
          simpa [xStarBoundaryEdgeMember, xStarEdgeMember] using starMember⟩
      have hrectangle :
          (⟨Sum.inl (⟨Sum.inr boundary, starMember⟩, segment),
            boundaryMember⟩ : ZSubdivisionBoundaryEdge P z S) =
          subdivisionOriginalBoundaryEdge (transposePresentation P) z S
            boundaryEdge segment := by
        apply Subtype.ext
        rfl
      rcases bits with ⟨candidateCopy, endpoint⟩
      have hcopy : candidateCopy = copy := congrArg Prod.fst hcorner
      by_cases hendpoint : endpoint = 0
      · subst endpoint
        have hvertex :
            (subdivisionBoundaryEdgeStart (transposePresentation P) z S
            ⟨Sum.inl (⟨Sum.inr boundary, starMember⟩, segment),
              boundaryMember⟩).1 =
              Sum.inl ⟨Vertex.q q, member⟩ := by
          simpa [localCornerVertex, doubleCylinderRectangleCorner] using
            congrArg Prod.snd hcorner
        erw [subdivisionBoundaryEdgeStart_value] at hvertex
        simp only [subdivisionEdgeStart, subdivisionSegmentStart] at hvertex
        by_cases hzero : segment.1 = 0
        · simp [hzero, xStarEdgeStart] at hvertex
          have hq : boundary.1.1 = q := Vertex.q.inj hvertex
          have hsegment : segment = rzRadialGridZero S := by
            apply Fin.ext
            exact hzero
          subst candidateCopy
          subst segment
          let owner := (transposeTannerSquareAdmissibleV4 P A4)
            |>.xBoundaryFaceOwner z boundary starMember
          let ownerFace : XStarFace (transposePresentation P) z := owner.1.1
          let ownerCorner : Two := owner.1.2
          let ownerCell : ZDoubleCylinderFace P z S := twoSelect
            (Sum.inl (copy, ownerFace, lastHalfSegment S, rzRadialGridZero S))
            (Sum.inl (copy, ownerFace, rzRadialGridZero S, lastHalfSegment S))
            ownerCorner
          let ownerBits : Two × Two :=
            twoSelect (1, 0) (0, 1) ownerCorner
          let boundaryCorner : Two := twoSelect 1 0 ownerCorner
          have hownerQ : (transposePresentation P).faceQ
              ownerFace.1 ownerCorner = q := by
            have howner := owner.2
            have hstart := congrArg (fun edge : XStarEdge
                (transposePresentation P) z =>
              (xStarEdgeStart (transposePresentation P) z edge).1) howner
            have hstart' : (transposePresentation P).faceQ
                ownerFace.1 ownerCorner = boundary.1.1 := by
              exact Vertex.q.inj hstart
            exact hstart'.trans hq
          have hlast : S.half - 1 + 1 = S.half := by
            have := S.half_pos
            omega
          have hownerZ : localFaceZ P S
              ⟨z, ownerCell, ownerBits⟩ =
                rzOriginalQZVertex P S z copy q member := by
            rw [localFaceZ_eq_localCornerVertex]
            generalize hc : ownerCorner = c at hownerQ ⊢
            fin_cases c
            all_goals
              apply Sigma.ext
                (x := ⟨z, localCornerVertex P z S ownerCell ownerBits⟩)
                (y := rzOriginalQZVertex P S z copy q member) rfl
              apply heq_of_eq
              simp [ownerCell, ownerBits, localCornerVertex,
                gridEndpoint, twoSelect, lowerGridIndex, upperGridIndex,
                subdivisionGridVertex, lastHalfSegment, rzRadialGridZero,
                xStarFaceQVertex, rzOriginalQZVertex, hownerQ, hlast, hc]
            all_goals
              simp only [if_neg S.half_pos.ne']
              apply congrArg Sum.inl
              apply Subtype.ext
              exact congrArg Vertex.q hownerQ
          let successor := rzReplacementPresentation P
            A4.toTannerSquareAdmissible S
          let fixedZ := rzOriginalQZVertex P S z copy q member
          let ownerZFace : ZStarFace successor fixedZ :=
            ⟨Sum.inl ⟨z, ownerCell, ownerBits⟩, by
              simp only [zStarFaceMember, decide_eq_true_eq]
              exact hownerZ⟩
          let targetFace := rzOriginalQTargetZStarFace P A4 S z copy q
            member (Sum.inr (subdivisionOriginalBoundaryEdge
              (transposePresentation P) z S boundaryEdge (rzRadialGridZero S)))
              (copy, 0) (by simpa [hrectangle] using hcorner)
          have hownerRadial : successor.faceQ ownerZFace.1 ownerCorner =
              Sum.inl (rzOriginalQHubLocalQ P A4 S z copy q member) := by
            have hradial := rzOriginalQFaceRadialEdge_eq_owner
              P A4 z q member ownerFace ownerCorner hownerQ
            generalize hc : ownerCorner = c at hradial ⊢
            dsimp only [successor, ownerZFace]
            change rzFaceQ P A4.toTannerSquareAdmissible S
              (Sum.inl ⟨z, ownerCell, ownerBits⟩) c = _
            fin_cases c <;>
              simp [ownerCell, ownerBits,
                rzFaceQ, localFaceQ0, localFaceQ1, twoSelect, gridEndpoint,
                lowerGridIndex, lastHalfSegment, rzRadialGridZero,
                subdivisionHorizontalEdge, subdivisionVerticalEdge,
                rzOriginalQHubLocalQ, hc] <;>
              exact hradial
          have hownerBoundary : successor.faceQ ownerZFace.1 boundaryCorner =
              successor.faceQ targetFace.1 0 := by
            have howner := owner.2
            have howner' : xStarFaceQZEdge (transposePresentation P) z
                ownerFace ownerCorner =
              xStarBoundaryEdgeToStar (transposePresentation P) z
                boundaryEdge := by
              exact howner
            dsimp only [successor, ownerZFace, targetFace, boundaryCorner,
              rzOriginalQTargetZStarFace]
            change rzFaceQ P A4.toTannerSquareAdmissible S
                (Sum.inl ⟨z, ownerCell, ownerBits⟩)
                (twoSelect 1 0 ownerCorner) =
              rzFaceQ P A4.toTannerSquareAdmissible S
                (Sum.inl ⟨z, Sum.inr
                  (subdivisionOriginalBoundaryEdge (transposePresentation P)
                    z S boundaryEdge (rzRadialGridZero S)), (copy, 0)⟩) 0
            generalize hc : ownerCorner = c at howner' ⊢
            fin_cases c <;>
              simp [ownerCell, ownerBits,
                boundaryCorner, boundaryEdge, rzReplacementPresentation,
                rzReplacementData, rzFaceQ, localFaceQ0, localFaceQ1,
                twoSelect, gridEndpoint, lowerGridIndex, upperGridIndex,
                lastHalfSegment, rzRadialGridZero,
                subdivisionHorizontalEdge, subdivisionVerticalEdge,
                subdivisionOriginalBoundaryEdge, hlast, S.half_pos.ne', hc] <;>
              exact howner'
          let first := rzOriginalQRootToOwnerHubPath
            P A4 S z copy q member
          let middle :=
            (rzZStarFaceBoundaryPathToQ successor fixedZ ownerZFace
              ownerCorner).reverse.append
            (rzZStarFaceBoundaryPathToQ successor fixedZ ownerZFace
              boundaryCorner)
          let last :=
            (rzZStarFaceBoundaryPathToQ successor fixedZ targetFace 0).reverse.append
            (rzZStarFaceBoundaryPathToX successor fixedZ targetFace)
          have hhub : zBoundaryEdgeEnd successor fixedZ
                (rzZStarFaceBoundaryEdge successor fixedZ
                  (rzOriginalQOwnerZStarFace P A4 S z copy q member)
                  (rzOriginalQOwnerCorner P A4 z q member)) =
              zBoundaryEdgeEnd successor fixedZ
                (rzZStarFaceBoundaryEdge successor fixedZ ownerZFace
                  ownerCorner) := by
            apply Subtype.ext
            erw [rzZStarFaceBoundaryEdge_end_value,
              rzZStarFaceBoundaryEdge_end_value]
            apply congrArg Vertex.q
            rw [rzOriginalQOwnerFaceQ_eq_localQ]
            exact hownerRadial.symm
          have hboundary : zBoundaryEdgeEnd successor fixedZ
                (rzZStarFaceBoundaryEdge successor fixedZ ownerZFace
                  boundaryCorner) =
              zBoundaryEdgeEnd successor fixedZ
                (rzZStarFaceBoundaryEdge successor fixedZ targetFace 0) := by
            apply Subtype.ext
            erw [rzZStarFaceBoundaryEdge_end_value,
              rzZStarFaceBoundaryEdge_end_value]
            exact congrArg Vertex.q hownerBoundary
          exact first.append ((hhub ▸ middle).append (hboundary ▸ last))
        · simp [hzero] at hvertex
      · have hendpointOne : endpoint = 1 := by
          have hne : endpoint.1 ≠ 0 := by
            intro hzero
            apply hendpoint
            apply Fin.ext
            exact hzero
          have hval : endpoint.1 = (1 : Two).1 := by omega
          exact Fin.ext hval
        subst endpoint
        have hvertex :
            (subdivisionBoundaryEdgeEnd (transposePresentation P) z S
            ⟨Sum.inl (⟨Sum.inr boundary, starMember⟩, segment),
              boundaryMember⟩).1 =
              Sum.inl ⟨Vertex.q q, member⟩ := by
          simpa [localCornerVertex, doubleCylinderRectangleCorner] using
            congrArg Prod.snd hcorner
        erw [subdivisionBoundaryEdgeEnd_value] at hvertex
        simp only [subdivisionEdgeEnd, subdivisionSegmentEnd] at hvertex
        split at hvertex <;> cases hvertex
  · simp [subdivisionBoundaryEdgeMember] at boundaryMember

/-- Constructor-complete route to the X of a concrete local face at the
fixed original-Q coordinate. -/
private noncomputable def rzOriginalQBoundaryPathToMaterializedX
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two) (q : P.Q)
    (member : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true)
    (cell : ZDoubleCylinderFace P z S) (bits : Two × Two)
    (hcorner : localCornerVertex P z S cell bits =
      (copy, Sum.inl ⟨Vertex.q q, member⟩)) :
    UndirectedPath
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalQZVertex P S z copy q member))
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalQZVertex P S z copy q member))
      (rzReplacementZBoundaryRoot P A4.toTannerSquareAdmissibleV3 S
        (rzOriginalQZVertex P S z copy q member))
      (zBoundaryEdgeStart (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S)
        (rzOriginalQZVertex P S z copy q member)
        (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S)
          (rzOriginalQZVertex P S z copy q member)
          (rzOriginalQTargetZStarFace P A4 S z copy q member
            cell bits hcorner) 0)) := by
  rcases cell with copyFace | rectangle
  · rcases copyFace with ⟨candidateCopy, face, a, b⟩
    exact rzOriginalQBoundaryPathToCopyX P A4 S z copy q member
      candidateCopy face a b bits hcorner
  · exact rzOriginalQBoundaryPathToRectangleX P A4 S z copy q member
      rectangle bits hcorner

/-- Route to any local-face X tag on the original-Q fixed-Z boundary. -/
private noncomputable def rzOriginalQBoundaryPathToLocalX
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two) (q : P.Q)
    (originalMember : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true)
    (localX : Sigma fun oldZ : P.Z => ZDoubleCylinderFace P oldZ S)
    (member : zStarBoundaryVertexMember
      (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
      (rzOriginalQZVertex P S z copy q originalMember)
      (Vertex.x (Sum.inl (Sum.inl localX))) = true) :
    UndirectedPath
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalQZVertex P S z copy q originalMember))
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalQZVertex P S z copy q originalMember))
      (rzReplacementZBoundaryRoot P A4.toTannerSquareAdmissibleV3 S
        (rzOriginalQZVertex P S z copy q originalMember))
      ⟨Vertex.x (Sum.inl (Sum.inl localX)), member⟩ := by
  let successor := rzReplacementPresentation P A4.toTannerSquareAdmissible S
  let fixedVertex : ZDoubleCylinderVertex P z S :=
    (copy, Sum.inl ⟨Vertex.q q, originalMember⟩)
  let fixedZ : successor.Z := rzOriginalQZVertex P S z copy q originalMember
  rcases localX with ⟨targetZ, cell⟩
  by_cases htargetZ : targetZ = z
  · subst targetZ
    let build (bits : Two × Two)
        (hcorner : localCornerVertex P z S cell bits = fixedVertex) :
        UndirectedPath
          (zBoundaryEdgeStart successor fixedZ)
          (zBoundaryEdgeEnd successor fixedZ)
          (rzReplacementZBoundaryRoot P A4.toTannerSquareAdmissibleV3 S fixedZ)
          ⟨Vertex.x (Sum.inl (Sum.inl ⟨z, cell⟩)), member⟩ := by
      let face := rzOriginalQTargetZStarFace P A4 S z copy q
        originalMember cell bits hcorner
      let path := rzOriginalQBoundaryPathToMaterializedX P A4 S z copy q
        originalMember cell bits hcorner
      have htarget : zBoundaryEdgeStart successor fixedZ
            (rzZStarFaceBoundaryEdge successor fixedZ face 0) =
          (⟨Vertex.x (Sum.inl (Sum.inl ⟨z, cell⟩)), member⟩ :
            ZStarBoundaryVertex successor fixedZ) := by
        apply Subtype.ext
        rw [rzZStarFaceBoundaryEdge_start_value]
        rfl
      exact htarget ▸ path
    by_cases h00 : localCornerVertex P z S cell (0, 0) = fixedVertex
    · exact build (0, 0) h00
    · by_cases h01 : localCornerVertex P z S cell (0, 1) = fixedVertex
      · exact build (0, 1) h01
      · by_cases h10 : localCornerVertex P z S cell (1, 0) = fixedVertex
        · exact build (1, 0) h10
        · by_cases h11 : localCornerVertex P z S cell (1, 1) = fixedVertex
          · exact build (1, 1) h11
          · exact False.elim (by
              simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
              obtain ⟨successorFace, hfaceZ, hfaceX⟩ := member
              simp only [zStarFaceMember, decide_eq_true_eq] at hfaceZ
              rcases successorFace with localFace | glueOrOld
              · rcases localFace with ⟨ownerZ, ownerCell, bits⟩
                change Sum.inl (Sum.inl (⟨z, cell⟩ :
                    Sigma fun oldZ : P.Z => ZDoubleCylinderFace P oldZ S)) =
                  Sum.inl (Sum.inl (⟨ownerZ, ownerCell⟩ :
                    Sigma fun oldZ : P.Z => ZDoubleCylinderFace P oldZ S))
                    at hfaceX
                have howner := Sum.inl.inj (Sum.inl.inj hfaceX)
                cases howner
                change localFaceZ P S ⟨z, cell, bits⟩ = fixedZ at hfaceZ
                rw [localFaceZ_eq_corner] at hfaceZ
                have hbits : localCornerVertex P z S cell bits = fixedVertex :=
                  eq_of_heq (Sigma.mk.inj_iff.mp hfaceZ).2
                rcases bits with ⟨firstBit, secondBit⟩
                fin_cases firstBit <;> fin_cases secondBit
                · exact h00 hbits
                · exact h01 hbits
                · exact h10 hbits
                · exact h11 hbits
              · rcases glueOrOld with glueFace | oldFace
                · change Sum.inl (Sum.inl _) = Sum.inl (Sum.inr _) at hfaceX
                  cases Sum.inl.inj hfaceX
                · change Sum.inl (Sum.inl _) = Sum.inr _ at hfaceX
                  cases hfaceX)
  · exact False.elim (by
      simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
      obtain ⟨successorFace, hfaceZ, hfaceX⟩ := member
      simp only [zStarFaceMember, decide_eq_true_eq] at hfaceZ
      rcases successorFace with localFace | glueOrOld
      · rcases localFace with ⟨ownerZ, ownerCell, bits⟩
        change Sum.inl (Sum.inl (⟨targetZ, cell⟩ :
            Sigma fun oldZ : P.Z => ZDoubleCylinderFace P oldZ S)) =
          Sum.inl (Sum.inl (⟨ownerZ, ownerCell⟩ :
            Sigma fun oldZ : P.Z => ZDoubleCylinderFace P oldZ S)) at hfaceX
        have howner := Sum.inl.inj (Sum.inl.inj hfaceX)
        have hz : targetZ = ownerZ := congrArg Sigma.fst howner
        have hownerZ : ownerZ = z := by
          change localFaceZ P S ⟨ownerZ, ownerCell, bits⟩ = fixedZ at hfaceZ
          rw [localFaceZ_eq_corner] at hfaceZ
          exact congrArg Sigma.fst hfaceZ
        exact htargetZ (hz.trans hownerZ)
      · rcases glueOrOld with glueFace | oldFace
        · change Sum.inl (Sum.inl _) = Sum.inl (Sum.inr _) at hfaceX
          cases Sum.inl.inj hfaceX
        · change Sum.inl (Sum.inl _) = Sum.inr _ at hfaceX
          cases hfaceX)

/-- Route to any local-edge Q tag on the original-Q fixed-Z boundary. -/
private noncomputable def rzOriginalQBoundaryPathToLocalQ
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two) (q : P.Q)
    (originalMember : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true)
    (localQ : Sigma fun oldZ : P.Z => ZDoubleCylinderEdge P oldZ S)
    (member : zStarBoundaryVertexMember
      (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
      (rzOriginalQZVertex P S z copy q originalMember)
      (Vertex.q (Sum.inl localQ)) = true) :
    UndirectedPath
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalQZVertex P S z copy q originalMember))
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalQZVertex P S z copy q originalMember))
      (rzReplacementZBoundaryRoot P A4.toTannerSquareAdmissibleV3 S
        (rzOriginalQZVertex P S z copy q originalMember))
      ⟨Vertex.q (Sum.inl localQ), member⟩ := by
  let A := A4.toTannerSquareAdmissible
  let successor := rzReplacementPresentation P A S
  let fixedVertex : ZDoubleCylinderVertex P z S :=
    (copy, Sum.inl ⟨Vertex.q q, originalMember⟩)
  let fixedZ : successor.Z := rzOriginalQZVertex P S z copy q originalMember
  have hqz : successor.qz (Sum.inl localQ) fixedZ = true := by
    simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
    obtain ⟨successorFace, hfaceZ, hfaceQ⟩ := member
    rcases hfaceQ with hfaceQ | hfaceQ
    · have h := successor.data.faceQ_qz successorFace 0
      change successor.qz (successor.faceQ successorFace 0)
        (successor.faceZ successorFace) = true at h
      change Sum.inl localQ = successor.faceQ successorFace 0 at hfaceQ
      have hz : successor.faceZ successorFace = fixedZ := by
        simpa [zStarFaceMember] using hfaceZ
      rw [← hfaceQ, hz] at h
      exact h
    · have h := successor.data.faceQ_qz successorFace 1
      change successor.qz (successor.faceQ successorFace 1)
        (successor.faceZ successorFace) = true at h
      change Sum.inl localQ = successor.faceQ successorFace 1 at hfaceQ
      have hz : successor.faceZ successorFace = fixedZ := by
        simpa [zStarFaceMember] using hfaceZ
      rw [← hfaceQ, hz] at h
      exact h
  rcases localQ with ⟨targetZ, edge⟩
  change successor.qz (Sum.inl ⟨targetZ, edge⟩) fixedZ = true at hqz
  by_cases htargetZ : z = targetZ
  · subst targetZ
    have hmatrix : doubleCylinderEdgeVertexMatrix (transposePresentation P) z S
        fixedVertex edge = 1 := by
      change decide (∃ h : z = z,
        doubleCylinderEdgeVertexMatrix (transposePresentation P) z S
          (h ▸ fixedVertex) edge = 1) = true at hqz
      obtain ⟨h, hmatrix⟩ := of_decide_eq_true hqz
      simpa only [Subsingleton.elim h rfl] using hmatrix
    let build (endpoint : Two)
        (hendpoint : BDL26TannerLocalRegularity.edgeEndpoint
          (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
          (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
          edge endpoint = fixedVertex) :
        UndirectedPath
          (zBoundaryEdgeStart successor fixedZ)
          (zBoundaryEdgeEnd successor fixedZ)
          (rzReplacementZBoundaryRoot P A4.toTannerSquareAdmissibleV3 S fixedZ)
          ⟨Vertex.q (Sum.inl ⟨z, edge⟩), member⟩ := by
      let owner := doubleCylinderEdgeFaceSlotOwner
        (transposePresentation P) (transposeTannerSquareAdmissibleV3 P
          A4.toTannerSquareAdmissibleV3) z S edge
      let corner := localCornerAtBoundaryEndpoint P z S
        owner.1.1 owner.1.2 endpoint
      have hcorner : localCornerVertex P z S owner.1.1 corner.1.1 =
          fixedVertex := by
        calc
          localCornerVertex P z S owner.1.1 corner.1.1 =
              BDL26TannerLocalRegularity.edgeEndpoint
                (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
                (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
                (doubleCylinderFaceBoundaryEdge (transposePresentation P) z S
                  owner.1.1 owner.1.2) endpoint := corner.2.2
          _ = BDL26TannerLocalRegularity.edgeEndpoint
                (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
                (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
                edge endpoint := by rw [owner.2]
          _ = fixedVertex := hendpoint
      let face := rzOriginalQTargetZStarFace P A4 S z copy q
        originalMember owner.1.1 corner.1.1 hcorner
      let first := rzOriginalQBoundaryPathToMaterializedX P A4 S z copy q
        originalMember owner.1.1 corner.1.1 hcorner
      let last := (rzZStarFaceBoundaryPathToX successor fixedZ face).reverse.append
        (rzZStarFaceBoundaryPathToQ successor fixedZ face corner.1.2)
      have htarget : zBoundaryEdgeEnd successor fixedZ
            (rzZStarFaceBoundaryEdge successor fixedZ face corner.1.2) =
          (⟨Vertex.q (Sum.inl ⟨z, edge⟩), member⟩ :
            ZStarBoundaryVertex successor fixedZ) := by
        apply Subtype.ext
        rw [rzZStarFaceBoundaryEdge_end_value]
        apply congrArg Vertex.q
        change twoSelect
            (localFaceQ0 P S ⟨z, owner.1.1, corner.1.1⟩)
            (localFaceQ1 P S ⟨z, owner.1.1, corner.1.1⟩)
            corner.1.2 = Sum.inl ⟨z, edge⟩
        rw [localFaceQ_eq_corner]
        apply congrArg Sum.inl
        exact Sigma.ext
          (x := (⟨z, localCornerEdge P z S owner.1.1
            (corner.1.1, corner.1.2)⟩ :
              Sigma fun oldZ : P.Z => ZDoubleCylinderEdge P oldZ S))
          (y := ⟨z, edge⟩) rfl
          (heq_of_eq (corner.2.1.trans owner.2))
      exact first.append (htarget.symm ▸ last)
    by_cases hstart :
        tannerDoubleCylinderEdgeStart (transposePresentation P) z S edge =
          fixedVertex
    · exact build 0 hstart
    · by_cases hend :
          tannerDoubleCylinderEdgeEnd (transposePresentation P) z S edge =
            fixedVertex
      · exact build 1 hend
      · exact False.elim (by
          rcases (doubleCylinderEdgeVertexMatrix_eq_one_iff
            (transposePresentation P) z S fixedVertex edge).1 hmatrix with h | h
          · exact hstart h.symm
          · exact hend h.symm)
  · exact False.elim (by
      change decide (∃ h : z = targetZ,
        doubleCylinderEdgeVertexMatrix (transposePresentation P) targetZ S
          (h ▸ fixedVertex) edge = 1) = true at hqz
      obtain ⟨h, _⟩ := of_decide_eq_true hqz
      exact htargetZ h)

/-- A glue-X tag on the original-Q fixed-Z link supplies its old Q-Z
incidence and one of the two mapped endpoint equalities. -/
private theorem rzOriginalQGlueX_endpoint
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (z : P.Z) (copy : Two) (q : P.Q)
    (originalMember : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true)
    (glueQ : P.Q)
    (qEdge : QDoubleCylinderEdge (transposePresentation P) glueQ S)
    (member : zStarBoundaryVertexMember (rzReplacementPresentation P A S)
      (rzOriginalQZVertex P S z copy q originalMember)
      (Vertex.x (Sum.inl (Sum.inr ⟨glueQ, qEdge⟩))) = true) :
    ∃ hqz : P.qz glueQ z = true,
      qToZDoubleCylinderVertex P A glueQ z hqz S
          (edgeEndpoint
            (qDoubleCylinderEdgeStart (transposePresentation P) glueQ S)
            (qDoubleCylinderEdgeEnd (transposePresentation P) glueQ S)
            qEdge 0) =
          (copy, Sum.inl ⟨Vertex.q q, originalMember⟩) ∨
        qToZDoubleCylinderVertex P A glueQ z hqz S
          (edgeEndpoint
            (qDoubleCylinderEdgeStart (transposePresentation P) glueQ S)
            (qDoubleCylinderEdgeEnd (transposePresentation P) glueQ S)
            qEdge 1) =
          (copy, Sum.inl ⟨Vertex.q q, originalMember⟩) := by
  classical
  simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
  obtain ⟨successorFace, hfaceZ, hfaceX⟩ := member
  simp only [zStarFaceMember, decide_eq_true_eq] at hfaceZ
  rcases successorFace with localFace | glueOrOld
  · change (Sum.inl (Sum.inr (⟨glueQ, qEdge⟩ : Sigma fun q : P.Q =>
        QDoubleCylinderEdge (transposePresentation P) q S)) : RZX P S) =
      localFaceX P S localFace at hfaceX
    simp [localFaceX] at hfaceX
  · rcases glueOrOld with glueFace | oldFace
    · rcases glueFace with ⟨⟨⟨q', z'⟩, hqz⟩, edge, endpoint⟩
      change (Sum.inl (Sum.inr (⟨glueQ, qEdge⟩ : Sigma fun q : P.Q =>
          QDoubleCylinderEdge (transposePresentation P) q S)) : RZX P S) =
        Sum.inl (Sum.inr (⟨q', edge⟩ : Sigma fun q : P.Q =>
          QDoubleCylinderEdge (transposePresentation P) q S)) at hfaceX
      have hedge : (⟨glueQ, qEdge⟩ : Sigma fun q : P.Q =>
          QDoubleCylinderEdge (transposePresentation P) q S) =
          ⟨q', edge⟩ := Sum.inr.inj (Sum.inl.inj hfaceX)
      cases hedge
      change glueFaceZ P A S ⟨⟨⟨glueQ, z'⟩, hqz⟩, qEdge, endpoint⟩ =
        rzOriginalQZVertex P S z copy q originalMember at hfaceZ
      have hz : z' = z := congrArg Sigma.fst hfaceZ
      subst z'
      have hvertex := eq_of_heq (Sigma.mk.inj_iff.mp hfaceZ).2
      refine ⟨hqz, ?_⟩
      fin_cases endpoint
      · left
        exact hvertex
      · right
        exact hvertex
    · change (Sum.inl (Sum.inr (⟨glueQ, qEdge⟩ : Sigma fun q : P.Q =>
          QDoubleCylinderEdge (transposePresentation P) q S)) : RZX P S) =
        oldXFaceX P S oldFace at hfaceX
      simp [oldXFaceX] at hfaceX

/-- Route to a retained glue-X tag on the original-Q fixed-Z boundary. -/
private noncomputable def rzOriginalQBoundaryPathToGlueX
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two) (q : P.Q)
    (originalMember : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true)
    (glueQ : P.Q)
    (qEdge : QDoubleCylinderEdge (transposePresentation P) glueQ S)
    (member : zStarBoundaryVertexMember
      (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
      (rzOriginalQZVertex P S z copy q originalMember)
      (Vertex.x (Sum.inl (Sum.inr ⟨glueQ, qEdge⟩))) = true) :
    UndirectedPath
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalQZVertex P S z copy q originalMember))
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalQZVertex P S z copy q originalMember))
      (rzReplacementZBoundaryRoot P A4.toTannerSquareAdmissibleV3 S
        (rzOriginalQZVertex P S z copy q originalMember))
      ⟨Vertex.x (Sum.inl (Sum.inr ⟨glueQ, qEdge⟩)), member⟩ := by
  classical
  let A := A4.toTannerSquareAdmissible
  let successor := rzReplacementPresentation P A S
  let fixedVertex : ZDoubleCylinderVertex P z S :=
    (copy, Sum.inl ⟨Vertex.q q, originalMember⟩)
  let fixedZ : successor.Z := rzOriginalQZVertex P S z copy q originalMember
  by_cases hqz : P.qz glueQ z = true
  · let build (endpoint : Two)
      (hmap : qToZDoubleCylinderVertex P A glueQ z hqz S
        (edgeEndpoint
          (qDoubleCylinderEdgeStart (transposePresentation P) glueQ S)
          (qDoubleCylinderEdgeEnd (transposePresentation P) glueQ S)
          qEdge endpoint) = fixedVertex) :
      UndirectedPath
        (zBoundaryEdgeStart successor fixedZ)
        (zBoundaryEdgeEnd successor fixedZ)
        (rzReplacementZBoundaryRoot P A4.toTannerSquareAdmissibleV3 S fixedZ)
        ⟨Vertex.x (Sum.inl (Sum.inr ⟨glueQ, qEdge⟩)), member⟩ := by
      let oldEdge : QZEdge P := ⟨(glueQ, z), hqz⟩
      let localQ : Sigma fun oldZ : P.Z => ZDoubleCylinderEdge P oldZ S :=
        ⟨z, qToZDoubleCylinderEdge P A glueQ z hqz S qEdge⟩
      let glue : RZQZGlueFace P S := ⟨oldEdge, qEdge, endpoint⟩
      have hfaceZ : glueFaceZ P A S glue = fixedZ := by
        apply Sigma.ext (x := glueFaceZ P A S glue) (y := fixedZ) rfl
        apply heq_of_eq
        exact hmap
      have hlocalMember : zStarBoundaryVertexMember successor fixedZ
          (Vertex.q (Sum.inl localQ)) = true := by
        change decide (∃ successorFace : successor.Face,
          zStarFaceMember successor fixedZ successorFace = true ∧
            (Sum.inl localQ = successor.faceQ successorFace 0 ∨
              Sum.inl localQ = successor.faceQ successorFace 1)) = true
        rw [decide_eq_true_eq]
        refine ⟨Sum.inr (Sum.inl glue), ?_, Or.inl ?_⟩
        · simp only [zStarFaceMember, decide_eq_true_eq]
          exact hfaceZ
        · rfl
      let face : ZStarFace successor fixedZ :=
        ⟨Sum.inr (Sum.inl glue), by
          simp only [zStarFaceMember, decide_eq_true_eq]
          exact hfaceZ⟩
      let first := rzOriginalQBoundaryPathToLocalQ P A4 S z copy q
        originalMember localQ hlocalMember
      let last := rzZStarFaceBoundaryPathToX successor fixedZ face
      have hlocal :
          (⟨Vertex.q (Sum.inl localQ), hlocalMember⟩ :
            ZStarBoundaryVertex successor fixedZ) =
          zBoundaryEdgeEnd successor fixedZ
            (rzZStarFaceBoundaryEdge successor fixedZ face 0) := by
        apply Subtype.ext
        rw [rzZStarFaceBoundaryEdge_end_value]
        rfl
      have htarget : zBoundaryEdgeStart successor fixedZ
            (rzZStarFaceBoundaryEdge successor fixedZ face 0) =
          (⟨Vertex.x (Sum.inl (Sum.inr ⟨glueQ, qEdge⟩)), member⟩ :
            ZStarBoundaryVertex successor fixedZ) := by
        apply Subtype.ext
        rw [rzZStarFaceBoundaryEdge_start_value]
        rfl
      exact first.append (hlocal ▸ (htarget.symm ▸ last))
    by_cases hzero : qToZDoubleCylinderVertex P A glueQ z hqz S
        (edgeEndpoint
          (qDoubleCylinderEdgeStart (transposePresentation P) glueQ S)
          (qDoubleCylinderEdgeEnd (transposePresentation P) glueQ S)
          qEdge 0) = fixedVertex
    · exact build 0 hzero
    · by_cases hone : qToZDoubleCylinderVertex P A glueQ z hqz S
          (edgeEndpoint
            (qDoubleCylinderEdgeStart (transposePresentation P) glueQ S)
            (qDoubleCylinderEdgeEnd (transposePresentation P) glueQ S)
            qEdge 1) = fixedVertex
      · exact build 1 hone
      · exact False.elim (by
          obtain ⟨hqz', hendpoint⟩ := rzOriginalQGlueX_endpoint
            P A S z copy q originalMember glueQ qEdge member
          rcases hendpoint with hzero' | hone'
          · exact hzero (by
              simpa only [Subsingleton.elim hqz' hqz] using hzero')
          · exact hone (by
              simpa only [Subsingleton.elim hqz' hqz] using hone'))
  · exact False.elim (by
      obtain ⟨hqz', _⟩ := rzOriginalQGlueX_endpoint
        P A S z copy q originalMember glueQ qEdge member
      exact hqz hqz')

/-- A glue-X tag on the original-Z fixed-Z link supplies its old Q-Z
incidence and one of the two mapped endpoint equalities. -/
private theorem rzOriginalZGlueX_endpoint
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (z : P.Z) (copy : Two) (x : P.X)
    (originalMember : xStarVertexMember (transposePresentation P) z
      (Vertex.z x) = true)
    (glueQ : P.Q)
    (qEdge : QDoubleCylinderEdge (transposePresentation P) glueQ S)
    (member : zStarBoundaryVertexMember (rzReplacementPresentation P A S)
      (rzOriginalZZVertex P S z copy x originalMember)
      (Vertex.x (Sum.inl (Sum.inr ⟨glueQ, qEdge⟩))) = true) :
    ∃ hqz : P.qz glueQ z = true,
      qToZDoubleCylinderVertex P A glueQ z hqz S
          (edgeEndpoint
            (qDoubleCylinderEdgeStart (transposePresentation P) glueQ S)
            (qDoubleCylinderEdgeEnd (transposePresentation P) glueQ S)
            qEdge 0) =
          (copy, Sum.inl ⟨Vertex.z x, originalMember⟩) ∨
        qToZDoubleCylinderVertex P A glueQ z hqz S
          (edgeEndpoint
            (qDoubleCylinderEdgeStart (transposePresentation P) glueQ S)
            (qDoubleCylinderEdgeEnd (transposePresentation P) glueQ S)
            qEdge 1) =
          (copy, Sum.inl ⟨Vertex.z x, originalMember⟩) := by
  classical
  simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
  obtain ⟨successorFace, hfaceZ, hfaceX⟩ := member
  simp only [zStarFaceMember, decide_eq_true_eq] at hfaceZ
  rcases successorFace with localFace | glueOrOld
  · change (Sum.inl (Sum.inr (⟨glueQ, qEdge⟩ : Sigma fun q : P.Q =>
        QDoubleCylinderEdge (transposePresentation P) q S)) : RZX P S) =
      localFaceX P S localFace at hfaceX
    simp [localFaceX] at hfaceX
  · rcases glueOrOld with glueFace | oldFace
    · rcases glueFace with ⟨⟨⟨q', z'⟩, hqz⟩, edge, endpoint⟩
      change (Sum.inl (Sum.inr (⟨glueQ, qEdge⟩ : Sigma fun q : P.Q =>
          QDoubleCylinderEdge (transposePresentation P) q S)) : RZX P S) =
        Sum.inl (Sum.inr (⟨q', edge⟩ : Sigma fun q : P.Q =>
          QDoubleCylinderEdge (transposePresentation P) q S)) at hfaceX
      have hedge : (⟨glueQ, qEdge⟩ : Sigma fun q : P.Q =>
          QDoubleCylinderEdge (transposePresentation P) q S) =
          ⟨q', edge⟩ := Sum.inr.inj (Sum.inl.inj hfaceX)
      cases hedge
      change glueFaceZ P A S ⟨⟨⟨glueQ, z'⟩, hqz⟩, qEdge, endpoint⟩ =
        rzOriginalZZVertex P S z copy x originalMember at hfaceZ
      have hz : z' = z := congrArg Sigma.fst hfaceZ
      subst z'
      have hvertex := eq_of_heq (Sigma.mk.inj_iff.mp hfaceZ).2
      refine ⟨hqz, ?_⟩
      fin_cases endpoint
      · left
        exact hvertex
      · right
        exact hvertex
    · change (Sum.inl (Sum.inr (⟨glueQ, qEdge⟩ : Sigma fun q : P.Q =>
          QDoubleCylinderEdge (transposePresentation P) q S)) : RZX P S) =
        oldXFaceX P S oldFace at hfaceX
      simp [oldXFaceX] at hfaceX

/-- Route to a retained glue-X tag on the original-Z fixed-Z boundary. -/
private noncomputable def rzOriginalZBoundaryPathToGlueX
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (z : P.Z) (copy : Two) (x : P.X)
    (originalMember : xStarVertexMember (transposePresentation P) z
      (Vertex.z x) = true)
    (glueQ : P.Q)
    (qEdge : QDoubleCylinderEdge (transposePresentation P) glueQ S)
    (member : zStarBoundaryVertexMember
      (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
      (rzOriginalZZVertex P S z copy x originalMember)
      (Vertex.x (Sum.inl (Sum.inr ⟨glueQ, qEdge⟩))) = true) :
    UndirectedPath
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalZZVertex P S z copy x originalMember))
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalZZVertex P S z copy x originalMember))
      (rzReplacementZBoundaryRoot P A4.toTannerSquareAdmissibleV3 S
        (rzOriginalZZVertex P S z copy x originalMember))
      ⟨Vertex.x (Sum.inl (Sum.inr ⟨glueQ, qEdge⟩)), member⟩ := by
  classical
  let A := A4.toTannerSquareAdmissible
  let successor := rzReplacementPresentation P A S
  let fixedVertex : ZDoubleCylinderVertex P z S :=
    (copy, Sum.inl ⟨Vertex.z x, originalMember⟩)
  let fixedZ : successor.Z := rzOriginalZZVertex P S z copy x originalMember
  by_cases hqz : P.qz glueQ z = true
  · let build (endpoint : Two)
      (hmap : qToZDoubleCylinderVertex P A glueQ z hqz S
        (edgeEndpoint
          (qDoubleCylinderEdgeStart (transposePresentation P) glueQ S)
          (qDoubleCylinderEdgeEnd (transposePresentation P) glueQ S)
          qEdge endpoint) = fixedVertex) :
      UndirectedPath
        (zBoundaryEdgeStart successor fixedZ)
        (zBoundaryEdgeEnd successor fixedZ)
        (rzReplacementZBoundaryRoot P A4.toTannerSquareAdmissibleV3 S fixedZ)
        ⟨Vertex.x (Sum.inl (Sum.inr ⟨glueQ, qEdge⟩)), member⟩ := by
      let oldEdge : QZEdge P := ⟨(glueQ, z), hqz⟩
      let localQ : Sigma fun oldZ : P.Z => ZDoubleCylinderEdge P oldZ S :=
        ⟨z, qToZDoubleCylinderEdge P A glueQ z hqz S qEdge⟩
      let glue : RZQZGlueFace P S := ⟨oldEdge, qEdge, endpoint⟩
      have hfaceZ : glueFaceZ P A S glue = fixedZ := by
        apply Sigma.ext (x := glueFaceZ P A S glue) (y := fixedZ) rfl
        apply heq_of_eq
        exact hmap
      have hlocalMember : zStarBoundaryVertexMember successor fixedZ
          (Vertex.q (Sum.inl localQ)) = true := by
        change decide (∃ successorFace : successor.Face,
          zStarFaceMember successor fixedZ successorFace = true ∧
            (Sum.inl localQ = successor.faceQ successorFace 0 ∨
              Sum.inl localQ = successor.faceQ successorFace 1)) = true
        rw [decide_eq_true_eq]
        refine ⟨Sum.inr (Sum.inl glue), ?_, Or.inl ?_⟩
        · simp only [zStarFaceMember, decide_eq_true_eq]
          exact hfaceZ
        · rfl
      let face : ZStarFace successor fixedZ :=
        ⟨Sum.inr (Sum.inl glue), by
          simp only [zStarFaceMember, decide_eq_true_eq]
          exact hfaceZ⟩
      let first := rzOriginalZBoundaryPathToLocalQ P A4 R S z copy x
        originalMember localQ hlocalMember
      let last := rzZStarFaceBoundaryPathToX successor fixedZ face
      have hlocal :
          (⟨Vertex.q (Sum.inl localQ), hlocalMember⟩ :
            ZStarBoundaryVertex successor fixedZ) =
          zBoundaryEdgeEnd successor fixedZ
            (rzZStarFaceBoundaryEdge successor fixedZ face 0) := by
        apply Subtype.ext
        rw [rzZStarFaceBoundaryEdge_end_value]
        rfl
      have htarget : zBoundaryEdgeStart successor fixedZ
            (rzZStarFaceBoundaryEdge successor fixedZ face 0) =
          (⟨Vertex.x (Sum.inl (Sum.inr ⟨glueQ, qEdge⟩)), member⟩ :
            ZStarBoundaryVertex successor fixedZ) := by
        apply Subtype.ext
        rw [rzZStarFaceBoundaryEdge_start_value]
        rfl
      exact first.append (hlocal ▸ (htarget.symm ▸ last))
    by_cases hzero : qToZDoubleCylinderVertex P A glueQ z hqz S
        (edgeEndpoint
          (qDoubleCylinderEdgeStart (transposePresentation P) glueQ S)
          (qDoubleCylinderEdgeEnd (transposePresentation P) glueQ S)
          qEdge 0) = fixedVertex
    · exact build 0 hzero
    · by_cases hone : qToZDoubleCylinderVertex P A glueQ z hqz S
          (edgeEndpoint
            (qDoubleCylinderEdgeStart (transposePresentation P) glueQ S)
            (qDoubleCylinderEdgeEnd (transposePresentation P) glueQ S)
            qEdge 1) = fixedVertex
      · exact build 1 hone
      · exact False.elim (by
          obtain ⟨hqz', hendpoint⟩ := rzOriginalZGlueX_endpoint
            P A S z copy x originalMember glueQ qEdge member
          rcases hendpoint with hzero' | hone'
          · exact hzero (by
              simpa only [Subsingleton.elim hqz' hqz] using hzero')
          · exact hone (by
              simpa only [Subsingleton.elim hqz' hqz] using hone'))
  · exact False.elim (by
      obtain ⟨hqz', _⟩ := rzOriginalZGlueX_endpoint
        P A S z copy x originalMember glueQ qEdge member
      exact hqz hqz')


/-- In the original-central sector, the selected Q corner of the actual
successor root is the endpoint-one lift of the historical anchor edge. -/
private theorem rzOriginalCentralRootQ_eq_anchorEdgeVertex
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two) :
    zBoundaryEdgeEnd (rzReplacementPresentation P
        A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
      (rzOriginalCentralZVertex P S z copy)
      (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
          A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        (rzOriginalCentralZVertex P S z copy)
        (rzReplacementZBoundaryRootFace P A4.toTannerSquareAdmissibleV3 S
          (rzOriginalCentralZVertex P S z copy))
        (rzReplacementZBoundaryRootCorner P A4.toTannerSquareAdmissibleV3 S
          (rzOriginalCentralZVertex P S z copy))) =
      rzOriginalCentralBoundaryEdgeVertex P A4 S z copy
        (rzOriginalCentralAnchorBoundaryEdge P A4 z) 1 := by
  apply Subtype.ext
  erw [rzZStarFaceBoundaryEdge_end_value]
  change Vertex.q _ =
    (zBoundaryEdgeEnd (rzReplacementPresentation P
        A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
      (rzOriginalCentralZVertex P S z copy)
      (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
          A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        (rzOriginalCentralZVertex P S z copy)
        (rzOriginalCentralOwnerLocalZStarFace P A4 S z copy
          (rzOriginalCentralAnchorBoundaryEdge P A4 z))
        (rzInputZBoundaryFaceOwner P A4 z
          (rzOriginalCentralAnchorBoundaryEdge P A4 z)).1.2)).1
  erw [rzZStarFaceBoundaryEdge_end_value]
  apply congrArg Vertex.q
  erw [rzReplacementZBoundaryRootFaceQ_eq_incidentEdge]
  change (Sum.inl (⟨z,
    (doubleCylinderVertexIncidentEdge (transposePresentation P)
      (transposeTannerSquareAdmissibleV3 P
        A4.toTannerSquareAdmissibleV3) z S
      (rzOriginalCentralZVertex P S z copy).2).1.1⟩ :
        Sigma fun oldZ : P.Z => ZDoubleCylinderEdge P oldZ S) :
      RZQ P S) = _
  rw [rzOriginalCentralRootIncidentEdge_eq]
  simp only [rzReplacementPresentation, rzReplacementData,
    rzOriginalCentralOwnerLocalZStarFace]
  change (Sum.inl ⟨z, Sum.inl (copy, Sum.inl
      ((xStarAnchorRadialEdge (transposePresentation P)
        (transposeTannerSquareAdmissibleV3 P
          A4.toTannerSquareAdmissibleV3) z).1, rzRadialGridZero S))⟩ :
        RZQ P S) =
    twoSelect
      (localFaceQ0 P S ⟨z,
        rzOriginalCentralOwnerCell P A4 S z copy
          (rzOriginalCentralAnchorBoundaryEdge P A4 z), (0, 0)⟩)
      (localFaceQ1 P S ⟨z,
        rzOriginalCentralOwnerCell P A4 S z copy
          (rzOriginalCentralAnchorBoundaryEdge P A4 z), (0, 0)⟩)
      (rzInputZBoundaryFaceOwner P A4 z
        (rzOriginalCentralAnchorBoundaryEdge P A4 z)).1.2
  rw [localFaceQ_eq_corner]
  apply congrArg Sum.inl
  apply Sigma.ext
    (x := (⟨z, Sum.inl (copy, Sum.inl
      ((xStarAnchorRadialEdge (transposePresentation P)
        (transposeTannerSquareAdmissibleV3 P
          A4.toTannerSquareAdmissibleV3) z).1, rzRadialGridZero S))⟩ :
        Sigma fun oldZ : P.Z => ZDoubleCylinderEdge P oldZ S))
    (y := ⟨z, localCornerEdge P z S
      (rzOriginalCentralOwnerCell P A4 S z copy
        (rzOriginalCentralAnchorBoundaryEdge P A4 z))
      ((0, 0), (rzInputZBoundaryFaceOwner P A4 z
        (rzOriginalCentralAnchorBoundaryEdge P A4 z)).1.2)⟩) rfl
  apply heq_of_eq
  generalize hcorner : (rzInputZBoundaryFaceOwner P A4 z
    (rzOriginalCentralAnchorBoundaryEdge P A4 z)).1.2 = corner
  have hradial := rzOriginalCentralAnchorOwnerRadialEdge_eq P A4 z
  rw [hcorner] at hradial
  have hgridZero : lowerGridIndex (rzRadialGridZero S) =
      (0 : Fin (S.half + 1)) := by
    apply Fin.ext
    rfl
  fin_cases corner <;>
    simpa [rzOriginalCentralOwnerCell, localCornerEdge, gridEndpoint,
      twoSelect, subdivisionHorizontalEdge, subdivisionVerticalEdge,
      hgridZero] using congrArg
        (fun edge =>
          (Sum.inl (copy,
            (Sum.inl (edge, rzRadialGridZero S) :
              SubdivisionEdge (transposePresentation P) z S)) :
            ZDoubleCylinderEdge P z S)) hradial.symm

/-- Bridge the actual successor root to the lifted historical input root
through the Q endpoint shared by the anchor edge. -/
private noncomputable def rzOriginalCentralRootToHistoricalRootPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (z : P.Z) (copy : Two) :=
  let anchor := rzOriginalCentralAnchorBoundaryEdge P A4 z
  let historical := rzOriginalCentralHistoricalBoundaryPath P A4 R S z copy
    (zBoundaryEdgeEnd P z anchor)
  let rootToQ := rzReplacementZBoundaryRootPathToQ P
    A4.toTannerSquareAdmissibleV3 S
    (rzOriginalCentralZVertex P S z copy)
    (rzReplacementZBoundaryRootCorner P A4.toTannerSquareAdmissibleV3 S
      (rzOriginalCentralZVertex P S z copy))
  have hlift : rzOriginalCentralBoundaryVertexLift P A4 S z copy
      (zBoundaryEdgeEnd P z anchor) =
      rzOriginalCentralBoundaryEdgeVertex P A4 S z copy anchor 1 :=
    rzOriginalCentralBoundaryVertexLift_eq_edgeVertex
      P A4 R S z copy (zBoundaryEdgeEnd P z anchor) anchor 1 (by
        simp only [BDL26TannerLocalRegularity.edgeEndpoint_one])
  have hrootQ :
      zBoundaryEdgeEnd (rzReplacementPresentation P
          A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        (rzOriginalCentralZVertex P S z copy)
        (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
          (rzOriginalCentralZVertex P S z copy)
          (rzReplacementZBoundaryRootFace P A4.toTannerSquareAdmissibleV3 S
            (rzOriginalCentralZVertex P S z copy))
          (rzReplacementZBoundaryRootCorner P A4.toTannerSquareAdmissibleV3 S
            (rzOriginalCentralZVertex P S z copy))) =
        rzOriginalCentralBoundaryEdgeVertex P A4 S z copy anchor 1 := by
    simpa [anchor] using
      rzOriginalCentralRootQ_eq_anchorEdgeVertex P A4 S z copy
  rootToQ.append ((hlift.trans hrootQ.symm ▸ historical).reverse)

/-- Follow the root bridge by the lifted historical connectedness path to
any old boundary target. -/
private noncomputable def rzOriginalCentralRootToHistoricalBoundaryPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (z : P.Z) (copy : Two) (target : ZStarBoundaryVertex P z) :=
  (rzOriginalCentralRootToHistoricalRootPath P A4 R S z copy).append
    (rzOriginalCentralHistoricalBoundaryPath P A4 R S z copy target)

/-- Total boundary dispatcher at an original-central successor Z coordinate.
The target is decoded by its concrete retained X/Q tag; proposition-level
surjectivity is used only to rule out impossible untagged constructors. -/
private noncomputable def rzOriginalCentralBoundaryPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (z : P.Z) (copy : Two)
    (vertex : ZStarBoundaryVertex (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S)
      (rzOriginalCentralZVertex P S z copy)) :
    UndirectedPath
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalCentralZVertex P S z copy))
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalCentralZVertex P S z copy))
      (rzReplacementZBoundaryRoot P A4.toTannerSquareAdmissibleV3 S
        (rzOriginalCentralZVertex P S z copy))
      vertex := by
  rcases vertex with ⟨value, member⟩
  rcases value with newX | newQ | impossible
  · generalize htag : rzOriginalCentralXTag P S newX = tag
    rcases tag with _ | x
    · exact False.elim
        ((rzOriginalCentralXTag_ne_none P A4 R S z copy newX member) htag)
    · let xMember := rzOriginalCentralXTag_member
        P A4 R S z copy newX member x htag
      let oldVertex : ZStarBoundaryVertex P z :=
        ⟨Vertex.x x, xMember⟩
      have himage := rzOriginalCentralXTag_image
        P A4 R S z copy newX member x htag xMember
      exact himage ▸
        rzOriginalCentralRootToHistoricalBoundaryPath
          P A4 R S z copy oldVertex
  · generalize htag : rzOriginalCentralQTag P S newQ = tag
    rcases tag with _ | q
    · exact False.elim
        ((rzOriginalCentralQTag_ne_none P A4 R S z copy newQ member) htag)
    · let qMember := rzOriginalCentralQTag_member
        P A4 R S z copy newQ member q htag
      let oldVertex : ZStarBoundaryVertex P z :=
        ⟨Vertex.q q, qMember⟩
      have himage := rzOriginalCentralQTag_image
        P A4 R S z copy newQ member q htag qMember
      exact himage ▸
        rzOriginalCentralRootToHistoricalBoundaryPath
          P A4 R S z copy oldVertex
  · simp [zStarBoundaryVertexMember] at member

/-- At a stored face-interior successor Z vertex, the deterministic root is
the X corner of the southwest adjacent small cell. -/
private theorem rzReplacementZBoundaryRoot_faceInterior
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (face : XStarFace (transposePresentation P) z)
    (i j : Fin (S.half - 1)) :
    rzReplacementZBoundaryRoot P A3 S
        ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩ =
      zBoundaryEdgeStart
        (rzReplacementPresentation P
          A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
        (rzZStarFaceBoundaryEdge
          (rzReplacementPresentation P
            A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
          ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
          (rzFaceInteriorZStarFaceSW P
            A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
            S z copy face i j) 0) := by
  have hrow0 : j.1 + 1 ≠ 0 := by omega
  have hrowlast : j.1 + 1 ≠ S.half := by
    have := (Nat.lt_sub_iff_add_lt).1 j.2
    omega
  have hselected : subdivisionHorizontalEdge (transposePresentation P) z S
      face ⟨i.1, by have := i.2; omega⟩
      ⟨j.1 + 1, by have := j.2; omega⟩ =
        (Sum.inr (Sum.inl (face,
          ⟨i.1, by have := i.2; omega⟩, j)) :
          SubdivisionEdge (transposePresentation P) z S) := by
    simp [subdivisionHorizontalEdge, hrow0, hrowlast]
    apply Fin.ext
    change (j.1 + 1) - 1 = j.1
    omega
  have hincident :
      (doubleCylinderVertexIncidentEdge (transposePresentation P)
        (transposeTannerSquareAdmissibleV3 P A3) z S
        (copy, Sum.inr (Sum.inr (face, i, j)))).1.1 =
        Sum.inl (copy, Sum.inr (Sum.inl (face,
          ⟨i.1, by have := i.2; omega⟩, j))) := by
    simp [doubleCylinderVertexIncidentEdge, subdivisionVertexIncidentEdge]
    rw [hselected]
  apply Subtype.ext
  rw [rzReplacementZBoundaryRoot_value]
  erw [rzZStarFaceBoundaryEdge_start_value]
  have hfaceX :
      (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S).faceX
          (rzFaceInteriorZStarFaceSW P
            A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
            S z copy face i j).1 =
        rzFaceX P S
          (rzFaceInteriorZStarFaceSW P
            A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
            S z copy face i j).1 := rfl
  rw [hfaceX]
  rw [hincident]
  simp [doubleCylinderEdgeFaceSlotOwner, rzFaceInteriorZStarFaceSW,
    rzFaceInteriorLocalFaceSW, rzReplacementPresentation,
    rzReplacementData, rzFaceX, localFaceX, rzInteriorLowerFaceIndex]

/-- The direct path from the deterministic southwest X root to either Q
corner of that same small cell. -/
private noncomputable def rzFaceInteriorBoundaryPathSW
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (face : XStarFace (transposePresentation P) z)
    (i j : Fin (S.half - 1)) (qCorner : Two) :=
  (rzZStarFaceBoundaryPathToX
      (rzReplacementPresentation P A S)
      ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
      (rzFaceInteriorZStarFaceSW P A S z copy face i j)).reverse.append
    (rzZStarFaceBoundaryPathToQ
      (rzReplacementPresentation P A S)
      ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
      (rzFaceInteriorZStarFaceSW P A S z copy face i j) qCorner)

/-- The southeast and southwest small cells share their vertical boundary
edge at the stored face-interior vertex. -/
private theorem rzFaceInteriorBoundaryQEqSWSE
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (face : XStarFace (transposePresentation P) z)
    (i j : Fin (S.half - 1)) :
    zBoundaryEdgeEnd (rzReplacementPresentation P A S)
        ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
        (rzZStarFaceBoundaryEdge (rzReplacementPresentation P A S)
          ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
          (rzFaceInteriorZStarFaceSW P A S z copy face i j) 1) =
      zBoundaryEdgeEnd (rzReplacementPresentation P A S)
        ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
        (rzZStarFaceBoundaryEdge (rzReplacementPresentation P A S)
          ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
          (rzFaceInteriorZStarFaceSE P A S z copy face i j) 1) := by
  apply Subtype.ext
  erw [rzZStarFaceBoundaryEdge_end_value]

/-- The northwest and southwest small cells share their horizontal boundary
edge at the stored face-interior vertex. -/
private theorem rzFaceInteriorBoundaryQEqSWNW
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (face : XStarFace (transposePresentation P) z)
    (i j : Fin (S.half - 1)) :
    zBoundaryEdgeEnd (rzReplacementPresentation P A S)
        ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
        (rzZStarFaceBoundaryEdge (rzReplacementPresentation P A S)
          ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
          (rzFaceInteriorZStarFaceSW P A S z copy face i j) 0) =
      zBoundaryEdgeEnd (rzReplacementPresentation P A S)
        ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
        (rzZStarFaceBoundaryEdge (rzReplacementPresentation P A S)
          ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
          (rzFaceInteriorZStarFaceNW P A S z copy face i j) 0) := by
  apply Subtype.ext
  erw [rzZStarFaceBoundaryEdge_end_value]

/-- The northeast and southeast small cells share their horizontal boundary
edge at the stored face-interior vertex. -/
private theorem rzFaceInteriorBoundaryQEqSENE
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (face : XStarFace (transposePresentation P) z)
    (i j : Fin (S.half - 1)) :
    zBoundaryEdgeEnd (rzReplacementPresentation P A S)
        ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
        (rzZStarFaceBoundaryEdge (rzReplacementPresentation P A S)
          ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
          (rzFaceInteriorZStarFaceSE P A S z copy face i j) 0) =
      zBoundaryEdgeEnd (rzReplacementPresentation P A S)
        ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
        (rzZStarFaceBoundaryEdge (rzReplacementPresentation P A S)
          ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
          (rzFaceInteriorZStarFaceNE P A S z copy face i j) 0) := by
  apply Subtype.ext
  erw [rzZStarFaceBoundaryEdge_end_value]

/-- Reach the X corner of the southeast adjacent small cell. -/
private noncomputable def rzFaceInteriorBoundaryPathToXSE
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (face : XStarFace (transposePresentation P) z)
    (i j : Fin (S.half - 1)) := by
  let first := rzFaceInteriorBoundaryPathSW P A S z copy face i j 1
  let bridge := (rzZStarFaceBoundaryPathToQ
    (rzReplacementPresentation P A S)
    ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
    (rzFaceInteriorZStarFaceSE P A S z copy face i j) 1).reverse
  let last := rzZStarFaceBoundaryPathToX
    (rzReplacementPresentation P A S)
    ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
    (rzFaceInteriorZStarFaceSE P A S z copy face i j)
  exact first.append
    ((rzFaceInteriorBoundaryQEqSWSE P A S z copy face i j) ▸
      bridge.append last)

/-- Reach the X corner of the northwest adjacent small cell. -/
private noncomputable def rzFaceInteriorBoundaryPathToXNW
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (face : XStarFace (transposePresentation P) z)
    (i j : Fin (S.half - 1)) := by
  let first := rzFaceInteriorBoundaryPathSW P A S z copy face i j 0
  let last := rzZStarFaceBoundaryPathToX
    (rzReplacementPresentation P A S)
    ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
    (rzFaceInteriorZStarFaceNW P A S z copy face i j)
  exact first.append
    ((rzFaceInteriorBoundaryQEqSWNW P A S z copy face i j) ▸ last)

/-- Reach the X corner of the northeast adjacent small cell. -/
private noncomputable def rzFaceInteriorBoundaryPathToXNE
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (face : XStarFace (transposePresentation P) z)
    (i j : Fin (S.half - 1)) := by
  let toSE := rzFaceInteriorBoundaryPathToXSE P A S z copy face i j
  let toQ := (rzZStarFaceBoundaryPathToX
    (rzReplacementPresentation P A S)
    ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
    (rzFaceInteriorZStarFaceSE P A S z copy face i j)).reverse
  let toNE := rzZStarFaceBoundaryPathToX
    (rzReplacementPresentation P A S)
    ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
    (rzFaceInteriorZStarFaceNE P A S z copy face i j)
  exact toSE.append (toQ.append
    ((rzFaceInteriorBoundaryQEqSENE P A S z copy face i j) ▸ toNE))

/-- Reach either Q corner of the southeast adjacent small cell. -/
private noncomputable def rzFaceInteriorBoundaryPathToQSE
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (face : XStarFace (transposePresentation P) z)
    (i j : Fin (S.half - 1)) (corner : Two) :=
  (rzFaceInteriorBoundaryPathToXSE P A S z copy face i j).append
    ((rzZStarFaceBoundaryPathToX (rzReplacementPresentation P A S)
      ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
      (rzFaceInteriorZStarFaceSE P A S z copy face i j)).reverse.append
      (rzZStarFaceBoundaryPathToQ (rzReplacementPresentation P A S)
        ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
        (rzFaceInteriorZStarFaceSE P A S z copy face i j) corner))

/-- Reach either Q corner of the northwest adjacent small cell. -/
private noncomputable def rzFaceInteriorBoundaryPathToQNW
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (face : XStarFace (transposePresentation P) z)
    (i j : Fin (S.half - 1)) (corner : Two) :=
  (rzFaceInteriorBoundaryPathToXNW P A S z copy face i j).append
    ((rzZStarFaceBoundaryPathToX (rzReplacementPresentation P A S)
      ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
      (rzFaceInteriorZStarFaceNW P A S z copy face i j)).reverse.append
      (rzZStarFaceBoundaryPathToQ (rzReplacementPresentation P A S)
        ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
        (rzFaceInteriorZStarFaceNW P A S z copy face i j) corner))

/-- Reach either Q corner of the northeast adjacent small cell. -/
private noncomputable def rzFaceInteriorBoundaryPathToQNE
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (face : XStarFace (transposePresentation P) z)
    (i j : Fin (S.half - 1)) (corner : Two) :=
  (rzFaceInteriorBoundaryPathToXNE P A S z copy face i j).append
    ((rzZStarFaceBoundaryPathToX (rzReplacementPresentation P A S)
      ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
      (rzFaceInteriorZStarFaceNE P A S z copy face i j)).reverse.append
      (rzZStarFaceBoundaryPathToQ (rzReplacementPresentation P A S)
        ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
        (rzFaceInteriorZStarFaceNE P A S z copy face i j) corner))

/-- Constructor-complete route to a local-face X boundary vertex around a
stored face-interior successor Z tag.  The raw local-face tag drives the four
finite branches; the existential boundary membership is consumed only to
refute the unreachable fallback in `Prop`. -/
private noncomputable def rzFaceInteriorBoundaryPathToLocalX
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (face : XStarFace (transposePresentation P) z)
    (i j : Fin (S.half - 1))
    (localX : Sigma fun oldZ : P.Z => ZDoubleCylinderFace P oldZ S)
    (member : zStarBoundaryVertexMember
      (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
      ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
      (Vertex.x (Sum.inl (Sum.inl localX))) = true) :
    UndirectedPath
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩)
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩)
      (rzReplacementZBoundaryRoot P A3 S
        ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩)
      ⟨Vertex.x (Sum.inl (Sum.inl localX)), member⟩ := by
  let A := A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  rw [rzReplacementZBoundaryRoot_faceInterior P A3 S z copy face i j]
  rcases localX with ⟨targetZ, cell⟩
  by_cases hz : targetZ = z
  · subst targetZ
    by_cases hSW : cell =
        (rzFaceInteriorLocalFaceSW P S z copy face i j).2.1
    · subst cell
      have htarget :
          (⟨Vertex.x (Sum.inl (Sum.inl ⟨z,
              (rzFaceInteriorLocalFaceSW P S z copy face i j).2.1⟩)), member⟩ :
            ZStarBoundaryVertex (rzReplacementPresentation P A S)
              ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩) =
          zBoundaryEdgeStart (rzReplacementPresentation P A S)
            ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
            (rzZStarFaceBoundaryEdge (rzReplacementPresentation P A S)
              ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
              (rzFaceInteriorZStarFaceSW P A S z copy face i j) 0) := by
        apply Subtype.ext
        erw [rzZStarFaceBoundaryEdge_start_value]
        rfl
      exact htarget.symm ▸ .nil
    · by_cases hSE : cell =
          (rzFaceInteriorLocalFaceSE P S z copy face i j).2.1
      · subst cell
        have htarget :
            (⟨Vertex.x (Sum.inl (Sum.inl ⟨z,
                (rzFaceInteriorLocalFaceSE P S z copy face i j).2.1⟩)), member⟩ :
              ZStarBoundaryVertex (rzReplacementPresentation P A S)
                ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩) =
            zBoundaryEdgeStart (rzReplacementPresentation P A S)
              ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
              (rzZStarFaceBoundaryEdge (rzReplacementPresentation P A S)
                ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
                (rzFaceInteriorZStarFaceSE P A S z copy face i j) 0) := by
          apply Subtype.ext
          erw [rzZStarFaceBoundaryEdge_start_value]
          rfl
        exact htarget.symm ▸
          rzFaceInteriorBoundaryPathToXSE P A S z copy face i j
      · by_cases hNW : cell =
            (rzFaceInteriorLocalFaceNW P S z copy face i j).2.1
        · subst cell
          have htarget :
              (⟨Vertex.x (Sum.inl (Sum.inl ⟨z,
                  (rzFaceInteriorLocalFaceNW P S z copy face i j).2.1⟩)), member⟩ :
                ZStarBoundaryVertex (rzReplacementPresentation P A S)
                  ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩) =
              zBoundaryEdgeStart (rzReplacementPresentation P A S)
                ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
                (rzZStarFaceBoundaryEdge (rzReplacementPresentation P A S)
                  ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
                  (rzFaceInteriorZStarFaceNW P A S z copy face i j) 0) := by
            apply Subtype.ext
            erw [rzZStarFaceBoundaryEdge_start_value]
            rfl
          exact htarget.symm ▸
            rzFaceInteriorBoundaryPathToXNW P A S z copy face i j
        · by_cases hNE : cell =
              (rzFaceInteriorLocalFaceNE P S z copy face i j).2.1
          · subst cell
            have htarget :
                (⟨Vertex.x (Sum.inl (Sum.inl ⟨z,
                    (rzFaceInteriorLocalFaceNE P S z copy face i j).2.1⟩)), member⟩ :
                  ZStarBoundaryVertex (rzReplacementPresentation P A S)
                    ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩) =
                zBoundaryEdgeStart (rzReplacementPresentation P A S)
                  ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
                  (rzZStarFaceBoundaryEdge (rzReplacementPresentation P A S)
                    ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
                    (rzFaceInteriorZStarFaceNE P A S z copy face i j) 0) := by
              apply Subtype.ext
              erw [rzZStarFaceBoundaryEdge_start_value]
              rfl
            exact htarget.symm ▸
              rzFaceInteriorBoundaryPathToXNE P A S z copy face i j
          · have himpossible : False := by
              simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
              obtain ⟨successorFace, hfaceZ, hfaceX⟩ := member
              have hfaceX' := hfaceX
              simp only [zStarFaceMember, decide_eq_true_eq] at hfaceZ
              rcases successorFace with localFace | glueOrOld
              · rcases localFace with ⟨ownerZ, ownerCell, bits⟩
                have howner : (⟨z, cell⟩ :
                    Sigma fun oldZ : P.Z => ZDoubleCylinderFace P oldZ S) =
                    ⟨ownerZ, ownerCell⟩ := by
                  change Sum.inl (Sum.inl (⟨z, cell⟩ :
                      Sigma fun oldZ : P.Z => ZDoubleCylinderFace P oldZ S)) =
                    Sum.inl (Sum.inl (⟨ownerZ, ownerCell⟩ :
                      Sigma fun oldZ : P.Z => ZDoubleCylinderFace P oldZ S))
                      at hfaceX'
                  exact Sum.inl.inj (Sum.inl.inj hfaceX')
                cases howner
                have hcorner : localCornerVertex P z S cell bits =
                    (copy, Sum.inr (Sum.inr (face, i, j))) := by
                  change rzFaceZ P A S (Sum.inl ⟨z, cell, bits⟩) =
                    ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩ at hfaceZ
                  change localFaceZ P S ⟨z, cell, bits⟩ =
                    ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩ at hfaceZ
                  rw [localFaceZ_eq_corner] at hfaceZ
                  exact eq_of_heq (Sigma.mk.inj_iff.mp hfaceZ).2
                rcases rzFaceInteriorLocalCell_cases P S z copy face i j
                    cell bits hcorner with h | h | h | h
                · cases h
                  exact hSW rfl
                · cases h
                  exact hSE rfl
                · cases h
                  exact hNW rfl
                · cases h
                  exact hNE rfl
              · rcases glueOrOld with glueFace | oldFace
                · change Sum.inl (Sum.inl (⟨z, cell⟩ :
                      Sigma fun oldZ : P.Z => ZDoubleCylinderFace P oldZ S)) =
                    rzFaceX P S (Sum.inr (Sum.inl glueFace)) at hfaceX'
                  simp only [rzFaceX, glueFaceX] at hfaceX'
                  cases Sum.inl.inj hfaceX'
                · change Sum.inl (Sum.inl (⟨z, cell⟩ :
                      Sigma fun oldZ : P.Z => ZDoubleCylinderFace P oldZ S)) =
                    rzFaceX P S (Sum.inr (Sum.inr oldFace)) at hfaceX'
                  simp only [rzFaceX, oldXFaceX] at hfaceX'
                  cases hfaceX'
            exact himpossible.elim
  · have himpossible : False := by
      simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
      obtain ⟨successorFace, hfaceZ, hfaceX⟩ := member
      have hfaceX' := hfaceX
      simp only [zStarFaceMember, decide_eq_true_eq] at hfaceZ
      rcases successorFace with localFace | glueOrOld
      · rcases localFace with ⟨ownerZ, ownerCell, bits⟩
        change Sum.inl (Sum.inl (⟨targetZ, cell⟩ :
            Sigma fun oldZ : P.Z => ZDoubleCylinderFace P oldZ S)) =
          Sum.inl (Sum.inl (⟨ownerZ, ownerCell⟩ :
            Sigma fun oldZ : P.Z => ZDoubleCylinderFace P oldZ S)) at hfaceX'
        have htargetZ : targetZ = ownerZ := congrArg Sigma.fst
          (Sum.inl.inj (Sum.inl.inj hfaceX'))
        change rzFaceZ P A S (Sum.inl ⟨ownerZ, ownerCell, bits⟩) =
          ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩ at hfaceZ
        change localFaceZ P S ⟨ownerZ, ownerCell, bits⟩ =
          ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩ at hfaceZ
        rw [localFaceZ_eq_corner] at hfaceZ
        have hownerZ : ownerZ = z := congrArg Sigma.fst hfaceZ
        exact hz (htargetZ.trans hownerZ)
      · rcases glueOrOld with glueFace | oldFace
        · change Sum.inl (Sum.inl (⟨targetZ, cell⟩ :
              Sigma fun oldZ : P.Z => ZDoubleCylinderFace P oldZ S)) =
            rzFaceX P S (Sum.inr (Sum.inl glueFace)) at hfaceX'
          simp only [rzFaceX, glueFaceX] at hfaceX'
          cases Sum.inl.inj hfaceX'
        · change Sum.inl (Sum.inl (⟨targetZ, cell⟩ :
              Sigma fun oldZ : P.Z => ZDoubleCylinderFace P oldZ S)) =
            rzFaceX P S (Sum.inr (Sum.inr oldFace)) at hfaceX'
          simp only [rzFaceX, oldXFaceX] at hfaceX'
          cases hfaceX'
    exact himpossible.elim

/-- Constructor-complete route to a local-edge Q boundary vertex around a
stored face-interior successor Z tag.  The eight ordered face corners are
tested explicitly; the boundary-membership existential is used only in the
unreachable fallback proof. -/
private noncomputable def rzFaceInteriorBoundaryPathToLocalQ
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (face : XStarFace (transposePresentation P) z)
    (i j : Fin (S.half - 1))
    (localQ : Sigma fun oldZ : P.Z => ZDoubleCylinderEdge P oldZ S)
    (member : zStarBoundaryVertexMember
      (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
      ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
      (Vertex.q (Sum.inl localQ)) = true) :
    UndirectedPath
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩)
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩)
      (rzReplacementZBoundaryRoot P A3 S
        ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩)
      ⟨Vertex.q (Sum.inl localQ), member⟩ := by
  let A := A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  rw [rzReplacementZBoundaryRoot_faceInterior P A3 S z copy face i j]
  let fixedZ : (rzReplacementPresentation P A S).Z :=
    ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
  let sw := rzFaceInteriorLocalFaceSW P S z copy face i j
  let se := rzFaceInteriorLocalFaceSE P S z copy face i j
  let nw := rzFaceInteriorLocalFaceNW P S z copy face i j
  let ne := rzFaceInteriorLocalFaceNE P S z copy face i j
  let targetQ : (rzReplacementPresentation P A S).Q := Sum.inl localQ
  by_cases hSW0 : targetQ = localFaceQ0 P S sw
  · have htarget :
        (⟨Vertex.q targetQ, member⟩ : ZStarBoundaryVertex
          (rzReplacementPresentation P A S) fixedZ) =
        zBoundaryEdgeEnd (rzReplacementPresentation P A S) fixedZ
          (rzZStarFaceBoundaryEdge (rzReplacementPresentation P A S) fixedZ
            (rzFaceInteriorZStarFaceSW P A S z copy face i j) 0) := by
      apply Subtype.ext
      rw [rzZStarFaceBoundaryEdge_end_value]
      exact congrArg Vertex.q hSW0
    exact htarget.symm ▸
      rzFaceInteriorBoundaryPathSW P A S z copy face i j 0
  · by_cases hSW1 : targetQ = localFaceQ1 P S sw
    · have htarget :
          (⟨Vertex.q targetQ, member⟩ : ZStarBoundaryVertex
            (rzReplacementPresentation P A S) fixedZ) =
          zBoundaryEdgeEnd (rzReplacementPresentation P A S) fixedZ
            (rzZStarFaceBoundaryEdge (rzReplacementPresentation P A S) fixedZ
              (rzFaceInteriorZStarFaceSW P A S z copy face i j) 1) := by
        apply Subtype.ext
        rw [rzZStarFaceBoundaryEdge_end_value]
        exact congrArg Vertex.q hSW1
      exact htarget.symm ▸
        rzFaceInteriorBoundaryPathSW P A S z copy face i j 1
    · by_cases hSE0 : targetQ = localFaceQ0 P S se
      · have htarget :
            (⟨Vertex.q targetQ, member⟩ : ZStarBoundaryVertex
              (rzReplacementPresentation P A S) fixedZ) =
            zBoundaryEdgeEnd (rzReplacementPresentation P A S) fixedZ
              (rzZStarFaceBoundaryEdge (rzReplacementPresentation P A S) fixedZ
                (rzFaceInteriorZStarFaceSE P A S z copy face i j) 0) := by
          apply Subtype.ext
          rw [rzZStarFaceBoundaryEdge_end_value]
          exact congrArg Vertex.q hSE0
        exact htarget.symm ▸
          rzFaceInteriorBoundaryPathToQSE P A S z copy face i j 0
      · by_cases hSE1 : targetQ = localFaceQ1 P S se
        · have htarget :
              (⟨Vertex.q targetQ, member⟩ : ZStarBoundaryVertex
                (rzReplacementPresentation P A S) fixedZ) =
              zBoundaryEdgeEnd (rzReplacementPresentation P A S) fixedZ
                (rzZStarFaceBoundaryEdge (rzReplacementPresentation P A S) fixedZ
                  (rzFaceInteriorZStarFaceSE P A S z copy face i j) 1) := by
            apply Subtype.ext
            rw [rzZStarFaceBoundaryEdge_end_value]
            exact congrArg Vertex.q hSE1
          exact htarget.symm ▸
            rzFaceInteriorBoundaryPathToQSE P A S z copy face i j 1
        · by_cases hNW0 : targetQ = localFaceQ0 P S nw
          · have htarget :
                (⟨Vertex.q targetQ, member⟩ : ZStarBoundaryVertex
                  (rzReplacementPresentation P A S) fixedZ) =
                zBoundaryEdgeEnd (rzReplacementPresentation P A S) fixedZ
                  (rzZStarFaceBoundaryEdge (rzReplacementPresentation P A S) fixedZ
                    (rzFaceInteriorZStarFaceNW P A S z copy face i j) 0) := by
              apply Subtype.ext
              rw [rzZStarFaceBoundaryEdge_end_value]
              exact congrArg Vertex.q hNW0
            exact htarget.symm ▸
              rzFaceInteriorBoundaryPathToQNW P A S z copy face i j 0
          · by_cases hNW1 : targetQ = localFaceQ1 P S nw
            · have htarget :
                  (⟨Vertex.q targetQ, member⟩ : ZStarBoundaryVertex
                    (rzReplacementPresentation P A S) fixedZ) =
                  zBoundaryEdgeEnd (rzReplacementPresentation P A S) fixedZ
                    (rzZStarFaceBoundaryEdge (rzReplacementPresentation P A S)
                      fixedZ (rzFaceInteriorZStarFaceNW P A S z copy face i j)
                      1) := by
                apply Subtype.ext
                rw [rzZStarFaceBoundaryEdge_end_value]
                exact congrArg Vertex.q hNW1
              exact htarget.symm ▸
                rzFaceInteriorBoundaryPathToQNW P A S z copy face i j 1
            · by_cases hNE0 : targetQ = localFaceQ0 P S ne
              · have htarget :
                    (⟨Vertex.q targetQ, member⟩ : ZStarBoundaryVertex
                      (rzReplacementPresentation P A S) fixedZ) =
                    zBoundaryEdgeEnd (rzReplacementPresentation P A S) fixedZ
                      (rzZStarFaceBoundaryEdge (rzReplacementPresentation P A S)
                        fixedZ (rzFaceInteriorZStarFaceNE P A S z copy face i j)
                        0) := by
                  apply Subtype.ext
                  rw [rzZStarFaceBoundaryEdge_end_value]
                  exact congrArg Vertex.q hNE0
                exact htarget.symm ▸
                  rzFaceInteriorBoundaryPathToQNE P A S z copy face i j 0
              · by_cases hNE1 : targetQ = localFaceQ1 P S ne
                · have htarget :
                      (⟨Vertex.q targetQ, member⟩ : ZStarBoundaryVertex
                        (rzReplacementPresentation P A S) fixedZ) =
                      zBoundaryEdgeEnd (rzReplacementPresentation P A S) fixedZ
                        (rzZStarFaceBoundaryEdge (rzReplacementPresentation P A S)
                          fixedZ
                          (rzFaceInteriorZStarFaceNE P A S z copy face i j) 1) := by
                    apply Subtype.ext
                    rw [rzZStarFaceBoundaryEdge_end_value]
                    exact congrArg Vertex.q hNE1
                  exact htarget.symm ▸
                    rzFaceInteriorBoundaryPathToQNE P A S z copy face i j 1
                · have himpossible : False := by
                    simp only [zStarBoundaryVertexMember, decide_eq_true_eq]
                      at member
                    obtain ⟨successorFace, hfaceZ, hfaceQ⟩ := member
                    simp only [zStarFaceMember, decide_eq_true_eq] at hfaceZ
                    rcases successorFace with localFace | glueOrOld
                    · rcases localFace with ⟨ownerZ, ownerCell, bits⟩
                      change rzFaceZ P A S
                          (Sum.inl ⟨ownerZ, ownerCell, bits⟩) = fixedZ
                        at hfaceZ
                      change localFaceZ P S ⟨ownerZ, ownerCell, bits⟩ =
                        fixedZ at hfaceZ
                      rw [localFaceZ_eq_corner] at hfaceZ
                      have hownerZ : ownerZ = z := congrArg Sigma.fst hfaceZ
                      subst ownerZ
                      have hcorner : localCornerVertex P z S ownerCell bits =
                          (copy, Sum.inr (Sum.inr (face, i, j))) :=
                        eq_of_heq (Sigma.mk.inj_iff.mp hfaceZ).2
                      rcases rzFaceInteriorLocalCell_cases P S z copy face i j
                          ownerCell bits hcorner with hcell | hcell | hcell | hcell
                      all_goals cases hcell
                      · rcases hfaceQ with hq | hq
                        · exact hSW0 hq
                        · exact hSW1 hq
                      · rcases hfaceQ with hq | hq
                        · exact hSE0 hq
                        · exact hSE1 hq
                      · rcases hfaceQ with hq | hq
                        · exact hNW0 hq
                        · exact hNW1 hq
                      · rcases hfaceQ with hq | hq
                        · exact hNE0 hq
                        · exact hNE1 hq
                    · rcases glueOrOld with glueFace | oldFace
                      · rcases glueFace with ⟨a, edge, endpoint⟩
                        change glueFaceZ P A S ⟨a, edge, endpoint⟩ = fixedZ
                          at hfaceZ
                        have hztag : a.1.2 = z := congrArg Sigma.fst hfaceZ
                        subst z
                        have hvertex := eq_of_heq (Sigma.mk.inj_iff.mp hfaceZ).2
                        exact (qToZDoubleCylinderVertex_ne_faceInterior P A
                          a.1.1 a.1.2 a.2 S
                          (edgeEndpoint
                            (qDoubleCylinderEdgeStart (transposePresentation P)
                              a.1.1 S)
                            (qDoubleCylinderEdgeEnd (transposePresentation P)
                              a.1.1 S) edge endpoint)
                          copy face i j) hvertex
                      · rcases hfaceQ with hq | hq
                        · change targetQ = oldXFaceQ P S 0 oldFace at hq
                          simp [targetQ, oldXFaceQ] at hq
                        · change targetQ = oldXFaceQ P S 1 oldFace at hq
                          simp [targetQ, oldXFaceQ] at hq
                  exact himpossible.elim

/-- Total historical boundary path at a stored face-interior successor Z
vertex.  The concrete successor tags determine the local X/Q dispatcher;
membership is used only to refute constructors that cannot meet a stored
square-interior coordinate. -/
private noncomputable def rzFaceInteriorBoundaryPath
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (face : XStarFace (transposePresentation P) z)
    (i j : Fin (S.half - 1))
    (vertex : ZStarBoundaryVertex (rzReplacementPresentation P
      A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
      ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩) :
    UndirectedPath
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩)
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩)
      (rzReplacementZBoundaryRoot P A3 S
        ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩)
      vertex := by
  let A := A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  rcases vertex with ⟨value, member⟩
  rcases value with successorX | successorQ | impossible
  · rcases successorX with (localX | glueX) | oldX
    · exact rzFaceInteriorBoundaryPathToLocalX
        P A3 S z copy face i j localX member
    · have himpossible : False := by
        simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
        obtain ⟨successorFace, hfaceZ, hfaceX⟩ := member
        simp only [zStarFaceMember, decide_eq_true_eq] at hfaceZ
        rcases successorFace with localFace | glueOrOld
        · change Sum.inl (Sum.inr glueX) =
            rzFaceX P S (Sum.inl localFace) at hfaceX
          simp [rzFaceX, localFaceX] at hfaceX
        · rcases glueOrOld with glueFace | oldFace
          · rcases glueFace with ⟨a, edge, endpoint⟩
            change glueFaceZ P A S ⟨a, edge, endpoint⟩ =
              ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩ at hfaceZ
            have hztag : a.1.2 = z := congrArg Sigma.fst hfaceZ
            subst z
            have hvertex := eq_of_heq (Sigma.mk.inj_iff.mp hfaceZ).2
            exact (qToZDoubleCylinderVertex_ne_faceInterior P A
              a.1.1 a.1.2 a.2 S
              (edgeEndpoint
                (qDoubleCylinderEdgeStart (transposePresentation P) a.1.1 S)
                (qDoubleCylinderEdgeEnd (transposePresentation P) a.1.1 S)
                edge endpoint)
              copy face i j) hvertex
          · rcases oldFace with ⟨oldFace, oldCopy⟩
            change Sum.inl (Sum.inr glueX) =
              oldXFaceX P S (oldFace, oldCopy) at hfaceX
            simp [oldXFaceX] at hfaceX
      exact himpossible.elim
    · have himpossible : False := by
        simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
        obtain ⟨successorFace, hfaceZ, hfaceX⟩ := member
        simp only [zStarFaceMember, decide_eq_true_eq] at hfaceZ
        rcases successorFace with localFace | glueOrOld
        · change Sum.inr oldX = localFaceX P S localFace at hfaceX
          simp [localFaceX] at hfaceX
        · rcases glueOrOld with glueFace | oldFace
          · change Sum.inr oldX = glueFaceX P S glueFace at hfaceX
            simp [glueFaceX] at hfaceX
          · rcases oldFace with ⟨oldFace, faceCopy⟩
            change oldXFaceZ P S (oldFace, faceCopy) =
              ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩ at hfaceZ
            simp only [oldXFaceZ, Sigma.mk.inj_iff] at hfaceZ
            have hztag := hfaceZ.1
            subst z
            have hvertex := eq_of_heq hfaceZ.2
            simp at hvertex
      exact himpossible.elim
  · rcases successorQ with localQ | qVertex
    · exact rzFaceInteriorBoundaryPathToLocalQ
        P A3 S z copy face i j localQ member
    · have himpossible : False := by
        simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
        obtain ⟨successorFace, hfaceZ, hfaceQ⟩ := member
        simp only [zStarFaceMember, decide_eq_true_eq] at hfaceZ
        rcases successorFace with localFace | glueOrOld
        · rcases localFace with ⟨ownerZ, ownerCell, bits⟩
          rcases ownerCell with copyFace | boundaryEdge
          · rcases hfaceQ with hq | hq
            · change Sum.inr qVertex =
                localFaceQ0 P S ⟨ownerZ, Sum.inl copyFace, bits⟩ at hq
              simp [localFaceQ0] at hq
            · change Sum.inr qVertex =
                localFaceQ1 P S ⟨ownerZ, Sum.inl copyFace, bits⟩ at hq
              simp [localFaceQ1] at hq
          · rcases hfaceQ with hq | hq
            · change Sum.inr qVertex =
                localFaceQ0 P S ⟨ownerZ, Sum.inr boundaryEdge, bits⟩ at hq
              simp [localFaceQ0] at hq
            · change Sum.inr qVertex =
                localFaceQ1 P S ⟨ownerZ, Sum.inr boundaryEdge, bits⟩ at hq
              simp [localFaceQ1] at hq
        · rcases glueOrOld with glueFace | oldFace
          · rcases glueFace with ⟨a, edge, endpoint⟩
            change glueFaceZ P A S ⟨a, edge, endpoint⟩ =
              ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩ at hfaceZ
            have hztag : a.1.2 = z := congrArg Sigma.fst hfaceZ
            subst z
            have hvertex := eq_of_heq (Sigma.mk.inj_iff.mp hfaceZ).2
            exact (qToZDoubleCylinderVertex_ne_faceInterior P A
              a.1.1 a.1.2 a.2 S
              (edgeEndpoint
                (qDoubleCylinderEdgeStart (transposePresentation P) a.1.1 S)
                (qDoubleCylinderEdgeEnd (transposePresentation P) a.1.1 S)
                edge endpoint)
              copy face i j) hvertex
          · rcases oldFace with ⟨oldFace, faceCopy⟩
            change oldXFaceZ P S (oldFace, faceCopy) =
              ⟨z, (copy, Sum.inr (Sum.inr (face, i, j)))⟩ at hfaceZ
            simp only [oldXFaceZ, Sigma.mk.inj_iff] at hfaceZ
            have hztag := hfaceZ.1
            subst z
            have hvertex := eq_of_heq hfaceZ.2
            simp at hvertex
      exact himpossible.elim
  · simp [zStarBoundaryVertexMember] at member

/-! ### Fixed-Z star-edge-interior link -/

/-- A grid vertex carrying a stored star-edge-interior tag lies on exactly
one of the four boundary sides of the candidate original face.  This is a
`Prop`-only constructor inversion: it recovers equalities but does not select
a face, corner, or path. -/
private theorem subdivisionGridVertex_eq_starEdgeInterior
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale)
    (candidate : XStarFace (transposePresentation P) z)
    (u v : Fin (S.half + 1))
    (starEdge : XStarEdge (transposePresentation P) z)
    (index : Fin (S.half - 1))
    (h : subdivisionGridVertex (transposePresentation P) z S candidate u v =
      Sum.inr (Sum.inl (starEdge, index))) :
    (starEdge = xStarFaceXQEdge (transposePresentation P) z candidate 1 ∧
        u.1 = 0 ∧ v.1 = index.1 + 1) ∨
      (starEdge = xStarFaceQZEdge (transposePresentation P) z candidate 0 ∧
        u.1 = S.half ∧ v.1 = index.1 + 1) ∨
      (starEdge = xStarFaceXQEdge (transposePresentation P) z candidate 0 ∧
        u.1 = index.1 + 1 ∧ v.1 = 0) ∨
      (starEdge = xStarFaceQZEdge (transposePresentation P) z candidate 1 ∧
        u.1 = index.1 + 1 ∧ v.1 = S.half) := by
  dsimp only [subdivisionGridVertex] at h
  split at h <;> rename_i hu0
  · split at h <;> rename_i hv0
    · cases h
    · split at h <;> rename_i hvlast
      · cases h
      · left
        have hpayload := Sum.inl.inj (Sum.inr.inj h)
        have hedge :
            xStarFaceXQEdge (transposePresentation P) z candidate 1 =
              starEdge := congrArg Prod.fst hpayload
        have hindex := congrArg Fin.val
          (congrArg Prod.snd hpayload)
        change v.1 - 1 = index.1 at hindex
        exact ⟨hedge.symm, hu0, by omega⟩
  · split at h <;> rename_i hulast
    · split at h <;> rename_i hv0
      · cases h
      · split at h <;> rename_i hvlast
        · cases h
        · right; left
          have hpayload := Sum.inl.inj (Sum.inr.inj h)
          have hedge :
              xStarFaceQZEdge (transposePresentation P) z candidate 0 =
                starEdge := congrArg Prod.fst hpayload
          have hindex := congrArg Fin.val
            (congrArg Prod.snd hpayload)
          change v.1 - 1 = index.1 at hindex
          exact ⟨hedge.symm, hulast, by omega⟩
    · split at h <;> rename_i hv0
      · right; right; left
        have hpayload := Sum.inl.inj (Sum.inr.inj h)
        have hedge :
            xStarFaceXQEdge (transposePresentation P) z candidate 0 =
              starEdge := congrArg Prod.fst hpayload
        have hindex := congrArg Fin.val
          (congrArg Prod.snd hpayload)
        change u.1 - 1 = index.1 at hindex
        exact ⟨hedge.symm, by omega, hv0⟩
      · split at h <;> rename_i hvlast
        · right; right; right
          have hpayload := Sum.inl.inj (Sum.inr.inj h)
          have hedge :
              xStarFaceQZEdge (transposePresentation P) z candidate 1 =
                starEdge := congrArg Prod.fst hpayload
          have hindex := congrArg Fin.val
            (congrArg Prod.snd hpayload)
          change u.1 - 1 = index.1 at hindex
          exact ⟨hedge.symm, by omega, hvlast⟩
        · cases Sum.inr.inj h

/-- The segment ending at a stored path-interior star-edge vertex. -/
private def rzStarEdgeInteriorPrecedingSegment (S : OddScale)
    (index : Fin (S.half - 1)) : Fin S.half :=
  ⟨index.1, by have := index.2; omega⟩

/-- The segment starting at a stored path-interior star-edge vertex. -/
private def rzStarEdgeInteriorNextSegment (S : OddScale)
    (index : Fin (S.half - 1)) : Fin S.half :=
  ⟨index.1 + 1, by have := index.2; omega⟩

/-- The explicit end-copy cylinder edge over one segment of the stored star
edge. -/
private def rzStarEdgeInteriorEndEdge
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z)
    (copy : Two) (starEdge : XStarEdge (transposePresentation P) z)
    (segment : Fin S.half) : ZDoubleCylinderEdge P z S :=
  Sum.inl (copy, Sum.inl (starEdge, segment))

/-- The explicit owner face and corner over a chosen endpoint of one stored
star-edge segment.  Both choices are constructor data; no incident face is
recovered from an existential boundary witness. -/
private noncomputable def rzStarEdgeInteriorLocalAnchor
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (starEdge : XStarEdge (transposePresentation P) z)
    (segment : Fin S.half) (endpoint : Two) : RZLocalFace P S × Two := by
  let edge := rzStarEdgeInteriorEndEdge P S z copy starEdge segment
  let owner := doubleCylinderEdgeFaceSlotOwner (transposePresentation P)
    (transposeTannerSquareAdmissibleV3 P A3) z S edge
  let corner := localCornerAtBoundaryEndpoint P z S
    owner.1.1 owner.1.2 endpoint
  exact (⟨z, owner.1.1, corner.1.1⟩, corner.1.2)

private noncomputable def rzStarEdgeInteriorPrecedingAnchor
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (starEdge : XStarEdge (transposePresentation P) z)
    (index : Fin (S.half - 1)) : RZLocalFace P S × Two :=
  rzStarEdgeInteriorLocalAnchor P A3 S z copy starEdge
    (rzStarEdgeInteriorPrecedingSegment S index) 1

private noncomputable def rzStarEdgeInteriorNextAnchor
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (starEdge : XStarEdge (transposePresentation P) z)
    (index : Fin (S.half - 1)) : RZLocalFace P S × Two :=
  rzStarEdgeInteriorLocalAnchor P A3 S z copy starEdge
    (rzStarEdgeInteriorNextSegment S index) 0

/-- The preceding owner corner is exactly the stored path-interior vertex. -/
private theorem rzStarEdgeInteriorPrecedingAnchorZ_eq
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (starEdge : XStarEdge (transposePresentation P) z)
    (index : Fin (S.half - 1)) :
    localFaceZ P S
        (rzStarEdgeInteriorPrecedingAnchor P A3 S z copy starEdge index).1 =
      ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩ := by
  let segment := rzStarEdgeInteriorPrecedingSegment S index
  let edge := rzStarEdgeInteriorEndEdge P S z copy starEdge segment
  let owner := doubleCylinderEdgeFaceSlotOwner (transposePresentation P)
    (transposeTannerSquareAdmissibleV3 P A3) z S edge
  let corner := localCornerAtBoundaryEndpoint P z S
    owner.1.1 owner.1.2 1
  change localFaceZ P S ⟨z, owner.1.1, corner.1.1⟩ = _
  rw [localFaceZ_eq_localCornerVertex]
  apply Sigma.ext
    (x := (⟨z, localCornerVertex P z S owner.1.1 corner.1.1⟩ : RZZ P S))
    (y := ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩) rfl
  apply heq_of_eq
  calc
    localCornerVertex P z S owner.1.1 corner.1.1 =
        BDL26TannerLocalRegularity.edgeEndpoint
          (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
          (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
          (doubleCylinderFaceBoundaryEdge (transposePresentation P) z S
            owner.1.1 owner.1.2) 1 := corner.2.2
    _ = BDL26TannerLocalRegularity.edgeEndpoint
          (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
          (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S) edge 1 := by
        rw [owner.2]
    _ = (copy, Sum.inr (Sum.inl (starEdge, index))) := by
      rw [BDL26TannerLocalRegularity.edgeEndpoint_one]
      have hnot : segment.1 + 1 ≠ S.half := by
        dsimp [segment, rzStarEdgeInteriorPrecedingSegment]
        have := (Nat.lt_sub_iff_add_lt).1 index.2
        omega
      simp [edge, rzStarEdgeInteriorEndEdge, tannerDoubleCylinderEdgeEnd,
        subdivisionEdgeEnd, subdivisionSegmentEnd, segment, hnot]
      apply Fin.ext
      rfl

/-- The next owner corner is the same stored path-interior vertex. -/
private theorem rzStarEdgeInteriorNextAnchorZ_eq
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (starEdge : XStarEdge (transposePresentation P) z)
    (index : Fin (S.half - 1)) :
    localFaceZ P S
        (rzStarEdgeInteriorNextAnchor P A3 S z copy starEdge index).1 =
      ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩ := by
  let segment := rzStarEdgeInteriorNextSegment S index
  let edge := rzStarEdgeInteriorEndEdge P S z copy starEdge segment
  let owner := doubleCylinderEdgeFaceSlotOwner (transposePresentation P)
    (transposeTannerSquareAdmissibleV3 P A3) z S edge
  let corner := localCornerAtBoundaryEndpoint P z S
    owner.1.1 owner.1.2 0
  change localFaceZ P S ⟨z, owner.1.1, corner.1.1⟩ = _
  rw [localFaceZ_eq_localCornerVertex]
  apply Sigma.ext
    (x := (⟨z, localCornerVertex P z S owner.1.1 corner.1.1⟩ : RZZ P S))
    (y := ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩) rfl
  apply heq_of_eq
  calc
    localCornerVertex P z S owner.1.1 corner.1.1 =
        BDL26TannerLocalRegularity.edgeEndpoint
          (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
          (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
          (doubleCylinderFaceBoundaryEdge (transposePresentation P) z S
            owner.1.1 owner.1.2) 0 := corner.2.2
    _ = BDL26TannerLocalRegularity.edgeEndpoint
          (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
          (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S) edge 0 := by
        rw [owner.2]
    _ = (copy, Sum.inr (Sum.inl (starEdge, index))) := by
      rw [BDL26TannerLocalRegularity.edgeEndpoint_zero]
      have hnot : segment.1 ≠ 0 := by
        dsimp [segment, rzStarEdgeInteriorNextSegment]
        omega
      simp [edge, rzStarEdgeInteriorEndEdge, tannerDoubleCylinderEdgeStart,
        subdivisionEdgeStart, subdivisionSegmentStart, segment, hnot]
      apply Fin.ext
      dsimp [segment, rzStarEdgeInteriorNextSegment]

private noncomputable def rzStarEdgeInteriorPrecedingZStarFace
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (starEdge : XStarEdge (transposePresentation P) z)
    (index : Fin (S.half - 1)) :
    ZStarFace (rzReplacementPresentation P
      A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
      ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩ :=
  ⟨Sum.inl
      (rzStarEdgeInteriorPrecedingAnchor P A3 S z copy starEdge index).1, by
    simp only [zStarFaceMember, decide_eq_true_eq]
    rw [show (rzReplacementPresentation P
      A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S).faceZ =
        rzFaceZ P A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S
      from rfl]
    exact rzStarEdgeInteriorPrecedingAnchorZ_eq P A3 S z copy starEdge index⟩

private noncomputable def rzStarEdgeInteriorNextZStarFace
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (starEdge : XStarEdge (transposePresentation P) z)
    (index : Fin (S.half - 1)) :
    ZStarFace (rzReplacementPresentation P
      A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
      ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩ :=
  ⟨Sum.inl (rzStarEdgeInteriorNextAnchor P A3 S z copy starEdge index).1, by
    simp only [zStarFaceMember, decide_eq_true_eq]
    rw [show (rzReplacementPresentation P
      A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S).faceZ =
        rzFaceZ P A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S
      from rfl]
    exact rzStarEdgeInteriorNextAnchorZ_eq P A3 S z copy starEdge index⟩

/-- At a stored star-edge-interior successor Z vertex, the deterministic root
is the X endpoint of the explicitly constructed preceding-segment owner. -/
private theorem rzReplacementZBoundaryRoot_starEdgeInterior
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (starEdge : XStarEdge (transposePresentation P) z)
    (index : Fin (S.half - 1)) :
    rzReplacementZBoundaryRoot P A3 S
        ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩ =
      zBoundaryEdgeStart (rzReplacementPresentation P
          A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩
        (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
            A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
          ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩
          (rzStarEdgeInteriorPrecedingZStarFace P A3 S z copy starEdge index)
          (rzStarEdgeInteriorPrecedingAnchor P A3 S z copy starEdge index).2) := by
  let preceding := rzStarEdgeInteriorPrecedingSegment S index
  have hnot : preceding.1 + 1 ≠ S.half := by
    dsimp [preceding, rzStarEdgeInteriorPrecedingSegment]
    have := (Nat.lt_sub_iff_add_lt).1 index.2
    omega
  have hincident :
      (doubleCylinderVertexIncidentEdge (transposePresentation P)
        (transposeTannerSquareAdmissibleV3 P A3) z S
        (copy, Sum.inr (Sum.inl (starEdge, index)))).1.1 =
      rzStarEdgeInteriorEndEdge P S z copy starEdge preceding := by
    simp [doubleCylinderVertexIncidentEdge, subdivisionVertexIncidentEdge,
      rzStarEdgeInteriorEndEdge, preceding, subdivisionEdgeEnd,
      subdivisionSegmentEnd, hnot]
    apply Fin.ext
    rfl
  apply Subtype.ext
  rw [rzReplacementZBoundaryRoot_value]
  erw [rzZStarFaceBoundaryEdge_start_value]
  rw [hincident]
  rfl

/-- The other ordered Q corner of a local face. -/
private def rzOtherCorner (corner : Two) : Two :=
  twoSelect 1 0 corner

private theorem rzOtherCorner_ne (corner : Two) : rzOtherCorner corner ≠ corner := by
  fin_cases corner <;> decide

/-- The distinguished Q corner of either anchor is exactly its stored
preceding/next end-copy edge. -/
private theorem rzStarEdgeInteriorAnchorQ_eq
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (starEdge : XStarEdge (transposePresentation P) z)
    (segment : Fin S.half) (endpoint : Two) :
    (rzReplacementPresentation P
      A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S).faceQ
        (Sum.inl (rzStarEdgeInteriorLocalAnchor P A3 S z copy starEdge
          segment endpoint).1)
        (rzStarEdgeInteriorLocalAnchor P A3 S z copy starEdge
          segment endpoint).2 =
      Sum.inl ⟨z, rzStarEdgeInteriorEndEdge P S z copy starEdge segment⟩ := by
  let edge := rzStarEdgeInteriorEndEdge P S z copy starEdge segment
  let owner := doubleCylinderEdgeFaceSlotOwner (transposePresentation P)
    (transposeTannerSquareAdmissibleV3 P A3) z S edge
  let corner := localCornerAtBoundaryEndpoint P z S
    owner.1.1 owner.1.2 endpoint
  change twoSelect (localFaceQ0 P S ⟨z, owner.1.1, corner.1.1⟩)
      (localFaceQ1 P S ⟨z, owner.1.1, corner.1.1⟩) corner.1.2 = _
  rw [localFaceQ_eq_corner]
  apply congrArg Sum.inl
  apply Sigma.ext
    (x := (⟨z, localCornerEdge P z S owner.1.1
      (corner.1.1, corner.1.2)⟩ : Sigma fun oldZ : P.Z =>
        ZDoubleCylinderEdge P oldZ S))
    (y := ⟨z, rzStarEdgeInteriorEndEdge P S z copy starEdge segment⟩) rfl
  apply heq_of_eq
  exact corner.2.1.trans owner.2

/-- The non-segment Q corners of the preceding and next owner faces agree.
For a radial edge this is their common transverse grid edge; for a boundary
edge this is the common vertical rectangle edge at the stored vertex. -/
private theorem rzStarEdgeInteriorAnchorBridgeQ_eq
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (starEdge : XStarEdge (transposePresentation P) z)
    (index : Fin (S.half - 1)) :
    (rzReplacementPresentation P
      A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S).faceQ
        (Sum.inl
          (rzStarEdgeInteriorPrecedingAnchor P A3 S z copy starEdge index).1)
        (rzOtherCorner
          (rzStarEdgeInteriorPrecedingAnchor P A3 S z copy starEdge index).2) =
      (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S).faceQ
          (Sum.inl
            (rzStarEdgeInteriorNextAnchor P A3 S z copy starEdge index).1)
          (rzOtherCorner
            (rzStarEdgeInteriorNextAnchor P A3 S z copy starEdge index).2) := by
  change twoSelect
      (localFaceQ0 P S
        (rzStarEdgeInteriorPrecedingAnchor P A3 S z copy starEdge index).1)
      (localFaceQ1 P S
        (rzStarEdgeInteriorPrecedingAnchor P A3 S z copy starEdge index).1)
      (rzOtherCorner
        (rzStarEdgeInteriorPrecedingAnchor P A3 S z copy starEdge index).2) =
    twoSelect
      (localFaceQ0 P S
        (rzStarEdgeInteriorNextAnchor P A3 S z copy starEdge index).1)
      (localFaceQ1 P S
        (rzStarEdgeInteriorNextAnchor P A3 S z copy starEdge index).1)
      (rzOtherCorner
        (rzStarEdgeInteriorNextAnchor P A3 S z copy starEdge index).2)
  rcases starEdge with ⟨rawEdge, member⟩
  rcases rawEdge with radial | boundary
  · let owner :=
      (transposeTannerSquareAdmissibleV3 P A3).xRadialFaceOwner z radial member
    generalize hcorner : owner.1.2 = ownerCorner
    fin_cases ownerCorner
    · have hc : owner.1.2 = 0 := hcorner
      simp [rzStarEdgeInteriorPrecedingAnchor,
        rzStarEdgeInteriorNextAnchor, rzStarEdgeInteriorLocalAnchor,
        rzStarEdgeInteriorEndEdge, doubleCylinderEdgeFaceSlotOwner,
        radialSubdivisionFaceSlotOwner,
        radialSubdivisionFaceSlotOwnerValue, owner, hc,
        localCornerAtBoundaryEndpoint,
        rzStarEdgeInteriorPrecedingSegment, rzStarEdgeInteriorNextSegment,
        rzOtherCorner, rzReplacementPresentation, rzReplacementData,
        rzFaceQ, localFaceQ0, localFaceQ1, twoSelect,
        subdivisionHorizontalEdge, subdivisionVerticalEdge, gridEndpoint,
        lowerGridIndex, upperGridIndex, rzRadialGridZero]
    · have hc : owner.1.2 = 1 := hcorner
      simp [rzStarEdgeInteriorPrecedingAnchor,
        rzStarEdgeInteriorNextAnchor, rzStarEdgeInteriorLocalAnchor,
        rzStarEdgeInteriorEndEdge, doubleCylinderEdgeFaceSlotOwner,
        radialSubdivisionFaceSlotOwner,
        radialSubdivisionFaceSlotOwnerValue, owner, hc,
        localCornerAtBoundaryEndpoint,
        rzStarEdgeInteriorPrecedingSegment, rzStarEdgeInteriorNextSegment,
        rzOtherCorner, rzReplacementPresentation, rzReplacementData,
        rzFaceQ, localFaceQ0, localFaceQ1, twoSelect,
        subdivisionHorizontalEdge, subdivisionVerticalEdge, gridEndpoint,
        lowerGridIndex, upperGridIndex, rzRadialGridZero]
  · simp [rzStarEdgeInteriorPrecedingAnchor,
      rzStarEdgeInteriorNextAnchor, rzStarEdgeInteriorLocalAnchor,
      rzStarEdgeInteriorEndEdge, doubleCylinderEdgeFaceSlotOwner,
      localCornerAtBoundaryEndpoint,
      rzStarEdgeInteriorPrecedingSegment, rzStarEdgeInteriorNextSegment,
      rzOtherCorner, rzReplacementPresentation, rzReplacementData,
      rzFaceQ, localFaceQ0, localFaceQ1, twoSelect,
      edgeEndpoint, doubleCylinderRectangleBoundaryEdge,
      subdivisionBoundaryEdgeStart_value, subdivisionBoundaryEdgeEnd_value,
      subdivisionOriginalBoundaryEdge]
    apply Subtype.ext
    have hpre : index.1 + 1 ≠ S.half := by
      have := (Nat.lt_sub_iff_add_lt).1 index.2
      omega
    have hnext : index.1 + 1 ≠ 0 := by omega
    dsimp only [subdivisionBoundaryEdgeStart, subdivisionBoundaryEdgeEnd]
    simp [subdivisionBoundaryEdgeStart_value,
      subdivisionBoundaryEdgeEnd_value, subdivisionEdgeStart,
      subdivisionEdgeEnd, subdivisionSegmentStart, subdivisionSegmentEnd,
      rzStarEdgeInteriorPrecedingSegment, rzStarEdgeInteriorNextSegment,
      hpre, hnext]

/-- At any materialized local-face corner carrying the fixed star-edge-
interior vertex, one of the two ordered corner edges is the explicit
preceding or next segment.  The proof only eliminates constructors in
`Prop`; it does not recover the face as data. -/
private theorem rzStarEdgeInteriorLocalCornerEdge_cases
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z)
    (copy : Two) (starEdge : XStarEdge (transposePresentation P) z)
    (index : Fin (S.half - 1))
    (cell : ZDoubleCylinderFace P z S) (bits : Two × Two)
    (h : localCornerVertex P z S cell bits =
      (copy, Sum.inr (Sum.inl (starEdge, index)))) :
    localCornerEdge P z S cell (bits, 0) =
        rzStarEdgeInteriorEndEdge P S z copy starEdge
          (rzStarEdgeInteriorPrecedingSegment S index) ∨
      localCornerEdge P z S cell (bits, 0) =
        rzStarEdgeInteriorEndEdge P S z copy starEdge
          (rzStarEdgeInteriorNextSegment S index) ∨
      localCornerEdge P z S cell (bits, 1) =
        rzStarEdgeInteriorEndEdge P S z copy starEdge
          (rzStarEdgeInteriorPrecedingSegment S index) ∨
      localCornerEdge P z S cell (bits, 1) =
        rzStarEdgeInteriorEndEdge P S z copy starEdge
          (rzStarEdgeInteriorNextSegment S index) := by
  rcases cell with copyFace | rectangle
  · rcases copyFace with ⟨candidateCopy, candidate, a, b⟩
    have hcopy : candidateCopy = copy := congrArg Prod.fst h
    have hgrid : subdivisionGridVertex (transposePresentation P) z S
        candidate (gridEndpoint a bits.1) (gridEndpoint b bits.2) =
          Sum.inr (Sum.inl (starEdge, index)) := congrArg Prod.snd h
    obtain hside | hside | hside | hside :=
      subdivisionGridVertex_eq_starEdgeInterior P z S candidate
        (gridEndpoint a bits.1) (gridEndpoint b bits.2)
        starEdge index hgrid
    · rcases hside with ⟨hedge, hu, hv⟩
      rcases bits with ⟨first, second⟩
      have huFin : gridEndpoint a first = 0 := Fin.ext hu
      subst candidateCopy
      fin_cases second
      · right; right; right
        simp [localCornerEdge, huFin, subdivisionVerticalEdge,
          rzStarEdgeInteriorEndEdge, hedge,
          rzStarEdgeInteriorNextSegment]
        apply Fin.ext
        exact hv
      · right; right; left
        simp [localCornerEdge, huFin, subdivisionVerticalEdge,
          rzStarEdgeInteriorEndEdge, hedge,
          rzStarEdgeInteriorPrecedingSegment]
        apply Fin.ext
        have := hv
        change b.1 + 1 = index.1 + 1 at this
        exact Nat.add_right_cancel this
    · rcases hside with ⟨hedge, hu, hv⟩
      rcases bits with ⟨first, second⟩
      have huFin : (gridEndpoint a first).1 = S.half := hu
      subst candidateCopy
      fin_cases second
      · right; right; right
        have hhalf : S.half ≠ 0 := Nat.ne_of_gt S.half_pos
        simp [localCornerEdge, subdivisionVerticalEdge, huFin,
          rzStarEdgeInteriorEndEdge, hedge,
          rzStarEdgeInteriorNextSegment, hhalf]
        apply Fin.ext
        exact hv
      · right; right; left
        have hhalf : S.half ≠ 0 := Nat.ne_of_gt S.half_pos
        simp [localCornerEdge, subdivisionVerticalEdge, huFin,
          rzStarEdgeInteriorEndEdge, hedge,
          rzStarEdgeInteriorPrecedingSegment, hhalf]
        apply Fin.ext
        have := hv
        change b.1 + 1 = index.1 + 1 at this
        exact Nat.add_right_cancel this
    · rcases hside with ⟨hedge, hu, hv⟩
      rcases bits with ⟨first, second⟩
      have hvFin : gridEndpoint b second = 0 := Fin.ext hv
      subst candidateCopy
      fin_cases first
      · right; left
        simp [localCornerEdge, hvFin, subdivisionHorizontalEdge,
          rzStarEdgeInteriorEndEdge, hedge,
          rzStarEdgeInteriorNextSegment]
        apply Fin.ext
        exact hu
      · left
        simp [localCornerEdge, hvFin, subdivisionHorizontalEdge,
          rzStarEdgeInteriorEndEdge, hedge,
          rzStarEdgeInteriorPrecedingSegment]
        apply Fin.ext
        have := hu
        change a.1 + 1 = index.1 + 1 at this
        exact Nat.add_right_cancel this
    · rcases hside with ⟨hedge, hu, hv⟩
      rcases bits with ⟨first, second⟩
      have hvFin : (gridEndpoint b second).1 = S.half := hv
      subst candidateCopy
      fin_cases first
      · right; left
        have hhalf : S.half ≠ 0 := Nat.ne_of_gt S.half_pos
        simp [localCornerEdge, subdivisionHorizontalEdge, hvFin,
          rzStarEdgeInteriorEndEdge, hedge,
          rzStarEdgeInteriorNextSegment, hhalf]
        apply Fin.ext
        exact hu
      · left
        have hhalf : S.half ≠ 0 := Nat.ne_of_gt S.half_pos
        simp [localCornerEdge, subdivisionHorizontalEdge, hvFin,
          rzStarEdgeInteriorEndEdge, hedge,
          rzStarEdgeInteriorPrecedingSegment, hhalf]
        apply Fin.ext
        have := hu
        change a.1 + 1 = index.1 + 1 at this
        exact Nat.add_right_cancel this
  · rcases rectangle with ⟨rawEdge, boundary⟩
    rcases rawEdge with boundarySegment | interior
    · rcases boundarySegment with ⟨candidateEdge, segment⟩
      rcases bits with ⟨candidateCopy, endpoint⟩
      fin_cases endpoint
      · change (candidateCopy, subdivisionSegmentStart
          (transposePresentation P) z S candidateEdge segment) =
            (copy, Sum.inr (Sum.inl (starEdge, index))) at h
        have hcopy : candidateCopy = copy := congrArg Prod.fst h
        have hvertex := congrArg Prod.snd h
        dsimp only [subdivisionSegmentStart] at hvertex
        by_cases hzero : segment.1 = 0
        · simp [hzero] at hvertex
        · simp [hzero] at hvertex
          rcases hvertex with ⟨hedge, hsegment⟩
          have hindex := congrArg Fin.val hsegment
          change segment.1 - 1 = index.1 at hindex
          right; left
          simp [localCornerEdge, rzStarEdgeInteriorEndEdge, hcopy, hedge,
            rzStarEdgeInteriorNextSegment]
          apply Fin.ext
          calc
            segment.1 = segment.1 - 1 + 1 :=
              (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hzero)).symm
            _ = index.1 + 1 := congrArg (fun n => n + 1) hindex
      · change (candidateCopy, subdivisionSegmentEnd
          (transposePresentation P) z S candidateEdge segment) =
            (copy, Sum.inr (Sum.inl (starEdge, index))) at h
        have hcopy : candidateCopy = copy := congrArg Prod.fst h
        have hvertex := congrArg Prod.snd h
        dsimp only [subdivisionSegmentEnd] at hvertex
        by_cases hlast : segment.1 + 1 = S.half
        · simp [hlast] at hvertex
        · simp [hlast] at hvertex
          rcases hvertex with ⟨hedge, hsegment⟩
          have hindex := congrArg Fin.val hsegment
          change segment.1 = index.1 at hindex
          left
          simp [localCornerEdge, rzStarEdgeInteriorEndEdge, hcopy, hedge,
            rzStarEdgeInteriorPrecedingSegment]
          apply Fin.ext
          exact hindex
    · simp [subdivisionBoundaryEdgeMember] at boundary

/-- Reach either ordered Q corner of the preceding anchor face from the
deterministic root. -/
private noncomputable def rzStarEdgeInteriorBoundaryPathToPrecedingQ
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (starEdge : XStarEdge (transposePresentation P) z)
    (index : Fin (S.half - 1)) (corner : Two) :
    UndirectedPath
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩)
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩)
      (rzReplacementZBoundaryRoot P A3 S
        ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩)
      (zBoundaryEdgeEnd (rzReplacementPresentation P
          A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩
        (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
            A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
          ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩
          (rzStarEdgeInteriorPrecedingZStarFace P A3 S z copy starEdge index)
          corner)) := by
  let A := A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  let fixedZ : (rzReplacementPresentation P A S).Z :=
    ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩
  let face := rzStarEdgeInteriorPrecedingZStarFace P A3 S z copy starEdge index
  rw [rzReplacementZBoundaryRoot_starEdgeInterior P A3 S z copy starEdge index]
  exact (rzZStarFaceBoundaryPathToX
      (rzReplacementPresentation P A S) fixedZ face).reverse.append
    (rzZStarFaceBoundaryPathToQ
      (rzReplacementPresentation P A S) fixedZ face corner)

/-- Reach the X endpoint of the next-segment anchor through the Q edge shared
by the two explicit owner faces. -/
private noncomputable def rzStarEdgeInteriorBoundaryPathToNextX
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (starEdge : XStarEdge (transposePresentation P) z)
    (index : Fin (S.half - 1)) :
    UndirectedPath
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩)
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩)
      (rzReplacementZBoundaryRoot P A3 S
        ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩)
      (zBoundaryEdgeStart (rzReplacementPresentation P
          A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩
        (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
            A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
          ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩
          (rzStarEdgeInteriorNextZStarFace P A3 S z copy starEdge index) 0)) := by
  let A := A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  let fixedZ : (rzReplacementPresentation P A S).Z :=
    ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩
  let pre := rzStarEdgeInteriorPrecedingAnchor P A3 S z copy starEdge index
  let next := rzStarEdgeInteriorNextAnchor P A3 S z copy starEdge index
  let nextFace := rzStarEdgeInteriorNextZStarFace P A3 S z copy starEdge index
  let first := rzStarEdgeInteriorBoundaryPathToPrecedingQ
    P A3 S z copy starEdge index (rzOtherCorner pre.2)
  let last := (rzZStarFaceBoundaryPathToQ
      (rzReplacementPresentation P A S) fixedZ nextFace
      (rzOtherCorner next.2)).reverse.append
    (rzZStarFaceBoundaryPathToX
      (rzReplacementPresentation P A S) fixedZ nextFace)
  have hbridge :
      zBoundaryEdgeEnd (rzReplacementPresentation P A S) fixedZ
          (rzZStarFaceBoundaryEdge (rzReplacementPresentation P A S) fixedZ
            (rzStarEdgeInteriorPrecedingZStarFace
              P A3 S z copy starEdge index) (rzOtherCorner pre.2)) =
        zBoundaryEdgeEnd (rzReplacementPresentation P A S) fixedZ
          (rzZStarFaceBoundaryEdge (rzReplacementPresentation P A S) fixedZ
            nextFace (rzOtherCorner next.2)) := by
    apply Subtype.ext
    rw [rzZStarFaceBoundaryEdge_end_value, rzZStarFaceBoundaryEdge_end_value]
    exact congrArg Vertex.q
      (rzStarEdgeInteriorAnchorBridgeQ_eq P A3 S z copy starEdge index)
  exact first.append
    (hbridge ▸ last)

/-- Reach either ordered Q corner of the next anchor face. -/
private noncomputable def rzStarEdgeInteriorBoundaryPathToNextQ
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (starEdge : XStarEdge (transposePresentation P) z)
    (index : Fin (S.half - 1)) (corner : Two) :
    UndirectedPath
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩)
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩)
      (rzReplacementZBoundaryRoot P A3 S
        ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩)
      (zBoundaryEdgeEnd (rzReplacementPresentation P
          A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩
        (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
            A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
          ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩
          (rzStarEdgeInteriorNextZStarFace P A3 S z copy starEdge index)
          corner)) := by
  let A := A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  let fixedZ : (rzReplacementPresentation P A S).Z :=
    ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩
  let face := rzStarEdgeInteriorNextZStarFace P A3 S z copy starEdge index
  exact (rzStarEdgeInteriorBoundaryPathToNextX
      P A3 S z copy starEdge index).append
    ((rzZStarFaceBoundaryPathToX
      (rzReplacementPresentation P A S) fixedZ face).reverse.append
      (rzZStarFaceBoundaryPathToQ
        (rzReplacementPresentation P A S) fixedZ face corner))

/-- A materialized local face/corner whose Z value is the fixed stored
star-edge-interior tag, packaged without any existential selection. -/
private noncomputable def rzStarEdgeInteriorTargetZStarFace
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (starEdge : XStarEdge (transposePresentation P) z)
    (index : Fin (S.half - 1))
    (cell : ZDoubleCylinderFace P z S) (bits : Two × Two)
    (hcorner : localCornerVertex P z S cell bits =
      (copy, Sum.inr (Sum.inl (starEdge, index)))) :
    ZStarFace (rzReplacementPresentation P
      A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
      ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩ :=
  ⟨Sum.inl ⟨z, cell, bits⟩, by
    simp only [zStarFaceMember, decide_eq_true_eq]
    change localFaceZ P S ⟨z, cell, bits⟩ =
      ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩
    rw [localFaceZ_eq_corner]
    exact Sigma.ext rfl (heq_of_eq hcorner)⟩

/-- Constructor-complete route to the X of any explicitly materialized local
face at the fixed star-edge-interior vertex. -/
private noncomputable def rzStarEdgeInteriorBoundaryPathToMaterializedX
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (starEdge : XStarEdge (transposePresentation P) z)
    (index : Fin (S.half - 1))
    (cell : ZDoubleCylinderFace P z S) (bits : Two × Two)
    (hcorner : localCornerVertex P z S cell bits =
      (copy, Sum.inr (Sum.inl (starEdge, index)))) :
    UndirectedPath
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩)
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩)
      (rzReplacementZBoundaryRoot P A3 S
        ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩)
      (zBoundaryEdgeStart (rzReplacementPresentation P
          A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩
        (rzZStarFaceBoundaryEdge (rzReplacementPresentation P
            A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
          ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩
          (rzStarEdgeInteriorTargetZStarFace P A3 S z copy starEdge index
            cell bits hcorner) 0)) := by
  let A := A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  let fixedZ : (rzReplacementPresentation P A S).Z :=
    ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩
  let targetFace := rzStarEdgeInteriorTargetZStarFace
    P A3 S z copy starEdge index cell bits hcorner
  by_cases hpre0 : localCornerEdge P z S cell (bits, 0) =
      rzStarEdgeInteriorEndEdge P S z copy starEdge
        (rzStarEdgeInteriorPrecedingSegment S index)
  · let first := rzStarEdgeInteriorBoundaryPathToPrecedingQ
      P A3 S z copy starEdge index
        (rzStarEdgeInteriorPrecedingAnchor P A3 S z copy starEdge index).2
    let last := (rzZStarFaceBoundaryPathToQ
        (rzReplacementPresentation P A S) fixedZ targetFace 0).reverse.append
      (rzZStarFaceBoundaryPathToX
        (rzReplacementPresentation P A S) fixedZ targetFace)
    have hbridge :
        zBoundaryEdgeEnd (rzReplacementPresentation P A S) fixedZ
            (rzZStarFaceBoundaryEdge (rzReplacementPresentation P A S) fixedZ
              (rzStarEdgeInteriorPrecedingZStarFace
                P A3 S z copy starEdge index)
              (rzStarEdgeInteriorPrecedingAnchor
                P A3 S z copy starEdge index).2) =
          zBoundaryEdgeEnd (rzReplacementPresentation P A S) fixedZ
            (rzZStarFaceBoundaryEdge (rzReplacementPresentation P A S) fixedZ
              targetFace 0) := by
      apply Subtype.ext
      rw [rzZStarFaceBoundaryEdge_end_value,
        rzZStarFaceBoundaryEdge_end_value]
      apply congrArg Vertex.q
      change (rzReplacementPresentation P A S).faceQ
          (Sum.inl (rzStarEdgeInteriorPrecedingAnchor
            P A3 S z copy starEdge index).1)
          (rzStarEdgeInteriorPrecedingAnchor
            P A3 S z copy starEdge index).2 =
        (rzReplacementPresentation P A S).faceQ
          (Sum.inl ⟨z, cell, bits⟩) 0
      dsimp only [rzStarEdgeInteriorPrecedingAnchor]
      rw [rzStarEdgeInteriorAnchorQ_eq]
      rw [show (rzReplacementPresentation P A S).faceQ
          (Sum.inl ⟨z, cell, bits⟩) 0 =
          twoSelect (localFaceQ0 P S ⟨z, cell, bits⟩)
            (localFaceQ1 P S ⟨z, cell, bits⟩) 0 from rfl]
      rw [localFaceQ_eq_corner]
      exact congrArg Sum.inl (Sigma.ext rfl (heq_of_eq hpre0.symm))
    exact first.append (hbridge ▸ last)
  · by_cases hnext0 : localCornerEdge P z S cell (bits, 0) =
        rzStarEdgeInteriorEndEdge P S z copy starEdge
          (rzStarEdgeInteriorNextSegment S index)
    · let first := rzStarEdgeInteriorBoundaryPathToNextQ
        P A3 S z copy starEdge index
          (rzStarEdgeInteriorNextAnchor P A3 S z copy starEdge index).2
      let last := (rzZStarFaceBoundaryPathToQ
          (rzReplacementPresentation P A S) fixedZ targetFace 0).reverse.append
        (rzZStarFaceBoundaryPathToX
          (rzReplacementPresentation P A S) fixedZ targetFace)
      have hbridge :
          zBoundaryEdgeEnd (rzReplacementPresentation P A S) fixedZ
              (rzZStarFaceBoundaryEdge (rzReplacementPresentation P A S) fixedZ
                (rzStarEdgeInteriorNextZStarFace
                  P A3 S z copy starEdge index)
                (rzStarEdgeInteriorNextAnchor
                  P A3 S z copy starEdge index).2) =
            zBoundaryEdgeEnd (rzReplacementPresentation P A S) fixedZ
              (rzZStarFaceBoundaryEdge (rzReplacementPresentation P A S) fixedZ
                targetFace 0) := by
        apply Subtype.ext
        rw [rzZStarFaceBoundaryEdge_end_value,
          rzZStarFaceBoundaryEdge_end_value]
        apply congrArg Vertex.q
        change (rzReplacementPresentation P A S).faceQ
            (Sum.inl (rzStarEdgeInteriorNextAnchor
              P A3 S z copy starEdge index).1)
            (rzStarEdgeInteriorNextAnchor
              P A3 S z copy starEdge index).2 =
          (rzReplacementPresentation P A S).faceQ
            (Sum.inl ⟨z, cell, bits⟩) 0
        dsimp only [rzStarEdgeInteriorNextAnchor]
        rw [rzStarEdgeInteriorAnchorQ_eq]
        rw [show (rzReplacementPresentation P A S).faceQ
            (Sum.inl ⟨z, cell, bits⟩) 0 =
            twoSelect (localFaceQ0 P S ⟨z, cell, bits⟩)
              (localFaceQ1 P S ⟨z, cell, bits⟩) 0 from rfl]
        rw [localFaceQ_eq_corner]
        exact congrArg Sum.inl (Sigma.ext rfl (heq_of_eq hnext0.symm))
      exact first.append (hbridge ▸ last)
    · by_cases hpre1 : localCornerEdge P z S cell (bits, 1) =
          rzStarEdgeInteriorEndEdge P S z copy starEdge
            (rzStarEdgeInteriorPrecedingSegment S index)
      · let first := rzStarEdgeInteriorBoundaryPathToPrecedingQ
          P A3 S z copy starEdge index
            (rzStarEdgeInteriorPrecedingAnchor P A3 S z copy starEdge index).2
        let last := (rzZStarFaceBoundaryPathToQ
            (rzReplacementPresentation P A S) fixedZ targetFace 1).reverse.append
          (rzZStarFaceBoundaryPathToX
            (rzReplacementPresentation P A S) fixedZ targetFace)
        have hbridge :
            zBoundaryEdgeEnd (rzReplacementPresentation P A S) fixedZ
                (rzZStarFaceBoundaryEdge (rzReplacementPresentation P A S) fixedZ
                  (rzStarEdgeInteriorPrecedingZStarFace
                    P A3 S z copy starEdge index)
                  (rzStarEdgeInteriorPrecedingAnchor
                    P A3 S z copy starEdge index).2) =
              zBoundaryEdgeEnd (rzReplacementPresentation P A S) fixedZ
                (rzZStarFaceBoundaryEdge (rzReplacementPresentation P A S) fixedZ
                  targetFace 1) := by
          apply Subtype.ext
          rw [rzZStarFaceBoundaryEdge_end_value,
            rzZStarFaceBoundaryEdge_end_value]
          apply congrArg Vertex.q
          change (rzReplacementPresentation P A S).faceQ
              (Sum.inl (rzStarEdgeInteriorPrecedingAnchor
                P A3 S z copy starEdge index).1)
              (rzStarEdgeInteriorPrecedingAnchor
                P A3 S z copy starEdge index).2 =
            (rzReplacementPresentation P A S).faceQ
              (Sum.inl ⟨z, cell, bits⟩) 1
          dsimp only [rzStarEdgeInteriorPrecedingAnchor]
          rw [rzStarEdgeInteriorAnchorQ_eq]
          rw [show (rzReplacementPresentation P A S).faceQ
              (Sum.inl ⟨z, cell, bits⟩) 1 =
              twoSelect (localFaceQ0 P S ⟨z, cell, bits⟩)
                (localFaceQ1 P S ⟨z, cell, bits⟩) 1 from rfl]
          rw [localFaceQ_eq_corner]
          exact congrArg Sum.inl (Sigma.ext rfl (heq_of_eq hpre1.symm))
        exact first.append (hbridge ▸ last)
      · by_cases hnext1 : localCornerEdge P z S cell (bits, 1) =
            rzStarEdgeInteriorEndEdge P S z copy starEdge
              (rzStarEdgeInteriorNextSegment S index)
        · let first := rzStarEdgeInteriorBoundaryPathToNextQ
            P A3 S z copy starEdge index
              (rzStarEdgeInteriorNextAnchor P A3 S z copy starEdge index).2
          let last := (rzZStarFaceBoundaryPathToQ
              (rzReplacementPresentation P A S) fixedZ targetFace 1).reverse.append
            (rzZStarFaceBoundaryPathToX
              (rzReplacementPresentation P A S) fixedZ targetFace)
          have hbridge :
              zBoundaryEdgeEnd (rzReplacementPresentation P A S) fixedZ
                  (rzZStarFaceBoundaryEdge (rzReplacementPresentation P A S) fixedZ
                    (rzStarEdgeInteriorNextZStarFace
                      P A3 S z copy starEdge index)
                    (rzStarEdgeInteriorNextAnchor
                      P A3 S z copy starEdge index).2) =
                zBoundaryEdgeEnd (rzReplacementPresentation P A S) fixedZ
                  (rzZStarFaceBoundaryEdge (rzReplacementPresentation P A S)
                    fixedZ targetFace 1) := by
            apply Subtype.ext
            rw [rzZStarFaceBoundaryEdge_end_value,
              rzZStarFaceBoundaryEdge_end_value]
            apply congrArg Vertex.q
            change (rzReplacementPresentation P A S).faceQ
                (Sum.inl (rzStarEdgeInteriorNextAnchor
                  P A3 S z copy starEdge index).1)
                (rzStarEdgeInteriorNextAnchor
                  P A3 S z copy starEdge index).2 =
              (rzReplacementPresentation P A S).faceQ
                (Sum.inl ⟨z, cell, bits⟩) 1
            dsimp only [rzStarEdgeInteriorNextAnchor]
            rw [rzStarEdgeInteriorAnchorQ_eq]
            rw [show (rzReplacementPresentation P A S).faceQ
                (Sum.inl ⟨z, cell, bits⟩) 1 =
                twoSelect (localFaceQ0 P S ⟨z, cell, bits⟩)
                  (localFaceQ1 P S ⟨z, cell, bits⟩) 1 from rfl]
            rw [localFaceQ_eq_corner]
            exact congrArg Sum.inl (Sigma.ext rfl (heq_of_eq hnext1.symm))
          exact first.append (hbridge ▸ last)
        · have himpossible : False := by
            rcases rzStarEdgeInteriorLocalCornerEdge_cases
                P S z copy starEdge index cell bits hcorner with
              h | h | h | h
            · exact hpre0 h
            · exact hnext0 h
            · exact hpre1 h
            · exact hnext1 h
          exact himpossible.elim

/-- Choice-free route to a local-edge Q boundary vertex at a stored
star-edge-interior coordinate.  The target edge itself supplies a canonical
incident face; its endpoint is recovered from the concrete successor Q-Z
incidence, not from a selected boundary face. -/
private noncomputable def rzStarEdgeInteriorBoundaryPathToLocalQ
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (starEdge : XStarEdge (transposePresentation P) z)
    (index : Fin (S.half - 1))
    (localQ : Sigma fun oldZ : P.Z => ZDoubleCylinderEdge P oldZ S)
    (member : zStarBoundaryVertexMember
      (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
      ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩
      (Vertex.q (Sum.inl localQ)) = true) :
    UndirectedPath
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩)
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩)
      (rzReplacementZBoundaryRoot P A3 S
        ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩)
      ⟨Vertex.q (Sum.inl localQ), member⟩ := by
  let A := A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  let successor := rzReplacementPresentation P A S
  let fixedZ : successor.Z :=
    ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩
  have hqz : successor.qz (Sum.inl localQ) fixedZ = true := by
    simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
    obtain ⟨successorFace, hfaceZ, hfaceQ⟩ := member
    rcases hfaceQ with hfaceQ | hfaceQ
    · have h := successor.data.faceQ_qz successorFace 0
      change successor.qz (successor.faceQ successorFace 0)
        (successor.faceZ successorFace) = true at h
      change Sum.inl localQ = successor.faceQ successorFace 0 at hfaceQ
      have hz : successor.faceZ successorFace = fixedZ := by
        simpa [zStarFaceMember] using hfaceZ
      rw [← hfaceQ, hz] at h
      exact h
    · have h := successor.data.faceQ_qz successorFace 1
      change successor.qz (successor.faceQ successorFace 1)
        (successor.faceZ successorFace) = true at h
      change Sum.inl localQ = successor.faceQ successorFace 1 at hfaceQ
      have hz : successor.faceZ successorFace = fixedZ := by
        simpa [zStarFaceMember] using hfaceZ
      rw [← hfaceQ, hz] at h
      exact h
  rcases localQ with ⟨targetZ, edge⟩
  change successor.qz (Sum.inl ⟨targetZ, edge⟩) fixedZ = true at hqz
  by_cases htargetZ : z = targetZ
  · subst targetZ
    have hmatrix : doubleCylinderEdgeVertexMatrix (transposePresentation P) z S
        (copy, Sum.inr (Sum.inl (starEdge, index))) edge = 1 := by
      change decide (∃ h : z = z,
        doubleCylinderEdgeVertexMatrix (transposePresentation P) z S
          (h ▸ (copy, Sum.inr (Sum.inl (starEdge, index)))) edge = 1) = true
        at hqz
      have hexists := of_decide_eq_true hqz
      rcases hexists with ⟨h, hmatrix⟩
      simpa only [Subsingleton.elim h rfl] using hmatrix
    let build (endpoint : Two)
        (hendpoint : BDL26TannerLocalRegularity.edgeEndpoint
          (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
          (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
          edge endpoint = (copy, Sum.inr (Sum.inl (starEdge, index)))) :
        UndirectedPath
          (zBoundaryEdgeStart successor fixedZ)
          (zBoundaryEdgeEnd successor fixedZ)
          (rzReplacementZBoundaryRoot P A3 S fixedZ)
          ⟨Vertex.q (Sum.inl ⟨z, edge⟩), member⟩ := by
      let owner := doubleCylinderEdgeFaceSlotOwner
        (transposePresentation P) (transposeTannerSquareAdmissibleV3 P A3)
        z S edge
      let corner := localCornerAtBoundaryEndpoint P z S
        owner.1.1 owner.1.2 endpoint
      have hcorner : localCornerVertex P z S owner.1.1 corner.1.1 =
          (copy, Sum.inr (Sum.inl (starEdge, index))) := by
        calc
          localCornerVertex P z S owner.1.1 corner.1.1 =
              BDL26TannerLocalRegularity.edgeEndpoint
                (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
                (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
                (doubleCylinderFaceBoundaryEdge (transposePresentation P) z S
                  owner.1.1 owner.1.2) endpoint := corner.2.2
          _ = BDL26TannerLocalRegularity.edgeEndpoint
                (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
                (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
                edge endpoint := by rw [owner.2]
          _ = (copy, Sum.inr (Sum.inl (starEdge, index))) := hendpoint
      let face := rzStarEdgeInteriorTargetZStarFace
        P A3 S z copy starEdge index owner.1.1 corner.1.1 hcorner
      let first := rzStarEdgeInteriorBoundaryPathToMaterializedX
        P A3 S z copy starEdge index owner.1.1 corner.1.1 hcorner
      let last := (rzZStarFaceBoundaryPathToX successor fixedZ face).reverse.append
        (rzZStarFaceBoundaryPathToQ successor fixedZ face corner.1.2)
      have htarget : zBoundaryEdgeEnd successor fixedZ
            (rzZStarFaceBoundaryEdge successor fixedZ face corner.1.2) =
          (⟨Vertex.q (Sum.inl ⟨z, edge⟩), member⟩ :
            ZStarBoundaryVertex successor fixedZ) := by
        apply Subtype.ext
        rw [rzZStarFaceBoundaryEdge_end_value]
        apply congrArg Vertex.q
        change twoSelect
            (localFaceQ0 P S ⟨z, owner.1.1, corner.1.1⟩)
            (localFaceQ1 P S ⟨z, owner.1.1, corner.1.1⟩)
            corner.1.2 = Sum.inl ⟨z, edge⟩
        rw [localFaceQ_eq_corner]
        apply congrArg Sum.inl
        exact Sigma.ext
          (x := (⟨z, localCornerEdge P z S owner.1.1
            (corner.1.1, corner.1.2)⟩ :
              Sigma fun oldZ : P.Z => ZDoubleCylinderEdge P oldZ S))
          (y := ⟨z, edge⟩) rfl
          (heq_of_eq (corner.2.1.trans owner.2))
      exact first.append (htarget.symm ▸ last)
    by_cases hstart :
        tannerDoubleCylinderEdgeStart (transposePresentation P) z S edge =
          (copy, Sum.inr (Sum.inl (starEdge, index)))
    · exact build 0 hstart
    · by_cases hend :
          tannerDoubleCylinderEdgeEnd (transposePresentation P) z S edge =
            (copy, Sum.inr (Sum.inl (starEdge, index)))
      · exact build 1 hend
      · exact False.elim (by
          have hcases := (doubleCylinderEdgeVertexMatrix_eq_one_iff
            (transposePresentation P) z S
            (copy, Sum.inr (Sum.inl (starEdge, index))) edge).1 hmatrix
          rcases hcases with h | h
          · exact hstart h.symm
          · exact hend h.symm)
  · exact False.elim (by
      change decide (∃ h : z = targetZ,
        doubleCylinderEdgeVertexMatrix (transposePresentation P) targetZ S
          (h ▸ (copy, Sum.inr (Sum.inl (starEdge, index)))) edge = 1) = true
        at hqz
      obtain ⟨h, _⟩ := of_decide_eq_true hqz
      exact htargetZ h)

/-- Choice-free route to a materialized X boundary vertex at a stored
star-edge-interior coordinate.  The four concrete corner bits are tested
directly; the boundary existential is used only to refute the fallback. -/
private noncomputable def rzStarEdgeInteriorBoundaryPathToLocalX
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (starEdge : XStarEdge (transposePresentation P) z)
    (index : Fin (S.half - 1))
    (localX : Sigma fun oldZ : P.Z => ZDoubleCylinderFace P oldZ S)
    (member : zStarBoundaryVertexMember
      (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
      ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩
      (Vertex.x (Sum.inl (Sum.inl localX))) = true) :
    UndirectedPath
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩)
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩)
      (rzReplacementZBoundaryRoot P A3 S
        ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩)
      ⟨Vertex.x (Sum.inl (Sum.inl localX)), member⟩ := by
  let A := A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  let successor := rzReplacementPresentation P A S
  let fixedVertex : ZDoubleCylinderVertex P z S :=
    (copy, Sum.inr (Sum.inl (starEdge, index)))
  let fixedZ : successor.Z := ⟨z, fixedVertex⟩
  rcases localX with ⟨targetZ, cell⟩
  by_cases htargetZ : targetZ = z
  · subst targetZ
    let build (bits : Two × Two)
        (hcorner : localCornerVertex P z S cell bits = fixedVertex) :
        UndirectedPath
          (zBoundaryEdgeStart successor fixedZ)
          (zBoundaryEdgeEnd successor fixedZ)
          (rzReplacementZBoundaryRoot P A3 S fixedZ)
          ⟨Vertex.x (Sum.inl (Sum.inl ⟨z, cell⟩)), member⟩ := by
      let face := rzStarEdgeInteriorTargetZStarFace
        P A3 S z copy starEdge index cell bits hcorner
      let path := rzStarEdgeInteriorBoundaryPathToMaterializedX
        P A3 S z copy starEdge index cell bits hcorner
      have htarget : zBoundaryEdgeStart successor fixedZ
            (rzZStarFaceBoundaryEdge successor fixedZ face 0) =
          (⟨Vertex.x (Sum.inl (Sum.inl ⟨z, cell⟩)), member⟩ :
            ZStarBoundaryVertex successor fixedZ) := by
        apply Subtype.ext
        rw [rzZStarFaceBoundaryEdge_start_value]
        rfl
      exact htarget ▸ path
    by_cases h00 : localCornerVertex P z S cell (0, 0) = fixedVertex
    · exact build (0, 0) h00
    · by_cases h01 : localCornerVertex P z S cell (0, 1) = fixedVertex
      · exact build (0, 1) h01
      · by_cases h10 : localCornerVertex P z S cell (1, 0) = fixedVertex
        · exact build (1, 0) h10
        · by_cases h11 : localCornerVertex P z S cell (1, 1) = fixedVertex
          · exact build (1, 1) h11
          · exact False.elim (by
              simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
              obtain ⟨successorFace, hfaceZ, hfaceX⟩ := member
              simp only [zStarFaceMember, decide_eq_true_eq] at hfaceZ
              rcases successorFace with localFace | glueOrOld
              · rcases localFace with ⟨ownerZ, ownerCell, bits⟩
                change Sum.inl (Sum.inl (⟨z, cell⟩ :
                    Sigma fun oldZ : P.Z => ZDoubleCylinderFace P oldZ S)) =
                  Sum.inl (Sum.inl (⟨ownerZ, ownerCell⟩ :
                    Sigma fun oldZ : P.Z => ZDoubleCylinderFace P oldZ S)) at hfaceX
                have howner := Sum.inl.inj (Sum.inl.inj hfaceX)
                cases howner
                change localFaceZ P S ⟨z, cell, bits⟩ = fixedZ at hfaceZ
                rw [localFaceZ_eq_corner] at hfaceZ
                have hbits : localCornerVertex P z S cell bits = fixedVertex :=
                  eq_of_heq (Sigma.mk.inj_iff.mp hfaceZ).2
                rcases bits with ⟨firstBit, secondBit⟩
                fin_cases firstBit <;> fin_cases secondBit
                · exact h00 hbits
                · exact h01 hbits
                · exact h10 hbits
                · exact h11 hbits
              · rcases glueOrOld with glueFace | oldFace
                · change Sum.inl (Sum.inl (⟨z, cell⟩ :
                      Sigma fun oldZ : P.Z => ZDoubleCylinderFace P oldZ S)) =
                    Sum.inl (Sum.inr _) at hfaceX
                  cases Sum.inl.inj hfaceX
                · change Sum.inl (Sum.inl (⟨z, cell⟩ :
                      Sigma fun oldZ : P.Z => ZDoubleCylinderFace P oldZ S)) =
                    Sum.inr _ at hfaceX
                  cases hfaceX)
  · exact False.elim (by
      simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
      obtain ⟨successorFace, hfaceZ, hfaceX⟩ := member
      simp only [zStarFaceMember, decide_eq_true_eq] at hfaceZ
      rcases successorFace with localFace | glueOrOld
      · rcases localFace with ⟨ownerZ, ownerCell, bits⟩
        change Sum.inl (Sum.inl (⟨targetZ, cell⟩ :
            Sigma fun oldZ : P.Z => ZDoubleCylinderFace P oldZ S)) =
          Sum.inl (Sum.inl (⟨ownerZ, ownerCell⟩ :
            Sigma fun oldZ : P.Z => ZDoubleCylinderFace P oldZ S)) at hfaceX
        have howner := Sum.inl.inj (Sum.inl.inj hfaceX)
        have hz : targetZ = ownerZ := congrArg Sigma.fst howner
        have hownerZ : ownerZ = z := by
          change localFaceZ P S ⟨ownerZ, ownerCell, bits⟩ = fixedZ at hfaceZ
          rw [localFaceZ_eq_corner] at hfaceZ
          exact congrArg Sigma.fst hfaceZ
        exact htargetZ (hz.trans hownerZ)
      · rcases glueOrOld with glueFace | oldFace
        · change Sum.inl (Sum.inl (⟨targetZ, cell⟩ :
              Sigma fun oldZ : P.Z => ZDoubleCylinderFace P oldZ S)) =
            Sum.inl (Sum.inr _) at hfaceX
          cases Sum.inl.inj hfaceX
        · change Sum.inl (Sum.inl (⟨targetZ, cell⟩ :
              Sigma fun oldZ : P.Z => ZDoubleCylinderFace P oldZ S)) =
            Sum.inr _ at hfaceX
          cases hfaceX)

/-- A glue-X tag on a fixed star-edge-interior Z link supplies its old Q-Z
incidence and one of the two concrete mapped endpoint equalities.  This is a
`Prop`-only inversion; the path constructor below tests the two endpoints
directly and never extracts a Type-valued witness from boundary membership. -/
private theorem rzStarEdgeInteriorGlueX_endpoint
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (starEdge : XStarEdge (transposePresentation P) z)
    (index : Fin (S.half - 1)) (q : P.Q)
    (qEdge : QDoubleCylinderEdge (transposePresentation P) q S)
    (member : zStarBoundaryVertexMember (rzReplacementPresentation P A S)
      ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩
      (Vertex.x (Sum.inl (Sum.inr ⟨q, qEdge⟩))) = true) :
    ∃ hqz : P.qz q z = true,
      qToZDoubleCylinderVertex P A q z hqz S
          (edgeEndpoint
            (qDoubleCylinderEdgeStart (transposePresentation P) q S)
            (qDoubleCylinderEdgeEnd (transposePresentation P) q S)
            qEdge 0) =
          (copy, Sum.inr (Sum.inl (starEdge, index))) ∨
        qToZDoubleCylinderVertex P A q z hqz S
          (edgeEndpoint
            (qDoubleCylinderEdgeStart (transposePresentation P) q S)
            (qDoubleCylinderEdgeEnd (transposePresentation P) q S)
            qEdge 1) =
          (copy, Sum.inr (Sum.inl (starEdge, index))) := by
  classical
  simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
  obtain ⟨successorFace, hfaceZ, hfaceX⟩ := member
  simp only [zStarFaceMember, decide_eq_true_eq] at hfaceZ
  rcases successorFace with localFace | glueOrOld
  · change (Sum.inl (Sum.inr (⟨q, qEdge⟩ : Sigma fun q : P.Q =>
        QDoubleCylinderEdge (transposePresentation P) q S)) : RZX P S) =
      localFaceX P S localFace at hfaceX
    simp [localFaceX] at hfaceX
  · rcases glueOrOld with glueFace | oldFace
    · rcases glueFace with ⟨⟨⟨q', z'⟩, hqz⟩, edge, endpoint⟩
      change (Sum.inl (Sum.inr (⟨q, qEdge⟩ : Sigma fun q : P.Q =>
          QDoubleCylinderEdge (transposePresentation P) q S)) : RZX P S) =
        Sum.inl (Sum.inr (⟨q', edge⟩ : Sigma fun q : P.Q =>
          QDoubleCylinderEdge (transposePresentation P) q S)) at hfaceX
      have hedge : (⟨q, qEdge⟩ : Sigma fun q : P.Q =>
          QDoubleCylinderEdge (transposePresentation P) q S) =
          ⟨q', edge⟩ := Sum.inr.inj (Sum.inl.inj hfaceX)
      cases hedge
      change glueFaceZ P A S ⟨⟨⟨q, z'⟩, hqz⟩, qEdge, endpoint⟩ =
        ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩ at hfaceZ
      have hz : z' = z := congrArg Sigma.fst hfaceZ
      subst z'
      have hvertex := eq_of_heq (Sigma.mk.inj_iff.mp hfaceZ).2
      refine ⟨hqz, ?_⟩
      fin_cases endpoint
      · left
        exact hvertex
      · right
        exact hvertex
    · change (Sum.inl (Sum.inr (⟨q, qEdge⟩ : Sigma fun q : P.Q =>
          QDoubleCylinderEdge (transposePresentation P) q S)) : RZX P S) =
        oldXFaceX P S oldFace at hfaceX
      simp [oldXFaceX] at hfaceX

/-- Route from the deterministic root to a retained glue-X tag at a stored
star-edge-interior coordinate.  The old Q-Z proof is recovered in `Prop`,
then the two endpoint equalities are tested as concrete decisions. -/
private noncomputable def rzStarEdgeInteriorBoundaryPathToGlueX
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (starEdge : XStarEdge (transposePresentation P) z)
    (index : Fin (S.half - 1)) (q : P.Q)
    (qEdge : QDoubleCylinderEdge (transposePresentation P) q S)
    (member : zStarBoundaryVertexMember
      (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
      ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩
      (Vertex.x (Sum.inl (Sum.inr ⟨q, qEdge⟩))) = true) :
    UndirectedPath
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩)
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩)
      (rzReplacementZBoundaryRoot P A3 S
        ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩)
      ⟨Vertex.x (Sum.inl (Sum.inr ⟨q, qEdge⟩)), member⟩ := by
  classical
  let A := A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  let successor := rzReplacementPresentation P A S
  let fixedVertex : ZDoubleCylinderVertex P z S :=
    (copy, Sum.inr (Sum.inl (starEdge, index)))
  let fixedZ : successor.Z := ⟨z, fixedVertex⟩
  by_cases hqz : P.qz q z = true
  · let build (endpoint : Two)
      (hmap : qToZDoubleCylinderVertex P A q z hqz S
        (edgeEndpoint
          (qDoubleCylinderEdgeStart (transposePresentation P) q S)
          (qDoubleCylinderEdgeEnd (transposePresentation P) q S)
          qEdge endpoint) = fixedVertex) :
      UndirectedPath
        (zBoundaryEdgeStart successor fixedZ)
        (zBoundaryEdgeEnd successor fixedZ)
        (rzReplacementZBoundaryRoot P A3 S fixedZ)
        ⟨Vertex.x (Sum.inl (Sum.inr ⟨q, qEdge⟩)), member⟩ := by
      let oldEdge : QZEdge P := ⟨(q, z), hqz⟩
      let localQ : Sigma fun oldZ : P.Z => ZDoubleCylinderEdge P oldZ S :=
        ⟨z, qToZDoubleCylinderEdge P A q z hqz S qEdge⟩
      let glue : RZQZGlueFace P S := ⟨oldEdge, qEdge, endpoint⟩
      have hfaceZ : glueFaceZ P A S glue = fixedZ := by
        apply Sigma.ext (x := glueFaceZ P A S glue) (y := fixedZ) rfl
        apply heq_of_eq
        exact hmap
      have hlocalMember : zStarBoundaryVertexMember successor fixedZ
          (Vertex.q (Sum.inl localQ)) = true := by
        change decide (∃ successorFace : successor.Face,
          zStarFaceMember successor fixedZ successorFace = true ∧
            (Sum.inl localQ = successor.faceQ successorFace 0 ∨
              Sum.inl localQ = successor.faceQ successorFace 1)) = true
        rw [decide_eq_true_eq]
        refine ⟨Sum.inr (Sum.inl glue), ?_, Or.inl ?_⟩
        · simp only [zStarFaceMember, decide_eq_true_eq]
          exact hfaceZ
        · rfl
      let face : ZStarFace successor fixedZ :=
        ⟨Sum.inr (Sum.inl glue), by
          simp only [zStarFaceMember, decide_eq_true_eq]
          exact hfaceZ⟩
      let first := rzStarEdgeInteriorBoundaryPathToLocalQ
        P A3 S z copy starEdge index localQ hlocalMember
      let last := rzZStarFaceBoundaryPathToX successor fixedZ face
      have hlocal :
          (⟨Vertex.q (Sum.inl localQ), hlocalMember⟩ :
            ZStarBoundaryVertex successor fixedZ) =
          zBoundaryEdgeEnd successor fixedZ
            (rzZStarFaceBoundaryEdge successor fixedZ face 0) := by
        apply Subtype.ext
        rw [rzZStarFaceBoundaryEdge_end_value]
        rfl
      have htarget : zBoundaryEdgeStart successor fixedZ
            (rzZStarFaceBoundaryEdge successor fixedZ face 0) =
          (⟨Vertex.x (Sum.inl (Sum.inr ⟨q, qEdge⟩)), member⟩ :
            ZStarBoundaryVertex successor fixedZ) := by
        apply Subtype.ext
        rw [rzZStarFaceBoundaryEdge_start_value]
        rfl
      exact first.append (hlocal ▸ (htarget.symm ▸ last))
    by_cases hzero : qToZDoubleCylinderVertex P A q z hqz S
        (edgeEndpoint
          (qDoubleCylinderEdgeStart (transposePresentation P) q S)
          (qDoubleCylinderEdgeEnd (transposePresentation P) q S)
          qEdge 0) = fixedVertex
    · exact build 0 hzero
    · by_cases hone : qToZDoubleCylinderVertex P A q z hqz S
          (edgeEndpoint
            (qDoubleCylinderEdgeStart (transposePresentation P) q S)
            (qDoubleCylinderEdgeEnd (transposePresentation P) q S)
            qEdge 1) = fixedVertex
      · exact build 1 hone
      · exact False.elim (by
          obtain ⟨hqz', hendpoint⟩ := rzStarEdgeInteriorGlueX_endpoint
            P A S z copy starEdge index q qEdge member
          rcases hendpoint with hzero' | hone'
          · exact hzero (by
              simpa only [Subsingleton.elim hqz' hqz] using hzero')
          · exact hone (by
              simpa only [Subsingleton.elim hqz' hqz] using hone'))
  · exact False.elim (by
      obtain ⟨hqz', _⟩ := rzStarEdgeInteriorGlueX_endpoint
        P A S z copy starEdge index q qEdge member
      exact hqz hqz')

/-- Every vertex of the transposed Q-cylinder has a choice-free incident
edge.  Cone points use the input historical X-Q root, old endpoints use their
stored radial edge, and path-interior vertices use the preceding segment. -/
private def qDoubleCylinderVertexIncidentEdge
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (S : OddScale)
    (vertex : QDoubleCylinderVertex (transposePresentation P) q S) :
    {owned : QDoubleCylinderEdge (transposePresentation P) q S × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (qDoubleCylinderEdgeStart (transposePresentation P) q S)
        (qDoubleCylinderEdgeEnd (transposePresentation P) q S)
        owned.1 owned.2 = vertex} := by
  rcases vertex with ⟨copy, vertex⟩
  rcases vertex with original | interior
  · rcases original with center | endpoint
    · let radial : QStarEdge (transposePresentation P) q :=
        ⟨(A.xqRoot q).1, (A.xqRoot q).2⟩
      let first : Fin S.half := ⟨0, S.half_pos⟩
      refine ⟨⟨Sum.inl (copy, radial, first), 0⟩, ?_⟩
      rw [BDL26TannerLocalRegularity.edgeEndpoint_zero]
      simp [qDoubleCylinderEdgeStart, qSubdivisionEdgeStart, first,
        qStarEdgeStart]
    · let last : Fin S.half :=
        ⟨S.half - 1, by have := S.half_pos; omega⟩
      refine ⟨⟨Sum.inl (copy, endpoint, last), 1⟩, ?_⟩
      rw [BDL26TannerLocalRegularity.edgeEndpoint_one]
      have hlast : last.1 + 1 = S.half := by
        dsimp [last]
        have := S.half_pos
        omega
      simp [qDoubleCylinderEdgeEnd, qSubdivisionEdgeEnd, qStarEdgeEnd, hlast]
  · rcases interior with ⟨edge, index⟩
    let preceding : Fin S.half :=
      ⟨index.1, by have := index.2; omega⟩
    refine ⟨⟨Sum.inl (copy, edge, preceding), 1⟩, ?_⟩
    rw [BDL26TannerLocalRegularity.edgeEndpoint_one]
    have hlt : index.1 + 1 < S.half :=
      (Nat.lt_sub_iff_add_lt).1 index.2
    have hnot : preceding.1 + 1 ≠ S.half := by
      dsimp [preceding]
      omega
    simp [qDoubleCylinderEdgeEnd, qSubdivisionEdgeEnd, hnot, preceding]

/-- Route to a retained Q-cylinder vertex on the original-Q fixed-Z
boundary. -/
private noncomputable def rzOriginalQBoundaryPathToQVertex
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two) (q : P.Q)
    (originalMember : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true)
    (qVertex : Sigma fun glueQ : P.Q =>
      QDoubleCylinderVertex (transposePresentation P) glueQ S)
    (member : zStarBoundaryVertexMember
      (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
      (rzOriginalQZVertex P S z copy q originalMember)
      (Vertex.q (Sum.inr qVertex)) = true) :
    UndirectedPath
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalQZVertex P S z copy q originalMember))
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalQZVertex P S z copy q originalMember))
      (rzReplacementZBoundaryRoot P A4.toTannerSquareAdmissibleV3 S
        (rzOriginalQZVertex P S z copy q originalMember))
      ⟨Vertex.q (Sum.inr qVertex), member⟩ := by
  classical
  let A := A4.toTannerSquareAdmissible
  let successor := rzReplacementPresentation P A S
  let fixedVertex : ZDoubleCylinderVertex P z S :=
    (copy, Sum.inl ⟨Vertex.q q, originalMember⟩)
  let fixedZ : successor.Z := rzOriginalQZVertex P S z copy q originalMember
  have hsuccessorQZ : successor.qz (Sum.inr qVertex) fixedZ = true := by
    simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
    obtain ⟨successorFace, hfaceZ, hfaceQ⟩ := member
    rcases hfaceQ with hfaceQ | hfaceQ
    · have h := successor.data.faceQ_qz successorFace 0
      change successor.qz (successor.faceQ successorFace 0)
        (successor.faceZ successorFace) = true at h
      change Sum.inr qVertex = successor.faceQ successorFace 0 at hfaceQ
      have hz : successor.faceZ successorFace = fixedZ := by
        simpa [zStarFaceMember] using hfaceZ
      rw [← hfaceQ, hz] at h
      exact h
    · have h := successor.data.faceQ_qz successorFace 1
      change successor.qz (successor.faceQ successorFace 1)
        (successor.faceZ successorFace) = true at h
      change Sum.inr qVertex = successor.faceQ successorFace 1 at hfaceQ
      have hz : successor.faceZ successorFace = fixedZ := by
        simpa [zStarFaceMember] using hfaceZ
      rw [← hfaceQ, hz] at h
      exact h
  rcases qVertex with ⟨glueQ, qVertex⟩
  change successor.qz (Sum.inr ⟨glueQ, qVertex⟩) fixedZ = true
    at hsuccessorQZ
  by_cases hqz : P.qz glueQ z = true
  · have hmap : qToZDoubleCylinderVertex P A glueQ z hqz S qVertex =
        fixedVertex := by
      change decide (∃ hqz' : P.qz glueQ z = true,
        qToZDoubleCylinderVertex P A glueQ z hqz' S qVertex =
          fixedVertex) = true at hsuccessorQZ
      obtain ⟨hqz', hmap⟩ := of_decide_eq_true hsuccessorQZ
      simpa only [Subsingleton.elim hqz' hqz] using hmap
    obtain ⟨⟨qEdge, endpoint⟩, hendpoint⟩ :=
      qDoubleCylinderVertexIncidentEdge P A glueQ S qVertex
    have hendpoint' : edgeEndpoint
          (qDoubleCylinderEdgeStart (transposePresentation P) glueQ S)
          (qDoubleCylinderEdgeEnd (transposePresentation P) glueQ S)
          qEdge endpoint = qVertex := by
      fin_cases endpoint <;> simpa [edgeEndpoint, twoSelect] using hendpoint
    let oldEdge : QZEdge P := ⟨(glueQ, z), hqz⟩
    let localEdge : ZDoubleCylinderEdge P z S :=
      qToZDoubleCylinderEdge P A glueQ z hqz S qEdge
    let localQ : Sigma fun oldZ : P.Z => ZDoubleCylinderEdge P oldZ S :=
      ⟨z, localEdge⟩
    let glue : RZQZGlueFace P S := ⟨oldEdge, qEdge, endpoint⟩
    have hfaceZ : glueFaceZ P A S glue = fixedZ := by
      apply Sigma.ext (x := glueFaceZ P A S glue) (y := fixedZ) rfl
      apply heq_of_eq
      simp only [glueFaceZ, glue, oldEdge, fixedZ]
      change qToZDoubleCylinderVertex P A glueQ z hqz S
          (edgeEndpoint
            (qDoubleCylinderEdgeStart (transposePresentation P) glueQ S)
            (qDoubleCylinderEdgeEnd (transposePresentation P) glueQ S)
            qEdge endpoint) = fixedVertex
      rw [hendpoint']
      exact hmap
    have hlocalMember : zStarBoundaryVertexMember successor fixedZ
        (Vertex.q (Sum.inl localQ)) = true := by
      change decide (∃ successorFace : successor.Face,
        zStarFaceMember successor fixedZ successorFace = true ∧
          (Sum.inl localQ = successor.faceQ successorFace 0 ∨
            Sum.inl localQ = successor.faceQ successorFace 1)) = true
      rw [decide_eq_true_eq]
      refine ⟨Sum.inr (Sum.inl glue), ?_, Or.inl ?_⟩
      · simp only [zStarFaceMember, decide_eq_true_eq]
        exact hfaceZ
      · rfl
    let face : ZStarFace successor fixedZ :=
      ⟨Sum.inr (Sum.inl glue), by
        simp only [zStarFaceMember, decide_eq_true_eq]
        exact hfaceZ⟩
    let first := rzOriginalQBoundaryPathToLocalQ P A4 S z copy q
      originalMember localQ hlocalMember
    let last := rzZStarFaceBoundaryPathToQ successor fixedZ face 1
    have hlocal :
        (⟨Vertex.q (Sum.inl localQ), hlocalMember⟩ :
          ZStarBoundaryVertex successor fixedZ) =
        zBoundaryEdgeEnd successor fixedZ
          (rzZStarFaceBoundaryEdge successor fixedZ face 0) := by
      apply Subtype.ext
      rw [rzZStarFaceBoundaryEdge_end_value]
      rfl
    have htarget : zBoundaryEdgeEnd successor fixedZ
          (rzZStarFaceBoundaryEdge successor fixedZ face 1) =
        (⟨Vertex.q (Sum.inr ⟨glueQ, qVertex⟩), member⟩ :
          ZStarBoundaryVertex successor fixedZ) := by
      apply Subtype.ext
      rw [rzZStarFaceBoundaryEdge_end_value]
      apply congrArg Vertex.q
      change glueFaceQ1 P S glue = Sum.inr ⟨glueQ, qVertex⟩
      simp only [glueFaceQ1, glue, oldEdge]
      apply congrArg Sum.inr
      exact Sigma.ext rfl (heq_of_eq hendpoint')
    exact first.append (hlocal ▸ (htarget.symm ▸ last))
  · exact False.elim (by
      change decide (∃ hqz' : P.qz glueQ z = true,
        qToZDoubleCylinderVertex P A glueQ z hqz' S qVertex =
          fixedVertex) = true at hsuccessorQZ
      obtain ⟨hqz', _⟩ := of_decide_eq_true hsuccessorQZ
      exact hqz hqz')

/-- Route to a retained Q-cylinder vertex on the original-Z fixed-Z
boundary. -/
private noncomputable def rzOriginalZBoundaryPathToQVertex
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (z : P.Z) (copy : Two) (x : P.X)
    (originalMember : xStarVertexMember (transposePresentation P) z
      (Vertex.z x) = true)
    (qVertex : Sigma fun glueQ : P.Q =>
      QDoubleCylinderVertex (transposePresentation P) glueQ S)
    (member : zStarBoundaryVertexMember
      (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
      (rzOriginalZZVertex P S z copy x originalMember)
      (Vertex.q (Sum.inr qVertex)) = true) :
    UndirectedPath
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalZZVertex P S z copy x originalMember))
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalZZVertex P S z copy x originalMember))
      (rzReplacementZBoundaryRoot P A4.toTannerSquareAdmissibleV3 S
        (rzOriginalZZVertex P S z copy x originalMember))
      ⟨Vertex.q (Sum.inr qVertex), member⟩ := by
  classical
  let A := A4.toTannerSquareAdmissible
  let successor := rzReplacementPresentation P A S
  let fixedVertex : ZDoubleCylinderVertex P z S :=
    (copy, Sum.inl ⟨Vertex.z x, originalMember⟩)
  let fixedZ : successor.Z := rzOriginalZZVertex P S z copy x originalMember
  have hsuccessorQZ : successor.qz (Sum.inr qVertex) fixedZ = true := by
    simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
    obtain ⟨successorFace, hfaceZ, hfaceQ⟩ := member
    rcases hfaceQ with hfaceQ | hfaceQ
    · have h := successor.data.faceQ_qz successorFace 0
      change successor.qz (successor.faceQ successorFace 0)
        (successor.faceZ successorFace) = true at h
      change Sum.inr qVertex = successor.faceQ successorFace 0 at hfaceQ
      have hz : successor.faceZ successorFace = fixedZ := by
        simpa [zStarFaceMember] using hfaceZ
      rw [← hfaceQ, hz] at h
      exact h
    · have h := successor.data.faceQ_qz successorFace 1
      change successor.qz (successor.faceQ successorFace 1)
        (successor.faceZ successorFace) = true at h
      change Sum.inr qVertex = successor.faceQ successorFace 1 at hfaceQ
      have hz : successor.faceZ successorFace = fixedZ := by
        simpa [zStarFaceMember] using hfaceZ
      rw [← hfaceQ, hz] at h
      exact h
  rcases qVertex with ⟨glueQ, qVertex⟩
  change successor.qz (Sum.inr ⟨glueQ, qVertex⟩) fixedZ = true
    at hsuccessorQZ
  by_cases hqz : P.qz glueQ z = true
  · have hmap : qToZDoubleCylinderVertex P A glueQ z hqz S qVertex =
        fixedVertex := by
      change decide (∃ hqz' : P.qz glueQ z = true,
        qToZDoubleCylinderVertex P A glueQ z hqz' S qVertex =
          fixedVertex) = true at hsuccessorQZ
      obtain ⟨hqz', hmap⟩ := of_decide_eq_true hsuccessorQZ
      simpa only [Subsingleton.elim hqz' hqz] using hmap
    obtain ⟨⟨qEdge, endpoint⟩, hendpoint⟩ :=
      qDoubleCylinderVertexIncidentEdge P A glueQ S qVertex
    have hendpoint' : edgeEndpoint
          (qDoubleCylinderEdgeStart (transposePresentation P) glueQ S)
          (qDoubleCylinderEdgeEnd (transposePresentation P) glueQ S)
          qEdge endpoint = qVertex := by
      fin_cases endpoint <;> simpa [edgeEndpoint, twoSelect] using hendpoint
    let oldEdge : QZEdge P := ⟨(glueQ, z), hqz⟩
    let localEdge : ZDoubleCylinderEdge P z S :=
      qToZDoubleCylinderEdge P A glueQ z hqz S qEdge
    let localQ : Sigma fun oldZ : P.Z => ZDoubleCylinderEdge P oldZ S :=
      ⟨z, localEdge⟩
    let glue : RZQZGlueFace P S := ⟨oldEdge, qEdge, endpoint⟩
    have hfaceZ : glueFaceZ P A S glue = fixedZ := by
      apply Sigma.ext (x := glueFaceZ P A S glue) (y := fixedZ) rfl
      apply heq_of_eq
      simp only [glueFaceZ, glue, oldEdge, fixedZ]
      change qToZDoubleCylinderVertex P A glueQ z hqz S
          (edgeEndpoint
            (qDoubleCylinderEdgeStart (transposePresentation P) glueQ S)
            (qDoubleCylinderEdgeEnd (transposePresentation P) glueQ S)
            qEdge endpoint) = fixedVertex
      rw [hendpoint']
      exact hmap
    have hlocalMember : zStarBoundaryVertexMember successor fixedZ
        (Vertex.q (Sum.inl localQ)) = true := by
      change decide (∃ successorFace : successor.Face,
        zStarFaceMember successor fixedZ successorFace = true ∧
          (Sum.inl localQ = successor.faceQ successorFace 0 ∨
            Sum.inl localQ = successor.faceQ successorFace 1)) = true
      rw [decide_eq_true_eq]
      refine ⟨Sum.inr (Sum.inl glue), ?_, Or.inl ?_⟩
      · simp only [zStarFaceMember, decide_eq_true_eq]
        exact hfaceZ
      · rfl
    let face : ZStarFace successor fixedZ :=
      ⟨Sum.inr (Sum.inl glue), by
        simp only [zStarFaceMember, decide_eq_true_eq]
        exact hfaceZ⟩
    let first := rzOriginalZBoundaryPathToLocalQ P A4 R S z copy x
      originalMember localQ hlocalMember
    let last := rzZStarFaceBoundaryPathToQ successor fixedZ face 1
    have hlocal :
        (⟨Vertex.q (Sum.inl localQ), hlocalMember⟩ :
          ZStarBoundaryVertex successor fixedZ) =
        zBoundaryEdgeEnd successor fixedZ
          (rzZStarFaceBoundaryEdge successor fixedZ face 0) := by
      apply Subtype.ext
      rw [rzZStarFaceBoundaryEdge_end_value]
      rfl
    have htarget : zBoundaryEdgeEnd successor fixedZ
          (rzZStarFaceBoundaryEdge successor fixedZ face 1) =
        (⟨Vertex.q (Sum.inr ⟨glueQ, qVertex⟩), member⟩ :
          ZStarBoundaryVertex successor fixedZ) := by
      apply Subtype.ext
      rw [rzZStarFaceBoundaryEdge_end_value]
      apply congrArg Vertex.q
      change glueFaceQ1 P S glue = Sum.inr ⟨glueQ, qVertex⟩
      simp only [glueFaceQ1, glue, oldEdge]
      apply congrArg Sum.inr
      exact Sigma.ext rfl (heq_of_eq hendpoint')
    exact first.append (hlocal ▸ (htarget.symm ▸ last))
  · exact False.elim (by
      change decide (∃ hqz' : P.qz glueQ z = true,
        qToZDoubleCylinderVertex P A glueQ z hqz' S qVertex =
          fixedVertex) = true at hsuccessorQZ
      obtain ⟨hqz', _⟩ := of_decide_eq_true hsuccessorQZ
      exact hqz hqz')

/-- Route to a retained old-X tag on the original-Z fixed-Z boundary through
the Q0 corner of its witnessing old face. -/
private noncomputable def rzOriginalZBoundaryPathToOldX
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (z : P.Z) (copy : Two) (x : P.X)
    (originalMember : xStarVertexMember (transposePresentation P) z
      (Vertex.z x) = true)
    (oldX : P.X × Two)
    (member : zStarBoundaryVertexMember
      (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
      (rzOriginalZZVertex P S z copy x originalMember)
      (Vertex.x (Sum.inr oldX)) = true) :
    UndirectedPath
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalZZVertex P S z copy x originalMember))
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalZZVertex P S z copy x originalMember))
      (rzReplacementZBoundaryRoot P A4.toTannerSquareAdmissibleV3 S
        (rzOriginalZZVertex P S z copy x originalMember))
      ⟨Vertex.x (Sum.inr oldX), member⟩ := by
  classical
  let A := A4.toTannerSquareAdmissible
  let successor := rzReplacementPresentation P A S
  let fixedZ : successor.Z := rzOriginalZZVertex P S z copy x originalMember
  by_cases holdX : oldX = (x, copy)
  · subst oldX
    let face : P.Face := (rzOriginalZOwnerFace P A4 z x originalMember).1
    have hfaceZ : P.faceZ face = z := by
      have hmember := (rzOriginalZOwnerFace P A4 z x originalMember).2
      simp only [xStarFaceMember, decide_eq_true_eq] at hmember
      exact hmember
    have hfaceX : P.faceX face = x := by
      exact rzOriginalZOwnerFace_x P A4 z x originalMember
    have holdFaceZ : oldXFaceZ P S (face, copy) = fixedZ := by
      let targetZ : P.Z := z
      have hzTag : targetZ = P.faceZ face := by
        exact hfaceZ.symm
      have hstar : xStarVertexMember (transposePresentation P) targetZ
          (Vertex.z (P.faceX face)) = true := by
        simp only [xStarVertexMember, decide_eq_true_eq]
        refine ⟨face, ?_, rfl⟩
        simp only [xStarFaceMember, decide_eq_true_eq]
        exact hfaceZ
      let materialize (target : P.Z)
          (htarget : target = P.faceZ face)
          (targetMember : xStarVertexMember (transposePresentation P) target
            (Vertex.z (P.faceX face)) = true) :
          (⟨target, (copy, Sum.inl
            (⟨Vertex.z (P.faceX face), targetMember⟩ :
              XStarVertex (transposePresentation P) target))⟩ : RZZ P S) =
            oldXFaceZ P S (face, copy) := by
        subst target
        apply Sigma.ext rfl
        apply heq_of_eq
        apply Prod.ext
        · rfl
        · apply congrArg Sum.inl
          apply Subtype.ext
          rfl
      have hmaterialized := materialize targetZ hzTag hstar
      have hfixed :
          (⟨targetZ, (copy, Sum.inl
            (⟨Vertex.z (P.faceX face), hstar⟩ :
              XStarVertex (transposePresentation P) targetZ))⟩ : RZZ P S) =
            fixedZ := by
        dsimp only [targetZ, fixedZ, rzOriginalZZVertex]
        apply Sigma.ext
          (x := (⟨z, (copy, Sum.inl
            (⟨Vertex.z (P.faceX face), hstar⟩ :
              XStarVertex (transposePresentation P) z))⟩ : RZZ P S))
          (y := (⟨z, (copy, Sum.inl
            (⟨Vertex.z x, originalMember⟩ :
              XStarVertex (transposePresentation P) z))⟩ : RZZ P S)) rfl
        apply heq_of_eq
        apply Prod.ext
        · rfl
        · apply congrArg Sum.inl
          apply Subtype.ext
          exact congrArg Vertex.z hfaceX
      exact hmaterialized.symm.trans hfixed
    let qVertex : Sigma fun glueQ : P.Q =>
        QDoubleCylinderVertex (transposePresentation P) glueQ S :=
      ⟨P.faceQ face 0,
        (copy, Sum.inl (Sum.inr
          (⟨P.faceX face, P.data.faceQ_xq face 0⟩ :
            QStarEdge (transposePresentation P) (P.faceQ face 0))))⟩
    have hqMember : zStarBoundaryVertexMember successor fixedZ
        (Vertex.q (Sum.inr qVertex)) = true := by
      change decide (∃ candidate : successor.Face,
        zStarFaceMember successor fixedZ candidate = true ∧
          (Sum.inr qVertex = successor.faceQ candidate 0 ∨
            Sum.inr qVertex = successor.faceQ candidate 1)) = true
      rw [decide_eq_true_eq]
      refine ⟨Sum.inr (Sum.inr (face, copy)), ?_, Or.inl ?_⟩
      · simp only [zStarFaceMember, decide_eq_true_eq]
        exact holdFaceZ
      · rfl
    let oldZFace : ZStarFace successor fixedZ :=
      ⟨Sum.inr (Sum.inr (face, copy)), by
        simp only [zStarFaceMember, decide_eq_true_eq]
        exact holdFaceZ⟩
    let first := rzOriginalZBoundaryPathToQVertex P A4 R S z copy x
      originalMember qVertex hqMember
    let last := rzZStarFaceBoundaryPathToX successor fixedZ oldZFace
    have hq :
        (⟨Vertex.q (Sum.inr qVertex), hqMember⟩ :
          ZStarBoundaryVertex successor fixedZ) =
        zBoundaryEdgeEnd successor fixedZ
          (rzZStarFaceBoundaryEdge successor fixedZ oldZFace 0) := by
      apply Subtype.ext
      rw [rzZStarFaceBoundaryEdge_end_value]
      rfl
    have htarget : zBoundaryEdgeStart successor fixedZ
          (rzZStarFaceBoundaryEdge successor fixedZ oldZFace 0) =
        (⟨Vertex.x (Sum.inr (x, copy)), member⟩ :
          ZStarBoundaryVertex successor fixedZ) := by
      apply Subtype.ext
      rw [rzZStarFaceBoundaryEdge_start_value]
      exact congrArg Vertex.x
        (congrArg (fun tagged : P.X =>
          (Sum.inr (tagged, copy) : RZX P S)) hfaceX)
    exact first.append (hq ▸ (htarget.symm ▸ last))
  · exact False.elim (by
      simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
      obtain ⟨successorFace, hsuccessorZ, hsuccessorX⟩ := member
      simp only [zStarFaceMember, decide_eq_true_eq] at hsuccessorZ
      rcases successorFace with localFace | glueOrOld
      · change Sum.inr oldX = localFaceX P S localFace at hsuccessorX
        simp [localFaceX] at hsuccessorX
      · rcases glueOrOld with glueFace | oldFace
        · change Sum.inr oldX = glueFaceX P S glueFace at hsuccessorX
          simp [glueFaceX] at hsuccessorX
        · rcases oldFace with ⟨candidateFace, candidateCopy⟩
          change oldXFaceZ P S (candidateFace, candidateCopy) = fixedZ
            at hsuccessorZ
          have hz : P.faceZ candidateFace = z :=
            congrArg Sigma.fst hsuccessorZ
          cases hz
          have hvertex := eq_of_heq
            (Sigma.mk.inj_iff.mp hsuccessorZ).2
          have hcopy : candidateCopy = copy := congrArg Prod.fst hvertex
          have htag := congrArg (fun value => value.2) hvertex
          have hx : P.faceX candidateFace = x := by
            simp [oldXFaceZ, fixedZ, rzOriginalZZVertex,
              xStarFaceZVertex, transposePresentation] at htag
            exact Vertex.z.inj htag
          have htarget : oldX = (P.faceX candidateFace, candidateCopy) := by
            change Sum.inr oldX = Sum.inr (P.faceX candidateFace,
              candidateCopy) at hsuccessorX
            exact Sum.inr.inj hsuccessorX
          exact holdX (htarget.trans (congrArg₂ Prod.mk hx hcopy)))

/-- Total boundary dispatcher at a copy-tagged original-Z successor Z
coordinate. -/
private noncomputable def rzOriginalZBoundaryPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (z : P.Z) (copy : Two) (x : P.X)
    (originalMember : xStarVertexMember (transposePresentation P) z
      (Vertex.z x) = true)
    (vertex : ZStarBoundaryVertex (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S)
      (rzOriginalZZVertex P S z copy x originalMember)) :
    UndirectedPath
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalZZVertex P S z copy x originalMember))
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalZZVertex P S z copy x originalMember))
      (rzReplacementZBoundaryRoot P A4.toTannerSquareAdmissibleV3 S
        (rzOriginalZZVertex P S z copy x originalMember))
      vertex := by
  rcases vertex with ⟨value, member⟩
  rcases value with successorX | successorQ | impossible
  · rcases successorX with (localX | glueX) | oldX
    · exact rzOriginalZBoundaryPathToLocalX P A4 R S z copy x
        originalMember localX member
    · rcases glueX with ⟨glueQ, qEdge⟩
      exact rzOriginalZBoundaryPathToGlueX P A4 R S z copy x
        originalMember glueQ qEdge member
    · exact rzOriginalZBoundaryPathToOldX P A4 R S z copy x
        originalMember oldX member
  · rcases successorQ with localQ | qVertex
    · exact rzOriginalZBoundaryPathToLocalQ P A4 R S z copy x
        originalMember localQ member
    · exact rzOriginalZBoundaryPathToQVertex P A4 R S z copy x
        originalMember qVertex member
  · exact False.elim (by
      simp [zStarBoundaryVertexMember] at member)


/-- Total boundary dispatcher at a copy-tagged original-Q successor Z
coordinate. -/
private noncomputable def rzOriginalQBoundaryPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (copy : Two) (q : P.Q)
    (originalMember : xStarVertexMember (transposePresentation P) z
      (Vertex.q q) = true)
    (vertex : ZStarBoundaryVertex (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S)
      (rzOriginalQZVertex P S z copy q originalMember)) :
    UndirectedPath
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalQZVertex P S z copy q originalMember))
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S)
        (rzOriginalQZVertex P S z copy q originalMember))
      (rzReplacementZBoundaryRoot P A4.toTannerSquareAdmissibleV3 S
        (rzOriginalQZVertex P S z copy q originalMember))
      vertex := by
  rcases vertex with ⟨value, member⟩
  rcases value with successorX | successorQ | impossible
  · rcases successorX with (localX | glueX) | oldX
    · exact rzOriginalQBoundaryPathToLocalX P A4 S z copy q
        originalMember localX member
    · rcases glueX with ⟨glueQ, qEdge⟩
      exact rzOriginalQBoundaryPathToGlueX P A4 S z copy q
        originalMember glueQ qEdge member
    · exact False.elim (by
        simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
        obtain ⟨successorFace, hfaceZ, hfaceX⟩ := member
        simp only [zStarFaceMember, decide_eq_true_eq] at hfaceZ
        rcases successorFace with localFace | glueOrOld
        · change Sum.inr oldX = localFaceX P S localFace at hfaceX
          simp [localFaceX] at hfaceX
        · rcases glueOrOld with glueFace | oldFace
          · change Sum.inr oldX = glueFaceX P S glueFace at hfaceX
            simp [glueFaceX] at hfaceX
          · rcases oldFace with ⟨oldFace, faceCopy⟩
            change oldXFaceZ P S (oldFace, faceCopy) =
              rzOriginalQZVertex P S z copy q originalMember at hfaceZ
            simp only [oldXFaceZ, rzOriginalQZVertex,
              Sigma.mk.inj_iff] at hfaceZ
            rcases hfaceZ with ⟨rfl, hvertex⟩
            have hvertex := eq_of_heq hvertex
            have htag := congrArg (fun value => value.2) hvertex
            simp [xStarFaceZVertex] at htag)
  · rcases successorQ with localQ | qVertex
    · exact rzOriginalQBoundaryPathToLocalQ P A4 S z copy q
        originalMember localQ member
    · exact rzOriginalQBoundaryPathToQVertex P A4 S z copy q
        originalMember qVertex member
  · exact False.elim (by
      simp [zStarBoundaryVertexMember] at member)

/-- Choice-free route to a retained Q-cylinder vertex at a stored
star-edge-interior coordinate.  Successor Q-Z incidence supplies the old Q-Z
proof; a deterministic incident Q-cylinder edge then materializes the glue
face connecting its local-edge image to the requested Q vertex. -/
private noncomputable def rzStarEdgeInteriorBoundaryPathToQVertex
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (starEdge : XStarEdge (transposePresentation P) z)
    (index : Fin (S.half - 1))
    (qVertex : Sigma fun q : P.Q =>
      QDoubleCylinderVertex (transposePresentation P) q S)
    (member : zStarBoundaryVertexMember
      (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
      ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩
      (Vertex.q (Sum.inr qVertex)) = true) :
    UndirectedPath
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩)
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩)
      (rzReplacementZBoundaryRoot P A3 S
        ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩)
      ⟨Vertex.q (Sum.inr qVertex), member⟩ := by
  classical
  let A := A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  let successor := rzReplacementPresentation P A S
  let fixedVertex : ZDoubleCylinderVertex P z S :=
    (copy, Sum.inr (Sum.inl (starEdge, index)))
  let fixedZ : successor.Z := ⟨z, fixedVertex⟩
  have hsuccessorQZ : successor.qz (Sum.inr qVertex) fixedZ = true := by
    simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
    obtain ⟨successorFace, hfaceZ, hfaceQ⟩ := member
    rcases hfaceQ with hfaceQ | hfaceQ
    · have h := successor.data.faceQ_qz successorFace 0
      change successor.qz (successor.faceQ successorFace 0)
        (successor.faceZ successorFace) = true at h
      change Sum.inr qVertex = successor.faceQ successorFace 0 at hfaceQ
      have hz : successor.faceZ successorFace = fixedZ := by
        simpa [zStarFaceMember] using hfaceZ
      rw [← hfaceQ, hz] at h
      exact h
    · have h := successor.data.faceQ_qz successorFace 1
      change successor.qz (successor.faceQ successorFace 1)
        (successor.faceZ successorFace) = true at h
      change Sum.inr qVertex = successor.faceQ successorFace 1 at hfaceQ
      have hz : successor.faceZ successorFace = fixedZ := by
        simpa [zStarFaceMember] using hfaceZ
      rw [← hfaceQ, hz] at h
      exact h
  rcases qVertex with ⟨q, qVertex⟩
  change successor.qz (Sum.inr ⟨q, qVertex⟩) fixedZ = true at hsuccessorQZ
  by_cases hqz : P.qz q z = true
  · have hmap : qToZDoubleCylinderVertex P A q z hqz S qVertex =
        fixedVertex := by
      change decide (∃ hqz' : P.qz q z = true,
        qToZDoubleCylinderVertex P A q z hqz' S qVertex = fixedVertex) = true
        at hsuccessorQZ
      have hexists := of_decide_eq_true hsuccessorQZ
      rcases hexists with ⟨hqz', hmap⟩
      simpa only [Subsingleton.elim hqz' hqz] using hmap
    obtain ⟨⟨qEdge, endpoint⟩, hendpoint⟩ :=
      qDoubleCylinderVertexIncidentEdge P A q S qVertex
    have hendpoint' : edgeEndpoint
          (qDoubleCylinderEdgeStart (transposePresentation P) q S)
          (qDoubleCylinderEdgeEnd (transposePresentation P) q S)
          qEdge endpoint = qVertex := by
      fin_cases endpoint <;> simpa [edgeEndpoint, twoSelect] using hendpoint
    let oldEdge : QZEdge P := ⟨(q, z), hqz⟩
    let localEdge : ZDoubleCylinderEdge P z S :=
      qToZDoubleCylinderEdge P A q z hqz S qEdge
    let localQ : Sigma fun oldZ : P.Z => ZDoubleCylinderEdge P oldZ S :=
      ⟨z, localEdge⟩
    let glue : RZQZGlueFace P S := ⟨oldEdge, qEdge, endpoint⟩
    have hfaceZ : glueFaceZ P A S glue = fixedZ := by
      apply Sigma.ext
        (x := glueFaceZ P A S glue)
        (y := fixedZ) rfl
      apply heq_of_eq
      simp only [glueFaceZ, glue, oldEdge, fixedZ]
      change qToZDoubleCylinderVertex P A q z hqz S
          (edgeEndpoint
            (qDoubleCylinderEdgeStart (transposePresentation P) q S)
            (qDoubleCylinderEdgeEnd (transposePresentation P) q S)
            qEdge endpoint) = fixedVertex
      rw [hendpoint']
      exact hmap
    have hlocalMember : zStarBoundaryVertexMember successor fixedZ
        (Vertex.q (Sum.inl localQ)) = true := by
      change decide (∃ successorFace : successor.Face,
        zStarFaceMember successor fixedZ successorFace = true ∧
          (Sum.inl localQ = successor.faceQ successorFace 0 ∨
            Sum.inl localQ = successor.faceQ successorFace 1)) = true
      rw [decide_eq_true_eq]
      refine ⟨Sum.inr (Sum.inl glue), ?_, Or.inl ?_⟩
      · simp only [zStarFaceMember, decide_eq_true_eq]
        exact hfaceZ
      · rfl
    let face : ZStarFace successor fixedZ :=
      ⟨Sum.inr (Sum.inl glue), by
        simp only [zStarFaceMember, decide_eq_true_eq]
        exact hfaceZ⟩
    let first := rzStarEdgeInteriorBoundaryPathToLocalQ
      P A3 S z copy starEdge index localQ hlocalMember
    let last := rzZStarFaceBoundaryPathToQ successor fixedZ face 1
    have hlocal :
        (⟨Vertex.q (Sum.inl localQ), hlocalMember⟩ :
          ZStarBoundaryVertex successor fixedZ) =
        zBoundaryEdgeEnd successor fixedZ
          (rzZStarFaceBoundaryEdge successor fixedZ face 0) := by
      apply Subtype.ext
      rw [rzZStarFaceBoundaryEdge_end_value]
      rfl
    have htarget : zBoundaryEdgeEnd successor fixedZ
          (rzZStarFaceBoundaryEdge successor fixedZ face 1) =
        (⟨Vertex.q (Sum.inr ⟨q, qVertex⟩), member⟩ :
          ZStarBoundaryVertex successor fixedZ) := by
      apply Subtype.ext
      rw [rzZStarFaceBoundaryEdge_end_value]
      apply congrArg Vertex.q
      change glueFaceQ1 P S glue = Sum.inr ⟨q, qVertex⟩
      simp only [glueFaceQ1, glue, oldEdge]
      apply congrArg Sum.inr
      apply Sigma.ext
        (x := (⟨q, edgeEndpoint
          (qDoubleCylinderEdgeStart (transposePresentation P) q S)
          (qDoubleCylinderEdgeEnd (transposePresentation P) q S)
          qEdge endpoint⟩ :
            Sigma fun q : P.Q =>
              QDoubleCylinderVertex (transposePresentation P) q S))
        (y := ⟨q, qVertex⟩) rfl
      apply heq_of_eq
      exact hendpoint'
    exact first.append (hlocal ▸ (htarget.symm ▸ last))
  · exact False.elim (by
      change decide (∃ hqz' : P.qz q z = true,
        qToZDoubleCylinderVertex P A q z hqz' S qVertex = fixedVertex) = true
        at hsuccessorQZ
      obtain ⟨hqz', _⟩ := of_decide_eq_true hsuccessorQZ
      exact hqz hqz')

/-- Total historical boundary dispatcher at a stored star-edge-interior
successor Z coordinate.  Local X, glue X, local Q, and retained Q-cylinder
tags use their explicit paths; old-X and Z constructors cannot meet this
stored one-dimensional interior coordinate. -/
private noncomputable def rzStarEdgeInteriorBoundaryPath
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (starEdge : XStarEdge (transposePresentation P) z)
    (index : Fin (S.half - 1))
    (vertex : ZStarBoundaryVertex (rzReplacementPresentation P
      A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
      ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩) :
    UndirectedPath
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩)
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S)
        ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩)
      (rzReplacementZBoundaryRoot P A3 S
        ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩)
      vertex := by
  let A := A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  rcases vertex with ⟨value, member⟩
  rcases value with successorX | successorQ | impossible
  · rcases successorX with (localX | glueX) | oldX
    · exact rzStarEdgeInteriorBoundaryPathToLocalX
        P A3 S z copy starEdge index localX member
    · rcases glueX with ⟨q, qEdge⟩
      exact rzStarEdgeInteriorBoundaryPathToGlueX
        P A3 S z copy starEdge index q qEdge member
    · exact False.elim (by
        simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
        obtain ⟨successorFace, hfaceZ, hfaceX⟩ := member
        simp only [zStarFaceMember, decide_eq_true_eq] at hfaceZ
        rcases successorFace with localFace | glueOrOld
        · change Sum.inr oldX = localFaceX P S localFace at hfaceX
          simp [localFaceX] at hfaceX
        · rcases glueOrOld with glueFace | oldFace
          · change Sum.inr oldX = glueFaceX P S glueFace at hfaceX
            simp [glueFaceX] at hfaceX
          · rcases oldFace with ⟨oldFace, faceCopy⟩
            change oldXFaceZ P S (oldFace, faceCopy) =
              ⟨z, (copy, Sum.inr (Sum.inl (starEdge, index)))⟩ at hfaceZ
            simp only [oldXFaceZ, Sigma.mk.inj_iff] at hfaceZ
            have hztag := hfaceZ.1
            subst z
            have hvertex := eq_of_heq hfaceZ.2
            simp at hvertex)
  · rcases successorQ with localQ | qVertex
    · exact rzStarEdgeInteriorBoundaryPathToLocalQ
        P A3 S z copy starEdge index localQ member
    · exact rzStarEdgeInteriorBoundaryPathToQVertex
        P A3 S z copy starEdge index qVertex member
  · simp [zStarBoundaryVertexMember] at member

/-- The complete successor Z-boundary path, obtained by structural dispatch
on the retained subdivision coordinate.  Each constructor is handled by its
already materialized central, endpoint, edge-interior, or face-interior
sector. -/
private noncomputable def rzReplacementHistoricalZBoundaryPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (successorZ : (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S).Z)
    (vertex : ZStarBoundaryVertex (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) successorZ) :
    UndirectedPath
      (zBoundaryEdgeStart (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) successorZ)
      (zBoundaryEdgeEnd (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) successorZ)
      (rzReplacementZBoundaryRoot P A4.toTannerSquareAdmissibleV3 S
        successorZ)
      vertex := by
  classical
  rcases successorZ with ⟨z, copy, subdivisionVertex⟩
  rcases subdivisionVertex with original | interior
  · rcases original with ⟨original, originalMember⟩
    rcases original with central | q | x
    · have hcentral : central = z := by
        simp only [xStarVertexMember, decide_eq_true_eq] at originalMember
        exact originalMember
      subst central
      exact rzOriginalCentralBoundaryPath P A4 R S z copy vertex
    · exact rzOriginalQBoundaryPath P A4 S z copy q
        originalMember vertex
    · exact rzOriginalZBoundaryPath P A4 R S z copy x
        originalMember vertex
  · rcases interior with edgeInterior | faceInterior
    · rcases edgeInterior with ⟨starEdge, index⟩
      exact rzStarEdgeInteriorBoundaryPath P A4.toTannerSquareAdmissibleV3
        S z copy starEdge index vertex
    · rcases faceInterior with ⟨face, i, j⟩
      exact rzFaceInteriorBoundaryPath P A4.toTannerSquareAdmissibleV3
        S z copy face i j vertex

/-- Every successor local-edge Q tag has an incident local-face X tag.  The
only non-cellular case is an old Q-Z radial segment, whose face is constructed
from the input V3 owner by `doubleCylinderEdgeFaceOwner`. -/
noncomputable def rzReplacementXQRootLocal
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale)
    (q : Sigma fun z : P.Z => ZDoubleCylinderEdge P z S) :
    {x : (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S).X //
      (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S).xq x
          (Sum.inl q) = true} := by
  let owner := doubleCylinderEdgeFaceOwner (transposePresentation P)
    (transposeTannerSquareAdmissibleV3 P A3) q.1 S q.2
  refine ⟨Sum.inl (Sum.inl ⟨q.1, owner.1⟩), ?_⟩
  simp only [rzReplacementPresentation, rzReplacementData, rzXQIncidence]
  apply decide_eq_true
  exact ⟨rfl, owner.2⟩

/-- The complete successor X-Q root, constructed in strict A3-to-A' order.
Local edges use `rzReplacementXQRootLocal`; Q-cylinder vertices retain an
explicit incident Q-cylinder edge. -/
noncomputable def rzReplacementXQRoot
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale)
    (q : (rzReplacementPresentation P
      A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S).Q) :
    {x : (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S).X //
      (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S).xq x q = true} := by
  let A := A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  rcases q with localEdge | qVertex
  · exact rzReplacementXQRootLocal P A3 S localEdge
  · obtain ⟨⟨edge, endpoint⟩, hendpoint⟩ :=
      qDoubleCylinderVertexIncidentEdge P A qVertex.1 S qVertex.2
    refine ⟨Sum.inl (Sum.inr ⟨qVertex.1, edge⟩), ?_⟩
    simp only [rzReplacementPresentation, rzReplacementData, rzXQIncidence]
    apply decide_eq_true
    refine ⟨rfl, ?_⟩
    exact rzTwoElim (motive := fun endpoint =>
        BDL26TannerLocalRegularity.edgeEndpoint
            (qDoubleCylinderEdgeStart (transposePresentation P) qVertex.1 S)
            (qDoubleCylinderEdgeEnd (transposePresentation P) qVertex.1 S)
            edge endpoint = qVertex.2 →
          qVertex.2 = qDoubleCylinderEdgeStart
              (transposePresentation P) qVertex.1 S edge ∨
            qVertex.2 = qDoubleCylinderEdgeEnd
              (transposePresentation P) qVertex.1 S edge)
      (fun h => Or.inl h.symm) (fun h => Or.inr h.symm) endpoint hendpoint

/-- Every successor Q tag has a constructor-level incident Z tag.  Local
edges use their start endpoint; q-side vertices use the old admissibility
root and the same-cell #879 embedding. -/
noncomputable def rzReplacementQZRoot
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (q : (rzReplacementPresentation P A S).Q) :
    {z : (rzReplacementPresentation P A S).Z //
      (rzReplacementPresentation P A S).qz q z = true} := by
  classical
  rcases q with localEdge | qVertex
  · refine ⟨⟨localEdge.1,
      tannerDoubleCylinderEdgeStart (transposePresentation P)
        localEdge.1 S localEdge.2⟩, ?_⟩
    simp only [rzReplacementPresentation, rzReplacementData, rzQZIncidence]
    apply decide_eq_true
    refine ⟨rfl, ?_⟩
    exact doubleCylinderEdgeVertexMatrix_start_eq_one
      (transposePresentation P) localEdge.1 S localEdge.2
  · let root := A.qzRoot qVertex.1
    refine ⟨⟨root.1,
      qToZDoubleCylinderVertex P A qVertex.1 root.1 root.2 S qVertex.2⟩, ?_⟩
    simp only [rzReplacementPresentation, rzReplacementData, rzQZIncidence]
    apply decide_eq_true
    exact ⟨root.2, rfl⟩

/-- The exact historical six-field admissibility package for the RZ
successor.  This is the A-prime object consumed by later versioned
successor constructions; it contains no V2 endpoint-owner fields. -/
noncomputable def rzReplacementAdmissible
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) :
    TannerSquareAdmissible
      (rzReplacementPresentation P A4.toTannerSquareAdmissible S) where
  xBoundaryRoot := rzReplacementHistoricalXBoundaryRoot P
    A4.toTannerSquareAdmissibleV3 S
  xBoundaryPath := rzReplacementHistoricalXBoundaryPath P
    A4.toTannerSquareAdmissibleV3 S
  zBoundaryRoot := rzReplacementZBoundaryRoot P
    A4.toTannerSquareAdmissibleV3 S
  zBoundaryPath := rzReplacementHistoricalZBoundaryPath P A4 R S
  qzRoot := rzReplacementQZRoot P A4.toTannerSquareAdmissible S
  xqRoot := rzReplacementXQRoot P A4.toTannerSquareAdmissibleV3 S

/-! ## Successor V2 endpoint routing -/

/-- A concrete local-cell Z corner is the end of either ordered Q-Z side of
the corresponding successor face. -/
private noncomputable def rzLocalCellBoundaryIncidentEdgeToZAt
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (cell : ZDoubleCylinderFace P z S)
    (newZ : RZZ P S)
    (member : xStarBoundaryVertexMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S)
      (Sum.inl (Sum.inl ⟨z, cell⟩)) (Vertex.z newZ) = true)
    (corner : Two × Two)
    (htarget : newZ = rzLocalCellZAt P S z cell corner) :
    {owned : XStarBoundaryEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inl ⟨z, cell⟩)) × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (xBoundaryEdgeStart (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inl ⟨z, cell⟩)))
        (xBoundaryEdgeEnd (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inl ⟨z, cell⟩)))
        owned.1 owned.2 = ⟨Vertex.z newZ, member⟩} := by
  let A := A4.toTannerSquareAdmissible
  let face := rzLocalCellXStarFace P A S z cell corner
  let edge := rzXStarFaceBoundaryEdge (rzReplacementPresentation P A S)
    (Sum.inl (Sum.inl ⟨z, cell⟩)) face 0
  refine ⟨⟨edge, 1⟩, ?_⟩
  rw [edgeEndpoint_one]
  apply Subtype.ext
  exact congrArg Vertex.z htarget.symm

/-- A concrete local-cell Q corner is the start of its ordered Q-Z side. -/
private noncomputable def rzLocalCellBoundaryIncidentEdgeToQAt
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (cell : ZDoubleCylinderFace P z S)
    (newQ : RZQ P S)
    (member : xStarBoundaryVertexMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S)
      (Sum.inl (Sum.inl ⟨z, cell⟩)) (Vertex.q newQ) = true)
    (corner : Two × Two) (qCorner : Two)
    (htarget : newQ = rzLocalCellQAt P A4.toTannerSquareAdmissible
      S z cell corner qCorner) :
    {owned : XStarBoundaryEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inl ⟨z, cell⟩)) × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (xBoundaryEdgeStart (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inl ⟨z, cell⟩)))
        (xBoundaryEdgeEnd (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inl ⟨z, cell⟩)))
        owned.1 owned.2 = ⟨Vertex.q newQ, member⟩} := by
  let A := A4.toTannerSquareAdmissible
  let face := rzLocalCellXStarFace P A S z cell corner
  let edge := rzXStarFaceBoundaryEdge (rzReplacementPresentation P A S)
    (Sum.inl (Sum.inl ⟨z, cell⟩)) face qCorner
  refine ⟨⟨edge, 0⟩, ?_⟩
  rw [edgeEndpoint_zero]
  apply Subtype.ext
  exact congrArg Vertex.q htarget.symm

/-- Constructor-complete endpoint routing for the local-face owner family of
the successor X boundary.  This realizes the five grouped RZ-X local rows of
the #908 table without recovering a face from boundary membership. -/
private noncomputable def rzLocalCellBoundaryIncidentEdge
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (cell : ZDoubleCylinderFace P z S)
    (vertex : XStarBoundaryVertex (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inl ⟨z, cell⟩))) :
    {owned : XStarBoundaryEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inl ⟨z, cell⟩)) × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (xBoundaryEdgeStart (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inl ⟨z, cell⟩)))
        (xBoundaryEdgeEnd (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inl ⟨z, cell⟩)))
        owned.1 owned.2 = vertex} := by
  let A := A4.toTannerSquareAdmissible
  rcases vertex with ⟨value, member⟩
  rcases value with impossible | newQ | newZ
  · simp [xStarBoundaryVertexMember] at member
  · have cases := rzLocalCellBoundaryQ_cases P A S z cell newQ member
    by_cases h000 : newQ = rzLocalCellQAt P A S z cell (0, 0) 0
    · exact rzLocalCellBoundaryIncidentEdgeToQAt P A4 S z cell newQ member
        (0, 0) 0 h000
    · by_cases h001 : newQ = rzLocalCellQAt P A S z cell (0, 0) 1
      · exact rzLocalCellBoundaryIncidentEdgeToQAt P A4 S z cell newQ member
          (0, 0) 1 h001
      · by_cases h010 : newQ = rzLocalCellQAt P A S z cell (0, 1) 0
        · exact rzLocalCellBoundaryIncidentEdgeToQAt P A4 S z cell newQ member
            (0, 1) 0 h010
        · by_cases h011 : newQ = rzLocalCellQAt P A S z cell (0, 1) 1
          · exact rzLocalCellBoundaryIncidentEdgeToQAt P A4 S z cell newQ
              member (0, 1) 1 h011
          · by_cases h100 : newQ = rzLocalCellQAt P A S z cell (1, 0) 0
            · exact rzLocalCellBoundaryIncidentEdgeToQAt P A4 S z cell newQ
                member (1, 0) 0 h100
            · by_cases h101 : newQ = rzLocalCellQAt P A S z cell (1, 0) 1
              · exact rzLocalCellBoundaryIncidentEdgeToQAt P A4 S z cell newQ
                  member (1, 0) 1 h101
              · by_cases h110 : newQ = rzLocalCellQAt P A S z cell (1, 1) 0
                · exact rzLocalCellBoundaryIncidentEdgeToQAt P A4 S z cell
                    newQ member (1, 1) 0 h110
                · have remaining001 := cases.resolve_left h000
                  have remaining010 := remaining001.resolve_left h001
                  have remaining011 := remaining010.resolve_left h010
                  have remaining100 := remaining011.resolve_left h011
                  have remaining101 := remaining100.resolve_left h100
                  have remaining110 := remaining101.resolve_left h101
                  have h111 := remaining110.resolve_left h110
                  exact rzLocalCellBoundaryIncidentEdgeToQAt P A4 S z cell
                    newQ member (1, 1) 1 h111
  · by_cases h00 : newZ = rzLocalCellZAt P S z cell (0, 0)
    · exact rzLocalCellBoundaryIncidentEdgeToZAt P A4 S z cell newZ member
        (0, 0) h00
    · by_cases h01 : newZ = rzLocalCellZAt P S z cell (0, 1)
      · exact rzLocalCellBoundaryIncidentEdgeToZAt P A4 S z cell newZ member
          (0, 1) h01
      · by_cases h10 : newZ = rzLocalCellZAt P S z cell (1, 0)
        · exact rzLocalCellBoundaryIncidentEdgeToZAt P A4 S z cell newZ member
            (1, 0) h10
        · have remaining01 :=
            (rzLocalCellBoundaryZ_cases P A S z cell newZ member).resolve_left h00
          have remaining10 := remaining01.resolve_left h01
          have h11 := remaining10.resolve_left h10
          exact rzLocalCellBoundaryIncidentEdgeToZAt P A4 S z cell newZ member
            (1, 1) h11

/-- The local-Q boundary tag of a glue X owner is the start of the concrete
Q-Z side retained by the glue face. -/
private noncomputable def rzGlueXBoundaryIncidentEdgeToLocalQ
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale)
    (qEdge : Sigma fun q : P.Q =>
      QDoubleCylinderEdge (transposePresentation P) q S)
    (localEdge : Sigma fun z : P.Z => ZDoubleCylinderEdge P z S)
    (member : xStarBoundaryVertexMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inr qEdge))
      (Vertex.q (Sum.inl localEdge)) = true) :
    {owned : XStarBoundaryEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inr qEdge)) × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (xBoundaryEdgeStart (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inr qEdge)))
        (xBoundaryEdgeEnd (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inr qEdge)))
        owned.1 owned.2 = ⟨Vertex.q (Sum.inl localEdge), member⟩} := by
  let A := A4.toTannerSquareAdmissible
  let hqz := rzGlueXBoundaryLocalQ_incidence P A S qEdge localEdge member
  let face := rzGlueXStarFace P A S qEdge localEdge.1 hqz 0
  let edge := rzXStarFaceBoundaryEdge (rzReplacementPresentation P A S)
    (Sum.inl (Sum.inr qEdge)) face 0
  refine ⟨⟨edge, 0⟩, ?_⟩
  rw [BDL26TannerLocalRegularity.edgeEndpoint_zero]
  apply Subtype.ext
  apply congrArg Vertex.q
  apply congrArg Sum.inl
  refine Sigma.ext (x := (⟨localEdge.1,
    qToZDoubleCylinderEdge P A qEdge.1 localEdge.1 hqz S qEdge.2⟩ :
      Sigma fun z : P.Z => ZDoubleCylinderEdge P z S))
    (y := localEdge) rfl ?_
  exact heq_of_eq
    (rzGlueXBoundaryLocalQ_edge P A S qEdge localEdge member).symm

/-- A Q-cylinder vertex of a glue X owner retains its structural edge
endpoint; the successor Q-Z side starts at that requested Q. -/
private noncomputable def rzGlueXBoundaryIncidentEdgeToQVertex
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale)
    (qEdge : Sigma fun q : P.Q =>
      QDoubleCylinderEdge (transposePresentation P) q S)
    (qVertex : Sigma fun q : P.Q =>
      QDoubleCylinderVertex (transposePresentation P) q S)
    (member : xStarBoundaryVertexMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inr qEdge))
      (Vertex.q (Sum.inr qVertex)) = true) :
    {owned : XStarBoundaryEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inr qEdge)) × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (xBoundaryEdgeStart (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inr qEdge)))
        (xBoundaryEdgeEnd (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inr qEdge)))
        owned.1 owned.2 = ⟨Vertex.q (Sum.inr qVertex), member⟩} := by
  let A := A4.toTannerSquareAdmissible
  have hdata := rzGlueXBoundaryQVertex_endpoints P A S qEdge qVertex member
  let startVertex : Sigma fun q : P.Q =>
      QDoubleCylinderVertex (transposePresentation P) q S :=
    ⟨qEdge.1, qDoubleCylinderEdgeStart
      (transposePresentation P) qEdge.1 S qEdge.2⟩
  let endVertex : Sigma fun q : P.Q =>
      QDoubleCylinderVertex (transposePresentation P) q S :=
    ⟨qEdge.1, qDoubleCylinderEdgeEnd
      (transposePresentation P) qEdge.1 S qEdge.2⟩
  let endpoint := rzOrientedBoundaryEndpoint
    (fun _ : Unit => startVertex) (fun _ : Unit => endVertex) () qVertex
  let root := A.qzRoot qEdge.1
  let face := rzGlueXStarFace P A S qEdge root.1 root.2 endpoint
  let edge := rzXStarFaceBoundaryEdge (rzReplacementPresentation P A S)
    (Sum.inl (Sum.inr qEdge)) face 1
  have hselected :
      (⟨qEdge.1, edgeEndpoint
        (qDoubleCylinderEdgeStart (transposePresentation P) qEdge.1 S)
        (qDoubleCylinderEdgeEnd (transposePresentation P) qEdge.1 S)
        qEdge.2 endpoint⟩ : Sigma fun q : P.Q =>
          QDoubleCylinderVertex (transposePresentation P) q S) = qVertex := by
    have hshape : edgeEndpoint
        (fun _ : Unit => startVertex) (fun _ : Unit => endVertex) () endpoint =
        (⟨qEdge.1, edgeEndpoint
          (qDoubleCylinderEdgeStart (transposePresentation P) qEdge.1 S)
          (qDoubleCylinderEdgeEnd (transposePresentation P) qEdge.1 S)
          qEdge.2 endpoint⟩ : Sigma fun q : P.Q =>
            QDoubleCylinderVertex (transposePresentation P) q S) := by
      by_cases hzero : endpoint = 0
      · rw [hzero]
        rfl
      · have hone : endpoint = 1 := by
          apply Fin.ext
          have hlt := endpoint.2
          have hne : endpoint.1 ≠ 0 := by
            intro h
            apply hzero
            apply Fin.ext
            exact h
          omega
        rw [hone]
        rfl
    exact hshape.symm.trans (rzOrientedBoundaryEndpoint_spec
      (fun _ : Unit => startVertex) (fun _ : Unit => endVertex)
      () qVertex hdata)
  refine ⟨⟨edge, 0⟩, ?_⟩
  rw [BDL26TannerLocalRegularity.edgeEndpoint_zero]
  apply Subtype.ext
  apply congrArg Vertex.q
  apply congrArg Sum.inr
  exact hselected

/-- A Z boundary tag of a glue X owner is the end of the concrete Q-Z side at
its uniquely retained oriented Q-cylinder endpoint. -/
private noncomputable def rzGlueXBoundaryIncidentEdgeToZ
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale)
    (qEdge : Sigma fun q : P.Q =>
      QDoubleCylinderEdge (transposePresentation P) q S)
    (newZ : RZZ P S)
    (member : xStarBoundaryVertexMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inr qEdge))
      (Vertex.z newZ) = true) :
    {owned : XStarBoundaryEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inr qEdge)) × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (xBoundaryEdgeStart (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inr qEdge)))
        (xBoundaryEdgeEnd (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inr qEdge)))
        owned.1 owned.2 = ⟨Vertex.z newZ, member⟩} := by
  classical
  let A := A4.toTannerSquareAdmissible
  let hqz := rzGlueXBoundaryZ_incidence P A S qEdge newZ member
  have hdata := rzGlueXBoundaryZ_endpoints P A S qEdge newZ member
  let startZ : RZZ P S := ⟨newZ.1,
    qToZDoubleCylinderVertex P A qEdge.1 newZ.1 hqz S
      (qDoubleCylinderEdgeStart
        (transposePresentation P) qEdge.1 S qEdge.2)⟩
  let endZ : RZZ P S := ⟨newZ.1,
    qToZDoubleCylinderVertex P A qEdge.1 newZ.1 hqz S
      (qDoubleCylinderEdgeEnd
        (transposePresentation P) qEdge.1 S qEdge.2)⟩
  let endpoint := rzOrientedBoundaryEndpoint
    (fun _ : Unit => startZ) (fun _ : Unit => endZ) () newZ
  let face := rzGlueXStarFace P A S qEdge newZ.1 hqz endpoint
  let edge := rzXStarFaceBoundaryEdge (rzReplacementPresentation P A S)
    (Sum.inl (Sum.inr qEdge)) face 0
  have hselected : edgeEndpoint
      (fun _ : Unit => startZ) (fun _ : Unit => endZ) () endpoint = newZ :=
    rzOrientedBoundaryEndpoint_spec _ _ _ _ hdata
  have hshape : edgeEndpoint
      (fun _ : Unit => startZ) (fun _ : Unit => endZ) () endpoint =
      ⟨newZ.1, qToZDoubleCylinderVertex P A qEdge.1 newZ.1 hqz S
        (edgeEndpoint
          (qDoubleCylinderEdgeStart (transposePresentation P) qEdge.1 S)
          (qDoubleCylinderEdgeEnd (transposePresentation P) qEdge.1 S)
          qEdge.2 endpoint)⟩ := by
    by_cases hzero : endpoint = 0
    · rw [hzero]
      rfl
    · have hone : endpoint = 1 := by
        apply Fin.ext
        have hlt := endpoint.2
        have hne : endpoint.1 ≠ 0 := by
          intro h
          apply hzero
          apply Fin.ext
          exact h
        omega
      rw [hone]
      rfl
  refine ⟨⟨edge, 1⟩, ?_⟩
  rw [BDL26TannerLocalRegularity.edgeEndpoint_one]
  apply Subtype.ext
  apply congrArg Vertex.z
  exact hshape.symm.trans hselected

/-- Constructor-complete endpoint routing for the q-edge/glue owner family of
the successor X boundary. -/
private noncomputable def rzGlueXBoundaryIncidentEdge
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale)
    (qEdge : Sigma fun q : P.Q =>
      QDoubleCylinderEdge (transposePresentation P) q S)
    (vertex : XStarBoundaryVertex (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inr qEdge))) :
    {owned : XStarBoundaryEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inr qEdge)) × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (xBoundaryEdgeStart (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inr qEdge)))
        (xBoundaryEdgeEnd (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inr qEdge)))
        owned.1 owned.2 = vertex} := by
  rcases vertex with ⟨value, member⟩
  rcases value with impossible | newQ | newZ
  · simp [xStarBoundaryVertexMember] at member
  · rcases newQ with localEdge | qVertex
    · exact rzGlueXBoundaryIncidentEdgeToLocalQ P A4 S qEdge localEdge member
    · exact rzGlueXBoundaryIncidentEdgeToQVertex P A4 S qEdge qVertex member
  · exact rzGlueXBoundaryIncidentEdgeToZ P A4 S qEdge newZ member

/-- Lift the input V2-owned old X-boundary edge and preserve its old endpoint
bit.  The two raw endpoint constructors become the two old-copy grouped rows. -/
private noncomputable def rzOldXBoundaryIncidentEdge
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (vertex : XStarBoundaryVertex (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) (Sum.inr (x, copy))) :
    {owned : XStarBoundaryEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) (Sum.inr (x, copy)) × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (xBoundaryEdgeStart (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) (Sum.inr (x, copy)))
        (xBoundaryEdgeEnd (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) (Sum.inr (x, copy)))
        owned.1 owned.2 = vertex} := by
  let A := A4.toTannerSquareAdmissible
  let projected := oldXBoundaryVertexProject P A S x copy vertex
  obtain ⟨⟨oldEdge, endpoint⟩, hendpoint⟩ :=
    A4.xBoundaryIncidentEdge x projected
  let edge := oldXBoundaryEdgeLift P A S x copy oldEdge
  refine ⟨⟨edge, endpoint⟩, ?_⟩
  fin_cases endpoint
  · have hstart : xBoundaryEdgeStart P x oldEdge = projected := by
      exact hendpoint
    change xBoundaryEdgeStart (rzReplacementPresentation P A S)
      (Sum.inr (x, copy)) edge = vertex
    rw [oldXBoundaryEdgeLift_start]
    exact (congrArg (oldXBoundaryVertexLift P A S x copy) hstart).trans
      (oldXBoundaryVertexLift_project P A S x copy vertex)
  · have hend : xBoundaryEdgeEnd P x oldEdge = projected := by
      exact hendpoint
    change xBoundaryEdgeEnd (rzReplacementPresentation P A S)
      (Sum.inr (x, copy)) edge = vertex
    rw [oldXBoundaryEdgeLift_end]
    exact (congrArg (oldXBoundaryVertexLift P A S x copy) hend).trans
      (oldXBoundaryVertexLift_project P A S x copy vertex)

/-- The total successor X-boundary endpoint owner.  Its three constructor
families realize the 16 RZ-X rows of the exact #908 table. -/
private noncomputable def rzReplacementXBoundaryIncidentEdge
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale)
    (x : (rzReplacementPresentation P A4.toTannerSquareAdmissible S).X)
    (vertex : XStarBoundaryVertex (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) x) :
    {owned : XStarBoundaryEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) x × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (xBoundaryEdgeStart (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) x)
        (xBoundaryEdgeEnd (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) x) owned.1 owned.2 = vertex} := by
  rcases x with localOrGlue | oldX
  · rcases localOrGlue with localCell | qEdge
    · exact rzLocalCellBoundaryIncidentEdge P A4 S
        localCell.1 localCell.2 vertex
    · exact rzGlueXBoundaryIncidentEdge P A4 S qEdge vertex
  · exact rzOldXBoundaryIncidentEdge P A4 S oldX.1 oldX.2 vertex

/-- Boundary membership of a successor local-Q tag retains its concrete
Q-Z incidence with the fixed successor Z.  The boundary-face existential is
eliminated only in this proposition-valued declaration. -/
private theorem rzLocalEdgeZBoundary_qz
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale)
    (fixedZ : RZZ P S)
    (localEdge : Sigma fun z : P.Z => ZDoubleCylinderEdge P z S)
    (member : zStarBoundaryVertexMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) fixedZ
      (Vertex.q (Sum.inl localEdge)) = true) :
    (rzReplacementPresentation P A4.toTannerSquareAdmissible S).qz
      (Sum.inl localEdge) fixedZ = true := by
  let successor := rzReplacementPresentation P A4.toTannerSquareAdmissible S
  simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
  obtain ⟨face, hfaceZ, hfaceQ⟩ := member
  rcases hfaceQ with hfaceQ | hfaceQ
  · have h := successor.data.faceQ_qz face 0
    change successor.qz (successor.faceQ face 0)
      (successor.faceZ face) = true at h
    change Sum.inl localEdge = successor.faceQ face 0 at hfaceQ
    have hz : successor.faceZ face = fixedZ := by
      simpa [zStarFaceMember] using hfaceZ
    rw [← hfaceQ, hz] at h
    exact h
  · have h := successor.data.faceQ_qz face 1
    change successor.qz (successor.faceQ face 1)
      (successor.faceZ face) = true at h
    change Sum.inl localEdge = successor.faceQ face 1 at hfaceQ
    have hz : successor.faceZ face = fixedZ := by
      simpa [zStarFaceMember] using hfaceZ
    rw [← hfaceQ, hz] at h
    exact h

/-- A non-radial local successor Q edge uses its constructor-level incident
local cell at the endpoint equal to the fixed Z.  This is the common producer
for the FIH, FIV, boundary-segment, and vertical grouped rows. -/
private noncomputable def rzLocalEdgeZBoundaryIncidentEdgeViaCell
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z)
    (fixedVertex : ZDoubleCylinderVertex P z S)
    (edge : ZDoubleCylinderEdge P z S)
    (member : zStarBoundaryVertexMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) ⟨z, fixedVertex⟩
      (Vertex.q (Sum.inl ⟨z, edge⟩)) = true) :
    {owned : ZStarBoundaryEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) ⟨z, fixedVertex⟩ × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) ⟨z, fixedVertex⟩)
        (zBoundaryEdgeEnd (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) ⟨z, fixedVertex⟩)
        owned.1 owned.2 = ⟨Vertex.q (Sum.inl ⟨z, edge⟩), member⟩} := by
  classical
  let A := A4.toTannerSquareAdmissible
  let successor := rzReplacementPresentation P A S
  have hqz := rzLocalEdgeZBoundary_qz P A4 S ⟨z, fixedVertex⟩
    ⟨z, edge⟩ member
  have hmatrix : doubleCylinderEdgeVertexMatrix
      (transposePresentation P) z S fixedVertex edge = 1 := by
    change decide (Exists fun h : z = z =>
      doubleCylinderEdgeVertexMatrix (transposePresentation P) z S
        (h ▸ fixedVertex) edge = 1) = true at hqz
    obtain ⟨h, hmatrix⟩ := of_decide_eq_true hqz
    simpa only [Subsingleton.elim h rfl] using hmatrix
  have hendpoints : fixedVertex =
        tannerDoubleCylinderEdgeStart (transposePresentation P) z S edge ∨
      fixedVertex =
        tannerDoubleCylinderEdgeEnd (transposePresentation P) z S edge :=
    (doubleCylinderEdgeVertexMatrix_eq_one_iff
      (transposePresentation P) z S fixedVertex edge).1 hmatrix
  let endpoint := rzOrientedBoundaryEndpoint
    (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
    (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
    edge fixedVertex
  let owner := doubleCylinderEdgeFaceSlotOwner (transposePresentation P)
    (transposeTannerSquareAdmissibleV3 P
      A4.toTannerSquareAdmissibleV3) z S edge
  let corner := localCornerAtBoundaryEndpoint P z S
    owner.1.1 owner.1.2 endpoint
  have hcorner : localCornerVertex P z S owner.1.1 corner.1.1 =
      fixedVertex := by
    calc
      localCornerVertex P z S owner.1.1 corner.1.1 =
          BDL26TannerLocalRegularity.edgeEndpoint
            (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
            (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
            (doubleCylinderFaceBoundaryEdge (transposePresentation P) z S
              owner.1.1 owner.1.2) endpoint := corner.2.2
      _ = BDL26TannerLocalRegularity.edgeEndpoint
            (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
            (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
            edge endpoint := by rw [owner.2]
      _ = fixedVertex := by
        have hselected := rzOrientedBoundaryEndpoint_spec
          (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
          (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
          edge fixedVertex hendpoints
        have hbridge : BDL26TannerLocalRegularity.edgeEndpoint
            (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
            (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
            edge endpoint =
          edgeEndpoint
            (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
            (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
            edge endpoint := by
          have hbits : endpoint = 0 ∨ endpoint = 1 := by
            by_cases hzero : endpoint = 0
            · exact Or.inl hzero
            · right
              apply Fin.ext
              have hlt := endpoint.2
              have hne : endpoint.1 ≠ 0 := by
                intro h
                apply hzero
                apply Fin.ext
                exact h
              omega
          rcases hbits with hzero | hone
          · rw [hzero]
            rfl
          · rw [hone]
            rfl
        exact hbridge.trans hselected
  let face : ZStarFace successor ⟨z, fixedVertex⟩ :=
    ⟨Sum.inl ⟨z, owner.1.1, corner.1.1⟩, by
      simp only [zStarFaceMember, decide_eq_true_eq]
      change localFaceZ P S ⟨z, owner.1.1, corner.1.1⟩ =
        ⟨z, fixedVertex⟩
      rw [localFaceZ_eq_corner]
      exact Sigma.ext rfl (heq_of_eq hcorner)⟩
  let boundaryEdge := rzZStarFaceBoundaryEdge successor
    ⟨z, fixedVertex⟩ face corner.1.2
  refine ⟨⟨boundaryEdge, 1⟩, ?_⟩
  rw [BDL26TannerLocalRegularity.edgeEndpoint_one]
  apply Subtype.ext
  erw [rzZStarFaceBoundaryEdge_end_value]
  apply congrArg Vertex.q
  change twoSelect
      (localFaceQ0 P S ⟨z, owner.1.1, corner.1.1⟩)
      (localFaceQ1 P S ⟨z, owner.1.1, corner.1.1⟩)
      corner.1.2 = Sum.inl ⟨z, edge⟩
  rw [localFaceQ_eq_corner]
  apply congrArg Sum.inl
  exact Sigma.ext
    (x := (⟨z, localCornerEdge P z S owner.1.1
      (corner.1.1, corner.1.2)⟩ :
        Sigma fun z : P.Z => ZDoubleCylinderEdge P z S))
    (y := ⟨z, edge⟩) rfl
    (heq_of_eq (corner.2.1.trans owner.2))

/-- The radial local-Q fallback retains the requested successor Q and takes
the X-Q root already present in the historical successor admissibility.  Its
ordered Z-boundary endpoint is therefore bit one. -/
private noncomputable def rzRadialLocalEdgeZBoundaryIncidentEdge
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (fixedZ : RZZ P S)
    (localEdge : Sigma fun z : P.Z => ZDoubleCylinderEdge P z S)
    (member : zStarBoundaryVertexMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) fixedZ
      (Vertex.q (Sum.inl localEdge)) = true) :
    {owned : ZStarBoundaryEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) fixedZ × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) fixedZ)
        (zBoundaryEdgeEnd (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) fixedZ)
        owned.1 owned.2 = ⟨Vertex.q (Sum.inl localEdge), member⟩} := by
  let successor := rzReplacementPresentation P A4.toTannerSquareAdmissible S
  let A' := rzReplacementAdmissible P A4 R S
  let q : successor.Q := Sum.inl localEdge
  let hqz := rzLocalEdgeZBoundary_qz P A4 S fixedZ localEdge member
  let root := A'.xqRoot q
  let radial : QStarEdge (transposePresentation successor) q :=
    ⟨root.1, root.2⟩
  let edge := qToZBoundaryEdge successor q fixedZ hqz radial
  refine ⟨⟨edge, 1⟩, ?_⟩
  rw [BDL26TannerLocalRegularity.edgeEndpoint_one]
  apply Subtype.ext
  rfl

/-- Constructor-complete endpoint routing for the five local-edge grouped
rows of the successor Z boundary.  The radial constructor is deliberately
kept separate so its #908 fallback consumes `A'.xqRoot` at endpoint one. -/
private noncomputable def rzLocalEdgeZBoundaryIncidentEdge
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (fixedZ : RZZ P S)
    (localEdge : Sigma fun z : P.Z => ZDoubleCylinderEdge P z S)
    (member : zStarBoundaryVertexMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) fixedZ
      (Vertex.q (Sum.inl localEdge)) = true) :
    {owned : ZStarBoundaryEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) fixedZ × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) fixedZ)
        (zBoundaryEdgeEnd (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) fixedZ)
        owned.1 owned.2 = ⟨Vertex.q (Sum.inl localEdge), member⟩} := by
  rcases fixedZ with ⟨z, fixedVertex⟩
  rcases localEdge with ⟨targetZ, edge⟩
  have hqz := rzLocalEdgeZBoundary_qz P A4 S ⟨z, fixedVertex⟩
    ⟨targetZ, edge⟩ member
  by_cases htarget : z = targetZ
  · subst targetZ
    rcases edge with endEdge | vertical
    · rcases endEdge with ⟨copy, subdivisionEdge⟩
      rcases subdivisionEdge with boundarySegment | interior
      · rcases boundarySegment with ⟨starEdge, segment⟩
        rcases starEdge.1 with radial | boundary
        · exact rzRadialLocalEdgeZBoundaryIncidentEdge P A4 R S
            ⟨z, fixedVertex⟩
            ⟨z, Sum.inl (copy, Sum.inl (starEdge, segment))⟩ member
        · exact rzLocalEdgeZBoundaryIncidentEdgeViaCell P A4 S z fixedVertex
            (Sum.inl (copy, Sum.inl (starEdge, segment))) member
      · rcases interior with horizontal | verticalEdge
        · exact rzLocalEdgeZBoundaryIncidentEdgeViaCell P A4 S z fixedVertex
            (Sum.inl (copy, Sum.inr (Sum.inl horizontal))) member
        · exact rzLocalEdgeZBoundaryIncidentEdgeViaCell P A4 S z fixedVertex
            (Sum.inl (copy, Sum.inr (Sum.inr verticalEdge))) member
    · exact rzLocalEdgeZBoundaryIncidentEdgeViaCell P A4 S z fixedVertex
        (Sum.inr vertical) member
  · exact False.elim (by
    change decide (Exists fun h : z = targetZ =>
      doubleCylinderEdgeVertexMatrix (transposePresentation P) targetZ S
        (h ▸ fixedVertex) edge = 1) = true at hqz
    obtain ⟨h, _⟩ := of_decide_eq_true hqz
    exact htarget h)

/-- Boundary membership of a successor Q-cylinder tag retains its concrete
Q-Z incidence with the fixed successor Z.  The witnessing boundary face is
eliminated only in this proposition-valued declaration. -/
private theorem rzQVertexZBoundary_qz
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (fixedZ : RZZ P S)
    (qVertex : Sigma fun q : P.Q =>
      QDoubleCylinderVertex (transposePresentation P) q S)
    (member : zStarBoundaryVertexMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) fixedZ
      (Vertex.q (Sum.inr qVertex)) = true) :
    (rzReplacementPresentation P A4.toTannerSquareAdmissible S).qz
      (Sum.inr qVertex) fixedZ = true := by
  let successor := rzReplacementPresentation P A4.toTannerSquareAdmissible S
  simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
  obtain ⟨face, hfaceZ, hfaceQ⟩ := member
  rcases hfaceQ with hfaceQ | hfaceQ
  · have h := successor.data.faceQ_qz face 0
    change successor.qz (successor.faceQ face 0)
      (successor.faceZ face) = true at h
    change Sum.inr qVertex = successor.faceQ face 0 at hfaceQ
    have hz : successor.faceZ face = fixedZ := by
      simpa [zStarFaceMember] using hfaceZ
    rw [← hfaceQ, hz] at h
    exact h
  · have h := successor.data.faceQ_qz face 1
    change successor.qz (successor.faceQ face 1)
      (successor.faceZ face) = true at h
    change Sum.inr qVertex = successor.faceQ face 1 at hfaceQ
    have hz : successor.faceZ face = fixedZ := by
      simpa [zStarFaceMember] using hfaceZ
    rw [← hfaceQ, hz] at h
    exact h

/-- Center and interior Q-cylinder vertices retain the requested vertex in a
concrete glue face.  Corner one is the requested successor Q, so its boundary
endpoint bit is one. -/
private noncomputable def rzQVertexZBoundaryIncidentEdgeViaGlue
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z)
    (fixedVertex : ZDoubleCylinderVertex P z S)
    (q : P.Q)
    (qVertex : QDoubleCylinderVertex (transposePresentation P) q S)
    (member : zStarBoundaryVertexMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) ⟨z, fixedVertex⟩
      (Vertex.q (Sum.inr ⟨q, qVertex⟩)) = true) :
    {owned : ZStarBoundaryEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) ⟨z, fixedVertex⟩ × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) ⟨z, fixedVertex⟩)
        (zBoundaryEdgeEnd (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) ⟨z, fixedVertex⟩)
        owned.1 owned.2 =
          ⟨Vertex.q (Sum.inr ⟨q, qVertex⟩), member⟩} := by
  classical
  let A := A4.toTannerSquareAdmissible
  let successor := rzReplacementPresentation P A S
  have hsuccessorQZ := rzQVertexZBoundary_qz P A4 S ⟨z, fixedVertex⟩
    ⟨q, qVertex⟩ member
  by_cases hqz : P.qz q z = true
  · have hmap : qToZDoubleCylinderVertex P A q z hqz S qVertex =
        fixedVertex := by
      change decide (Exists fun hqz' : P.qz q z = true =>
        qToZDoubleCylinderVertex P A q z hqz' S qVertex =
          fixedVertex) = true at hsuccessorQZ
      obtain ⟨hqz', hmap⟩ := of_decide_eq_true hsuccessorQZ
      simpa only [Subsingleton.elim hqz' hqz] using hmap
    obtain ⟨⟨qEdge, endpoint⟩, hendpoint⟩ :=
      qDoubleCylinderVertexIncidentEdge P A q S qVertex
    have hendpoint' : edgeEndpoint
          (qDoubleCylinderEdgeStart (transposePresentation P) q S)
          (qDoubleCylinderEdgeEnd (transposePresentation P) q S)
          qEdge endpoint = qVertex := by
      fin_cases endpoint <;> simpa [edgeEndpoint, twoSelect] using hendpoint
    let oldEdge : QZEdge P := ⟨(q, z), hqz⟩
    let glue : RZQZGlueFace P S := ⟨oldEdge, qEdge, endpoint⟩
    have hfaceZ : glueFaceZ P A S glue = ⟨z, fixedVertex⟩ := by
      apply Sigma.ext (x := glueFaceZ P A S glue)
        (y := ⟨z, fixedVertex⟩) rfl
      apply heq_of_eq
      simp only [glueFaceZ, glue, oldEdge]
      change qToZDoubleCylinderVertex P A q z hqz S
          (edgeEndpoint
            (qDoubleCylinderEdgeStart (transposePresentation P) q S)
            (qDoubleCylinderEdgeEnd (transposePresentation P) q S)
            qEdge endpoint) = fixedVertex
      rw [hendpoint']
      exact hmap
    let face : ZStarFace successor ⟨z, fixedVertex⟩ :=
      ⟨Sum.inr (Sum.inl glue), by
        simp only [zStarFaceMember, decide_eq_true_eq]
        exact hfaceZ⟩
    let boundaryEdge := rzZStarFaceBoundaryEdge successor
      ⟨z, fixedVertex⟩ face 1
    refine ⟨⟨boundaryEdge, 1⟩, ?_⟩
    rw [BDL26TannerLocalRegularity.edgeEndpoint_one]
    apply Subtype.ext
    erw [rzZStarFaceBoundaryEdge_end_value]
    apply congrArg Vertex.q
    change glueFaceQ1 P S glue = Sum.inr ⟨q, qVertex⟩
    simp only [glueFaceQ1, glue, oldEdge]
    apply congrArg Sum.inr
    exact Sigma.ext rfl (heq_of_eq hendpoint')
  · exact False.elim (by
      change decide (Exists fun hqz' : P.qz q z = true =>
        qToZDoubleCylinderVertex P A q z hqz' S qVertex =
          fixedVertex) = true at hsuccessorQZ
      obtain ⟨hqz', _⟩ := of_decide_eq_true hsuccessorQZ
      exact hqz hqz')

/-- A terminal Q-cylinder vertex keeps its stored old X-Q edge.  The old face
needed to certify the successor X-Q edge is recovered only inside the boundary
membership proposition; no face owner is exported as data. -/
private noncomputable def rzTerminalQVertexZBoundaryIncidentEdge
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z)
    (fixedVertex : ZDoubleCylinderVertex P z S)
    (q : P.Q) (copy : Two)
    (stored : QStarEdge (transposePresentation P) q)
    (member : zStarBoundaryVertexMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) ⟨z, fixedVertex⟩
      (Vertex.q (Sum.inr ⟨q,
        (copy, Sum.inl (Sum.inr stored))⟩)) = true) :
    {owned : ZStarBoundaryEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) ⟨z, fixedVertex⟩ × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) ⟨z, fixedVertex⟩)
        (zBoundaryEdgeEnd (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) ⟨z, fixedVertex⟩)
        owned.1 owned.2 = ⟨Vertex.q (Sum.inr ⟨q,
          (copy, Sum.inl (Sum.inr stored))⟩), member⟩} := by
  classical
  let A := A4.toTannerSquareAdmissible
  let successor := rzReplacementPresentation P A S
  let requestedQ : successor.Q :=
    Sum.inr ⟨q, (copy, Sum.inl (Sum.inr stored))⟩
  let hsuccessorQZ := rzQVertexZBoundary_qz P A4 S ⟨z, fixedVertex⟩
    ⟨q, (copy, Sum.inl (Sum.inr stored))⟩ member
  have hqz : P.qz q z = true := by
    by_contra hqz
    change decide (Exists fun hqz' : P.qz q z = true =>
      qToZDoubleCylinderVertex P A q z hqz' S
        (copy, Sum.inl (Sum.inr stored)) = fixedVertex) = true
      at hsuccessorQZ
    obtain ⟨hqz', _⟩ := of_decide_eq_true hsuccessorQZ
    exact hqz hqz'
  have hxq : successor.xq (Sum.inr (stored.1, copy)) requestedQ = true := by
    simp only [successor, rzReplacementPresentation, rzReplacementData,
      rzXQIncidence]
    apply decide_eq_true
    have hstoredXQ : P.xq stored.1 q = true := stored.2
    let shared : SharedQ P.data stored.1 z :=
      ⟨q, by simp [hstoredXQ, hqz]⟩
    obtain ⟨corner, hcorner⟩ := (P.perfectPairing stored.1 z).2 shared
    have hq : P.faceQ corner.1.1 corner.2 = q :=
      congrArg Subtype.val hcorner
    have hedge : HEq
        (⟨P.faceX corner.1.1,
          P.data.faceQ_xq corner.1.1 corner.2⟩ :
            QStarEdge (transposePresentation P)
              (P.faceQ corner.1.1 corner.2)) stored := by
      apply (Subtype.heq_iff_coe_eq (fun x => by rw [hq])).2
      exact corner.1.2.1
    have hSigmaEdge :
        (⟨P.faceQ corner.1.1 corner.2,
          (⟨P.faceX corner.1.1,
            P.data.faceQ_xq corner.1.1 corner.2⟩ :
              QStarEdge (transposePresentation P)
                (P.faceQ corner.1.1 corner.2))⟩ :
          Sigma fun q : P.Q => QStarEdge (transposePresentation P) q) =
        ⟨q, stored⟩ := Sigma.ext hq hedge
    let wrap : (Sigma fun q : P.Q =>
        QStarEdge (transposePresentation P) q) →
        (Sigma fun q : P.Q =>
          QDoubleCylinderVertex (transposePresentation P) q S) :=
      fun tagged => ⟨tagged.1,
        (copy, Sum.inl (Sum.inr tagged.2))⟩
    have hSigmaVertex := congrArg wrap hSigmaEdge
    have hvertex : HEq
        ((copy, Sum.inl (Sum.inr
          (⟨P.faceX corner.1.1,
            P.data.faceQ_xq corner.1.1 corner.2⟩ :
              QStarEdge (transposePresentation P)
                (P.faceQ corner.1.1 corner.2)))) :
          QDoubleCylinderVertex (transposePresentation P)
            (P.faceQ corner.1.1 corner.2) S)
        ((copy, Sum.inl (Sum.inr stored)) :
          QDoubleCylinderVertex (transposePresentation P) q S) := by
      exact (Sigma.mk.inj_iff.mp hSigmaVertex).2
    refine ⟨corner.1.1, corner.2, corner.1.2.1, ?_⟩
    change oldXFaceQ P S corner.2 (corner.1.1, copy) =
      Sum.inr ⟨q, (copy, Sum.inl (Sum.inr stored))⟩
    simp only [oldXFaceQ]
    apply congrArg Sum.inr
    apply Sigma.ext hq
    exact hvertex
  let storedEdge : QStarEdge (transposePresentation successor) requestedQ :=
    ⟨Sum.inr (stored.1, copy), hxq⟩
  let edge := qToZBoundaryEdge successor requestedQ ⟨z, fixedVertex⟩
    hsuccessorQZ storedEdge
  refine ⟨⟨edge, 1⟩, ?_⟩
  rw [BDL26TannerLocalRegularity.edgeEndpoint_one]
  apply Subtype.ext
  rfl

/-- Constructor-complete endpoint routing for the four Q-cylinder-vertex
grouped rows of the successor Z boundary: center, interior, and the two
terminal copies. -/
private noncomputable def rzQVertexZBoundaryIncidentEdge
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (fixedZ : RZZ P S)
    (qVertex : Sigma fun q : P.Q =>
      QDoubleCylinderVertex (transposePresentation P) q S)
    (member : zStarBoundaryVertexMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) fixedZ
      (Vertex.q (Sum.inr qVertex)) = true) :
    {owned : ZStarBoundaryEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) fixedZ × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) fixedZ)
        (zBoundaryEdgeEnd (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) fixedZ)
        owned.1 owned.2 = ⟨Vertex.q (Sum.inr qVertex), member⟩} := by
  rcases fixedZ with ⟨z, fixedVertex⟩
  rcases qVertex with ⟨q, copy, vertex⟩
  rcases vertex with original | interior
  · rcases original with center | stored
    · cases center
      exact rzQVertexZBoundaryIncidentEdgeViaGlue P A4 S z fixedVertex q
        (copy, Sum.inl (Sum.inl ())) member
    · exact rzTerminalQVertexZBoundaryIncidentEdge P A4 S z fixedVertex
        q copy stored member
  · exact rzQVertexZBoundaryIncidentEdgeViaGlue P A4 S z fixedVertex q
      (copy, Sum.inr interior) member

/-- A materialized local face whose selected corner is the fixed successor Z
supplies its own X-Q boundary edge at endpoint zero. -/
private noncomputable def rzLocalXZBoundaryIncidentEdgeAt
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z)
    (fixedVertex : ZDoubleCylinderVertex P z S)
    (cell : ZDoubleCylinderFace P z S)
    (member : zStarBoundaryVertexMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) ⟨z, fixedVertex⟩
      (Vertex.x (Sum.inl (Sum.inl ⟨z, cell⟩))) = true)
    (bits : Two × Two)
    (hcorner : localCornerVertex P z S cell bits = fixedVertex) :
    {owned : ZStarBoundaryEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) ⟨z, fixedVertex⟩ × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) ⟨z, fixedVertex⟩)
        (zBoundaryEdgeEnd (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) ⟨z, fixedVertex⟩)
        owned.1 owned.2 =
          ⟨Vertex.x (Sum.inl (Sum.inl ⟨z, cell⟩)), member⟩} := by
  let successor := rzReplacementPresentation P A4.toTannerSquareAdmissible S
  let face : ZStarFace successor ⟨z, fixedVertex⟩ :=
    ⟨Sum.inl ⟨z, cell, bits⟩, by
      simp only [zStarFaceMember, decide_eq_true_eq]
      change localFaceZ P S ⟨z, cell, bits⟩ = ⟨z, fixedVertex⟩
      rw [localFaceZ_eq_corner]
      exact Sigma.ext rfl (heq_of_eq hcorner)⟩
  let edge := rzZStarFaceBoundaryEdge successor ⟨z, fixedVertex⟩ face 0
  refine ⟨⟨edge, 0⟩, ?_⟩
  rw [BDL26TannerLocalRegularity.edgeEndpoint_zero]
  apply Subtype.ext
  erw [rzZStarFaceBoundaryEdge_start_value]

/-- Constructor-complete local-face X routing.  The two outer calls split
this common corner search into the end-copy and boundary-rectangle rows. -/
private noncomputable def rzLocalXZBoundaryIncidentEdge
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (fixedZ : RZZ P S)
    (localX : Sigma fun z : P.Z => ZDoubleCylinderFace P z S)
    (member : zStarBoundaryVertexMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) fixedZ
      (Vertex.x (Sum.inl (Sum.inl localX))) = true) :
    {owned : ZStarBoundaryEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) fixedZ × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) fixedZ)
        (zBoundaryEdgeEnd (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) fixedZ)
        owned.1 owned.2 = ⟨Vertex.x (Sum.inl (Sum.inl localX)), member⟩} := by
  rcases fixedZ with ⟨z, fixedVertex⟩
  rcases localX with ⟨targetZ, cell⟩
  by_cases htarget : targetZ = z
  · subst targetZ
    by_cases h00 : localCornerVertex P z S cell (0, 0) = fixedVertex
    · exact rzLocalXZBoundaryIncidentEdgeAt P A4 S z fixedVertex cell
        member (0, 0) h00
    · by_cases h01 : localCornerVertex P z S cell (0, 1) = fixedVertex
      · exact rzLocalXZBoundaryIncidentEdgeAt P A4 S z fixedVertex cell
          member (0, 1) h01
      · by_cases h10 : localCornerVertex P z S cell (1, 0) = fixedVertex
        · exact rzLocalXZBoundaryIncidentEdgeAt P A4 S z fixedVertex cell
            member (1, 0) h10
        · by_cases h11 : localCornerVertex P z S cell (1, 1) = fixedVertex
          · exact rzLocalXZBoundaryIncidentEdgeAt P A4 S z fixedVertex cell
              member (1, 1) h11
          · exact False.elim (by
              simp only [zStarBoundaryVertexMember, decide_eq_true_eq]
                at member
              obtain ⟨face, hfaceZ, hfaceX⟩ := member
              simp only [zStarFaceMember, decide_eq_true_eq] at hfaceZ
              rcases face with localFace | glueOrOld
              · rcases localFace with ⟨ownerZ, ownerCell, bits⟩
                change Sum.inl (Sum.inl (⟨z, cell⟩ :
                    Sigma fun z : P.Z => ZDoubleCylinderFace P z S)) =
                  Sum.inl (Sum.inl ⟨ownerZ, ownerCell⟩) at hfaceX
                have howner := Sum.inl.inj (Sum.inl.inj hfaceX)
                cases howner
                change localFaceZ P S ⟨z, cell, bits⟩ =
                  ⟨z, fixedVertex⟩ at hfaceZ
                rw [localFaceZ_eq_corner] at hfaceZ
                have hbits : localCornerVertex P z S cell bits =
                    fixedVertex :=
                  eq_of_heq (Sigma.mk.inj_iff.mp hfaceZ).2
                rcases bits with ⟨first, second⟩
                fin_cases first <;> fin_cases second
                · exact h00 hbits
                · exact h01 hbits
                · exact h10 hbits
                · exact h11 hbits
              · rcases glueOrOld with glue | old
                · change Sum.inl (Sum.inl _) = Sum.inl (Sum.inr _)
                    at hfaceX
                  cases Sum.inl.inj hfaceX
                · change Sum.inl (Sum.inl _) = Sum.inr _ at hfaceX
                  cases hfaceX)
  · exact False.elim (by
      simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
      obtain ⟨face, hfaceZ, hfaceX⟩ := member
      simp only [zStarFaceMember, decide_eq_true_eq] at hfaceZ
      rcases face with localFace | glueOrOld
      · rcases localFace with ⟨ownerZ, ownerCell, bits⟩
        change Sum.inl (Sum.inl (⟨targetZ, cell⟩ :
            Sigma fun z : P.Z => ZDoubleCylinderFace P z S)) =
          Sum.inl (Sum.inl ⟨ownerZ, ownerCell⟩) at hfaceX
        have howner := Sum.inl.inj (Sum.inl.inj hfaceX)
        have hz : targetZ = ownerZ := congrArg Sigma.fst howner
        have hownerZ : ownerZ = z := by
          change localFaceZ P S ⟨ownerZ, ownerCell, bits⟩ =
            ⟨z, fixedVertex⟩ at hfaceZ
          rcases ownerCell with copyFace | boundaryEdge
          · simpa [localFaceZ] using congrArg Sigma.fst hfaceZ
          · simpa [localFaceZ] using congrArg Sigma.fst hfaceZ
        exact htarget (hz.trans hownerZ)
      · rcases glueOrOld with glue | old
        · change Sum.inl (Sum.inl _) = Sum.inl (Sum.inr _) at hfaceX
          cases Sum.inl.inj hfaceX
        · change Sum.inl (Sum.inl _) = Sum.inr _ at hfaceX
          cases hfaceX)

/-- Split the end-copy and boundary-rectangle local X rows by their concrete
double-cylinder face constructors. -/
private noncomputable def rzLocalXZBoundaryIncidentEdgeByConstructor
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (fixedZ : RZZ P S)
    (localX : Sigma fun z : P.Z => ZDoubleCylinderFace P z S)
    (member : zStarBoundaryVertexMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) fixedZ
      (Vertex.x (Sum.inl (Sum.inl localX))) = true) :
    {owned : ZStarBoundaryEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) fixedZ × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) fixedZ)
        (zBoundaryEdgeEnd (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) fixedZ)
        owned.1 owned.2 =
          ⟨Vertex.x (Sum.inl (Sum.inl localX)), member⟩} := by
  rcases localX with ⟨z, cell⟩
  rcases cell with endCopy | rectangle
  · exact rzLocalXZBoundaryIncidentEdge P A4 S fixedZ
      ⟨z, Sum.inl endCopy⟩ member
  · exact rzLocalXZBoundaryIncidentEdge P A4 S fixedZ
      ⟨z, Sum.inr rectangle⟩ member

/-- A fixed-Z glue-X boundary member retains its old Q-Z incidence and one
of the two mapped q-edge endpoint equalities.  This inversion remains in
`Prop`; the producer below computes the endpoint from the explicit values. -/
private theorem rzQEdgeZBoundary_endpoint
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (z : P.Z)
    (fixedVertex : ZDoubleCylinderVertex P z S) (q : P.Q)
    (qEdge : QDoubleCylinderEdge (transposePresentation P) q S)
    (member : zStarBoundaryVertexMember (rzReplacementPresentation P A S)
      ⟨z, fixedVertex⟩
      (Vertex.x (Sum.inl (Sum.inr ⟨q, qEdge⟩))) = true) :
    ∃ hqz : P.qz q z = true,
      qToZDoubleCylinderVertex P A q z hqz S
          (edgeEndpoint
            (qDoubleCylinderEdgeStart (transposePresentation P) q S)
            (qDoubleCylinderEdgeEnd (transposePresentation P) q S)
            qEdge 0) = fixedVertex ∨
        qToZDoubleCylinderVertex P A q z hqz S
          (edgeEndpoint
            (qDoubleCylinderEdgeStart (transposePresentation P) q S)
            (qDoubleCylinderEdgeEnd (transposePresentation P) q S)
            qEdge 1) = fixedVertex := by
  classical
  simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
  obtain ⟨face, hfaceZ, hfaceX⟩ := member
  simp only [zStarFaceMember, decide_eq_true_eq] at hfaceZ
  rcases face with localFace | glueOrOld
  · change Sum.inl (Sum.inr (⟨q, qEdge⟩ : Sigma fun q : P.Q =>
        QDoubleCylinderEdge (transposePresentation P) q S)) =
      localFaceX P S localFace at hfaceX
    simp [localFaceX] at hfaceX
  · rcases glueOrOld with glue | old
    · rcases glue with ⟨⟨⟨q', z'⟩, hqz⟩, edge, endpoint⟩
      change Sum.inl (Sum.inr (⟨q, qEdge⟩ : Sigma fun q : P.Q =>
          QDoubleCylinderEdge (transposePresentation P) q S)) =
        Sum.inl (Sum.inr ⟨q', edge⟩) at hfaceX
      have hedge : (⟨q, qEdge⟩ : Sigma fun q : P.Q =>
          QDoubleCylinderEdge (transposePresentation P) q S) =
          ⟨q', edge⟩ := Sum.inr.inj (Sum.inl.inj hfaceX)
      cases hedge
      change glueFaceZ P A S ⟨⟨⟨q, z'⟩, hqz⟩, qEdge, endpoint⟩ =
        ⟨z, fixedVertex⟩ at hfaceZ
      have hz : z' = z := congrArg Sigma.fst hfaceZ
      subst z'
      have hvertex := eq_of_heq (Sigma.mk.inj_iff.mp hfaceZ).2
      refine ⟨hqz, ?_⟩
      fin_cases endpoint
      · left
        exact hvertex
      · right
        exact hvertex
    · change Sum.inl (Sum.inr (⟨q, qEdge⟩ : Sigma fun q : P.Q =>
          QDoubleCylinderEdge (transposePresentation P) q S)) =
        oldXFaceX P S old at hfaceX
      simp [oldXFaceX] at hfaceX

/-- Both q-edge X constructors retain the stored q-edge in a glue face at
corner zero; only the structural q-edge constructor distinguishes the two
frozen grouped rows. -/
private noncomputable def rzQEdgeXZBoundaryIncidentEdge
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z)
    (fixedVertex : ZDoubleCylinderVertex P z S) (q : P.Q)
    (qEdge : QDoubleCylinderEdge (transposePresentation P) q S)
    (member : zStarBoundaryVertexMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) ⟨z, fixedVertex⟩
      (Vertex.x (Sum.inl (Sum.inr ⟨q, qEdge⟩))) = true) :
    {owned : ZStarBoundaryEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) ⟨z, fixedVertex⟩ × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) ⟨z, fixedVertex⟩)
        (zBoundaryEdgeEnd (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) ⟨z, fixedVertex⟩)
        owned.1 owned.2 =
          ⟨Vertex.x (Sum.inl (Sum.inr ⟨q, qEdge⟩)), member⟩} := by
  classical
  let A := A4.toTannerSquareAdmissible
  let successor := rzReplacementPresentation P A S
  have hqz : P.qz q z = true := by
    by_contra hqz
    obtain ⟨hqz', _⟩ := rzQEdgeZBoundary_endpoint P A S z fixedVertex
      q qEdge member
    exact hqz hqz'
  have hcases :
      qToZDoubleCylinderVertex P A q z hqz S
          (edgeEndpoint
            (qDoubleCylinderEdgeStart (transposePresentation P) q S)
            (qDoubleCylinderEdgeEnd (transposePresentation P) q S)
            qEdge 0) = fixedVertex ∨
        qToZDoubleCylinderVertex P A q z hqz S
          (edgeEndpoint
            (qDoubleCylinderEdgeStart (transposePresentation P) q S)
            (qDoubleCylinderEdgeEnd (transposePresentation P) q S)
            qEdge 1) = fixedVertex := by
    obtain ⟨hqz', hcases⟩ := rzQEdgeZBoundary_endpoint P A S z fixedVertex
      q qEdge member
    simpa only [Subsingleton.elim hqz' hqz] using hcases
  let startZ := qToZDoubleCylinderVertex P A q z hqz S
    (edgeEndpoint
      (qDoubleCylinderEdgeStart (transposePresentation P) q S)
      (qDoubleCylinderEdgeEnd (transposePresentation P) q S) qEdge 0)
  let endZ := qToZDoubleCylinderVertex P A q z hqz S
    (edgeEndpoint
      (qDoubleCylinderEdgeStart (transposePresentation P) q S)
      (qDoubleCylinderEdgeEnd (transposePresentation P) q S) qEdge 1)
  let endpoint := rzOrientedBoundaryEndpoint
    (fun _ : Unit => startZ) (fun _ : Unit => endZ) () fixedVertex
  have hselected : edgeEndpoint (fun _ : Unit => startZ)
      (fun _ : Unit => endZ) () endpoint = fixedVertex :=
    rzOrientedBoundaryEndpoint_spec _ _ _ _
      (hcases.imp Eq.symm Eq.symm)
  have hmap : qToZDoubleCylinderVertex P A q z hqz S
      (edgeEndpoint
        (qDoubleCylinderEdgeStart (transposePresentation P) q S)
        (qDoubleCylinderEdgeEnd (transposePresentation P) q S)
        qEdge endpoint) = fixedVertex := by
    have hshape : edgeEndpoint (fun _ : Unit => startZ)
        (fun _ : Unit => endZ) () endpoint =
        qToZDoubleCylinderVertex P A q z hqz S
          (edgeEndpoint
            (qDoubleCylinderEdgeStart (transposePresentation P) q S)
            (qDoubleCylinderEdgeEnd (transposePresentation P) q S)
            qEdge endpoint) := by
      by_cases hzero : endpoint = 0
      · rw [hzero]
        rfl
      · have hone : endpoint = 1 := by
          apply Fin.ext
          have hlt := endpoint.2
          have hne : endpoint.1 ≠ 0 := by
            intro h
            apply hzero
            apply Fin.ext
            exact h
          omega
        rw [hone]
        rfl
    exact hshape.symm.trans hselected
  let oldEdge : QZEdge P := ⟨(q, z), hqz⟩
  let glue : RZQZGlueFace P S := ⟨oldEdge, qEdge, endpoint⟩
  have hfaceZ : glueFaceZ P A S glue = ⟨z, fixedVertex⟩ := by
    apply Sigma.ext (x := glueFaceZ P A S glue)
      (y := ⟨z, fixedVertex⟩) rfl
    exact heq_of_eq (by simpa [glueFaceZ, glue, oldEdge] using hmap)
  let face : ZStarFace successor ⟨z, fixedVertex⟩ :=
    ⟨Sum.inr (Sum.inl glue), by
      simp only [zStarFaceMember, decide_eq_true_eq]
      exact hfaceZ⟩
  let edge := rzZStarFaceBoundaryEdge successor ⟨z, fixedVertex⟩ face 0
  refine ⟨⟨edge, 0⟩, ?_⟩
  rw [BDL26TannerLocalRegularity.edgeEndpoint_zero]
  apply Subtype.ext
  erw [rzZStarFaceBoundaryEdge_start_value]

/-- Split the two q-edge X grouped rows without changing their common owner
semantics. -/
private noncomputable def rzQEdgeXZBoundaryIncidentEdgeByConstructor
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (fixedZ : RZZ P S)
    (qEdge : Sigma fun q : P.Q =>
      QDoubleCylinderEdge (transposePresentation P) q S)
    (member : zStarBoundaryVertexMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) fixedZ
      (Vertex.x (Sum.inl (Sum.inr qEdge))) = true) :
    {owned : ZStarBoundaryEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) fixedZ × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) fixedZ)
        (zBoundaryEdgeEnd (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) fixedZ)
        owned.1 owned.2 = ⟨Vertex.x (Sum.inl (Sum.inr qEdge)), member⟩} := by
  rcases fixedZ with ⟨z, fixedVertex⟩
  rcases qEdge with ⟨q, edge⟩
  rcases edge with segment | vertical
  · exact rzQEdgeXZBoundaryIncidentEdge P A4 S z fixedVertex q
      (Sum.inl segment) member
  · exact rzQEdgeXZBoundaryIncidentEdge P A4 S z fixedVertex q
      (Sum.inr vertical) member

/-- An old-X successor boundary witness can only come from an old-X face.
The constructor inversion remains entirely in `Prop`. -/
private theorem rzOldXZBoundary_face
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (fixedZ : RZZ P S) (oldX : P.X × Two)
    (member : zStarBoundaryVertexMember (rzReplacementPresentation P A S)
      fixedZ (Vertex.x (Sum.inr oldX)) = true) :
    ∃ face : P.Face,
      P.faceX face = oldX.1 ∧ oldXFaceZ P S (face, oldX.2) = fixedZ := by
  simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
  obtain ⟨candidate, hfaceZ, hfaceX⟩ := member
  simp only [zStarFaceMember, decide_eq_true_eq] at hfaceZ
  rcases candidate with localFace | glueOrOld
  · change Sum.inr oldX = localFaceX P S localFace at hfaceX
    simp [localFaceX] at hfaceX
  · rcases glueOrOld with glue | old
    · change Sum.inr oldX = glueFaceX P S glue at hfaceX
      simp [glueFaceX] at hfaceX
    · rcases old with ⟨face, copy⟩
      change oldXFaceZ P S (face, copy) = fixedZ at hfaceZ
      change Sum.inr oldX = Sum.inr (P.faceX face, copy) at hfaceX
      have htag : oldX = (P.faceX face, copy) := Sum.inr.inj hfaceX
      have hx : P.faceX face = oldX.1 :=
        (congrArg Prod.fst htag).symm
      have hcopy : copy = oldX.2 :=
        (congrArg Prod.snd htag).symm
      refine ⟨face, hx, ?_⟩
      simpa [hcopy] using hfaceZ

/-- The old X selected by a successor old-X tag is already a historical
Z-boundary vertex at the fixed old Z coordinate. -/
private theorem rzOldXZBoundary_historicalMember
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (z : P.Z) (fixedVertex : ZDoubleCylinderVertex P z S)
    (oldX : P.X × Two)
    (member : zStarBoundaryVertexMember (rzReplacementPresentation P A S)
      ⟨z, fixedVertex⟩ (Vertex.x (Sum.inr oldX)) = true) :
    zStarBoundaryVertexMember P z (Vertex.x oldX.1) = true := by
  obtain ⟨face, hx, hfaceZ⟩ := rzOldXZBoundary_face P A S
    ⟨z, fixedVertex⟩ oldX member
  simp only [zStarBoundaryVertexMember, decide_eq_true_eq]
  refine ⟨face, ?_, hx.symm⟩
  simp only [zStarFaceMember, decide_eq_true_eq]
  exact congrArg Sigma.fst hfaceZ

/-- The input V2 endpoint owner at the retained old X. -/
private noncomputable def rzOldXZBoundaryIncident
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (fixedVertex : ZDoubleCylinderVertex P z S)
    (oldX : P.X × Two)
    (member : zStarBoundaryVertexMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) ⟨z, fixedVertex⟩
      (Vertex.x (Sum.inr oldX)) = true) :=
  A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2.zBoundaryIncidentEdge
    z ⟨Vertex.x oldX.1,
      rzOldXZBoundary_historicalMember P A4.toTannerSquareAdmissible S
        z fixedVertex oldX member⟩

/-- Historical Z-boundary orientation places the retained old X at bit zero. -/
private theorem rzOldXZBoundaryIncident_bit
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (fixedVertex : ZDoubleCylinderVertex P z S)
    (oldX : P.X × Two)
    (member : zStarBoundaryVertexMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) ⟨z, fixedVertex⟩
      (Vertex.x (Sum.inr oldX)) = true) :
    (rzOldXZBoundaryIncident P A4 S z fixedVertex oldX member).1.2 = 0 := by
  generalize hincident : rzOldXZBoundaryIncident P A4 S z fixedVertex
    oldX member = incident
  rcases incident with ⟨⟨edge, endpoint⟩, hendpoint⟩
  fin_cases endpoint
  · rfl
  · change BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart P z) (zBoundaryEdgeEnd P z) edge 1 =
      ⟨Vertex.x oldX.1,
        rzOldXZBoundary_historicalMember P A4.toTannerSquareAdmissible S
          z fixedVertex oldX member⟩ at hendpoint
    rw [BDL26TannerLocalRegularity.edgeEndpoint_one] at hendpoint
    have hvalue := congrArg Subtype.val hendpoint
    rw [rzInputZBoundaryEdge_end_value] at hvalue
    cases hvalue

/-- The raw input X-Q edge selected at the old endpoint retains the requested
old X value. -/
private theorem rzOldXZBoundaryIncident_x
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (fixedVertex : ZDoubleCylinderVertex P z S)
    (oldX : P.X × Two)
    (member : zStarBoundaryVertexMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) ⟨z, fixedVertex⟩
      (Vertex.x (Sum.inr oldX)) = true) :
    (rzInputZBoundaryXQEdge P z
      (rzOldXZBoundaryIncident P A4 S z fixedVertex oldX member).1.1).1.1 =
      oldX.1 := by
  have hbit := rzOldXZBoundaryIncident_bit P A4 S z fixedVertex oldX member
  have hendpoint :=
    (rzOldXZBoundaryIncident P A4 S z fixedVertex oldX member).2
  rw [hbit, BDL26TannerLocalRegularity.edgeEndpoint_zero] at hendpoint
  have hvalue := congrArg Subtype.val hendpoint
  rw [rzInputZBoundaryEdge_start_value] at hvalue
  exact Vertex.x.inj hvalue

/-- Regularity identifies the V4 owner of the A2-selected old X-Q edge with
the old-X face already supplied by boundary membership.  No face is exported
from the proposition-valued membership witness. -/
private theorem rzOldXZBoundaryOwner_faceZ
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (z : P.Z) (fixedVertex : ZDoubleCylinderVertex P z S)
    (oldX : P.X × Two)
    (member : zStarBoundaryVertexMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) ⟨z, fixedVertex⟩
      (Vertex.x (Sum.inr oldX)) = true) :
    oldXFaceZ P S
      ((rzInputZBoundaryFaceOwner P A4 z
        (rzOldXZBoundaryIncident P A4 S z fixedVertex oldX member).1.1).1.1.1,
        oldX.2) = ⟨z, fixedVertex⟩ := by
  let incident := rzOldXZBoundaryIncident P A4 S z fixedVertex oldX member
  let edge := incident.1.1
  obtain ⟨face, hx, hfaceZ⟩ := rzOldXZBoundary_face P
    A4.toTannerSquareAdmissible S ⟨z, fixedVertex⟩ oldX member
  let candidate : ZStarFace P z := ⟨face, by
    simp only [zStarFaceMember, decide_eq_true_eq]
    exact congrArg Sigma.fst hfaceZ⟩
  have hinputX := rzOldXZBoundaryIncident_x P A4 S z fixedVertex oldX member
  have hcandidateX : P.faceX candidate.1 =
      (rzInputZBoundaryXQEdge P z edge).1.1 := by
    exact hx.trans hinputX.symm
  have howner := rzInputZBoundaryOwnerFace_eq P A4 R z edge candidate
    hcandidateX
  change oldXFaceZ P S
      ((rzInputZBoundaryFaceOwner P A4 z edge).1.1.1, oldX.2) =
    ⟨z, fixedVertex⟩
  rw [howner]
  exact hfaceZ

/-- The old-X grouped row consumes the input A2 Z-boundary endpoint owner to
retain its exact old Q data, and exposes the requested successor old X at the
fixed successor endpoint zero. -/
private noncomputable def rzOldXZBoundaryIncidentEdge
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (z : P.Z) (fixedVertex : ZDoubleCylinderVertex P z S)
    (oldX : P.X × Two)
    (member : zStarBoundaryVertexMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) ⟨z, fixedVertex⟩
      (Vertex.x (Sum.inr oldX)) = true) :
    {owned : ZStarBoundaryEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) ⟨z, fixedVertex⟩ × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) ⟨z, fixedVertex⟩)
        (zBoundaryEdgeEnd (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) ⟨z, fixedVertex⟩)
        owned.1 owned.2 = ⟨Vertex.x (Sum.inr oldX), member⟩} := by
  classical
  let A := A4.toTannerSquareAdmissible
  let successor := rzReplacementPresentation P A S
  let incident := rzOldXZBoundaryIncident P A4 S z fixedVertex oldX member
  let edge := incident.1.1
  let inputXQ := rzInputZBoundaryXQEdge P z edge
  let owner := rzInputZBoundaryFaceOwner P A4 z edge
  have hinputX : inputXQ.1.1 = oldX.1 := by
    simpa [incident, edge, inputXQ] using
      rzOldXZBoundaryIncident_x P A4 S z fixedVertex oldX member
  have hstored : P.xq oldX.1 inputXQ.1.2 = true := by
    simpa [hinputX] using inputXQ.2
  let stored : QStarEdge (transposePresentation P) inputXQ.1.2 :=
    ⟨oldX.1, hstored⟩
  let requestedVertex : Sigma fun q : P.Q =>
      QDoubleCylinderVertex (transposePresentation P) q S :=
    ⟨inputXQ.1.2, (oldX.2, Sum.inl (Sum.inr stored))⟩
  let requestedQ : successor.Q := Sum.inr requestedVertex
  have hownerVertex : oldXFaceQ P S owner.1.2
      (owner.1.1.1, oldX.2) = requestedQ := by
    let wrap : (Sigma fun q : P.Q =>
        QStarEdge (transposePresentation P) q) →
        (Sigma fun q : P.Q =>
          QDoubleCylinderVertex (transposePresentation P) q S) :=
      fun tagged => ⟨tagged.1,
        (oldX.2, Sum.inl (Sum.inr tagged.2))⟩
    have hownerX := rzInputZBoundaryOwner_faceX P A4 z edge
    have hownerQ := rzInputZBoundaryOwner_faceQ P A4 z edge
    have hedge : HEq
        (⟨P.faceX owner.1.1.1,
          P.data.faceQ_xq owner.1.1.1 owner.1.2⟩ :
          QStarEdge (transposePresentation P)
            (P.faceQ owner.1.1.1 owner.1.2)) stored := by
      apply (Subtype.heq_iff_coe_eq (fun x => by rw [hownerQ])).2
      exact hownerX.trans hinputX
    have hSigmaEdge :
        (⟨P.faceQ owner.1.1.1 owner.1.2,
          (⟨P.faceX owner.1.1.1,
            P.data.faceQ_xq owner.1.1.1 owner.1.2⟩ :
            QStarEdge (transposePresentation P)
              (P.faceQ owner.1.1.1 owner.1.2))⟩ :
          Sigma fun q : P.Q => QStarEdge (transposePresentation P) q) =
        ⟨inputXQ.1.2, stored⟩ := Sigma.ext hownerQ hedge
    change Sum.inr (wrap ⟨P.faceQ owner.1.1.1 owner.1.2,
      ⟨P.faceX owner.1.1.1,
        P.data.faceQ_xq owner.1.1.1 owner.1.2⟩⟩) =
      Sum.inr (wrap ⟨inputXQ.1.2, stored⟩)
    exact congrArg Sum.inr (congrArg wrap hSigmaEdge)
  have hxq : successor.xq (Sum.inr oldX) requestedQ = true := by
    simp only [successor, rzReplacementPresentation, rzReplacementData,
      rzXQIncidence]
    apply decide_eq_true
    exact ⟨owner.1.1.1, owner.1.2,
      (rzInputZBoundaryOwner_faceX P A4 z edge).trans hinputX,
      hownerVertex⟩
  have hownerZ : oldXFaceZ P S (owner.1.1.1, oldX.2) =
      ⟨z, fixedVertex⟩ := by
    simpa [incident, edge, owner] using
      rzOldXZBoundaryOwner_faceZ P A4 R S z fixedVertex oldX member
  have hrequestedMember : zStarBoundaryVertexMember successor
      ⟨z, fixedVertex⟩ (Vertex.q requestedQ) = true := by
    simp only [zStarBoundaryVertexMember, decide_eq_true_eq]
    refine ⟨Sum.inr (Sum.inr (owner.1.1.1, oldX.2)), ?_, ?_⟩
    · simp only [zStarFaceMember, decide_eq_true_eq]
      exact hownerZ
    · by_cases hzero : owner.1.2 = 0
      · left
        have hvertex := hownerVertex.symm
        rw [hzero] at hvertex
        exact hvertex
      · have hone : owner.1.2 = 1 := by
          apply Fin.ext
          have hlt := owner.1.2.2
          have hne : owner.1.2.1 ≠ 0 := by
            intro h
            apply hzero
            apply Fin.ext
            exact h
          omega
        right
        have hvertex := hownerVertex.symm
        rw [hone] at hvertex
        exact hvertex
  have hqz : successor.qz requestedQ ⟨z, fixedVertex⟩ = true := by
    exact rzQVertexZBoundary_qz P A4 S ⟨z, fixedVertex⟩
      requestedVertex hrequestedMember
  let radial : QStarEdge (transposePresentation successor) requestedQ :=
    ⟨Sum.inr oldX, hxq⟩
  let successorEdge := qToZBoundaryEdge successor requestedQ
    ⟨z, fixedVertex⟩ hqz radial
  refine ⟨⟨successorEdge, 0⟩, ?_⟩
  rw [BDL26TannerLocalRegularity.edgeEndpoint_zero]
  apply Subtype.ext
  rfl

/-- The total successor Z-boundary endpoint owner.  Structural dispatch over
the successor vertex constructors combines the 14 frozen RZ-Z grouped rows
without changing any producer's requested-vertex semantics. -/
private noncomputable def rzReplacementZBoundaryIncidentEdge
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (fixedZ : (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S).Z)
    (vertex : ZStarBoundaryVertex (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) fixedZ) :
    {owned : ZStarBoundaryEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) fixedZ × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) fixedZ)
        (zBoundaryEdgeEnd (rzReplacementPresentation P
          A4.toTannerSquareAdmissible S) fixedZ)
        owned.1 owned.2 = vertex} := by
  rcases fixedZ with ⟨z, fixedVertex⟩
  rcases vertex with ⟨value, member⟩
  rcases value with successorX | successorQ | impossible
  · rcases successorX with localOrGlue | oldX
    · rcases localOrGlue with localX | qEdge
      · exact rzLocalXZBoundaryIncidentEdgeByConstructor P A4 S
          ⟨z, fixedVertex⟩ localX member
      · exact rzQEdgeXZBoundaryIncidentEdgeByConstructor P A4 S
          ⟨z, fixedVertex⟩ qEdge member
    · exact rzOldXZBoundaryIncidentEdge P A4 R S z fixedVertex oldX member
  · rcases successorQ with localEdge | qVertex
    · exact rzLocalEdgeZBoundaryIncidentEdge P A4 R S
        ⟨z, fixedVertex⟩ localEdge member
    · exact rzQVertexZBoundaryIncidentEdge P A4 S
        ⟨z, fixedVertex⟩ qVertex member
  · exact False.elim (by
      simp [zStarBoundaryVertexMember] at member)

/-- The endpoint-owned successor admissibility package.  Its historical
six-field projection is exactly `rzReplacementAdmissible`; the two new V2
fields are the constructor-complete X- and Z-boundary dispatchers above.
This declaration makes no successor V3 or V4 owner claim. -/
noncomputable def rzReplacementAdmissibleV2
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) :
    TannerSquareAdmissibleV2
      (rzReplacementPresentation P A4.toTannerSquareAdmissible S) where
  toTannerSquareAdmissible := rzReplacementAdmissible P A4 R S
  xBoundaryIncidentEdge := rzReplacementXBoundaryIncidentEdge P A4 S
  zBoundaryIncidentEdge := rzReplacementZBoundaryIncidentEdge P A4 R S

/-! ## Successor V3 radial face owners -/

/-- A fixed double-cylinder face has a structural inverse for each of its
four cellular boundary slots.  The incidence existential is used only to
close the impossible final branch in `Prop`; the returned slot is selected by
the four explicit constructors. -/
private noncomputable def doubleCylinderFaceBoundarySlotOwner
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : DoubleCylinderFace P x S) (edge : DoubleCylinderEdge P x S)
    (hmatrix : doubleCylinderFaceEdgeMatrix P x S edge face = 1) :
    {slot : Two × Two //
      doubleCylinderFaceBoundaryEdge P x S face slot = edge} := by
  classical
  by_cases h00 : doubleCylinderFaceBoundaryEdge P x S face (0, 0) = edge
  · exact ⟨(0, 0), h00⟩
  · by_cases h01 : doubleCylinderFaceBoundaryEdge P x S face (0, 1) = edge
    · exact ⟨(0, 1), h01⟩
    · by_cases h10 : doubleCylinderFaceBoundaryEdge P x S face (1, 0) = edge
      · exact ⟨(1, 0), h10⟩
      · by_cases h11 : doubleCylinderFaceBoundaryEdge P x S face (1, 1) = edge
        · exact ⟨(1, 1), h11⟩
        · exfalso
          have hslot : ∃ slot : Two × Two,
              doubleCylinderFaceBoundaryEdge P x S face slot = edge := by
            rcases face with copyFace | rectangle
            · rcases copyFace with ⟨copy, smallFace⟩
              rcases edge with endEdge | vertical
              · rcases endEdge with ⟨edgeCopy, subdivisionEdge⟩
                have hcopy : edgeCopy = copy := by
                  by_contra hne
                  simp [doubleCylinderFaceEdgeMatrix, hne] at hmatrix
                subst edgeCopy
                have hsubdivision : subdivisionFaceEdgeMatrix P x S
                    subdivisionEdge smallFace = 1 := by
                  simpa [doubleCylinderFaceEdgeMatrix] using hmatrix
                obtain ⟨slot, hslot⟩ :=
                  (subdivisionFaceEdgeMatrix_eq_one_iff P x S
                    subdivisionEdge smallFace).1 hsubdivision
                exact ⟨slot, congrArg (fun value => Sum.inl (copy, value)) hslot⟩
              · simp [doubleCylinderFaceEdgeMatrix] at hmatrix
            · exact (doubleCylinderFaceEdgeMatrix_rectangle_eq_one_iff
                P x S edge rectangle).1 hmatrix
          obtain ⟨⟨first, second⟩, hslot⟩ := hslot
          fin_cases first <;> fin_cases second
          · exact h00 hslot
          · exact h01 hslot
          · exact h10 hslot
          · exact h11 hslot

/-- An X-Q edge in a closed X-star retains the requested X endpoint. -/
private theorem xStarXQEdge_first_eq
    (P : TannerSquarePresentation) (x : P.X) (edge : XQEdge P)
    (member : xStarEdgeMember P x (Sum.inl edge) = true) :
    edge.1.1 = x := by
  have hstart := (xStarEdgeStart P x ⟨Sum.inl edge, member⟩).2
  simpa [xStarVertexMember] using of_decide_eq_true hstart

/-- Frozen RZ-X radial row X/0: a local Q edge retains its concrete local
cell as owner, with the radial corner reconstructed from its structural face
slot. -/
private noncomputable def rzLocalXRadialFaceOwner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (localX : Sigma fun z : P.Z => ZDoubleCylinderFace P z S)
    (localEdge : Sigma fun z : P.Z => ZDoubleCylinderEdge P z S)
    (incidence : (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S).xq
        (Sum.inl (Sum.inl localX)) (Sum.inl localEdge) = true)
    (member : xStarEdgeMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inl localX))
        (Sum.inl (⟨(Sum.inl (Sum.inl localX), Sum.inl localEdge),
          incidence⟩ : XQEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S))) = true) :
    {owner : XStarFace (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inl localX)) × Two //
      xStarFaceXQEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inl localX))
        owner.1 owner.2 =
          ⟨Sum.inl (⟨(Sum.inl (Sum.inl localX), Sum.inl localEdge),
            incidence⟩ : XQEdge (rzReplacementPresentation P
              A4.toTannerSquareAdmissible S)), member⟩} := by
  classical
  let A := A4.toTannerSquareAdmissible
  rcases localX with ⟨z, cell⟩
  rcases localEdge with ⟨edgeZ, edge⟩
  change decide (Exists fun h : edgeZ = z =>
    doubleCylinderFaceEdgeMatrix (transposePresentation P) z S
      (h ▸ edge) cell = 1) = true at incidence
  have hZ : edgeZ = z := by
    obtain ⟨hZ, _⟩ := of_decide_eq_true incidence
    exact hZ
  subst edgeZ
  have hmatrix' : doubleCylinderFaceEdgeMatrix
      (transposePresentation P) z S edge cell = 1 := by
    obtain ⟨hZ', hmatrix⟩ := of_decide_eq_true incidence
    simpa only [Subsingleton.elim hZ' rfl] using hmatrix
  let slot := doubleCylinderFaceBoundarySlotOwner
    (transposePresentation P) z S cell edge hmatrix'
  let corner := localCornerAtBoundaryEndpoint P z S cell slot.1 0
  let face : XStarFace (rzReplacementPresentation P A S)
      (Sum.inl (Sum.inl ⟨z, cell⟩)) :=
    ⟨Sum.inl ⟨z, cell, corner.1.1⟩, by
      simp only [xStarFaceMember, decide_eq_true_eq]
      rfl⟩
  refine ⟨⟨face, corner.1.2⟩, ?_⟩
  apply Subtype.ext
  apply congrArg Sum.inl
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change twoSelect
        (localFaceQ0 P S ⟨z, cell, corner.1.1⟩)
        (localFaceQ1 P S ⟨z, cell, corner.1.1⟩) corner.1.2 =
      Sum.inl ⟨z, edge⟩
    rw [localFaceQ_eq_corner]
    apply congrArg Sum.inl
    refine Sigma.ext
      (x := (⟨z, localCornerEdge P z S cell
        (corner.1.1, corner.1.2)⟩ :
          Sigma fun z : P.Z => ZDoubleCylinderEdge P z S))
      (y := ⟨z, edge⟩) rfl ?_
    exact heq_of_eq (corner.2.1.trans slot.2)

/-- Frozen RZ-X radial row X/1: a glue face at endpoint zero owns the local
Q image of its transposed Q-cylinder edge. -/
private noncomputable def rzGlueXLocalRadialFaceOwner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale)
    (qEdge : Sigma fun q : P.Q =>
      QDoubleCylinderEdge (transposePresentation P) q S)
    (localEdge : Sigma fun z : P.Z => ZDoubleCylinderEdge P z S)
    (incidence : (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S).xq
        (Sum.inl (Sum.inr qEdge)) (Sum.inl localEdge) = true)
    (member : xStarEdgeMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inr qEdge))
        (Sum.inl (⟨(Sum.inl (Sum.inr qEdge), Sum.inl localEdge), incidence⟩ :
          XQEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S))) = true) :
    {owner : XStarFace (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inr qEdge)) × Two //
      xStarFaceXQEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inr qEdge))
        owner.1 owner.2 =
          ⟨Sum.inl (⟨(Sum.inl (Sum.inr qEdge), Sum.inl localEdge), incidence⟩ :
            XQEdge (rzReplacementPresentation P
              A4.toTannerSquareAdmissible S)), member⟩} := by
  classical
  let A := A4.toTannerSquareAdmissible
  change decide (Exists fun hqz : P.qz qEdge.1 localEdge.1 = true =>
    qToZDoubleCylinderEdge P A qEdge.1 localEdge.1 hqz S qEdge.2 =
      localEdge.2) = true at incidence
  have hqz : P.qz qEdge.1 localEdge.1 = true := by
    obtain ⟨hqz, _⟩ := of_decide_eq_true incidence
    exact hqz
  have hedge : qToZDoubleCylinderEdge P A qEdge.1 localEdge.1 hqz S qEdge.2 =
      localEdge.2 := by
    obtain ⟨hqz', hedge⟩ := of_decide_eq_true incidence
    simpa only [Subsingleton.elim hqz' hqz] using hedge
  let face := rzGlueXStarFace P A S qEdge localEdge.1 hqz 0
  refine ⟨⟨face, 0⟩, ?_⟩
  apply Subtype.ext
  apply congrArg Sum.inl
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change glueFaceQ0 P A S ⟨⟨(qEdge.1, localEdge.1), hqz⟩,
        qEdge.2, 0⟩ = Sum.inl localEdge
    apply congrArg Sum.inl
    exact Sigma.ext rfl (heq_of_eq hedge)

/-- Frozen RZ-X radial row X/2: a glue face at the requested structural
Q-cylinder endpoint owns the requested qVertex at radial corner one. -/
private noncomputable def rzGlueXQVertexRadialFaceOwner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale)
    (qEdge : Sigma fun q : P.Q =>
      QDoubleCylinderEdge (transposePresentation P) q S)
    (qVertex : Sigma fun q : P.Q =>
      QDoubleCylinderVertex (transposePresentation P) q S)
    (incidence : (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S).xq
        (Sum.inl (Sum.inr qEdge)) (Sum.inr qVertex) = true)
    (member : xStarEdgeMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inr qEdge))
        (Sum.inl (⟨(Sum.inl (Sum.inr qEdge), Sum.inr qVertex), incidence⟩ :
          XQEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S))) = true) :
    {owner : XStarFace (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inr qEdge)) × Two //
      xStarFaceXQEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inr qEdge))
        owner.1 owner.2 =
          ⟨Sum.inl (⟨(Sum.inl (Sum.inr qEdge), Sum.inr qVertex), incidence⟩ :
            XQEdge (rzReplacementPresentation P
              A4.toTannerSquareAdmissible S)), member⟩} := by
  let A := A4.toTannerSquareAdmissible
  rcases qVertex with ⟨qVertexQ, qVertexValue⟩
  change decide (Exists fun hq : qVertexQ = qEdge.1 =>
    hq ▸ qVertexValue = qDoubleCylinderEdgeStart
        (transposePresentation P) qEdge.1 S qEdge.2 ∨
      hq ▸ qVertexValue = qDoubleCylinderEdgeEnd
        (transposePresentation P) qEdge.1 S qEdge.2) = true at incidence
  have hq : qVertexQ = qEdge.1 := by
    obtain ⟨hq, _⟩ := of_decide_eq_true incidence
    exact hq
  subst qVertexQ
  have hendpoint : qVertexValue = qDoubleCylinderEdgeStart
        (transposePresentation P) qEdge.1 S qEdge.2 ∨
      qVertexValue = qDoubleCylinderEdgeEnd
        (transposePresentation P) qEdge.1 S qEdge.2 := by
    obtain ⟨hq', hendpoint⟩ := of_decide_eq_true incidence
    simpa only [Subsingleton.elim hq' rfl] using hendpoint
  let selected : Sigma fun q : P.Q =>
      QDoubleCylinderVertex (transposePresentation P) q S :=
    ⟨qEdge.1, qVertexValue⟩
  let endpoint := rzOrientedBoundaryEndpoint
    (fun _ : Unit => ⟨qEdge.1, qDoubleCylinderEdgeStart
      (transposePresentation P) qEdge.1 S qEdge.2⟩)
    (fun _ : Unit => ⟨qEdge.1, qDoubleCylinderEdgeEnd
      (transposePresentation P) qEdge.1 S qEdge.2⟩) () selected
  have hselected : (⟨qEdge.1, edgeEndpoint
      (qDoubleCylinderEdgeStart (transposePresentation P) qEdge.1 S)
      (qDoubleCylinderEdgeEnd (transposePresentation P) qEdge.1 S)
      qEdge.2 endpoint⟩ : Sigma fun q : P.Q =>
        QDoubleCylinderVertex (transposePresentation P) q S) = selected := by
    have hspec := rzOrientedBoundaryEndpoint_spec
      (fun _ : Unit => ⟨qEdge.1, qDoubleCylinderEdgeStart
        (transposePresentation P) qEdge.1 S qEdge.2⟩)
      (fun _ : Unit => ⟨qEdge.1, qDoubleCylinderEdgeEnd
        (transposePresentation P) qEdge.1 S qEdge.2⟩) () selected
      (by
        rcases hendpoint with hstart | hend
        · left; exact Sigma.ext rfl (heq_of_eq hstart)
        · right; exact Sigma.ext rfl (heq_of_eq hend))
    have hshape : edgeEndpoint
        (fun _ : Unit => ⟨qEdge.1, qDoubleCylinderEdgeStart
          (transposePresentation P) qEdge.1 S qEdge.2⟩)
        (fun _ : Unit => ⟨qEdge.1, qDoubleCylinderEdgeEnd
          (transposePresentation P) qEdge.1 S qEdge.2⟩) () endpoint =
      (⟨qEdge.1, edgeEndpoint
        (qDoubleCylinderEdgeStart (transposePresentation P) qEdge.1 S)
        (qDoubleCylinderEdgeEnd (transposePresentation P) qEdge.1 S)
        qEdge.2 endpoint⟩ : Sigma fun q : P.Q =>
          QDoubleCylinderVertex (transposePresentation P) q S) := by
      by_cases hzero : endpoint = 0
      · rw [hzero]
        rfl
      · have hone : endpoint = 1 := by
          apply Fin.ext
          have hlt := endpoint.2
          have hne : endpoint.1 ≠ 0 := by
            intro h
            apply hzero
            apply Fin.ext
            exact h
          omega
        rw [hone]
        rfl
    exact hshape.symm.trans hspec
  let root := A.qzRoot qEdge.1
  let face := rzGlueXStarFace P A S qEdge root.1 root.2 endpoint
  refine ⟨⟨face, 1⟩, ?_⟩
  apply Subtype.ext
  apply congrArg Sum.inl
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change glueFaceQ1 P S ⟨⟨(qEdge.1, root.1), root.2⟩,
        qEdge.2, endpoint⟩ = Sum.inr ⟨qEdge.1, qVertexValue⟩
    apply congrArg Sum.inr
    exact hselected

/-- Frozen RZ-X radial row X/3: a terminal old-X qVertex is owned by the
copy of the input V3 radial face.  The successor incidence proof is used only
to establish its terminal shape; the face itself comes exclusively from the
input V3 owner. -/
private noncomputable def rzOldXRadialFaceOwner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (oldX : P.X × Two)
    (qVertex : Sigma fun q : P.Q =>
      QDoubleCylinderVertex (transposePresentation P) q S)
    (incidence : (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S).xq
        (Sum.inr oldX) (Sum.inr qVertex) = true)
    (member : xStarEdgeMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) (Sum.inr oldX)
        (Sum.inl (⟨(Sum.inr oldX, Sum.inr qVertex), incidence⟩ :
          XQEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S))) = true) :
    {owner : XStarFace (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) (Sum.inr oldX) × Two //
      xStarFaceXQEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) (Sum.inr oldX)
        owner.1 owner.2 =
          ⟨Sum.inl (⟨(Sum.inr oldX, Sum.inr qVertex), incidence⟩ :
            XQEdge (rzReplacementPresentation P
              A4.toTannerSquareAdmissible S)), member⟩} := by
  classical
  let A := A4.toTannerSquareAdmissible
  rcases qVertex with ⟨q, copy, original | interior⟩
  · rcases original with central | radial
    · have himpossible : False := by
        change decide (Exists fun face : P.Face => Exists fun corner : Two =>
          P.faceX face = oldX.1 ∧
            oldXFaceQ P S corner (face, oldX.2) =
              Sum.inr ⟨q, (copy, Sum.inl (Sum.inl central))⟩) = true at incidence
        obtain ⟨face, corner, hfaceX, hq⟩ := of_decide_eq_true incidence
        change oldXFaceQ P S corner (face, oldX.2) =
          Sum.inr ⟨q, (copy, Sum.inl (Sum.inl central))⟩ at hq
        simp [oldXFaceQ] at hq
        cases hq.1
        have hvertex := eq_of_heq hq.2
        cases hvertex
      exact False.elim himpossible
    · change decide (Exists fun face : P.Face => Exists fun corner : Two =>
        P.faceX face = oldX.1 ∧
          oldXFaceQ P S corner (face, oldX.2) =
            Sum.inr ⟨q, (copy, Sum.inl (Sum.inr radial))⟩) = true at incidence
      have hcopy : copy = oldX.2 := by
        obtain ⟨face, corner, _, hq⟩ := of_decide_eq_true incidence
        have hcopy' := congrArg (fun value : RZQ P S =>
          match value with
          | Sum.inl _ => (0 : Two)
          | Sum.inr terminal => terminal.2.1) hq
        simpa [oldXFaceQ] using hcopy'.symm
      subst copy
      let inputEdge : XQEdge P := ⟨(radial.1, q), radial.2⟩
      have inputMember : xStarEdgeMember P oldX.1
          (Sum.inl inputEdge) = true := by
        obtain ⟨face, corner, hfaceX, hq⟩ :=
          of_decide_eq_true incidence
        change oldXFaceQ P S corner (face, oldX.2) =
          Sum.inr ⟨q, (oldX.2, Sum.inl (Sum.inr radial))⟩ at hq
        simp [oldXFaceQ] at hq
        cases hq.1
        have hvertex := eq_of_heq hq.2
        cases hvertex
        let inputFace : XStarFace P oldX.1 :=
          ⟨face, by simpa [xStarFaceMember] using hfaceX⟩
        simpa [xStarFaceXQEdge, inputFace, inputEdge, faceXQEdge, hfaceX] using
          (xStarFaceXQEdge P oldX.1 inputFace corner).2
      let inputOwner :=
        A4.toTannerSquareAdmissibleV3.xRadialFaceOwner
          oldX.1 inputEdge inputMember
      have hfaceX : P.faceX inputOwner.1.1.1 = oldX.1 := by
        simpa [xStarFaceMember] using inputOwner.1.1.2
      let face : XStarFace (rzReplacementPresentation P A S)
          (Sum.inr oldX) :=
        ⟨Sum.inr (Sum.inr (inputOwner.1.1.1, oldX.2)), by
          simp only [xStarFaceMember, decide_eq_true_eq]
          change Sum.inr (P.faceX inputOwner.1.1.1, oldX.2) = Sum.inr oldX
          exact congrArg Sum.inr (Prod.ext hfaceX rfl)⟩
      refine ⟨⟨face, inputOwner.1.2⟩, ?_⟩
      apply Subtype.ext
      apply congrArg Sum.inl
      apply Subtype.ext
      apply Prod.ext
      · change Sum.inr (P.faceX inputOwner.1.1.1, oldX.2) = Sum.inr oldX
        exact congrArg Sum.inr (Prod.ext hfaceX rfl)
      · let wrap : XQEdge P →
            Sigma fun q : P.Q =>
              QDoubleCylinderVertex (transposePresentation P) q S :=
          fun edge => ⟨edge.1.2,
            (oldX.2, Sum.inl (Sum.inr
              (⟨edge.1.1, edge.2⟩ :
                QStarEdge (transposePresentation P) edge.1.2)))⟩
        have hedge : faceXQEdge P inputOwner.1.1.1 inputOwner.1.2 =
            inputEdge := by
          have hraw := congrArg Subtype.val inputOwner.2
          exact Sum.inl.inj hraw
        change oldXFaceQ P S inputOwner.1.2
            (inputOwner.1.1.1, oldX.2) =
          Sum.inr ⟨q, (oldX.2, Sum.inl (Sum.inr radial))⟩
        apply congrArg Sum.inr
        simpa [wrap, inputEdge, faceXQEdge, oldXFaceQ] using
          congrArg wrap hedge
  · have himpossible : False := by
      change decide (Exists fun face : P.Face => Exists fun corner : Two =>
        P.faceX face = oldX.1 ∧
          oldXFaceQ P S corner (face, oldX.2) =
            Sum.inr ⟨q, (copy, Sum.inr interior)⟩) = true at incidence
      obtain ⟨face, corner, hfaceX, hq⟩ := of_decide_eq_true incidence
      change oldXFaceQ P S corner (face, oldX.2) =
        Sum.inr ⟨q, (copy, Sum.inr interior)⟩ at hq
      simp [oldXFaceQ] at hq
      cases hq.1
      have hvertex := eq_of_heq hq.2
      cases hvertex
    exact False.elim himpossible

/-- Total successor X radial owner dispatcher.  Its four structural branches
are exactly the frozen #908 rows X/0--X/3. -/
private noncomputable def rzReplacementXRadialFaceOwner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale)
    (x : (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S).X)
    (edge : XQEdge (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S))
    (member : xStarEdgeMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) x (Sum.inl edge) = true) :
    {owner : XStarFace (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) x × Two //
      xStarFaceXQEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) x owner.1 owner.2 =
          ⟨Sum.inl edge, member⟩} := by
  rcases edge with ⟨⟨edgeX, edgeQ⟩, incidence⟩
  have hx : edgeX = x := xStarXQEdge_first_eq
    (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
    x ⟨(edgeX, edgeQ), incidence⟩ member
  subst edgeX
  rcases x with localOrGlue | oldX
  · rcases localOrGlue with localX | qEdge
    · rcases edgeQ with localEdge | qVertex
      · exact rzLocalXRadialFaceOwner P A4 S localX localEdge
          incidence member
      · change false = true at incidence
        simp at incidence
    · rcases edgeQ with localEdge | qVertex
      · exact rzGlueXLocalRadialFaceOwner P A4 S qEdge localEdge
          incidence member
      · exact rzGlueXQVertexRadialFaceOwner P A4 S qEdge qVertex
          incidence member
  · rcases edgeQ with localEdge | qVertex
    · change false = true at incidence
      simp at incidence
    · exact rzOldXRadialFaceOwner P A4 S oldX qVertex incidence member

/-- A Q-Z edge in a closed Z-star retains the requested Z endpoint. -/
private theorem zStarQZEdge_second_eq
    (P : TannerSquarePresentation) (z : P.Z) (edge : QZEdge P)
    (member : zStarEdgeMember P z (Sum.inr edge) = true) :
    edge.1.2 = z := by
  let transposed : XQEdge (transposePresentation P) :=
    (transposeXQEdgeEquiv P).symm edge
  let starEdge : ZStarEdge P z := ⟨Sum.inr edge, member⟩
  have hmember : xStarEdgeMember (transposePresentation P) z
      (Sum.inl transposed) = true := by
    have hmapped := ((transposeXStarEdgeEquiv P z).symm starEdge).2
    simpa [transposed, starEdge, transposeXStarEdgeEquiv,
      transposeEdgeEquiv] using hmapped
  have hfirst := xStarXQEdge_first_eq
    (transposePresentation P) z transposed hmember
  exact hfirst

/-- Frozen RZ-Z radial row Z/0: a local Q edge and its requested local Z
endpoint retain the concrete local cell supplied by the existing cellular
owner chain.  Only the old-QZ radial subdivision subcase consumes the input
Z-radial owner, through `doubleCylinderEdgeFaceSlotOwner`. -/
private noncomputable def rzLocalQZRadialFaceOwner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale)
    (localEdge : Sigma fun z : P.Z => ZDoubleCylinderEdge P z S)
    (fixedZ : RZZ P S)
    (incidence : (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S).qz (Sum.inl localEdge) fixedZ = true)
    (member : zStarEdgeMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) fixedZ
        (Sum.inr (⟨(Sum.inl localEdge, fixedZ), incidence⟩ :
          QZEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S))) = true) :
    {owner : ZStarFace (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) fixedZ × Two //
      zStarFaceQZEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) fixedZ owner.1 owner.2 =
          ⟨Sum.inr (⟨(Sum.inl localEdge, fixedZ), incidence⟩ :
            QZEdge (rzReplacementPresentation P
              A4.toTannerSquareAdmissible S)), member⟩} := by
  classical
  let A := A4.toTannerSquareAdmissible
  let successor := rzReplacementPresentation P A S
  rcases localEdge with ⟨edgeZ, edge⟩
  rcases fixedZ with ⟨fixedBaseZ, fixedVertex⟩
  change decide (Exists fun h : fixedBaseZ = edgeZ =>
    doubleCylinderEdgeVertexMatrix (transposePresentation P) edgeZ S
      (h ▸ fixedVertex) edge = 1) = true at incidence
  have hZ : fixedBaseZ = edgeZ := by
    obtain ⟨hZ, _⟩ := of_decide_eq_true incidence
    exact hZ
  subst fixedBaseZ
  have hmatrix : doubleCylinderEdgeVertexMatrix
      (transposePresentation P) edgeZ S fixedVertex edge = 1 := by
    obtain ⟨hZ', hmatrix⟩ := of_decide_eq_true incidence
    simpa only [Subsingleton.elim hZ' rfl] using hmatrix
  have hendpoints : fixedVertex =
        tannerDoubleCylinderEdgeStart (transposePresentation P) edgeZ S edge ∨
      fixedVertex =
        tannerDoubleCylinderEdgeEnd (transposePresentation P) edgeZ S edge :=
    (doubleCylinderEdgeVertexMatrix_eq_one_iff
      (transposePresentation P) edgeZ S fixedVertex edge).1 hmatrix
  let endpoint := rzOrientedBoundaryEndpoint
    (tannerDoubleCylinderEdgeStart (transposePresentation P) edgeZ S)
    (tannerDoubleCylinderEdgeEnd (transposePresentation P) edgeZ S)
    edge fixedVertex
  let cellOwner := doubleCylinderEdgeFaceSlotOwner
    (transposePresentation P)
    (transposeTannerSquareAdmissibleV3 P
      A4.toTannerSquareAdmissibleV3) edgeZ S edge
  let corner := localCornerAtBoundaryEndpoint P edgeZ S
    cellOwner.1.1 cellOwner.1.2 endpoint
  have hcornerVertex : localCornerVertex P edgeZ S
      cellOwner.1.1 corner.1.1 = fixedVertex := by
    calc
      localCornerVertex P edgeZ S cellOwner.1.1 corner.1.1 =
          BDL26TannerLocalRegularity.edgeEndpoint
            (tannerDoubleCylinderEdgeStart (transposePresentation P) edgeZ S)
            (tannerDoubleCylinderEdgeEnd (transposePresentation P) edgeZ S)
            (doubleCylinderFaceBoundaryEdge (transposePresentation P)
              edgeZ S cellOwner.1.1 cellOwner.1.2) endpoint := corner.2.2
      _ = BDL26TannerLocalRegularity.edgeEndpoint
            (tannerDoubleCylinderEdgeStart (transposePresentation P) edgeZ S)
            (tannerDoubleCylinderEdgeEnd (transposePresentation P) edgeZ S)
            edge endpoint := by rw [cellOwner.2]
      _ = fixedVertex := by
        have hselected := rzOrientedBoundaryEndpoint_spec
          (tannerDoubleCylinderEdgeStart (transposePresentation P) edgeZ S)
          (tannerDoubleCylinderEdgeEnd (transposePresentation P) edgeZ S)
          edge fixedVertex hendpoints
        have hbridge : BDL26TannerLocalRegularity.edgeEndpoint
            (tannerDoubleCylinderEdgeStart (transposePresentation P) edgeZ S)
            (tannerDoubleCylinderEdgeEnd (transposePresentation P) edgeZ S)
            edge endpoint =
          edgeEndpoint
            (tannerDoubleCylinderEdgeStart (transposePresentation P) edgeZ S)
            (tannerDoubleCylinderEdgeEnd (transposePresentation P) edgeZ S)
            edge endpoint := by
          by_cases hzero : endpoint = 0
          · rw [hzero]
            rfl
          · have hone : endpoint = 1 := by
              apply Fin.ext
              have hlt := endpoint.2
              have hne : endpoint.1 ≠ 0 := by
                intro h
                apply hzero
                apply Fin.ext
                exact h
              omega
            rw [hone]
            rfl
        exact hbridge.trans hselected
  let face : ZStarFace successor ⟨edgeZ, fixedVertex⟩ :=
    ⟨Sum.inl ⟨edgeZ, cellOwner.1.1, corner.1.1⟩, by
      simp only [zStarFaceMember, decide_eq_true_eq]
      change localFaceZ P S ⟨edgeZ, cellOwner.1.1, corner.1.1⟩ =
        ⟨edgeZ, fixedVertex⟩
      rw [localFaceZ_eq_corner]
      exact Sigma.ext rfl (heq_of_eq hcornerVertex)⟩
  refine ⟨⟨face, corner.1.2⟩, ?_⟩
  apply Subtype.ext
  apply congrArg Sum.inr
  apply Subtype.ext
  apply Prod.ext
  · change twoSelect
        (localFaceQ0 P S ⟨edgeZ, cellOwner.1.1, corner.1.1⟩)
        (localFaceQ1 P S ⟨edgeZ, cellOwner.1.1, corner.1.1⟩)
        corner.1.2 = Sum.inl ⟨edgeZ, edge⟩
    rw [localFaceQ_eq_corner]
    apply congrArg Sum.inl
    exact Sigma.ext
      (x := (⟨edgeZ, localCornerEdge P edgeZ S cellOwner.1.1
        (corner.1.1, corner.1.2)⟩ :
          Sigma fun z : P.Z => ZDoubleCylinderEdge P z S))
      (y := ⟨edgeZ, edge⟩) rfl
      (heq_of_eq (corner.2.1.trans cellOwner.2))
  · change localFaceZ P S
        ⟨edgeZ, cellOwner.1.1, corner.1.1⟩ = ⟨edgeZ, fixedVertex⟩
    rw [localFaceZ_eq_corner]
    exact Sigma.ext rfl (heq_of_eq hcornerVertex)

/-- Frozen RZ-Z radial row Z/1: a requested Q-cylinder vertex uses its
choice-free incident Q-cylinder edge and the corresponding glue face. -/
private noncomputable def rzQVertexZRadialFaceOwner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale)
    (qVertex : Sigma fun q : P.Q =>
      QDoubleCylinderVertex (transposePresentation P) q S)
    (fixedZ : RZZ P S)
    (incidence : (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S).qz (Sum.inr qVertex) fixedZ = true)
    (member : zStarEdgeMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) fixedZ
        (Sum.inr (⟨(Sum.inr qVertex, fixedZ), incidence⟩ :
          QZEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S))) = true) :
    {owner : ZStarFace (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) fixedZ × Two //
      zStarFaceQZEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) fixedZ owner.1 owner.2 =
          ⟨Sum.inr (⟨(Sum.inr qVertex, fixedZ), incidence⟩ :
            QZEdge (rzReplacementPresentation P
              A4.toTannerSquareAdmissible S)), member⟩} := by
  classical
  let A := A4.toTannerSquareAdmissible
  let successor := rzReplacementPresentation P A S
  rcases qVertex with ⟨q, vertex⟩
  rcases fixedZ with ⟨z, fixedVertex⟩
  change decide (Exists fun hqz : P.qz q z = true =>
    qToZDoubleCylinderVertex P A q z hqz S vertex = fixedVertex) = true
    at incidence
  have hqz : P.qz q z = true := by
    obtain ⟨hqz, _⟩ := of_decide_eq_true incidence
    exact hqz
  have hmap : qToZDoubleCylinderVertex P A q z hqz S vertex =
      fixedVertex := by
    obtain ⟨hqz', hmap⟩ := of_decide_eq_true incidence
    simpa only [Subsingleton.elim hqz' hqz] using hmap
  obtain ⟨⟨qEdge, endpoint⟩, hendpoint⟩ :=
    qDoubleCylinderVertexIncidentEdge P A q S vertex
  have hendpoint' : edgeEndpoint
      (qDoubleCylinderEdgeStart (transposePresentation P) q S)
      (qDoubleCylinderEdgeEnd (transposePresentation P) q S)
      qEdge endpoint = vertex := by
    fin_cases endpoint <;> simpa [edgeEndpoint, twoSelect] using hendpoint
  let oldEdge : QZEdge P := ⟨(q, z), hqz⟩
  let glue : RZQZGlueFace P S := ⟨oldEdge, qEdge, endpoint⟩
  have hfaceZ : glueFaceZ P A S glue = ⟨z, fixedVertex⟩ := by
    apply Sigma.ext (x := glueFaceZ P A S glue)
      (y := ⟨z, fixedVertex⟩) rfl
    apply heq_of_eq
    simp only [glueFaceZ, glue, oldEdge]
    change qToZDoubleCylinderVertex P A q z hqz S
        (edgeEndpoint
          (qDoubleCylinderEdgeStart (transposePresentation P) q S)
          (qDoubleCylinderEdgeEnd (transposePresentation P) q S)
          qEdge endpoint) = fixedVertex
    rw [hendpoint']
    exact hmap
  let face : ZStarFace successor ⟨z, fixedVertex⟩ :=
    ⟨Sum.inr (Sum.inl glue), by
      simp only [zStarFaceMember, decide_eq_true_eq]
      exact hfaceZ⟩
  refine ⟨⟨face, 1⟩, ?_⟩
  apply Subtype.ext
  apply congrArg Sum.inr
  apply Subtype.ext
  apply Prod.ext
  · change glueFaceQ1 P S glue = Sum.inr ⟨q, vertex⟩
    simp only [glueFaceQ1, glue, oldEdge]
    apply congrArg Sum.inr
    exact Sigma.ext rfl (heq_of_eq hendpoint')
  · exact hfaceZ

/-- Total successor Z radial owner dispatcher.  Its two structural branches
are exactly the frozen #908 rows Z/0 and Z/1. -/
private noncomputable def rzReplacementZRadialFaceOwner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale)
    (z : (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S).Z)
    (edge : QZEdge (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S))
    (member : zStarEdgeMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) z (Sum.inr edge) = true) :
    {owner : ZStarFace (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) z × Two //
      zStarFaceQZEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) z owner.1 owner.2 =
          ⟨Sum.inr edge, member⟩} := by
  rcases edge with ⟨⟨edgeQ, edgeZ⟩, incidence⟩
  have hz : edgeZ = z := zStarQZEdge_second_eq
    (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
    z ⟨(edgeQ, edgeZ), incidence⟩ member
  subst edgeZ
  rcases edgeQ with localEdge | qVertex
  · exact rzLocalQZRadialFaceOwner P A4 S localEdge z incidence member
  · exact rzQVertexZRadialFaceOwner P A4 S qVertex z incidence member

/-- The radial-owner successor admissibility package.  Its V2 projection is
exactly `rzReplacementAdmissibleV2`; the two new fields are the complete
constructor dispatchers above.  This declaration makes no successor V4 or
regularity claim. -/
noncomputable def rzReplacementAdmissibleV3
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) :
    TannerSquareAdmissibleV3
      (rzReplacementPresentation P A4.toTannerSquareAdmissible S) where
  toTannerSquareAdmissibleV2 := rzReplacementAdmissibleV2 P A4 R S
  xRadialFaceOwner := rzReplacementXRadialFaceOwner P A4 S
  zRadialFaceOwner := rzReplacementZRadialFaceOwner P A4 S

/-! ## Successor V4 boundary face owners -/

/-- A Q-Z edge in a closed X-star retains the incidence of its requested Q
endpoint with the fixed X.  Star membership is eliminated only in `Prop`;
no face witness is exported as owner data. -/
private theorem xStarQZEdge_xq
    (P : TannerSquarePresentation) (fixedX : P.X) (edge : QZEdge P)
    (member : xStarEdgeMember P fixedX (Sum.inr edge) = true) :
    P.xq fixedX edge.1.1 = true := by
  have hstart := (xStarEdgeStart P fixedX
    (⟨Sum.inr edge, member⟩ : XStarEdge P fixedX)).2
  have hqMember : ∃ face : P.Face,
      xStarFaceMember P fixedX face = true ∧
        (edge.1.1 = P.faceQ face 0 ∨ edge.1.1 = P.faceQ face 1) := by
    simpa [xStarVertexMember] using of_decide_eq_true hstart
  obtain ⟨face, hface, hq | hq⟩ := hqMember
  · have hx : P.faceX face = fixedX := by
      simpa [xStarFaceMember] using of_decide_eq_true hface
    rw [← hx, hq]
    exact P.data.faceQ_xq face 0
  · have hx : P.faceX face = fixedX := by
      simpa [xStarFaceMember] using of_decide_eq_true hface
    rw [← hx, hq]
    exact P.data.faceQ_xq face 1

/-- Frozen RZ V4 X-boundary row X/0.  The requested local Q constructor and
the supplied local cell determine a structural face slot.  The Q-Z endpoint
then determines its orientation, so the local face bits and ordered corner
are computed without selecting Type-valued data from boundary membership. -/
private noncomputable def rzLocalXBoundaryFaceOwner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (localX : Sigma fun z : P.Z => ZDoubleCylinderFace P z S)
    (edge : QZEdge (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S))
    (member : xStarEdgeMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inl localX))
        (Sum.inr edge) = true) :
    {owner : XStarFace (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inl localX)) × Two //
      xStarFaceQZEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inl localX))
          owner.1 owner.2 = ⟨Sum.inr edge, member⟩} := by
  classical
  let A := A4.toTannerSquareAdmissible
  let successor := rzReplacementPresentation P A S
  have hxq : successor.xq (Sum.inl (Sum.inl localX)) edge.1.1 = true :=
    xStarQZEdge_xq successor (Sum.inl (Sum.inl localX)) edge member
  rcases edge with ⟨⟨edgeQ, fixedZ⟩, hqz⟩
  rcases edgeQ with localEdge | qVertex
  · rcases localX with ⟨z, cell⟩
    rcases localEdge with ⟨edgeZ, localEdge⟩
    rcases fixedZ with ⟨fixedBaseZ, fixedVertex⟩
    change decide (Exists fun h : edgeZ = z =>
      doubleCylinderFaceEdgeMatrix (transposePresentation P) z S
        (h ▸ localEdge) cell = 1) = true at hxq
    have hEdgeZ : edgeZ = z := by
      obtain ⟨hEdgeZ, _⟩ := of_decide_eq_true hxq
      exact hEdgeZ
    subst edgeZ
    have hfaceMatrix : doubleCylinderFaceEdgeMatrix
        (transposePresentation P) z S localEdge cell = 1 := by
      obtain ⟨hEdgeZ', hmatrix⟩ := of_decide_eq_true hxq
      simpa only [Subsingleton.elim hEdgeZ' rfl] using hmatrix
    change decide (Exists fun h : fixedBaseZ = z =>
      doubleCylinderEdgeVertexMatrix (transposePresentation P) z S
        (h ▸ fixedVertex) localEdge = 1) = true at hqz
    have hFixedZ : fixedBaseZ = z := by
      obtain ⟨hFixedZ, _⟩ := of_decide_eq_true hqz
      exact hFixedZ
    subst fixedBaseZ
    have hvertexMatrix : doubleCylinderEdgeVertexMatrix
        (transposePresentation P) z S fixedVertex localEdge = 1 := by
      obtain ⟨hFixedZ', hmatrix⟩ := of_decide_eq_true hqz
      simpa only [Subsingleton.elim hFixedZ' rfl] using hmatrix
    have hendpoints : fixedVertex =
          tannerDoubleCylinderEdgeStart (transposePresentation P) z S
            localEdge ∨
        fixedVertex =
          tannerDoubleCylinderEdgeEnd (transposePresentation P) z S
            localEdge :=
      (doubleCylinderEdgeVertexMatrix_eq_one_iff
        (transposePresentation P) z S fixedVertex localEdge).1 hvertexMatrix
    let slot := doubleCylinderFaceBoundarySlotOwner
      (transposePresentation P) z S cell localEdge hfaceMatrix
    let endpoint := rzOrientedBoundaryEndpoint
      (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
      localEdge fixedVertex
    let corner := localCornerAtBoundaryEndpoint P z S
      cell slot.1 endpoint
    have hcornerVertex : localCornerVertex P z S cell corner.1.1 =
        fixedVertex := by
      calc
        localCornerVertex P z S cell corner.1.1 =
            BDL26TannerLocalRegularity.edgeEndpoint
              (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
              (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
              (doubleCylinderFaceBoundaryEdge (transposePresentation P)
                z S cell slot.1) endpoint := corner.2.2
        _ = BDL26TannerLocalRegularity.edgeEndpoint
              (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
              (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
              localEdge endpoint := by rw [slot.2]
        _ = fixedVertex := by
          have hselected := rzOrientedBoundaryEndpoint_spec
            (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
            (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
            localEdge fixedVertex hendpoints
          have hbridge : BDL26TannerLocalRegularity.edgeEndpoint
              (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
              (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
              localEdge endpoint =
            edgeEndpoint
              (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
              (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
              localEdge endpoint := by
            exact rzTwoElim (motive := fun endpoint =>
                BDL26TannerLocalRegularity.edgeEndpoint
                    (tannerDoubleCylinderEdgeStart
                      (transposePresentation P) z S)
                    (tannerDoubleCylinderEdgeEnd
                      (transposePresentation P) z S)
                    localEdge endpoint =
                  edgeEndpoint
                    (tannerDoubleCylinderEdgeStart
                      (transposePresentation P) z S)
                    (tannerDoubleCylinderEdgeEnd
                      (transposePresentation P) z S)
                    localEdge endpoint)
              rfl rfl endpoint
          exact hbridge.trans hselected
    let face : XStarFace successor (Sum.inl (Sum.inl ⟨z, cell⟩)) :=
      ⟨Sum.inl ⟨z, cell, corner.1.1⟩, by
        simp only [xStarFaceMember, decide_eq_true_eq]
        rfl⟩
    refine ⟨⟨face, corner.1.2⟩, ?_⟩
    apply Subtype.ext
    apply congrArg Sum.inr
    apply Subtype.ext
    apply Prod.ext
    · change twoSelect
          (localFaceQ0 P S ⟨z, cell, corner.1.1⟩)
          (localFaceQ1 P S ⟨z, cell, corner.1.1⟩)
          corner.1.2 = Sum.inl ⟨z, localEdge⟩
      rw [localFaceQ_eq_corner]
      apply congrArg Sum.inl
      exact Sigma.ext
        (x := (⟨z, localCornerEdge P z S cell
          (corner.1.1, corner.1.2)⟩ :
            Sigma fun z : P.Z => ZDoubleCylinderEdge P z S))
        (y := ⟨z, localEdge⟩) rfl
        (heq_of_eq (corner.2.1.trans slot.2))
    · change localFaceZ P S ⟨z, cell, corner.1.1⟩ =
          ⟨z, fixedVertex⟩
      rw [localFaceZ_eq_corner]
      exact Sigma.ext rfl (heq_of_eq hcornerVertex)
  · change false = true at hxq
    exact False.elim (Bool.noConfusion hxq)

/-- Frozen RZ V4 X-boundary row X/1: the glue face at its explicit endpoint
owns the same-edge local Q-Z side at ordered corner zero. -/
private noncomputable def rzGlueXLocalBoundaryFaceOwner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale)
    (qEdge : Sigma fun q : P.Q =>
      QDoubleCylinderEdge (transposePresentation P) q S)
    (localEdge : Sigma fun z : P.Z => ZDoubleCylinderEdge P z S)
    (fixedZ : RZZ P S)
    (incidence : (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S).qz (Sum.inl localEdge) fixedZ = true)
    (member : xStarEdgeMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inr qEdge))
        (Sum.inr (⟨(Sum.inl localEdge, fixedZ), incidence⟩ :
          QZEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S))) = true) :
    {owner : XStarFace (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inr qEdge)) × Two //
      xStarFaceQZEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inr qEdge))
          owner.1 owner.2 =
        ⟨Sum.inr (⟨(Sum.inl localEdge, fixedZ), incidence⟩ :
          QZEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S)), member⟩} := by
  classical
  let A := A4.toTannerSquareAdmissible
  let successor := rzReplacementPresentation P A S
  rcases localEdge with ⟨edgeZ, edge⟩
  rcases fixedZ with ⟨fixedBaseZ, fixedVertex⟩
  change decide (Exists fun h : fixedBaseZ = edgeZ =>
    doubleCylinderEdgeVertexMatrix (transposePresentation P) edgeZ S
      (h ▸ fixedVertex) edge = 1) = true at incidence
  have hZ : fixedBaseZ = edgeZ := by
    obtain ⟨hZ, _⟩ := of_decide_eq_true incidence
    exact hZ
  subst fixedBaseZ
  have hmatrix : doubleCylinderEdgeVertexMatrix
      (transposePresentation P) edgeZ S fixedVertex edge = 1 := by
    obtain ⟨hZ', hmatrix⟩ := of_decide_eq_true incidence
    simpa only [Subsingleton.elim hZ' rfl] using hmatrix
  have hendpoints : fixedVertex =
        tannerDoubleCylinderEdgeStart (transposePresentation P) edgeZ S edge ∨
      fixedVertex =
        tannerDoubleCylinderEdgeEnd (transposePresentation P) edgeZ S edge :=
    (doubleCylinderEdgeVertexMatrix_eq_one_iff
      (transposePresentation P) edgeZ S fixedVertex edge).1 hmatrix
  let endpoint := rzOrientedBoundaryEndpoint
    (tannerDoubleCylinderEdgeStart (transposePresentation P) edgeZ S)
    (tannerDoubleCylinderEdgeEnd (transposePresentation P) edgeZ S)
    edge fixedVertex
  have hselected : edgeEndpoint
      (tannerDoubleCylinderEdgeStart (transposePresentation P) edgeZ S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation P) edgeZ S)
      edge endpoint = fixedVertex :=
    rzOrientedBoundaryEndpoint_spec _ _ _ _ hendpoints
  let starEdge : XStarEdge successor (Sum.inl (Sum.inr qEdge)) :=
    ⟨Sum.inr (⟨(Sum.inl ⟨edgeZ, edge⟩, ⟨edgeZ, fixedVertex⟩), incidence⟩ :
      QZEdge successor), member⟩
  have hqMember : xStarBoundaryVertexMember successor
      (Sum.inl (Sum.inr qEdge)) (Vertex.q (Sum.inl ⟨edgeZ, edge⟩)) = true :=
    (xStarEdgeStart successor (Sum.inl (Sum.inr qEdge)) starEdge).2
  let hqz := rzGlueXBoundaryLocalQ_incidence P A S qEdge
    ⟨edgeZ, edge⟩ hqMember
  have hedge : edge = qToZDoubleCylinderEdge P A qEdge.1 edgeZ hqz
      S qEdge.2 :=
    rzGlueXBoundaryLocalQ_edge P A S qEdge ⟨edgeZ, edge⟩ hqMember
  have hfaceZ : qToZDoubleCylinderVertex P A qEdge.1 edgeZ hqz S
      (edgeEndpoint
        (qDoubleCylinderEdgeStart (transposePresentation P) qEdge.1 S)
        (qDoubleCylinderEdgeEnd (transposePresentation P) qEdge.1 S)
        qEdge.2 endpoint) = fixedVertex := by
    by_cases hzero : endpoint = 0
    · rw [hzero]
      calc
        qToZDoubleCylinderVertex P A qEdge.1 edgeZ hqz S
            (qDoubleCylinderEdgeStart
              (transposePresentation P) qEdge.1 S qEdge.2) =
            tannerDoubleCylinderEdgeStart (transposePresentation P) edgeZ S
              (qToZDoubleCylinderEdge P A qEdge.1 edgeZ hqz S qEdge.2) :=
          qToZDoubleCylinderEdge_start P A qEdge.1 edgeZ hqz S qEdge.2
        _ = tannerDoubleCylinderEdgeStart
              (transposePresentation P) edgeZ S edge := by rw [← hedge]
        _ = fixedVertex := by
          simpa [hzero, edgeEndpoint, twoSelect] using hselected
    · have hone : endpoint = 1 := by
        apply Fin.ext
        have hlt := endpoint.2
        have hne : endpoint.1 ≠ 0 := by
          intro h
          apply hzero
          apply Fin.ext
          exact h
        omega
      rw [hone]
      calc
        qToZDoubleCylinderVertex P A qEdge.1 edgeZ hqz S
            (qDoubleCylinderEdgeEnd
              (transposePresentation P) qEdge.1 S qEdge.2) =
            tannerDoubleCylinderEdgeEnd (transposePresentation P) edgeZ S
              (qToZDoubleCylinderEdge P A qEdge.1 edgeZ hqz S qEdge.2) :=
          qToZDoubleCylinderEdge_end P A qEdge.1 edgeZ hqz S qEdge.2
        _ = tannerDoubleCylinderEdgeEnd
              (transposePresentation P) edgeZ S edge := by rw [← hedge]
        _ = fixedVertex := by
          simpa [hone, edgeEndpoint, twoSelect] using hselected
  let face := rzGlueXStarFace P A S qEdge edgeZ hqz endpoint
  refine ⟨⟨face, 0⟩, ?_⟩
  apply Subtype.ext
  apply congrArg Sum.inr
  apply Subtype.ext
  apply Prod.ext
  · change glueFaceQ0 P A S
        ⟨(⟨(qEdge.1, edgeZ), hqz⟩ : QZEdge P), qEdge.2, endpoint⟩ =
      Sum.inl ⟨edgeZ, edge⟩
    apply congrArg Sum.inl
    exact Sigma.ext rfl (heq_of_eq hedge.symm)
  · change glueFaceZ P A S
        ⟨(⟨(qEdge.1, edgeZ), hqz⟩ : QZEdge P), qEdge.2, endpoint⟩ =
      ⟨edgeZ, fixedVertex⟩
    exact Sigma.ext rfl (heq_of_eq hfaceZ)

/-- Frozen RZ V4 X-boundary row X/2: the glue face selected by the requested
Q-cylinder endpoint owns its Q-Z side at ordered corner one. -/
private noncomputable def rzGlueXQVertexBoundaryFaceOwner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale)
    (qEdge : Sigma fun q : P.Q =>
      QDoubleCylinderEdge (transposePresentation P) q S)
    (qVertex : Sigma fun q : P.Q =>
      QDoubleCylinderVertex (transposePresentation P) q S)
    (fixedZ : RZZ P S)
    (incidence : (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S).qz (Sum.inr qVertex) fixedZ = true)
    (member : xStarEdgeMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inr qEdge))
        (Sum.inr (⟨(Sum.inr qVertex, fixedZ), incidence⟩ :
          QZEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S))) = true) :
    {owner : XStarFace (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inr qEdge)) × Two //
      xStarFaceQZEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) (Sum.inl (Sum.inr qEdge))
          owner.1 owner.2 =
        ⟨Sum.inr (⟨(Sum.inr qVertex, fixedZ), incidence⟩ :
          QZEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S)), member⟩} := by
  classical
  let A := A4.toTannerSquareAdmissible
  let successor := rzReplacementPresentation P A S
  rcases qVertex with ⟨q, vertex⟩
  rcases fixedZ with ⟨z, fixedVertex⟩
  change decide (Exists fun hqz : P.qz q z = true =>
    qToZDoubleCylinderVertex P A q z hqz S vertex = fixedVertex) = true
    at incidence
  have hqz : P.qz q z = true := by
    obtain ⟨hqz, _⟩ := of_decide_eq_true incidence
    exact hqz
  have hmap : qToZDoubleCylinderVertex P A q z hqz S vertex =
      fixedVertex := by
    obtain ⟨hqz', hmap⟩ := of_decide_eq_true incidence
    simpa only [Subsingleton.elim hqz' hqz] using hmap
  let starEdge : XStarEdge successor (Sum.inl (Sum.inr qEdge)) :=
    ⟨Sum.inr (⟨(Sum.inr ⟨q, vertex⟩, ⟨z, fixedVertex⟩), incidence⟩ :
      QZEdge successor), member⟩
  have hqMember : xStarBoundaryVertexMember successor
      (Sum.inl (Sum.inr qEdge)) (Vertex.q (Sum.inr ⟨q, vertex⟩)) = true :=
    (xStarEdgeStart successor (Sum.inl (Sum.inr qEdge)) starEdge).2
  have hdata := rzGlueXBoundaryQVertex_endpoints P A S qEdge
    ⟨q, vertex⟩ hqMember
  let selected : Sigma fun q : P.Q =>
      QDoubleCylinderVertex (transposePresentation P) q S := ⟨q, vertex⟩
  let endpoint := rzOrientedBoundaryEndpoint
    (fun _ : Unit => ⟨qEdge.1, qDoubleCylinderEdgeStart
      (transposePresentation P) qEdge.1 S qEdge.2⟩)
    (fun _ : Unit => ⟨qEdge.1, qDoubleCylinderEdgeEnd
      (transposePresentation P) qEdge.1 S qEdge.2⟩) () selected
  have hselected : (⟨qEdge.1, edgeEndpoint
      (qDoubleCylinderEdgeStart (transposePresentation P) qEdge.1 S)
      (qDoubleCylinderEdgeEnd (transposePresentation P) qEdge.1 S)
      qEdge.2 endpoint⟩ : Sigma fun q : P.Q =>
        QDoubleCylinderVertex (transposePresentation P) q S) = selected := by
    have hspec := rzOrientedBoundaryEndpoint_spec
      (fun _ : Unit => ⟨qEdge.1, qDoubleCylinderEdgeStart
        (transposePresentation P) qEdge.1 S qEdge.2⟩)
      (fun _ : Unit => ⟨qEdge.1, qDoubleCylinderEdgeEnd
        (transposePresentation P) qEdge.1 S qEdge.2⟩) () selected hdata
    have hshape : edgeEndpoint
        (fun _ : Unit => ⟨qEdge.1, qDoubleCylinderEdgeStart
          (transposePresentation P) qEdge.1 S qEdge.2⟩)
        (fun _ : Unit => ⟨qEdge.1, qDoubleCylinderEdgeEnd
          (transposePresentation P) qEdge.1 S qEdge.2⟩) () endpoint =
      (⟨qEdge.1, edgeEndpoint
        (qDoubleCylinderEdgeStart (transposePresentation P) qEdge.1 S)
        (qDoubleCylinderEdgeEnd (transposePresentation P) qEdge.1 S)
        qEdge.2 endpoint⟩ : Sigma fun q : P.Q =>
          QDoubleCylinderVertex (transposePresentation P) q S) := by
      by_cases hzero : endpoint = 0
      · rw [hzero]
        rfl
      · have hone : endpoint = 1 := by
          apply Fin.ext
          have hlt := endpoint.2
          have hne : endpoint.1 ≠ 0 := by
            intro h
            apply hzero
            apply Fin.ext
            exact h
          omega
        rw [hone]
        rfl
    exact hshape.symm.trans hspec
  have hq : qEdge.1 = q := congrArg Sigma.fst hselected
  have hfaceZ : qToZDoubleCylinderVertex P A qEdge.1 z
      (hq ▸ hqz) S
      (edgeEndpoint
        (qDoubleCylinderEdgeStart (transposePresentation P) qEdge.1 S)
        (qDoubleCylinderEdgeEnd (transposePresentation P) qEdge.1 S)
        qEdge.2 endpoint) = fixedVertex := by
    have hvertex : HEq
        (edgeEndpoint
          (qDoubleCylinderEdgeStart (transposePresentation P) qEdge.1 S)
          (qDoubleCylinderEdgeEnd (transposePresentation P) qEdge.1 S)
          qEdge.2 endpoint) vertex :=
      (Sigma.mk.inj_iff.mp hselected).2
    subst q
    exact congrArg (qToZDoubleCylinderVertex P A qEdge.1 z hqz S)
      (eq_of_heq hvertex) |>.trans hmap
  let face := rzGlueXStarFace P A S qEdge z (hq ▸ hqz) endpoint
  refine ⟨⟨face, 1⟩, ?_⟩
  apply Subtype.ext
  apply congrArg Sum.inr
  apply Subtype.ext
  apply Prod.ext
  · change glueFaceQ1 P S
        ⟨(⟨(qEdge.1, z), hq ▸ hqz⟩ : QZEdge P), qEdge.2, endpoint⟩ =
      Sum.inr ⟨q, vertex⟩
    apply congrArg Sum.inr
    exact hselected
  · change glueFaceZ P A S
        ⟨(⟨(qEdge.1, z), hq ▸ hqz⟩ : QZEdge P), qEdge.2, endpoint⟩ =
      ⟨z, fixedVertex⟩
    exact Sigma.ext rfl (heq_of_eq hfaceZ)

/-- In the old-X X-star, a terminal Q-cylinder boundary tag retains exactly
the old-X copy and the stored old X endpoint.  The face witness is eliminated
only into these proposition-valued equalities. -/
private theorem rzOldXBoundaryTerminal_data
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (oldX : P.X × Two) (q : P.Q) (copy : Two)
    (stored : QStarEdge (transposePresentation P) q)
    (fixedZ : RZZ P S)
    (incidence : (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S).qz
        (Sum.inr ⟨q, (copy, Sum.inl (Sum.inr stored))⟩) fixedZ = true)
    (member : xStarEdgeMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) (Sum.inr oldX)
        (Sum.inr
          (⟨(Sum.inr ⟨q, (copy, Sum.inl (Sum.inr stored))⟩, fixedZ),
            incidence⟩ : QZEdge (rzReplacementPresentation P
              A4.toTannerSquareAdmissible S))) = true) :
    copy = oldX.2 ∧ stored.1 = oldX.1 := by
  let A := A4.toTannerSquareAdmissible
  simp only [xStarEdgeMember, decide_eq_true_eq] at member
  obtain ⟨face, hface, hedge⟩ := member
  simp only [xStarFaceMember, decide_eq_true_eq] at hface
  rw [show (rzReplacementPresentation P A S).faceX = rzFaceX P S from rfl]
    at hface
  rcases face with localFace | glueOrOld
  · cases hface
  · rcases glueOrOld with glue | oldFace
    · cases hface
    · rcases oldFace with ⟨face, faceCopy⟩
      change Sum.inr (P.faceX face, faceCopy) = Sum.inr oldX at hface
      have howner : (P.faceX face, faceCopy) = oldX := Sum.inr.inj hface
      rcases of_decide_eq_true hedge with hedge | hedge
      all_goals
        have hq := congrArg (fun edge : QZEdge
          (rzReplacementPresentation P A S) => edge.1.1) hedge
        change Sum.inr ⟨q, (copy, Sum.inl (Sum.inr stored))⟩ =
          oldXFaceQ P S _ (face, faceCopy) at hq
        have hq' := hq.symm
        simp only [oldXFaceQ] at hq'
        have hqBase := congrArg Sigma.fst (Sum.inr.inj hq')
        cases hqBase
        have hvertex := eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj hq')).2
        have hcopy : faceCopy = copy := congrArg Prod.fst hvertex
        have hstored :
            (⟨P.faceX face, P.data.faceQ_xq face _⟩ :
              QStarEdge (transposePresentation P) (P.faceQ face _)) = stored := by
          have hrest := congrArg Prod.snd hvertex
          exact Sum.inr.inj (Sum.inl.inj hrest)
        exact ⟨hcopy.symm.trans (congrArg Prod.snd howner),
          (congrArg Subtype.val hstored).symm.trans
            (congrArg Prod.fst howner)⟩

/-- Nonterminal Q-cylinder vertices cannot occur on an old-X Q-Z boundary
edge. -/
private theorem rzOldXBoundaryNonterminal_false
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (oldX : P.X × Two)
    (qVertex : Sigma fun q : P.Q =>
      QDoubleCylinderVertex (transposePresentation P) q S)
    (fixedZ : RZZ P S)
    (incidence : (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S).qz (Sum.inr qVertex) fixedZ = true)
    (member : xStarEdgeMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) (Sum.inr oldX)
        (Sum.inr (⟨(Sum.inr qVertex, fixedZ), incidence⟩ :
          QZEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S))) = true)
    (hnonterminal : ∀ (q : P.Q) (copy : Two)
      (stored : QStarEdge (transposePresentation P) q),
      qVertex ≠ ⟨q, (copy, Sum.inl (Sum.inr stored))⟩) : False := by
  let A := A4.toTannerSquareAdmissible
  simp only [xStarEdgeMember, decide_eq_true_eq] at member
  obtain ⟨face, hface, hedge⟩ := member
  simp only [xStarFaceMember, decide_eq_true_eq] at hface
  rw [show (rzReplacementPresentation P A S).faceX = rzFaceX P S from rfl]
    at hface
  rcases face with localFace | glueOrOld
  · cases hface
  · rcases glueOrOld with glue | oldFace
    · cases hface
    · rcases oldFace with ⟨face, faceCopy⟩
      rcases of_decide_eq_true hedge with hedge | hedge
      all_goals
        have hq := congrArg (fun edge : QZEdge
          (rzReplacementPresentation P A S) => edge.1.1) hedge
        change Sum.inr qVertex = oldXFaceQ P S _ (face, faceCopy) at hq
        apply hnonterminal (P.faceQ face _) faceCopy
          (⟨P.faceX face, P.data.faceQ_xq face _⟩ :
            QStarEdge (transposePresentation P) (P.faceQ face _))
        exact Sum.inr.inj hq

/-- Frozen RZ V4 X-boundary row X/3: an old-X copy is owned by the copy of
the input V4 Z-boundary face, with the input ordered corner unchanged. -/
private noncomputable def rzOldXBoundaryFaceOwner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (oldX : P.X × Two)
    (qVertex : Sigma fun q : P.Q =>
      QDoubleCylinderVertex (transposePresentation P) q S)
    (fixedZ : RZZ P S)
    (incidence : (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S).qz (Sum.inr qVertex) fixedZ = true)
    (member : xStarEdgeMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) (Sum.inr oldX)
        (Sum.inr (⟨(Sum.inr qVertex, fixedZ), incidence⟩ :
          QZEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S))) = true) :
    {owner : XStarFace (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) (Sum.inr oldX) × Two //
      xStarFaceQZEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) (Sum.inr oldX)
          owner.1 owner.2 =
        ⟨Sum.inr (⟨(Sum.inr qVertex, fixedZ), incidence⟩ :
          QZEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S)), member⟩} := by
  classical
  let A := A4.toTannerSquareAdmissible
  let successor := rzReplacementPresentation P A S
  rcases qVertex with ⟨q, copy, original | interior⟩
  · rcases original with center | stored
    · exact False.elim (rzOldXBoundaryNonterminal_false P A4 S oldX
        ⟨q, (copy, Sum.inl (Sum.inl center))⟩ fixedZ incidence member
        (by
          intro targetQ targetCopy targetStored h
          have hbase := congrArg Sigma.fst h
          cases hbase
          have hvalue := eq_of_heq (Sigma.mk.inj_iff.mp h).2
          cases hvalue))
    · have hdata := rzOldXBoundaryTerminal_data P A4 S oldX q copy stored
        fixedZ incidence member
      have hcopy : copy = oldX.2 := hdata.1
      subst copy
      rcases fixedZ with ⟨z, fixedVertex⟩
      change decide (Exists fun hqz : P.qz q z = true =>
        qToZDoubleCylinderVertex P A q z hqz S
          (oldX.2, Sum.inl (Sum.inr stored)) = fixedVertex) = true
        at incidence
      have hqz : P.qz q z = true := by
        obtain ⟨hqz, _⟩ := of_decide_eq_true incidence
        exact hqz
      have hmap : qToZDoubleCylinderVertex P A q z hqz S
          (oldX.2, Sum.inl (Sum.inr stored)) = fixedVertex := by
        obtain ⟨hqz', hmap⟩ := of_decide_eq_true incidence
        simpa only [Subsingleton.elim hqz' hqz] using hmap
      let inputBoundary : ZStarBoundaryEdge P z :=
        qToZBoundaryEdge P q z hqz stored
      let inputXQ := rzInputZBoundaryXQEdge P z inputBoundary
      let inputOwner := rzInputZBoundaryFaceOwner P A4 z inputBoundary
      have hinputX : inputXQ.1.1 = oldX.1 := by
        change stored.1 = oldX.1
        exact hdata.2
      have hownerX : P.faceX inputOwner.1.1.1 = oldX.1 :=
        (rzInputZBoundaryOwner_faceX P A4 z inputBoundary).trans hinputX
      have hownerQ : P.faceQ inputOwner.1.1.1 inputOwner.1.2 = q := by
        have h := rzInputZBoundaryOwner_faceQ P A4 z inputBoundary
        change P.faceQ inputOwner.1.1.1 inputOwner.1.2 = inputXQ.1.2
          at h
        exact h
      have hedge : HEq
          (⟨P.faceX inputOwner.1.1.1,
            P.data.faceQ_xq inputOwner.1.1.1 inputOwner.1.2⟩ :
            QStarEdge (transposePresentation P)
              (P.faceQ inputOwner.1.1.1 inputOwner.1.2)) stored := by
        apply (Subtype.heq_iff_coe_eq (fun value => by rw [hownerQ])).2
        exact hownerX.trans hdata.2.symm
      let wrap : (Sigma fun q : P.Q =>
          QStarEdge (transposePresentation P) q) →
          (Sigma fun q : P.Q =>
            QDoubleCylinderVertex (transposePresentation P) q S) :=
        fun tagged => ⟨tagged.1,
          (oldX.2, Sum.inl (Sum.inr tagged.2))⟩
      have hSigmaEdge :
          (⟨P.faceQ inputOwner.1.1.1 inputOwner.1.2,
            (⟨P.faceX inputOwner.1.1.1,
              P.data.faceQ_xq inputOwner.1.1.1 inputOwner.1.2⟩ :
              QStarEdge (transposePresentation P)
                (P.faceQ inputOwner.1.1.1 inputOwner.1.2))⟩ :
            Sigma fun q : P.Q => QStarEdge (transposePresentation P) q) =
          ⟨q, stored⟩ := Sigma.ext hownerQ hedge
      have hSigmaVertex := congrArg wrap hSigmaEdge
      have hownerVertex : oldXFaceQ P S inputOwner.1.2
          (inputOwner.1.1.1, oldX.2) =
        Sum.inr ⟨q, (oldX.2, Sum.inl (Sum.inr stored))⟩ := by
        change Sum.inr (wrap ⟨P.faceQ inputOwner.1.1.1 inputOwner.1.2,
          (⟨P.faceX inputOwner.1.1.1,
            P.data.faceQ_xq inputOwner.1.1.1 inputOwner.1.2⟩ :
              QStarEdge (transposePresentation P)
                (P.faceQ inputOwner.1.1.1 inputOwner.1.2))⟩) =
          Sum.inr (wrap ⟨q, stored⟩)
        exact congrArg Sum.inr hSigmaVertex
      have hownerBaseZ : P.faceZ inputOwner.1.1.1 = z := by
        simpa [zStarFaceMember] using inputOwner.1.1.2
      have hfaceZ : oldXFaceZ P S (inputOwner.1.1.1, oldX.2) =
          ⟨z, fixedVertex⟩ := by
        let Source := { tagged : Sigma fun z : P.Z =>
            Sigma fun q : P.Q =>
              QDoubleCylinderVertex (transposePresentation P) q S //
          P.qz tagged.2.1 tagged.1 = true }
        let mapSource : Source →
            Sigma fun z : P.Z => ZDoubleCylinderVertex P z S :=
          fun source => ⟨source.1.1,
            qToZDoubleCylinderVertex P A source.1.2.1 source.1.1
              source.2 S source.1.2.2⟩
        let ownerSource : Source := ⟨⟨P.faceZ inputOwner.1.1.1,
          ⟨P.faceQ inputOwner.1.1.1 inputOwner.1.2,
            (oldX.2, Sum.inl (Sum.inr
              (⟨P.faceX inputOwner.1.1.1,
                P.data.faceQ_xq inputOwner.1.1.1 inputOwner.1.2⟩ :
                QStarEdge (transposePresentation P)
                  (P.faceQ inputOwner.1.1.1 inputOwner.1.2))))⟩⟩,
          P.data.faceQ_qz inputOwner.1.1.1 inputOwner.1.2⟩
        let requestedSource : Source :=
          ⟨⟨z, ⟨q, (oldX.2, Sum.inl (Sum.inr stored))⟩⟩, hqz⟩
        have hsource : ownerSource = requestedSource := by
          apply Subtype.ext
          apply Sigma.ext
          · exact hownerBaseZ
          · exact heq_of_eq hSigmaVertex
        have hownerMapped : oldXFaceZ P S
            (inputOwner.1.1.1, oldX.2) = mapSource ownerSource := by
          apply Sigma.ext
          · rfl
          · exact heq_of_eq (oldXFaceQ_maps_to_faceZ P A S
              inputOwner.1.1.1 oldX.2 inputOwner.1.2).symm
        have hrequestedMapped : mapSource requestedSource =
            ⟨z, fixedVertex⟩ := by
          apply Sigma.ext
          · rfl
          · exact heq_of_eq hmap
        exact hownerMapped.trans
          ((congrArg mapSource hsource).trans hrequestedMapped)
      let face : XStarFace successor (Sum.inr oldX) :=
        ⟨Sum.inr (Sum.inr (inputOwner.1.1.1, oldX.2)), by
          simp only [xStarFaceMember, decide_eq_true_eq]
          change Sum.inr (P.faceX inputOwner.1.1.1, oldX.2) = Sum.inr oldX
          exact congrArg Sum.inr (Prod.ext hownerX rfl)⟩
      refine ⟨⟨face, inputOwner.1.2⟩, ?_⟩
      apply Subtype.ext
      apply congrArg Sum.inr
      apply Subtype.ext
      apply Prod.ext
      · exact hownerVertex
      · exact hfaceZ
  · exact False.elim (rzOldXBoundaryNonterminal_false P A4 S oldX
      ⟨q, (copy, Sum.inr interior)⟩ fixedZ incidence member
      (by
        intro targetQ targetCopy targetStored h
        have hbase := congrArg Sigma.fst h
        cases hbase
        have hvalue := eq_of_heq (Sigma.mk.inj_iff.mp h).2
        cases hvalue))

/-- A local Z-cylinder Q tag cannot be a Q-Z boundary side in an old-X
X-star.  The star face witness is used only to derive this proposition. -/
private theorem rzOldXLocalQBoundary_false
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (oldX : P.X × Two)
    (localEdge : Sigma fun z : P.Z => ZDoubleCylinderEdge P z S)
    (fixedZ : RZZ P S)
    (incidence : (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S).qz (Sum.inl localEdge) fixedZ = true)
    (member : xStarEdgeMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) (Sum.inr oldX)
        (Sum.inr (⟨(Sum.inl localEdge, fixedZ), incidence⟩ :
          QZEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S))) = true) : False := by
  let A := A4.toTannerSquareAdmissible
  simp only [xStarEdgeMember, decide_eq_true_eq] at member
  obtain ⟨face, hface, hedge⟩ := member
  simp only [xStarFaceMember, decide_eq_true_eq] at hface
  rw [show (rzReplacementPresentation P A S).faceX = rzFaceX P S from rfl]
    at hface
  rcases face with localFace | glueOrOld
  · cases hface
  · rcases glueOrOld with glue | oldFace
    · cases hface
    · rcases oldFace with ⟨face, faceCopy⟩
      rcases of_decide_eq_true hedge with hedge | hedge
      all_goals
        have hq := congrArg (fun edge : QZEdge
          (rzReplacementPresentation P A S) => edge.1.1) hedge
        change Sum.inl localEdge = oldXFaceQ P S _ (face, faceCopy) at hq
        cases hq

/-- Total successor X-boundary face owner.  Structural dispatch combines the
four frozen RZ V4 X-boundary rows without changing ordered-corner semantics. -/
private noncomputable def rzReplacementXBoundaryFaceOwner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale)
    (fixedX : (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S).X)
    (edge : QZEdge (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S))
    (member : xStarEdgeMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) fixedX (Sum.inr edge) = true) :
    {owner : XStarFace (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) fixedX × Two //
      xStarFaceQZEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) fixedX owner.1 owner.2 =
          ⟨Sum.inr edge, member⟩} := by
  rcases edge with ⟨⟨edgeQ, fixedZ⟩, incidence⟩
  rcases fixedX with localOrGlue | oldX
  · rcases localOrGlue with localX | qEdge
    · exact rzLocalXBoundaryFaceOwner P A4 S localX
        ⟨(edgeQ, fixedZ), incidence⟩ member
    · rcases edgeQ with localEdge | qVertex
      · exact rzGlueXLocalBoundaryFaceOwner P A4 S qEdge localEdge
          fixedZ incidence member
      · exact rzGlueXQVertexBoundaryFaceOwner P A4 S qEdge qVertex
          fixedZ incidence member
  · rcases edgeQ with localEdge | qVertex
    · exact False.elim (rzOldXLocalQBoundary_false P A4 S oldX
        localEdge fixedZ incidence member)
    · exact rzOldXBoundaryFaceOwner P A4 S oldX qVertex fixedZ
        incidence member

/-! ### Successor Z-boundary face-owner rows -/

/-- A closed Z-star X-Q side supplies its requested Q endpoint as a boundary
vertex.  The face witness remains entirely in `Prop`. -/
private theorem zStarXQEdge_q_boundary_member
    (P : TannerSquarePresentation) (fixedZ : P.Z) (edge : XQEdge P)
    (member : zStarEdgeMember P fixedZ (Sum.inl edge) = true) :
    zStarBoundaryVertexMember P fixedZ (Vertex.q edge.1.2) = true := by
  change decide (∃ face : P.Face, zStarFaceMember P fixedZ face = true ∧
    decide (edge = faceXQEdge P face 0 ∨
      edge = faceXQEdge P face 1) = true) = true at member
  obtain ⟨face, hface, hedge⟩ := of_decide_eq_true member
  have hedge' := of_decide_eq_true hedge
  simp only [zStarBoundaryVertexMember, decide_eq_true_eq]
  refine ⟨face, hface, ?_⟩
  rcases hedge' with hedge | hedge
  · left
    exact congrArg (fun value : XQEdge P => value.1.2) hedge
  · right
    exact congrArg (fun value : XQEdge P => value.1.2) hedge

/-- Frozen RZ V4 Z-boundary row Z/0.  The supplied local cell and local-Q
edge determine the face boundary slot; the fixed successor Z determines the
oriented endpoint of that edge.  Together these constructor data compute the
unique local face bits and ordered X-Q corner. -/
private noncomputable def rzLocalZBoundaryFaceOwner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (fixedZ : RZZ P S)
    (localX : Sigma fun z : P.Z => ZDoubleCylinderFace P z S)
    (localEdge : Sigma fun z : P.Z => ZDoubleCylinderEdge P z S)
    (incidence : (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S).xq
        (Sum.inl (Sum.inl localX)) (Sum.inl localEdge) = true)
    (member : zStarEdgeMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) fixedZ
        (Sum.inl (⟨(Sum.inl (Sum.inl localX), Sum.inl localEdge),
          incidence⟩ : XQEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S))) = true) :
    {owner : ZStarFace (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) fixedZ × Two //
      zStarFaceXQEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) fixedZ owner.1 owner.2 =
        ⟨Sum.inl (⟨(Sum.inl (Sum.inl localX), Sum.inl localEdge),
          incidence⟩ : XQEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S)), member⟩} := by
  classical
  let A := A4.toTannerSquareAdmissible
  let successor := rzReplacementPresentation P A S
  have hqMember : zStarBoundaryVertexMember successor fixedZ
      (Vertex.q (Sum.inl localEdge)) = true :=
    zStarXQEdge_q_boundary_member successor fixedZ
      ⟨(Sum.inl (Sum.inl localX), Sum.inl localEdge), incidence⟩ member
  have hqz := rzLocalEdgeZBoundary_qz P A4 S fixedZ localEdge hqMember
  rcases localX with ⟨z, cell⟩
  rcases localEdge with ⟨edgeZ, edge⟩
  rcases fixedZ with ⟨fixedBaseZ, fixedVertex⟩
  change decide (Exists fun h : edgeZ = z =>
    doubleCylinderFaceEdgeMatrix (transposePresentation P) z S
      (h ▸ edge) cell = 1) = true at incidence
  have hEdgeZ : edgeZ = z := by
    obtain ⟨hEdgeZ, _⟩ := of_decide_eq_true incidence
    exact hEdgeZ
  subst edgeZ
  have hfaceMatrix : doubleCylinderFaceEdgeMatrix
      (transposePresentation P) z S edge cell = 1 := by
    obtain ⟨hEdgeZ', hmatrix⟩ := of_decide_eq_true incidence
    simpa only [Subsingleton.elim hEdgeZ' rfl] using hmatrix
  change decide (Exists fun h : fixedBaseZ = z =>
    doubleCylinderEdgeVertexMatrix (transposePresentation P) z S
      (h ▸ fixedVertex) edge = 1) = true at hqz
  have hFixedZ : fixedBaseZ = z := by
    obtain ⟨hFixedZ, _⟩ := of_decide_eq_true hqz
    exact hFixedZ
  subst fixedBaseZ
  have hvertexMatrix : doubleCylinderEdgeVertexMatrix
      (transposePresentation P) z S fixedVertex edge = 1 := by
    obtain ⟨hFixedZ', hmatrix⟩ := of_decide_eq_true hqz
    simpa only [Subsingleton.elim hFixedZ' rfl] using hmatrix
  have hendpoints : fixedVertex =
        tannerDoubleCylinderEdgeStart (transposePresentation P) z S edge ∨
      fixedVertex =
        tannerDoubleCylinderEdgeEnd (transposePresentation P) z S edge :=
    (doubleCylinderEdgeVertexMatrix_eq_one_iff
      (transposePresentation P) z S fixedVertex edge).1 hvertexMatrix
  let slot := doubleCylinderFaceBoundarySlotOwner
    (transposePresentation P) z S cell edge hfaceMatrix
  let endpoint := rzOrientedBoundaryEndpoint
    (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
    (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
    edge fixedVertex
  let corner := localCornerAtBoundaryEndpoint P z S
    cell slot.1 endpoint
  have hcornerVertex : localCornerVertex P z S cell corner.1.1 =
      fixedVertex := by
    calc
      localCornerVertex P z S cell corner.1.1 =
          BDL26TannerLocalRegularity.edgeEndpoint
            (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
            (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
            (doubleCylinderFaceBoundaryEdge (transposePresentation P)
              z S cell slot.1) endpoint := corner.2.2
      _ = BDL26TannerLocalRegularity.edgeEndpoint
            (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
            (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
            edge endpoint := by rw [slot.2]
      _ = fixedVertex := by
        have hselected := rzOrientedBoundaryEndpoint_spec
          (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
          (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
          edge fixedVertex hendpoints
        have hbridge : BDL26TannerLocalRegularity.edgeEndpoint
            (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
            (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
            edge endpoint =
          edgeEndpoint
            (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
            (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
            edge endpoint := by
          by_cases hzero : endpoint = 0
          · rw [hzero]
            rfl
          · have hone : endpoint = 1 := by
              apply Fin.ext
              have hlt := endpoint.2
              have hne : endpoint.1 ≠ 0 := by
                intro h
                apply hzero
                apply Fin.ext
                exact h
              omega
            rw [hone]
            rfl
        exact hbridge.trans hselected
  let face : ZStarFace successor ⟨z, fixedVertex⟩ :=
    ⟨Sum.inl ⟨z, cell, corner.1.1⟩, by
      simp only [zStarFaceMember, decide_eq_true_eq]
      change localFaceZ P S ⟨z, cell, corner.1.1⟩ =
        ⟨z, fixedVertex⟩
      rw [localFaceZ_eq_corner]
      exact Sigma.ext rfl (heq_of_eq hcornerVertex)⟩
  refine ⟨⟨face, corner.1.2⟩, ?_⟩
  apply Subtype.ext
  apply congrArg Sum.inl
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change twoSelect
        (localFaceQ0 P S ⟨z, cell, corner.1.1⟩)
        (localFaceQ1 P S ⟨z, cell, corner.1.1⟩)
        corner.1.2 = Sum.inl ⟨z, edge⟩
    rw [localFaceQ_eq_corner]
    apply congrArg Sum.inl
    exact Sigma.ext
      (x := (⟨z, localCornerEdge P z S cell
        (corner.1.1, corner.1.2)⟩ :
          Sigma fun z : P.Z => ZDoubleCylinderEdge P z S))
      (y := ⟨z, edge⟩) rfl
      (heq_of_eq (corner.2.1.trans slot.2))

/-- Frozen RZ V4 Z-boundary row Z/1: a glue face at the structurally selected
local-Q endpoint owns its local X-Q side at ordered corner zero. -/
private noncomputable def rzGlueZLocalBoundaryFaceOwner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (fixedZ : RZZ P S)
    (qEdge : Sigma fun q : P.Q =>
      QDoubleCylinderEdge (transposePresentation P) q S)
    (localEdge : Sigma fun z : P.Z => ZDoubleCylinderEdge P z S)
    (incidence : (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S).xq
        (Sum.inl (Sum.inr qEdge)) (Sum.inl localEdge) = true)
    (member : zStarEdgeMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) fixedZ
        (Sum.inl (⟨(Sum.inl (Sum.inr qEdge), Sum.inl localEdge),
          incidence⟩ : XQEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S))) = true) :
    {owner : ZStarFace (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) fixedZ × Two //
      zStarFaceXQEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) fixedZ owner.1 owner.2 =
        ⟨Sum.inl (⟨(Sum.inl (Sum.inr qEdge), Sum.inl localEdge),
          incidence⟩ : XQEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S)), member⟩} := by
  classical
  let A := A4.toTannerSquareAdmissible
  let successor := rzReplacementPresentation P A S
  have hqMember : zStarBoundaryVertexMember successor fixedZ
      (Vertex.q (Sum.inl localEdge)) = true :=
    zStarXQEdge_q_boundary_member successor fixedZ
      ⟨(Sum.inl (Sum.inr qEdge), Sum.inl localEdge), incidence⟩ member
  have hfixedQZ := rzLocalEdgeZBoundary_qz P A4 S
    fixedZ localEdge hqMember
  change decide (Exists fun hqz : P.qz qEdge.1 localEdge.1 = true =>
    qToZDoubleCylinderEdge P A qEdge.1 localEdge.1 hqz S qEdge.2 =
      localEdge.2) = true at incidence
  have hqz : P.qz qEdge.1 localEdge.1 = true := by
    obtain ⟨hqz, _⟩ := of_decide_eq_true incidence
    exact hqz
  have hedge : qToZDoubleCylinderEdge P A qEdge.1 localEdge.1 hqz S qEdge.2 =
      localEdge.2 := by
    obtain ⟨hqz', hedge⟩ := of_decide_eq_true incidence
    simpa only [Subsingleton.elim hqz' hqz] using hedge
  rcases localEdge with ⟨z, edge⟩
  rcases fixedZ with ⟨fixedBaseZ, fixedVertex⟩
  change decide (Exists fun h : fixedBaseZ = z =>
    doubleCylinderEdgeVertexMatrix (transposePresentation P) z S
      (h ▸ fixedVertex) edge = 1) = true at hfixedQZ
  have hFixedZ : fixedBaseZ = z := by
    obtain ⟨hFixedZ, _⟩ := of_decide_eq_true hfixedQZ
    exact hFixedZ
  subst fixedBaseZ
  have hmatrix : doubleCylinderEdgeVertexMatrix
      (transposePresentation P) z S fixedVertex edge = 1 := by
    obtain ⟨hFixedZ', hmatrix⟩ := of_decide_eq_true hfixedQZ
    simpa only [Subsingleton.elim hFixedZ' rfl] using hmatrix
  have hendpoints : fixedVertex =
        tannerDoubleCylinderEdgeStart (transposePresentation P) z S edge ∨
      fixedVertex =
        tannerDoubleCylinderEdgeEnd (transposePresentation P) z S edge :=
    (doubleCylinderEdgeVertexMatrix_eq_one_iff
      (transposePresentation P) z S fixedVertex edge).1 hmatrix
  let endpoint := rzOrientedBoundaryEndpoint
    (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
    (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
    edge fixedVertex
  have hselected : edgeEndpoint
      (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
      edge endpoint = fixedVertex :=
    rzOrientedBoundaryEndpoint_spec
      (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
      edge fixedVertex hendpoints
  have hfaceZ : qToZDoubleCylinderVertex P A qEdge.1 z hqz S
      (edgeEndpoint
        (qDoubleCylinderEdgeStart (transposePresentation P) qEdge.1 S)
        (qDoubleCylinderEdgeEnd (transposePresentation P) qEdge.1 S)
        qEdge.2 endpoint) = fixedVertex := by
    by_cases hzero : endpoint = 0
    · rw [hzero]
      calc
        qToZDoubleCylinderVertex P A qEdge.1 z hqz S
            (qDoubleCylinderEdgeStart
              (transposePresentation P) qEdge.1 S qEdge.2) =
            tannerDoubleCylinderEdgeStart (transposePresentation P) z S
              (qToZDoubleCylinderEdge P A qEdge.1 z hqz S qEdge.2) :=
          qToZDoubleCylinderEdge_start P A qEdge.1 z hqz S qEdge.2
        _ = tannerDoubleCylinderEdgeStart
              (transposePresentation P) z S edge := by rw [hedge]
        _ = fixedVertex := by
          simpa [hzero, edgeEndpoint, twoSelect] using hselected
    · have hone : endpoint = 1 := by
        apply Fin.ext
        have hlt := endpoint.2
        have hne : endpoint.1 ≠ 0 := by
          intro h
          apply hzero
          apply Fin.ext
          exact h
        omega
      rw [hone]
      calc
        qToZDoubleCylinderVertex P A qEdge.1 z hqz S
            (qDoubleCylinderEdgeEnd
              (transposePresentation P) qEdge.1 S qEdge.2) =
            tannerDoubleCylinderEdgeEnd (transposePresentation P) z S
              (qToZDoubleCylinderEdge P A qEdge.1 z hqz S qEdge.2) :=
          qToZDoubleCylinderEdge_end P A qEdge.1 z hqz S qEdge.2
        _ = tannerDoubleCylinderEdgeEnd
              (transposePresentation P) z S edge := by rw [hedge]
        _ = fixedVertex := by
          simpa [hone, edgeEndpoint, twoSelect] using hselected
  let glue : RZQZGlueFace P S :=
    ⟨(⟨(qEdge.1, z), hqz⟩ : QZEdge P), qEdge.2, endpoint⟩
  let face : ZStarFace successor ⟨z, fixedVertex⟩ :=
    ⟨Sum.inr (Sum.inl glue), by
      simp only [zStarFaceMember, decide_eq_true_eq]
      change glueFaceZ P A S glue = ⟨z, fixedVertex⟩
      exact Sigma.ext rfl (heq_of_eq hfaceZ)⟩
  refine ⟨⟨face, 0⟩, ?_⟩
  apply Subtype.ext
  apply congrArg Sum.inl
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change glueFaceQ0 P A S glue = Sum.inl ⟨z, edge⟩
    apply congrArg Sum.inl
    exact Sigma.ext rfl (heq_of_eq hedge)

/-- Frozen RZ V4 Z-boundary row Z/2: the requested Q-cylinder vertex
structurally selects its incident glue-face endpoint and ordered corner one. -/
private noncomputable def rzGlueZQVertexBoundaryFaceOwner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (fixedZ : RZZ P S)
    (qEdge : Sigma fun q : P.Q =>
      QDoubleCylinderEdge (transposePresentation P) q S)
    (qVertex : Sigma fun q : P.Q =>
      QDoubleCylinderVertex (transposePresentation P) q S)
    (incidence : (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S).xq
        (Sum.inl (Sum.inr qEdge)) (Sum.inr qVertex) = true)
    (member : zStarEdgeMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) fixedZ
        (Sum.inl (⟨(Sum.inl (Sum.inr qEdge), Sum.inr qVertex),
          incidence⟩ : XQEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S))) = true) :
    {owner : ZStarFace (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) fixedZ × Two //
      zStarFaceXQEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) fixedZ owner.1 owner.2 =
        ⟨Sum.inl (⟨(Sum.inl (Sum.inr qEdge), Sum.inr qVertex),
          incidence⟩ : XQEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S)), member⟩} := by
  classical
  let A := A4.toTannerSquareAdmissible
  let successor := rzReplacementPresentation P A S
  have hqMember : zStarBoundaryVertexMember successor fixedZ
      (Vertex.q (Sum.inr qVertex)) = true :=
    zStarXQEdge_q_boundary_member successor fixedZ
      ⟨(Sum.inl (Sum.inr qEdge), Sum.inr qVertex), incidence⟩ member
  have hsuccessorQZ := rzQVertexZBoundary_qz P A4 S
    fixedZ qVertex hqMember
  rcases qVertex with ⟨q, vertex⟩
  change decide (Exists fun hq : q = qEdge.1 =>
    hq ▸ vertex = qDoubleCylinderEdgeStart
        (transposePresentation P) qEdge.1 S qEdge.2 ∨
      hq ▸ vertex = qDoubleCylinderEdgeEnd
        (transposePresentation P) qEdge.1 S qEdge.2) = true at incidence
  have hq : q = qEdge.1 := by
    obtain ⟨hq, _⟩ := of_decide_eq_true incidence
    exact hq
  subst q
  have hendpoint : vertex = qDoubleCylinderEdgeStart
        (transposePresentation P) qEdge.1 S qEdge.2 ∨
      vertex = qDoubleCylinderEdgeEnd
        (transposePresentation P) qEdge.1 S qEdge.2 := by
    obtain ⟨hq', hendpoint⟩ := of_decide_eq_true incidence
    simpa only [Subsingleton.elim hq' rfl] using hendpoint
  let selected : Sigma fun q : P.Q =>
      QDoubleCylinderVertex (transposePresentation P) q S :=
    ⟨qEdge.1, vertex⟩
  let endpoint := rzOrientedBoundaryEndpoint
    (fun _ : Unit => ⟨qEdge.1, qDoubleCylinderEdgeStart
      (transposePresentation P) qEdge.1 S qEdge.2⟩)
    (fun _ : Unit => ⟨qEdge.1, qDoubleCylinderEdgeEnd
      (transposePresentation P) qEdge.1 S qEdge.2⟩) () selected
  have hselected : (⟨qEdge.1, edgeEndpoint
      (qDoubleCylinderEdgeStart (transposePresentation P) qEdge.1 S)
      (qDoubleCylinderEdgeEnd (transposePresentation P) qEdge.1 S)
      qEdge.2 endpoint⟩ : Sigma fun q : P.Q =>
        QDoubleCylinderVertex (transposePresentation P) q S) = selected := by
    have hspec := rzOrientedBoundaryEndpoint_spec
      (fun _ : Unit => ⟨qEdge.1, qDoubleCylinderEdgeStart
        (transposePresentation P) qEdge.1 S qEdge.2⟩)
      (fun _ : Unit => ⟨qEdge.1, qDoubleCylinderEdgeEnd
        (transposePresentation P) qEdge.1 S qEdge.2⟩) () selected
      (by
        rcases hendpoint with hstart | hend
        · left; exact Sigma.ext rfl (heq_of_eq hstart)
        · right; exact Sigma.ext rfl (heq_of_eq hend))
    have hshape : edgeEndpoint
        (fun _ : Unit => ⟨qEdge.1, qDoubleCylinderEdgeStart
          (transposePresentation P) qEdge.1 S qEdge.2⟩)
        (fun _ : Unit => ⟨qEdge.1, qDoubleCylinderEdgeEnd
          (transposePresentation P) qEdge.1 S qEdge.2⟩) () endpoint =
      (⟨qEdge.1, edgeEndpoint
        (qDoubleCylinderEdgeStart (transposePresentation P) qEdge.1 S)
        (qDoubleCylinderEdgeEnd (transposePresentation P) qEdge.1 S)
        qEdge.2 endpoint⟩ : Sigma fun q : P.Q =>
          QDoubleCylinderVertex (transposePresentation P) q S) := by
      by_cases hzero : endpoint = 0
      · rw [hzero]
        rfl
      · have hone : endpoint = 1 := by
          apply Fin.ext
          have hlt := endpoint.2
          have hne : endpoint.1 ≠ 0 := by
            intro h
            apply hzero
            apply Fin.ext
            exact h
          omega
        rw [hone]
        rfl
    exact hshape.symm.trans hspec
  rcases fixedZ with ⟨z, fixedVertex⟩
  change decide (Exists fun hqz : P.qz qEdge.1 z = true =>
    qToZDoubleCylinderVertex P A qEdge.1 z hqz S vertex =
      fixedVertex) = true at hsuccessorQZ
  have hqz : P.qz qEdge.1 z = true := by
    obtain ⟨hqz, _⟩ := of_decide_eq_true hsuccessorQZ
    exact hqz
  have hmap : qToZDoubleCylinderVertex P A qEdge.1 z hqz S vertex =
      fixedVertex := by
    obtain ⟨hqz', hmap⟩ := of_decide_eq_true hsuccessorQZ
    simpa only [Subsingleton.elim hqz' hqz] using hmap
  have hfaceZ : qToZDoubleCylinderVertex P A qEdge.1 z hqz S
      (edgeEndpoint
        (qDoubleCylinderEdgeStart (transposePresentation P) qEdge.1 S)
        (qDoubleCylinderEdgeEnd (transposePresentation P) qEdge.1 S)
        qEdge.2 endpoint) = fixedVertex := by
    have hvertex : HEq
        (edgeEndpoint
          (qDoubleCylinderEdgeStart (transposePresentation P) qEdge.1 S)
          (qDoubleCylinderEdgeEnd (transposePresentation P) qEdge.1 S)
          qEdge.2 endpoint) vertex :=
      (Sigma.mk.inj_iff.mp hselected).2
    exact congrArg (qToZDoubleCylinderVertex P A qEdge.1 z hqz S)
      (eq_of_heq hvertex) |>.trans hmap
  let glue : RZQZGlueFace P S :=
    ⟨(⟨(qEdge.1, z), hqz⟩ : QZEdge P), qEdge.2, endpoint⟩
  let face : ZStarFace successor ⟨z, fixedVertex⟩ :=
    ⟨Sum.inr (Sum.inl glue), by
      simp only [zStarFaceMember, decide_eq_true_eq]
      change glueFaceZ P A S glue = ⟨z, fixedVertex⟩
      exact Sigma.ext rfl (heq_of_eq hfaceZ)⟩
  refine ⟨⟨face, 1⟩, ?_⟩
  apply Subtype.ext
  apply congrArg Sum.inl
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change glueFaceQ1 P S glue = Sum.inr ⟨qEdge.1, vertex⟩
    apply congrArg Sum.inr
    exact hselected

/-- The old-X X-Q incidence constructor fixes the copy and stored old X of a
terminal Q-cylinder vertex.  No face is exported from the proposition. -/
private theorem rzOldXZBoundaryTerminal_data
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (oldX : P.X × Two) (q : P.Q) (copy : Two)
    (stored : QStarEdge (transposePresentation P) q)
    (incidence : (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S).xq (Sum.inr oldX)
        (Sum.inr ⟨q, (copy, Sum.inl (Sum.inr stored))⟩) = true) :
    copy = oldX.2 ∧ stored.1 = oldX.1 := by
  classical
  change decide (Exists fun face : P.Face => Exists fun corner : Two =>
    P.faceX face = oldX.1 ∧
      oldXFaceQ P S corner (face, oldX.2) =
        Sum.inr ⟨q, (copy, Sum.inl (Sum.inr stored))⟩) = true at incidence
  obtain ⟨face, corner, hfaceX, hq⟩ := of_decide_eq_true incidence
  change oldXFaceQ P S corner (face, oldX.2) =
    Sum.inr ⟨q, (copy, Sum.inl (Sum.inr stored))⟩ at hq
  simp only [oldXFaceQ] at hq
  have hqBase := congrArg Sigma.fst (Sum.inr.inj hq)
  cases hqBase
  have hvertex := eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj hq)).2
  have hcopy : oldX.2 = copy := congrArg Prod.fst hvertex
  have hstored :
      (⟨P.faceX face, P.data.faceQ_xq face corner⟩ :
        QStarEdge (transposePresentation P) (P.faceQ face corner)) =
      stored := by
    have hrest := congrArg Prod.snd hvertex
    exact Sum.inr.inj (Sum.inl.inj hrest)
  exact ⟨hcopy.symm,
    (congrArg Subtype.val hstored).symm.trans hfaceX⟩

/-- Frozen RZ V4 Z-boundary row Z/3: a terminal old-X side is owned by the
copy of the input V4 Z-boundary face, preserving its ordered corner. -/
private noncomputable def rzOldXZBoundaryFaceOwner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (fixedZ : RZZ P S) (oldX : P.X × Two)
    (qVertex : Sigma fun q : P.Q =>
      QDoubleCylinderVertex (transposePresentation P) q S)
    (incidence : (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S).xq
        (Sum.inr oldX) (Sum.inr qVertex) = true)
    (member : zStarEdgeMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) fixedZ
        (Sum.inl (⟨(Sum.inr oldX, Sum.inr qVertex), incidence⟩ :
          XQEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S))) = true) :
    {owner : ZStarFace (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) fixedZ × Two //
      zStarFaceXQEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) fixedZ owner.1 owner.2 =
        ⟨Sum.inl (⟨(Sum.inr oldX, Sum.inr qVertex), incidence⟩ :
          XQEdge (rzReplacementPresentation P
            A4.toTannerSquareAdmissible S)), member⟩} := by
  classical
  let A := A4.toTannerSquareAdmissible
  let successor := rzReplacementPresentation P A S
  have hqMember : zStarBoundaryVertexMember successor fixedZ
      (Vertex.q (Sum.inr qVertex)) = true :=
    zStarXQEdge_q_boundary_member successor fixedZ
      ⟨(Sum.inr oldX, Sum.inr qVertex), incidence⟩ member
  have hsuccessorQZ := rzQVertexZBoundary_qz P A4 S
    fixedZ qVertex hqMember
  rcases qVertex with ⟨q, copy, original | interior⟩
  · rcases original with central | stored
    · have himpossible : False := by
        change decide (Exists fun face : P.Face => Exists fun corner : Two =>
          P.faceX face = oldX.1 ∧
            oldXFaceQ P S corner (face, oldX.2) =
              Sum.inr ⟨q, (copy, Sum.inl (Sum.inl central))⟩) = true
          at incidence
        obtain ⟨face, corner, hfaceX, hq⟩ := of_decide_eq_true incidence
        change oldXFaceQ P S corner (face, oldX.2) =
          Sum.inr ⟨q, (copy, Sum.inl (Sum.inl central))⟩ at hq
        simp [oldXFaceQ] at hq
        cases hq.1
        have hvertex := eq_of_heq hq.2
        cases hvertex
      exact False.elim himpossible
    · have hdata := rzOldXZBoundaryTerminal_data P A4 S oldX q copy
        stored incidence
      have hcopy : copy = oldX.2 := hdata.1
      subst copy
      rcases fixedZ with ⟨z, fixedVertex⟩
      change decide (Exists fun hqz : P.qz q z = true =>
        qToZDoubleCylinderVertex P A q z hqz S
          (oldX.2, Sum.inl (Sum.inr stored)) = fixedVertex) = true
        at hsuccessorQZ
      have hqz : P.qz q z = true := by
        obtain ⟨hqz, _⟩ := of_decide_eq_true hsuccessorQZ
        exact hqz
      have hmap : qToZDoubleCylinderVertex P A q z hqz S
          (oldX.2, Sum.inl (Sum.inr stored)) = fixedVertex := by
        obtain ⟨hqz', hmap⟩ := of_decide_eq_true hsuccessorQZ
        simpa only [Subsingleton.elim hqz' hqz] using hmap
      let inputBoundary : ZStarBoundaryEdge P z :=
        qToZBoundaryEdge P q z hqz stored
      let inputXQ := rzInputZBoundaryXQEdge P z inputBoundary
      let inputOwner := rzInputZBoundaryFaceOwner P A4 z inputBoundary
      have hinputX : inputXQ.1.1 = oldX.1 := by
        change stored.1 = oldX.1
        exact hdata.2
      have hownerX : P.faceX inputOwner.1.1.1 = oldX.1 :=
        (rzInputZBoundaryOwner_faceX P A4 z inputBoundary).trans hinputX
      have hownerQ : P.faceQ inputOwner.1.1.1 inputOwner.1.2 = q := by
        have h := rzInputZBoundaryOwner_faceQ P A4 z inputBoundary
        change P.faceQ inputOwner.1.1.1 inputOwner.1.2 = inputXQ.1.2 at h
        exact h
      have hedge : HEq
          (⟨P.faceX inputOwner.1.1.1,
            P.data.faceQ_xq inputOwner.1.1.1 inputOwner.1.2⟩ :
            QStarEdge (transposePresentation P)
              (P.faceQ inputOwner.1.1.1 inputOwner.1.2)) stored := by
        apply (Subtype.heq_iff_coe_eq (fun value => by rw [hownerQ])).2
        exact hownerX.trans hdata.2.symm
      let wrap : (Sigma fun q : P.Q =>
          QStarEdge (transposePresentation P) q) →
          (Sigma fun q : P.Q =>
            QDoubleCylinderVertex (transposePresentation P) q S) :=
        fun tagged => ⟨tagged.1,
          (oldX.2, Sum.inl (Sum.inr tagged.2))⟩
      have hSigmaEdge :
          (⟨P.faceQ inputOwner.1.1.1 inputOwner.1.2,
            (⟨P.faceX inputOwner.1.1.1,
              P.data.faceQ_xq inputOwner.1.1.1 inputOwner.1.2⟩ :
              QStarEdge (transposePresentation P)
                (P.faceQ inputOwner.1.1.1 inputOwner.1.2))⟩ :
            Sigma fun q : P.Q => QStarEdge (transposePresentation P) q) =
          ⟨q, stored⟩ := Sigma.ext hownerQ hedge
      have hSigmaVertex := congrArg wrap hSigmaEdge
      have hownerVertex : oldXFaceQ P S inputOwner.1.2
          (inputOwner.1.1.1, oldX.2) =
        Sum.inr ⟨q, (oldX.2, Sum.inl (Sum.inr stored))⟩ := by
        change Sum.inr (wrap ⟨P.faceQ inputOwner.1.1.1 inputOwner.1.2,
          (⟨P.faceX inputOwner.1.1.1,
            P.data.faceQ_xq inputOwner.1.1.1 inputOwner.1.2⟩ :
              QStarEdge (transposePresentation P)
                (P.faceQ inputOwner.1.1.1 inputOwner.1.2))⟩) =
          Sum.inr (wrap ⟨q, stored⟩)
        exact congrArg Sum.inr hSigmaVertex
      have hownerBaseZ : P.faceZ inputOwner.1.1.1 = z := by
        simpa [zStarFaceMember] using inputOwner.1.1.2
      have hfaceZ : oldXFaceZ P S (inputOwner.1.1.1, oldX.2) =
          ⟨z, fixedVertex⟩ := by
        let Source := { tagged : Sigma fun z : P.Z =>
            Sigma fun q : P.Q =>
              QDoubleCylinderVertex (transposePresentation P) q S //
          P.qz tagged.2.1 tagged.1 = true }
        let mapSource : Source →
            Sigma fun z : P.Z => ZDoubleCylinderVertex P z S :=
          fun source => ⟨source.1.1,
            qToZDoubleCylinderVertex P A source.1.2.1 source.1.1
              source.2 S source.1.2.2⟩
        let ownerSource : Source := ⟨⟨P.faceZ inputOwner.1.1.1,
          ⟨P.faceQ inputOwner.1.1.1 inputOwner.1.2,
            (oldX.2, Sum.inl (Sum.inr
              (⟨P.faceX inputOwner.1.1.1,
                P.data.faceQ_xq inputOwner.1.1.1 inputOwner.1.2⟩ :
                QStarEdge (transposePresentation P)
                  (P.faceQ inputOwner.1.1.1 inputOwner.1.2))))⟩⟩,
          P.data.faceQ_qz inputOwner.1.1.1 inputOwner.1.2⟩
        let requestedSource : Source :=
          ⟨⟨z, ⟨q, (oldX.2, Sum.inl (Sum.inr stored))⟩⟩, hqz⟩
        have hsource : ownerSource = requestedSource := by
          apply Subtype.ext
          apply Sigma.ext
          · exact hownerBaseZ
          · exact heq_of_eq hSigmaVertex
        have hownerMapped : oldXFaceZ P S
            (inputOwner.1.1.1, oldX.2) = mapSource ownerSource := by
          apply Sigma.ext
          · rfl
          · exact heq_of_eq (oldXFaceQ_maps_to_faceZ P A S
              inputOwner.1.1.1 oldX.2 inputOwner.1.2).symm
        have hrequestedMapped : mapSource requestedSource =
            ⟨z, fixedVertex⟩ := by
          apply Sigma.ext
          · rfl
          · exact heq_of_eq hmap
        exact hownerMapped.trans
          ((congrArg mapSource hsource).trans hrequestedMapped)
      let face : ZStarFace successor ⟨z, fixedVertex⟩ :=
        ⟨Sum.inr (Sum.inr (inputOwner.1.1.1, oldX.2)), by
          simp only [zStarFaceMember, decide_eq_true_eq]
          exact hfaceZ⟩
      refine ⟨⟨face, inputOwner.1.2⟩, ?_⟩
      apply Subtype.ext
      apply congrArg Sum.inl
      apply Subtype.ext
      apply Prod.ext
      · change Sum.inr (P.faceX inputOwner.1.1.1, oldX.2) =
          Sum.inr oldX
        exact congrArg Sum.inr (Prod.ext hownerX rfl)
      · exact hownerVertex
  · have himpossible : False := by
      change decide (Exists fun face : P.Face => Exists fun corner : Two =>
        P.faceX face = oldX.1 ∧
          oldXFaceQ P S corner (face, oldX.2) =
            Sum.inr ⟨q, (copy, Sum.inr interior)⟩) = true at incidence
      obtain ⟨face, corner, hfaceX, hq⟩ := of_decide_eq_true incidence
      change oldXFaceQ P S corner (face, oldX.2) =
        Sum.inr ⟨q, (copy, Sum.inr interior)⟩ at hq
      simp [oldXFaceQ] at hq
      cases hq.1
      have hvertex := eq_of_heq hq.2
      cases hvertex
    exact False.elim himpossible

/-- Total successor Z-boundary face owner.  Structural dispatch combines the
four frozen RZ V4 Z-boundary rows without changing ordered-corner semantics. -/
private noncomputable def rzReplacementZBoundaryFaceOwner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale)
    (fixedZ : (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S).Z)
    (edge : XQEdge (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S))
    (member : zStarEdgeMember (rzReplacementPresentation P
      A4.toTannerSquareAdmissible S) fixedZ (Sum.inl edge) = true) :
    {owner : ZStarFace (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) fixedZ × Two //
      zStarFaceXQEdge (rzReplacementPresentation P
        A4.toTannerSquareAdmissible S) fixedZ owner.1 owner.2 =
          ⟨Sum.inl edge, member⟩} := by
  rcases edge with ⟨⟨edgeX, edgeQ⟩, incidence⟩
  rcases edgeX with localOrGlue | oldX
  · rcases localOrGlue with localX | qEdge
    · rcases edgeQ with localEdge | qVertex
      · exact rzLocalZBoundaryFaceOwner P A4 S fixedZ localX localEdge
          incidence member
      · change false = true at incidence
        simp at incidence
    · rcases edgeQ with localEdge | qVertex
      · exact rzGlueZLocalBoundaryFaceOwner P A4 S fixedZ qEdge localEdge
          incidence member
      · exact rzGlueZQVertexBoundaryFaceOwner P A4 S fixedZ qEdge qVertex
          incidence member
  · rcases edgeQ with localEdge | qVertex
    · change false = true at incidence
      simp at incidence
    · exact rzOldXZBoundaryFaceOwner P A4 S fixedZ oldX qVertex
        incidence member

/-- The boundary-face-owner successor admissibility package.  Its V3
projection is exactly `rzReplacementAdmissibleV3`; the two new fields are the
complete structural X- and Z-boundary owner dispatchers above.  This
declaration makes no successor cellular-regularity claim. -/
noncomputable def rzReplacementAdmissibleV4
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) :
    TannerSquareAdmissibleV4
      (rzReplacementPresentation P A4.toTannerSquareAdmissible S) where
  toTannerSquareAdmissibleV3 := rzReplacementAdmissibleV3 P A4 R S
  xBoundaryFaceOwner := rzReplacementXBoundaryFaceOwner P A4 S
  zBoundaryFaceOwner := rzReplacementZBoundaryFaceOwner P A4 S

/-! ## Local RZ complexes and quotient coordinates -/

/-- The degree-zero local complex at an old X vertex consists of two isolated
points.  Its two coordinates are the cylinder-copy tags. -/
noncomputable def rzCx (P : TannerSquarePresentation) (_x : P.X) :
    ChainComplexData Field
      (Word Field Two) (Word Field (Fin 0)) (Word Field (Fin 0)) where
  boundary1 := 0
  boundary2 := 0
  boundary_squared := by simp

/-- The Q-local RZ complex is the degree-reversed cochain complex of the
explicit one-dimensional cylinder on the original X-Q neighborhood. -/
noncomputable def rzCq (P : TannerSquarePresentation) (q : P.Q) (S : OddScale) :
    ChainComplexData Field
      (Word Field (QDoubleCylinderEdge (transposePresentation P) q S))
      (Word Field (QDoubleCylinderVertex (transposePresentation P) q S))
      (Word Field (Fin 0)) where
  boundary1 := wordLinearMapTranspose
    (qDoubleCylinderBoundary1 (transposePresentation P) q S)
  boundary2 := 0
  boundary_squared := by simp

/-- The Z-local RZ complex is the degree reversal of the constructed Z-star
double-cylinder cellular chain complex. -/
noncomputable def rzCz (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) :
    ChainComplexData Field
      (Word Field (ZDoubleCylinderFace P z S))
      (Word Field (ZDoubleCylinderEdge P z S))
      (Word Field (ZDoubleCylinderVertex P z S)) :=
  zDoubleCylinderDualChainComplex P z S

/-- Total parity descends through a graph boundary. -/
noncomputable def graphCokernelParity {Vertex Edge : Type}
    [Fintype Vertex] [Fintype Edge] [DecidableEq Vertex]
    (edgeStart edgeEnd : Edge → Vertex) :
    (Word Field Vertex ⧸ LinearMap.range (graphBoundary edgeStart edgeEnd)) →ₗ[Field]
      Field :=
  (LinearMap.range (graphBoundary edgeStart edgeEnd)).liftQ totalParity (by
    rintro word ⟨chain, rfl⟩
    rw [LinearMap.mem_ker]
    exact totalParity_graphBoundary edgeStart edgeEnd chain)

@[simp] theorem graphCokernelParity_mk {Vertex Edge : Type}
    [Fintype Vertex] [Fintype Edge] [DecidableEq Vertex]
    (edgeStart edgeEnd : Edge → Vertex) (word : Word Field Vertex) :
    graphCokernelParity edgeStart edgeEnd
        ((LinearMap.range (graphBoundary edgeStart edgeEnd)).mkQ word) =
      totalParity word := rfl

/-- Constructive graph connectedness makes the parity coordinate a bijection
on the boundary quotient.  Representatives are used only inside the proof; no
quotient section is exported. -/
theorem graphCokernelParity_bijective {Vertex Edge : Type}
    [Fintype Vertex] [Fintype Edge] [DecidableEq Vertex] [DecidableEq Edge]
    (edgeStart edgeEnd : Edge → Vertex) (root : Vertex)
    (paths : ∀ vertex, UndirectedPath edgeStart edgeEnd root vertex) :
    Function.Bijective (graphCokernelParity edgeStart edgeEnd) := by
  classical
  have hrange : LinearMap.range (graphBoundary edgeStart edgeEnd) =
      LinearMap.ker totalParity :=
    graphBoundary_range_eq_totalParity_ker edgeStart edgeEnd root paths
  constructor
  · intro first
    refine Submodule.Quotient.induction_on
      (LinearMap.range (graphBoundary edgeStart edgeEnd)) first ?_
    intro firstWord second
    refine Submodule.Quotient.induction_on
      (LinearMap.range (graphBoundary edgeStart edgeEnd)) second ?_
    intro secondWord heq
    rw [Submodule.Quotient.eq, hrange, LinearMap.mem_ker]
    change totalParity firstWord = totalParity secondWord at heq
    rw [map_sub, heq, sub_self]
  · intro value
    refine ⟨(LinearMap.range (graphBoundary edgeStart edgeEnd)).mkQ
      (Pi.single root value), ?_⟩
    simp [graphCokernelParity, totalParity]

/-- The two old-X copy coordinates. -/
def rzCxCoordinates (word : Word Field Two) : Field × Field :=
  (word 0, word 1)

theorem rzCxCoordinates_bijective : Function.Bijective rzCxCoordinates := by
  constructor
  · intro first second h
    funext index
    fin_cases index
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  · rintro ⟨first, second⟩
    refine ⟨fun index => twoSelect first second index, ?_⟩
    ext <;> simp [rzCxCoordinates, twoSelect]

/-- Actual degree-zero cohomology of the concrete old-X block. -/
noncomputable abbrev RZXH0 (P : TannerSquarePresentation) (x : P.X) :=
  Word Field Two ⧸ LinearMap.range (rzCx P x).boundary1

/-- The raw two-copy coordinate map, before descending to cohomology. -/
def rzCxWordCoordinates : Word Field Two →ₗ[Field] Field × Field where
  toFun := rzCxCoordinates
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- The named F07 two-coordinate chart on actual degree-zero cohomology. -/
noncomputable def rzCxH0Coordinates (P : TannerSquarePresentation) (x : P.X) :
    RZXH0 P x →ₗ[Field] Field × Field :=
  (LinearMap.range (rzCx P x).boundary1).liftQ rzCxWordCoordinates (by
    intro boundary hboundary
    rcases hboundary with ⟨source, hsource⟩
    change boundary ∈ LinearMap.ker rzCxWordCoordinates
    rw [LinearMap.mem_ker]
    have hzero : (rzCx P x).boundary1 source = 0 := by
      simp [rzCx]
    have : boundary = 0 := by simpa [hzero] using hsource.symm
    simp [this, rzCxWordCoordinates, rzCxCoordinates])

@[simp] theorem rzCxH0Coordinates_mk (P : TannerSquarePresentation) (x : P.X)
    (word : Word Field Two) :
    rzCxH0Coordinates P x
        ((LinearMap.range (rzCx P x).boundary1).mkQ word) =
      (word 0, word 1) := rfl

/-- F07 `H⁰(Cx) = 𝔽₂²` as a named bijective coordinate map. -/
theorem rzCxH0Coordinates_bijective (P : TannerSquarePresentation) (x : P.X) :
    Function.Bijective (rzCxH0Coordinates P x) := by
  constructor
  · intro first
    refine Submodule.Quotient.induction_on _ first ?_
    intro firstWord second
    refine Submodule.Quotient.induction_on _ second ?_
    intro secondWord h
    rw [Submodule.Quotient.eq]
    have hwords : firstWord = secondWord := by
      funext index
      fin_cases index
      · exact congrArg Prod.fst h
      · exact congrArg Prod.snd h
    rw [hwords, sub_self]
    exact Submodule.zero_mem _
  · rintro ⟨first, second⟩
    let word : Word Field Two := fun index => twoSelect first second index
    refine ⟨(LinearMap.range (rzCx P x).boundary1).mkQ word, ?_⟩
    rw [rzCxH0Coordinates_mk]
    ext <;> simp [word, twoSelect]

/-- Concrete degree-one Q-local cohomology quotient. -/
abbrev RZQH1 (P : TannerSquarePresentation) (q : P.Q) (S : OddScale) :=
  Word Field (QDoubleCylinderVertex (transposePresentation P) q S) ⧸
    LinearMap.range
      (qDoubleCylinderBoundary1 (transposePresentation P) q S)

/-- The named F07 parity coordinate on Q-local cohomology. -/
noncomputable def rzCqH1Coordinate (P : TannerSquarePresentation)
    (q : P.Q) (S : OddScale) : RZQH1 P q S →ₗ[Field] Field :=
  graphCokernelParity
    (qDoubleCylinderEdgeStart (transposePresentation P) q S)
    (qDoubleCylinderEdgeEnd (transposePresentation P) q S)

theorem rzCqH1Coordinate_bijective (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q) (S : OddScale) :
    Function.Bijective (rzCqH1Coordinate P q S) :=
  graphCokernelParity_bijective
    (qDoubleCylinderEdgeStart (transposePresentation P) q S)
    (qDoubleCylinderEdgeEnd (transposePresentation P) q S)
    (0, Sum.inl (Sum.inl ()))
    (qDoubleCylinderPath (transposePresentation P)
      (transposeTannerSquareAdmissible P A) q S)

/-! ## Adjacent coordinate maps -/

/-- Sum coordinates along a concrete finite function. -/
noncomputable def wordPushforward {Source Target : Type}
    [Fintype Source] [Fintype Target] [DecidableEq Source] [DecidableEq Target]
    (map : Source → Target) : Word Field Source →ₗ[Field] Word Field Target :=
  Matrix.toLin' (fun target source => if target = map source then 1 else 0)

@[simp] theorem wordPushforward_apply {Source Target : Type}
    [Fintype Source] [Fintype Target] [DecidableEq Source] [DecidableEq Target]
    (map : Source → Target) (word : Word Field Source) (target : Target) :
    wordPushforward map word target =
      ∑ source : Source, if target = map source then word source else 0 := by
  classical
  change (∑ source : Source,
    (if target = map source then (1 : Field) else 0) * word source) = _
  simp only [ite_mul, one_mul, zero_mul]

/-- Finite pushforward preserves the total binary coordinate. -/
theorem totalParity_wordPushforward {Source Target : Type}
    [Fintype Source] [Fintype Target] [DecidableEq Source] [DecidableEq Target]
    (map : Source → Target) (word : Word Field Source) :
    totalParity (wordPushforward map word) = totalParity word := by
  classical
  simp only [totalParity_apply, wordPushforward_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro source _
  simp

@[simp] theorem wordPushforward_single {Source Target : Type}
    [Fintype Source] [Fintype Target] [DecidableEq Source] [DecidableEq Target]
    (map : Source → Target) (source : Source) (coefficient : Field) :
    wordPushforward map (Pi.single source coefficient) =
      Pi.single (map source) coefficient := by
  classical
  ext target
  rw [wordPushforward_apply, Fintype.sum_eq_single source]
  · by_cases h : target = map source
    · subst target
      simp only [Pi.single_eq_same]
      simp
    · simp only [Pi.single_apply]
      simp [h]
  · intro other hne
    rw [Pi.single_apply]
    simp [hne]

set_option maxHeartbeats 800000 in
/-- Pushforward commutes with graph boundaries when the endpoint tables
commute pointwise. -/
theorem wordPushforward_graphBoundary
    {SourceVertex SourceEdge TargetVertex TargetEdge : Type}
    [Fintype SourceVertex] [Fintype SourceEdge]
    [Fintype TargetVertex] [Fintype TargetEdge]
    [DecidableEq SourceVertex] [DecidableEq SourceEdge]
    [DecidableEq TargetVertex] [DecidableEq TargetEdge]
    (sourceStart sourceEnd : SourceEdge → SourceVertex)
    (targetStart targetEnd : TargetEdge → TargetVertex)
    (vertexMap : SourceVertex → TargetVertex)
    (edgeMap : SourceEdge → TargetEdge)
    (start_commutes : ∀ edge, targetStart (edgeMap edge) =
      vertexMap (sourceStart edge))
    (end_commutes : ∀ edge, targetEnd (edgeMap edge) =
      vertexMap (sourceEnd edge)) :
    (wordPushforward vertexMap).comp
        (graphBoundary sourceStart sourceEnd) =
      (graphBoundary targetStart targetEnd).comp
        (wordPushforward edgeMap) := by
  classical
  apply LinearMap.ext
  intro word
  rw [← word_eq_sum_single (F := Field) word]
  simp only [map_sum, LinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro edge _
  have hsingle : Pi.single edge (word edge) =
      word edge • Pi.single edge (1 : Field) := by
    ext other
    change (Pi.single edge (word edge) : Word Field SourceEdge) other =
      word edge * (Pi.single edge (1 : Field) : Word Field SourceEdge) other
    rw [Pi.single_apply, Pi.single_apply]
    by_cases h : other = edge <;> simp [h]
  rw [hsingle]
  simp only [map_smul]
  apply congrArg (fun value => word edge • value)
  rw [graphBoundary_single, graphEdgeBoundary, map_add,
    wordPushforward_single, wordPushforward_single,
    wordPushforward_single, graphBoundary_single, graphEdgeBoundary]
  rw [start_commutes edge, end_commutes edge]

/-- A copy bit is sent to the matching endpoint of the transposed Q-cylinder
for an actual old X-Q incidence. -/
def rzXQVertex (P : TannerSquarePresentation) (q : P.Q) (x : P.X)
    (hxq : P.xq x q = true) (S : OddScale) (copy : Two) :
    QDoubleCylinderVertex (transposePresentation P) q S :=
  (copy, Sum.inl (Sum.inr ⟨x, hxq⟩))

/-- The actual adjacent X-Q map on the nonzero local degree. -/
noncomputable def rzXQDegreeZero (P : TannerSquarePresentation)
    (q : P.Q) (x : P.X) (hxq : P.xq x q = true) (S : OddScale) :
    Word Field Two →ₗ[Field]
      Word Field (QDoubleCylinderVertex (transposePresentation P) q S) :=
  wordPushforward (rzXQVertex P q x hxq S)

/-- F09 X-Q coordinate formula: the two copy coordinates map by the
codiagonal. -/
theorem rzXQDegreeZero_totalParity (P : TannerSquarePresentation)
    (q : P.Q) (x : P.X) (hxq : P.xq x q = true) (S : OddScale)
    (word : Word Field Two) :
    totalParity (rzXQDegreeZero P q x hxq S word) =
      word 0 + word 1 := by
  rw [rzXQDegreeZero, totalParity_wordPushforward]
  change (∑ copy : Two, word copy) = _
  exact Fin.sum_univ_two word

/-- The actual adjacent Q-Z map on degree one is induced by the constructed
same-cell vertex embedding. -/
noncomputable def rzQZDegreeOne (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q) (z : P.Z)
    (hqz : P.qz q z = true) (S : OddScale) :
    Word Field (QDoubleCylinderVertex (transposePresentation P) q S) →ₗ[Field]
      Word Field (ZDoubleCylinderVertex P z S) := by
  classical
  exact wordPushforward (qToZDoubleCylinderVertex P A q z hqz S)

/-- The adjacent Q-Z map on degree zero uses the matching constructed edge
embedding. -/
noncomputable def rzQZDegreeZero (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q) (z : P.Z)
    (hqz : P.qz q z = true) (S : OddScale) :
    Word Field (QDoubleCylinderEdge (transposePresentation P) q S) →ₗ[Field]
      Word Field (ZDoubleCylinderEdge P z S) := by
  classical
  exact wordPushforward (qToZDoubleCylinderEdge P A q z hqz S)

/-- Endpoint boundary of the materialized Z-cylinder. -/
noncomputable def rzCzGraphBoundary (P : TannerSquarePresentation)
    (z : P.Z) (S : OddScale) :
    Word Field (ZDoubleCylinderEdge P z S) →ₗ[Field]
      Word Field (ZDoubleCylinderVertex P z S) := by
  classical
  exact graphBoundary
    (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
    (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)

theorem doubleCylinderBoundary1_single (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale)
    [DecidableEq (DoubleCylinderEdge P x S)]
    [DecidableEq (DoubleCylinderVertex P x S)]
    (edge : DoubleCylinderEdge P x S) :
    doubleCylinderBoundary1 P x S (Pi.single edge 1) =
      graphEdgeBoundary (tannerDoubleCylinderEdgeStart P x S)
        (tannerDoubleCylinderEdgeEnd P x S) edge := by
  classical
  ext vertex
  simp only [doubleCylinderBoundary1, Matrix.toLin'_apply,
    Matrix.mulVec, dotProduct]
  rw [Fintype.sum_eq_single edge]
  · rcases edge with ⟨copy, subdivisionEdge⟩ | boundaryVertex
    · rcases vertex with ⟨vertexCopy, vertexValue⟩
      fin_cases vertexCopy <;> fin_cases copy <;>
        simp [doubleCylinderEdgeVertexMatrix, subdivisionEdgeVertexMatrix,
        graphEdgeBoundary, tannerDoubleCylinderEdgeStart,
        tannerDoubleCylinderEdgeEnd, Pi.single_apply]
    · rcases vertex with ⟨vertexCopy, vertexValue⟩
      fin_cases vertexCopy <;>
        simp [doubleCylinderEdgeVertexMatrix, graphEdgeBoundary,
        tannerDoubleCylinderEdgeStart, tannerDoubleCylinderEdgeEnd,
        Pi.single_apply]
  · intro other hne
    simp [hne]

/-- The endpoint graph boundary is exactly the already constructed cellular
degree-one boundary, not a parallel chain-law assumption. -/
theorem rzCzGraphBoundary_eq_boundary1 (P : TannerSquarePresentation)
    (z : P.Z) (S : OddScale) :
    rzCzGraphBoundary P z S =
      doubleCylinderBoundary1 (transposePresentation P) z S := by
  classical
  apply LinearMap.ext
  intro word
  rw [← word_eq_sum_single (F := Field) word]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro edge _
  have hsingle : Pi.single edge (word edge) =
      word edge • Pi.single edge (1 : Field) := by
    ext other
    change (Pi.single edge (word edge) :
        Word Field (ZDoubleCylinderEdge P z S)) other =
      word edge * (Pi.single edge (1 : Field) :
        Word Field (ZDoubleCylinderEdge P z S)) other
    rw [Pi.single_apply, Pi.single_apply]
    by_cases h : other = edge <;> simp [h]
  rw [hsingle]
  simp only [map_smul]
  apply congrArg (fun value => word edge • value)
  erw [rzCzGraphBoundary, graphBoundary_single,
    doubleCylinderBoundary1_single]

/-- The actual top coboundary of `rzCz` is the materialized endpoint graph
boundary.  This is the concrete carrier bridge used by the F07 quotient. -/
theorem rzCzTopCoboundary_eq_graphBoundary (P : TannerSquarePresentation)
    (z : P.Z) (S : OddScale) :
    wordLinearMapTranspose (rzCz P z S).boundary2 =
      rzCzGraphBoundary P z S := by
  rw [rzCzGraphBoundary_eq_boundary1]
  simp [rzCz, zDoubleCylinderDualChainComplex,
    doubleCylinderDualChainComplex, doubleCylinderChainComplex,
    wordLinearMapTranspose_transpose]

/-- A Prop-valued connectedness witness is enough for binary graph exactness.
Each path is eliminated only while constructing the existential boundary
chain, so this lemma does not select or export a path family. -/
private theorem graphBoundary_range_eq_totalParity_ker_of_nonempty_paths
    {Vertex Edge : Type} [Fintype Vertex] [Fintype Edge]
    [DecidableEq Vertex] [DecidableEq Edge]
    (edgeStart edgeEnd : Edge → Vertex) (root : Vertex)
    (paths : ∀ vertex,
      Nonempty (UndirectedPath edgeStart edgeEnd root vertex)) :
    LinearMap.range (graphBoundary edgeStart edgeEnd) =
      LinearMap.ker totalParity := by
  classical
  ext word
  constructor
  · rintro ⟨chain, rfl⟩
    rw [LinearMap.mem_ker]
    exact totalParity_graphBoundary edgeStart edgeEnd chain
  · intro hword
    rw [LinearMap.mem_ker] at hword
    have hfinite : ∀ vertices : Finset Vertex,
        ∃ chain : Word Field Edge,
          graphBoundary edgeStart edgeEnd chain =
            ∑ vertex ∈ vertices,
              word vertex •
                (Pi.single root 1 + Pi.single vertex 1) := by
      intro vertices
      induction vertices using Finset.induction_on with
      | empty => exact ⟨0, by simp⟩
      | @insert vertex vertices hnot ih =>
          obtain ⟨previous, hprevious⟩ := ih
          obtain ⟨path⟩ := paths vertex
          refine ⟨previous + word vertex • pathChain path, ?_⟩
          rw [map_add, map_smul, hprevious,
            graphBoundary_pathChain edgeStart edgeEnd root]
          simp only [smul_add]
          rw [Finset.sum_insert hnot]
          abel
    obtain ⟨chain, hchain⟩ := hfinite Finset.univ
    refine ⟨chain, ?_⟩
    rw [hchain]
    simp only [smul_add, Finset.sum_add_distrib]
    have hroot :
        (∑ vertex : Vertex, word vertex • Pi.single root 1) =
          Pi.single root (totalParity word) := by
      ext vertex
      by_cases hvertex : vertex = root
      · subst vertex
        simp [totalParity]
      · simp [hvertex]
    have hdecomposition :
        (∑ vertex : Vertex, word vertex • Pi.single vertex 1) = word := by
      calc
        (∑ vertex : Vertex, word vertex • Pi.single vertex 1) =
            ∑ vertex : Vertex, Pi.single vertex (word vertex) := by
          apply Finset.sum_congr rfl
          intro vertex _
          ext target
          by_cases htarget : target = vertex
          · subst target
            simp
          · simp [htarget]
        _ = word := word_eq_sum_single (F := Field) word
    rw [hroot, hdecomposition, hword]
    simp

private def rzGridIndex (S : OddScale) (step : Nat)
    (hstep : step ≤ S.half) : Fin (S.half + 1) :=
  ⟨step, by omega⟩

/-- Horizontal prefixes in one materialized subdivision grid, retained only as
Prop-valued existence so no path family is exported. -/
private theorem subdivisionHorizontalPrefixPath_nonempty
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (step : Nat) (hstep : step ≤ S.half) :
    Nonempty (UndirectedPath (subdivisionEdgeStart P x S)
      (subdivisionEdgeEnd P x S)
      (subdivisionGridVertex P x S face 0 0)
      (subdivisionGridVertex P x S face (rzGridIndex S step hstep) 0)) := by
  induction step with
  | zero =>
      exact ⟨by simpa [rzGridIndex] using
        (UndirectedPath.nil : UndirectedPath
          (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S)
          (subdivisionGridVertex P x S face 0 0)
          (subdivisionGridVertex P x S face 0 0))⟩
  | succ previous ih =>
      have hprevious : previous ≤ S.half := by omega
      have hindex : previous < S.half := by omega
      obtain ⟨path⟩ := ih hprevious
      let index : Fin S.half := ⟨previous, hindex⟩
      let edge := subdivisionHorizontalEdge P x S face index (0 : Fin (S.half + 1))
      refine ⟨UndirectedPath.step (by
          simpa [rzGridIndex, index] using path) edge ?_⟩
      apply Or.inl
      constructor
      · exact subdivisionHorizontalEdge_start P x S face index
            (0 : Fin (S.half + 1))
      · exact subdivisionHorizontalEdge_end P x S face index
            (0 : Fin (S.half + 1))

/-- Vertical prefixes start at the horizontal endpoint and stay inside the
same explicit rectangle grid. -/
private theorem subdivisionVerticalPrefixPath_nonempty
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (i : Fin (S.half + 1))
    (step : Nat) (hstep : step ≤ S.half) :
    Nonempty (UndirectedPath (subdivisionEdgeStart P x S)
      (subdivisionEdgeEnd P x S)
      (subdivisionGridVertex P x S face i 0)
      (subdivisionGridVertex P x S face i (rzGridIndex S step hstep))) := by
  induction step with
  | zero =>
      exact ⟨by simpa [rzGridIndex] using
        (UndirectedPath.nil : UndirectedPath
          (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S)
          (subdivisionGridVertex P x S face i 0)
          (subdivisionGridVertex P x S face i 0))⟩
  | succ previous ih =>
      have hprevious : previous ≤ S.half := by omega
      have hindex : previous < S.half := by omega
      obtain ⟨path⟩ := ih hprevious
      let index : Fin S.half := ⟨previous, hindex⟩
      let edge := subdivisionVerticalEdge P x S face i index
      refine ⟨UndirectedPath.step (by
          simpa [rzGridIndex, index] using path) edge ?_⟩
      apply Or.inl
      constructor
      · exact subdivisionVerticalEdge_start P x S face i index
      · exact subdivisionVerticalEdge_end P x S face i index

/-- Every tagged grid point is connected to its face's old-X corner. -/
private theorem subdivisionGridPath_nonempty
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (i j : Fin (S.half + 1)) :
    Nonempty (UndirectedPath (subdivisionEdgeStart P x S)
      (subdivisionEdgeEnd P x S)
      (subdivisionGridVertex P x S face 0 0)
      (subdivisionGridVertex P x S face i j)) := by
  have hi : i.1 ≤ S.half := by omega
  have hj : j.1 ≤ S.half := by omega
  obtain ⟨horizontal⟩ :=
    subdivisionHorizontalPrefixPath_nonempty P x S face i.1 hi
  obtain ⟨vertical⟩ :=
    subdivisionVerticalPrefixPath_nonempty P x S face i j.1 hj
  have horizontal' : UndirectedPath (subdivisionEdgeStart P x S)
      (subdivisionEdgeEnd P x S)
      (subdivisionGridVertex P x S face 0 0)
      (subdivisionGridVertex P x S face i 0) := by
    simpa [rzGridIndex] using horizontal
  have vertical' : UndirectedPath (subdivisionEdgeStart P x S)
      (subdivisionEdgeEnd P x S)
      (subdivisionGridVertex P x S face i 0)
      (subdivisionGridVertex P x S face i j) := by
    simpa [rzGridIndex] using vertical
  exact ⟨horizontal'.append vertical'⟩

private def rzGridLast (S : OddScale) : Fin (S.half + 1) :=
  ⟨S.half, by omega⟩

private def rzSubdivisionCenter (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) : SubdivisionVertex P x S :=
  Sum.inl ⟨Vertex.x x, by simp [xStarVertexMember]⟩

/-- Original star vertices are reached inside one incident face.  The only
extra input is one already-existing face for the center case. -/
private theorem subdivisionOriginalVertexPath_nonempty
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face0 : XStarFace P x) (vertex : XStarVertex P x) :
    Nonempty (UndirectedPath (subdivisionEdgeStart P x S)
      (subdivisionEdgeEnd P x S) (rzSubdivisionCenter P x S)
      (Sum.inl vertex)) := by
  rcases vertex with ⟨value, hvalue⟩
  rcases value with oldX | q | z
  · simp only [xStarVertexMember, decide_eq_true_eq] at hvalue
    subst oldX
    have hxface : P.faceX face0.1 = x := by
      simpa [xStarFaceMember] using face0.2
    obtain ⟨path⟩ := subdivisionGridPath_nonempty P x S face0 0 0
    exact ⟨by simpa [rzSubdivisionCenter, subdivisionGridVertex,
      xStarFaceXVertex, hxface] using path⟩
  · simp only [xStarVertexMember, decide_eq_true_eq] at hvalue
    obtain ⟨faceValue, hface, hq | hq⟩ := hvalue
    · subst q
      let face : XStarFace P x := ⟨faceValue, hface⟩
      have hxface : P.faceX faceValue = x := by
        simpa [xStarFaceMember] using hface
      obtain ⟨path⟩ := subdivisionGridPath_nonempty P x S face
        (rzGridLast S) 0
      exact ⟨by simpa [rzSubdivisionCenter, rzGridLast,
        subdivisionGridVertex, xStarFaceXVertex, xStarFaceQVertex,
        face, hxface, S.half_pos.ne']
        using path⟩
    · subst q
      let face : XStarFace P x := ⟨faceValue, hface⟩
      have hxface : P.faceX faceValue = x := by
        simpa [xStarFaceMember] using hface
      obtain ⟨path⟩ := subdivisionGridPath_nonempty P x S face
        0 (rzGridLast S)
      exact ⟨by simpa [rzSubdivisionCenter, rzGridLast,
        subdivisionGridVertex, xStarFaceXVertex, xStarFaceQVertex,
        face, hxface, S.half_pos.ne']
        using path⟩
  · simp only [xStarVertexMember, decide_eq_true_eq] at hvalue
    obtain ⟨faceValue, hface, hz⟩ := hvalue
    subst z
    let face : XStarFace P x := ⟨faceValue, hface⟩
    have hxface : P.faceX faceValue = x := by
      simpa [xStarFaceMember] using hface
    obtain ⟨path⟩ := subdivisionGridPath_nonempty P x S face
      (rzGridLast S) (rzGridLast S)
    exact ⟨by simpa [rzSubdivisionCenter, rzGridLast,
      subdivisionGridVertex, xStarFaceXVertex, xStarFaceQVertex,
      xStarFaceZVertex, face, hxface, S.half_pos.ne']
      using path⟩

private def rzSubdivisionSegmentVertex
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : XStarEdge P x) (step : Nat) (hstep : step ≤ S.half) :
    SubdivisionVertex P x S :=
  if hzero : step = 0 then
    Sum.inl (xStarEdgeStart P x edge)
  else if hlast : step = S.half then
    Sum.inl (xStarEdgeEnd P x edge)
  else
    Sum.inr (Sum.inl (edge, ⟨step - 1, by omega⟩))

private theorem subdivisionSegmentPrefixPath_nonempty
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : XStarEdge P x) (step : Nat) (hstep : step ≤ S.half) :
    Nonempty (UndirectedPath (subdivisionEdgeStart P x S)
      (subdivisionEdgeEnd P x S) (Sum.inl (xStarEdgeStart P x edge))
      (rzSubdivisionSegmentVertex P x S edge step hstep)) := by
  induction step with
  | zero => exact ⟨UndirectedPath.nil⟩
  | succ previous ih =>
      have hprevious : previous ≤ S.half := by omega
      have hindex : previous < S.half := by omega
      obtain ⟨path⟩ := ih hprevious
      let index : Fin S.half := ⟨previous, hindex⟩
      refine ⟨UndirectedPath.step (by
          simpa [rzSubdivisionSegmentVertex, index] using path)
        (Sum.inl (edge, index)) ?_⟩
      apply Or.inl
      constructor
      · have hnotlast : previous ≠ S.half := by omega
        simp [subdivisionEdgeStart, subdivisionSegmentStart,
          index, hnotlast]
      · simp [subdivisionEdgeEnd, subdivisionSegmentEnd,
          rzSubdivisionSegmentVertex, index]

/-- Every full subdivision vertex is connected to the old-star center. -/
private theorem subdivisionVertexPath_nonempty
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face0 : XStarFace P x) (vertex : SubdivisionVertex P x S) :
    Nonempty (UndirectedPath (subdivisionEdgeStart P x S)
      (subdivisionEdgeEnd P x S) (rzSubdivisionCenter P x S) vertex) := by
  rcases vertex with original | remaining
  · exact subdivisionOriginalVertexPath_nonempty P x S face0 original
  · rcases remaining with edgeInterior | faceInterior
    · rcases edgeInterior with ⟨edge, index⟩
      obtain ⟨toStart⟩ := subdivisionOriginalVertexPath_nonempty
        P x S face0 (xStarEdgeStart P x edge)
      have hstep : index.1 + 1 ≤ S.half := by
        have := index.2
        have := S.half_pos
        omega
      obtain ⟨alongEdge⟩ := subdivisionSegmentPrefixPath_nonempty
        P x S edge (index.1 + 1) hstep
      have hzero : index.1 + 1 ≠ 0 := by omega
      have hlast : index.1 + 1 ≠ S.half := by
        have := index.2
        omega
      exact ⟨toStart.append (by simpa [rzSubdivisionSegmentVertex,
        hzero, hlast] using alongEdge)⟩
    · rcases faceInterior with ⟨face, i, j⟩
      have hxface : P.faceX face.1 = x := by
        simpa [xStarFaceMember] using face.2
      have hi0 : i.1 + 1 ≠ 0 := by omega
      have hj0 : j.1 + 1 ≠ 0 := by omega
      have hilast : i.1 + 1 ≠ S.half := by
        have := i.2
        omega
      have hjlast : j.1 + 1 ≠ S.half := by
        have := j.2
        omega
      obtain ⟨path⟩ := subdivisionGridPath_nonempty P x S face
        ⟨i.1 + 1, by have := i.2; have := S.half_pos; omega⟩
        ⟨j.1 + 1, by have := j.2; have := S.half_pos; omega⟩
      simp only [rzSubdivisionCenter, subdivisionGridVertex,
        xStarFaceXVertex, hxface, hi0, hj0, hilast, hjlast,
        if_false, if_true] at path ⊢
      exact ⟨path⟩

private theorem admissibleXBoundary_has_face
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (x : P.X) :
    Nonempty (XStarFace P x) := by
  rcases A.xBoundaryRoot x with ⟨value, hboundary⟩
  rcases value with oldX | q | z
  · simp [xStarBoundaryVertexMember] at hboundary
  · simp only [xStarBoundaryVertexMember, decide_eq_true_eq] at hboundary
    obtain ⟨face, hface, _⟩ := hboundary
    exact ⟨⟨face, hface⟩⟩
  · simp only [xStarBoundaryVertexMember, decide_eq_true_eq] at hboundary
    obtain ⟨face, hface, _⟩ := hboundary
    exact ⟨⟨face, hface⟩⟩

private theorem subdivisionPathAtCopy_nonempty
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face0 : XStarFace P x) (copy : Two)
    (vertex : SubdivisionVertex P x S) :
    Nonempty (UndirectedPath (tannerDoubleCylinderEdgeStart P x S)
      (tannerDoubleCylinderEdgeEnd P x S)
      (copy, rzSubdivisionCenter P x S) (copy, vertex)) := by
  obtain ⟨path⟩ := subdivisionVertexPath_nonempty P x S face0 vertex
  exact ⟨UndirectedPath.map
    (edgeStart := subdivisionEdgeStart P x S)
    (edgeEnd := subdivisionEdgeEnd P x S)
    (edgeStart' := tannerDoubleCylinderEdgeStart P x S)
    (edgeEnd' := tannerDoubleCylinderEdgeEnd P x S)
    (fun subdivisionVertex => (copy, subdivisionVertex))
    (fun subdivisionEdge => Sum.inl (copy, subdivisionEdge))
    (fun _ => rfl) (fun _ => rfl) path⟩

/-- The full double cylinder is connected in the Prop fragment.  The bridge
uses only the already registered admissible boundary root. -/
private theorem doubleCylinderPath_nonempty
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (vertex : DoubleCylinderVertex P x S) :
    Nonempty (UndirectedPath (tannerDoubleCylinderEdgeStart P x S)
      (tannerDoubleCylinderEdgeEnd P x S)
      (0, rzSubdivisionCenter P x S) vertex) := by
  obtain ⟨face0⟩ := admissibleXBoundary_has_face P A x
  rcases vertex with ⟨copy, vertex⟩
  fin_cases copy
  · exact subdivisionPathAtCopy_nonempty P x S face0 0 vertex
  · let boundaryVertex : SubdivisionBoundaryVertex P x S :=
      subdivisionOriginalBoundaryVertex P x S (A.xBoundaryRoot x)
    obtain ⟨toBoundaryZero⟩ := subdivisionPathAtCopy_nonempty
      P x S face0 0 boundaryVertex.1
    obtain ⟨toBoundaryOne⟩ := subdivisionPathAtCopy_nonempty
      P x S face0 1 boundaryVertex.1
    obtain ⟨toVertexOne⟩ := subdivisionPathAtCopy_nonempty
      P x S face0 1 vertex
    let bridge : UndirectedPath (tannerDoubleCylinderEdgeStart P x S)
        (tannerDoubleCylinderEdgeEnd P x S)
        (0, boundaryVertex.1) (1, boundaryVertex.1) :=
      .step .nil (Sum.inr boundaryVertex) (Or.inl ⟨rfl, rfl⟩)
    exact ⟨toBoundaryZero.append
      (bridge.append (toBoundaryOne.reverse.append toVertexOne))⟩

/-- Actual degree-two cohomology of the concrete dual Z block. -/
noncomputable abbrev RZZH2 (P : TannerSquarePresentation) (z : P.Z)
    (S : OddScale) :=
  Word Field (ZDoubleCylinderVertex P z S) ⧸
    LinearMap.range (wordLinearMapTranspose (rzCz P z S).boundary2)

/-- The named F07 parity coordinate on actual degree-two cohomology. -/
noncomputable def rzCzH2Coordinate (P : TannerSquarePresentation)
    (z : P.Z) (S : OddScale) : RZZH2 P z S →ₗ[Field] Field :=
  by
    classical
    exact (LinearMap.range
      (wordLinearMapTranspose (rzCz P z S).boundary2)).liftQ totalParity (by
      intro boundary hboundary
      rcases hboundary with ⟨chain, rfl⟩
      rw [LinearMap.mem_ker, rzCzTopCoboundary_eq_graphBoundary]
      exact totalParity_graphBoundary
        (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
        (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S) chain)

@[simp] theorem rzCzH2Coordinate_mk (P : TannerSquarePresentation)
    (z : P.Z) (S : OddScale)
    (word : Word Field (ZDoubleCylinderVertex P z S)) :
    rzCzH2Coordinate P z S
        ((LinearMap.range
          (wordLinearMapTranspose (rzCz P z S).boundary2)).mkQ word) =
      totalParity word := rfl

/-- The parity chart is always onto: an existing admissible boundary root gives
one concrete cylinder vertex on which to place the requested coefficient. -/
theorem rzCzH2Coordinate_surjective (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (z : P.Z) (S : OddScale) :
    Function.Surjective (rzCzH2Coordinate P z S) := by
  classical
  let boundaryRoot :
      XStarBoundaryVertex (transposePresentation P) z :=
    (transposeTannerSquareAdmissible P A).xBoundaryRoot z
  let root : ZDoubleCylinderVertex P z S :=
    (0, (subdivisionOriginalBoundaryVertex
      (transposePresentation P) z S boundaryRoot).1)
  intro value
  refine ⟨(LinearMap.range
    (wordLinearMapTranspose (rzCz P z S).boundary2)).mkQ
      (Pi.single root value), ?_⟩
  rw [rzCzH2Coordinate_mk]
  simp [totalParity, root]

/-- Exact reduction of the remaining F07 injectivity obligation.  Quotient
extensionality proves injectivity precisely when the concrete top coboundary
fills the even-parity kernel; no representative selector is introduced. -/
theorem rzCzH2Coordinate_injective_iff_range_eq_totalParity_ker
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) :
    Function.Injective (rzCzH2Coordinate P z S) ↔
      LinearMap.range (wordLinearMapTranspose (rzCz P z S).boundary2) =
        LinearMap.ker totalParity := by
  classical
  let boundary := wordLinearMapTranspose (rzCz P z S).boundary2
  have hrange_le : LinearMap.range boundary ≤ LinearMap.ker totalParity := by
    rintro word ⟨chain, rfl⟩
    rw [LinearMap.mem_ker]
    change totalParity
      (wordLinearMapTranspose (rzCz P z S).boundary2 chain) = 0
    rw [rzCzTopCoboundary_eq_graphBoundary]
    exact totalParity_graphBoundary
      (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S) chain
  constructor
  · intro hinjective
    apply le_antisymm hrange_le
    intro word hword
    rw [LinearMap.mem_ker] at hword
    have heq :
        rzCzH2Coordinate P z S
            ((LinearMap.range boundary).mkQ word) =
          rzCzH2Coordinate P z S
            ((LinearMap.range boundary).mkQ 0) := by
      change totalParity word = totalParity (0 :
        Word Field (ZDoubleCylinderVertex P z S))
      simpa using hword
    have hquotient := hinjective heq
    have hzero : (LinearMap.range boundary).mkQ word = 0 := by
      simpa using hquotient
    exact (Submodule.Quotient.mk_eq_zero
      (LinearMap.range boundary)).1 hzero
  · intro hrange first
    refine Submodule.Quotient.induction_on _ first ?_
    intro firstWord
    intro second
    refine Submodule.Quotient.induction_on _ second ?_
    intro secondWord heq
    rw [Submodule.Quotient.eq, hrange, LinearMap.mem_ker]
    change totalParity firstWord = totalParity secondWord at heq
    rw [map_sub, heq, sub_self]

/-- Consequently the exact F07 `H²(Cz) ≃ ᵓ₂` statement is equivalent to
the one remaining concrete graph-exactness equality. -/
theorem rzCzH2Coordinate_bijective_iff_range_eq_totalParity_ker
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (z : P.Z) (S : OddScale) :
    Function.Bijective (rzCzH2Coordinate P z S) ↔
      LinearMap.range (wordLinearMapTranspose (rzCz P z S).boundary2) =
        LinearMap.ker totalParity := by
  constructor
  · intro hbijective
    exact (rzCzH2Coordinate_injective_iff_range_eq_totalParity_ker
      P z S).1 hbijective.1
  · intro hrange
    exact ⟨(rzCzH2Coordinate_injective_iff_range_eq_totalParity_ker
      P z S).2 hrange, rzCzH2Coordinate_surjective P A z S⟩

/-- The materialized Z-cylinder top coboundary fills exactly the even-parity
words.  Connectivity is assembled locally from rectangle segments and the
existing admissible boundary root; no path selector is retained. -/
theorem rzCzTopCoboundary_range_eq_totalParity_ker
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (z : P.Z) (S : OddScale) :
    LinearMap.range (wordLinearMapTranspose (rzCz P z S).boundary2) =
      LinearMap.ker totalParity := by
  classical
  rw [rzCzTopCoboundary_eq_graphBoundary]
  exact graphBoundary_range_eq_totalParity_ker_of_nonempty_paths
    (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
    (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
    (0, rzSubdivisionCenter (transposePresentation P) z S)
    (doubleCylinderPath_nonempty (transposePresentation P)
      (transposeTannerSquareAdmissible P A) z S)

/-- Exact F07 degree-two chart for the concrete dual Z block. -/
theorem rzCzH2Coordinate_bijective
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (z : P.Z) (S : OddScale) :
    Function.Bijective (rzCzH2Coordinate P z S) :=
  (rzCzH2Coordinate_bijective_iff_range_eq_totalParity_ker P A z S).2
    (rzCzTopCoboundary_range_eq_totalParity_ker P A z S)

/-- The two adjacent Q-Z coordinate maps commute with their explicit endpoint
boundaries. -/
theorem rzQZ_graph_commutes (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q) (z : P.Z)
    (hqz : P.qz q z = true) (S : OddScale) :
    (rzQZDegreeOne P A q z hqz S).comp
        (qDoubleCylinderBoundary1 (transposePresentation P) q S) =
      (rzCzGraphBoundary P z S).comp
        (rzQZDegreeZero P A q z hqz S) := by
  classical
  exact wordPushforward_graphBoundary
    (qDoubleCylinderEdgeStart (transposePresentation P) q S)
    (qDoubleCylinderEdgeEnd (transposePresentation P) q S)
    (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
    (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
    (qToZDoubleCylinderVertex P A q z hqz S)
    (qToZDoubleCylinderEdge P A q z hqz S)
    (fun edge => (qToZDoubleCylinderEdge_start P A q z hqz S edge).symm)
    (fun edge => (qToZDoubleCylinderEdge_end P A q z hqz S edge).symm)

/-- Adjacent Q-Z commutation for the actual cellular boundary of `rzCz`. -/
theorem rzQZ_commutes (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q) (z : P.Z)
    (hqz : P.qz q z = true) (S : OddScale) :
    (rzQZDegreeOne P A q z hqz S).comp
        (qDoubleCylinderBoundary1 (transposePresentation P) q S) =
      (doubleCylinderBoundary1 (transposePresentation P) z S).comp
        (rzQZDegreeZero P A q z hqz S) := by
  rw [← rzCzGraphBoundary_eq_boundary1]
  exact rzQZ_graph_commutes P A q z hqz S

/-- F09 Q-Z coordinate formula: total parity is unchanged. -/
theorem rzQZDegreeOne_totalParity (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q) (z : P.Z)
    (hqz : P.qz q z = true) (S : OddScale)
    (word : Word Field (QDoubleCylinderVertex (transposePresentation P) q S)) :
    totalParity (rzQZDegreeOne P A q z hqz S word) = totalParity word := by
  classical
  exact totalParity_wordPushforward _ word

/-- The concrete degree-one X-Q restriction.  The source `rzCx` block has no
degree-one cells, so this is the unique map out of its `Fin 0` carrier. -/
noncomputable def rzXQDegreeOne (P : TannerSquarePresentation)
    (q : P.Q) (_x : P.X) (_hxq : P.xq _x q = true) (S : OddScale) :
    Word Field (Fin 0) →ₗ[Field]
      Word Field (QDoubleCylinderEdge (transposePresentation P) q S) := 0

/-- Adjacent X-Q commutation for the actual local boundaries.  The source
boundary is the concrete boundary of `rzCx`, and the target is the concrete
Q-cylinder graph boundary used by `rzCq`. -/
theorem rzXQ_commutes (P : TannerSquarePresentation)
    (q : P.Q) (x : P.X) (hxq : P.xq x q = true) (S : OddScale) :
    (rzXQDegreeZero P q x hxq S).comp (rzCx P x).boundary1 =
      (qDoubleCylinderBoundary1 (transposePresentation P) q S).comp
        (rzXQDegreeOne P q x hxq S) := by
  simp [rzCx, rzXQDegreeOne]

/-! ## Restriction-induced F09 quotient maps -/

/-- The actual X-Q restriction descends from the concrete degree-zero block
to the concrete Q-block quotient. -/
noncomputable def rzXQH0ToH1 (P : TannerSquarePresentation)
    (q : P.Q) (x : P.X) (hxq : P.xq x q = true) (S : OddScale) :
    RZXH0 P x →ₗ[Field] RZQH1 P q S := by
  classical
  let targetQ := LinearMap.range
    (qDoubleCylinderBoundary1 (transposePresentation P) q S)
  exact (LinearMap.range (rzCx P x).boundary1).liftQ
    (targetQ.mkQ.comp (rzXQDegreeZero P q x hxq S)) (by
      intro boundary hboundary
      rcases hboundary with ⟨source, rfl⟩
      rw [LinearMap.mem_ker]
      change targetQ.mkQ
          (rzXQDegreeZero P q x hxq S ((rzCx P x).boundary1 source)) = 0
      apply (Submodule.Quotient.mk_eq_zero targetQ).2
      refine ⟨rzXQDegreeOne P q x hxq S source, ?_⟩
      exact congrArg (fun map => map source)
        (rzXQ_commutes P q x hxq S).symm)

@[simp] theorem rzXQH0ToH1_mk (P : TannerSquarePresentation)
    (q : P.Q) (x : P.X) (hxq : P.xq x q = true) (S : OddScale)
    (word : Word Field Two) :
    rzXQH0ToH1 P q x hxq S
        ((LinearMap.range (rzCx P x).boundary1).mkQ word) =
      (LinearMap.range
        (qDoubleCylinderBoundary1 (transposePresentation P) q S)).mkQ
        (rzXQDegreeZero P q x hxq S word) := rfl

/-- F09 X-Q quotient-coordinate formula: the induced map is the codiagonal
in the named F07 charts. -/
theorem rzXQH0ToH1_coordinate (P : TannerSquarePresentation)
    (q : P.Q) (x : P.X) (hxq : P.xq x q = true) (S : OddScale)
    (cohomologyClass : RZXH0 P x) :
    rzCqH1Coordinate P q S
        (rzXQH0ToH1 P q x hxq S cohomologyClass) =
      (rzCxH0Coordinates P x cohomologyClass).1 +
        (rzCxH0Coordinates P x cohomologyClass).2 := by
  refine Submodule.Quotient.induction_on _ cohomologyClass ?_
  intro word
  change rzCqH1Coordinate P q S
      (rzXQH0ToH1 P q x hxq S
        ((LinearMap.range (rzCx P x).boundary1).mkQ word)) =
    (rzCxH0Coordinates P x
      ((LinearMap.range (rzCx P x).boundary1).mkQ word)).1 +
      (rzCxH0Coordinates P x
        ((LinearMap.range (rzCx P x).boundary1).mkQ word)).2
  rw [rzXQH0ToH1_mk, rzCxH0Coordinates_mk]
  change totalParity (rzXQDegreeZero P q x hxq S word) =
    word 0 + word 1
  exact rzXQDegreeZero_totalParity P q x hxq S word

/-- The actual Q-Z restriction descends through both concrete coboundary
ranges; its well-definedness is the previously proved cellular commutation. -/
noncomputable def rzQZH1ToH2 (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q) (z : P.Z)
    (hqz : P.qz q z = true) (S : OddScale) :
    RZQH1 P q S →ₗ[Field] RZZH2 P z S := by
  classical
  let targetQ := LinearMap.range
    (wordLinearMapTranspose (rzCz P z S).boundary2)
  exact (LinearMap.range
    (qDoubleCylinderBoundary1 (transposePresentation P) q S)).liftQ
      (targetQ.mkQ.comp (rzQZDegreeOne P A q z hqz S)) (by
        intro boundary hboundary
        rcases hboundary with ⟨source, rfl⟩
        rw [LinearMap.mem_ker]
        change targetQ.mkQ
            (rzQZDegreeOne P A q z hqz S
              (qDoubleCylinderBoundary1
                (transposePresentation P) q S source)) = 0
        apply (Submodule.Quotient.mk_eq_zero targetQ).2
        refine ⟨rzQZDegreeZero P A q z hqz S source, ?_⟩
        rw [rzCzTopCoboundary_eq_graphBoundary]
        exact congrArg (fun map => map source)
          (rzQZ_graph_commutes P A q z hqz S).symm)

@[simp] theorem rzQZH1ToH2_mk (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q) (z : P.Z)
    (hqz : P.qz q z = true) (S : OddScale)
    (word : Word Field
      (QDoubleCylinderVertex (transposePresentation P) q S)) :
    rzQZH1ToH2 P A q z hqz S
        ((LinearMap.range
          (qDoubleCylinderBoundary1 (transposePresentation P) q S)).mkQ word) =
      (LinearMap.range
        (wordLinearMapTranspose (rzCz P z S).boundary2)).mkQ
        (rzQZDegreeOne P A q z hqz S word) := rfl

/-- F09 Q-Z quotient-coordinate formula: the induced map is the identity in
the named parity charts. -/
theorem rzQZH1ToH2_coordinate (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q) (z : P.Z)
    (hqz : P.qz q z = true) (S : OddScale)
    (cohomologyClass : RZQH1 P q S) :
    rzCzH2Coordinate P z S
        (rzQZH1ToH2 P A q z hqz S cohomologyClass) =
      rzCqH1Coordinate P q S cohomologyClass := by
  refine Submodule.Quotient.induction_on _ cohomologyClass ?_
  intro word
  change rzCzH2Coordinate P z S
      (rzQZH1ToH2 P A q z hqz S
        ((LinearMap.range
          (qDoubleCylinderBoundary1
            (transposePresentation P) q S)).mkQ word)) =
    rzCqH1Coordinate P q S
      ((LinearMap.range
        (qDoubleCylinderBoundary1
          (transposePresentation P) q S)).mkQ word)
  rw [rzQZH1ToH2_mk, rzCzH2Coordinate_mk]
  change totalParity (rzQZDegreeOne P A q z hqz S word) =
    totalParity word
  exact rzQZDegreeOne_totalParity P A q z hqz S word

/-! ## Aggregate F07/F09 coordinate diagram -/

/-- The concrete bottom coboundary of the Q-local dual block is the original
Q-cylinder graph boundary.  This keeps the auxiliary `H⁰(Cq)` carrier tied to
the actual local complex rather than introducing a parallel kernel. -/
theorem rzCqBottomCoboundary_eq_boundary1 (P : TannerSquarePresentation)
    (q : P.Q) (S : OddScale) :
    wordLinearMapTranspose (rzCq P q S).boundary1 =
      qDoubleCylinderBoundary1 (transposePresentation P) q S := by
  simp [rzCq, qDoubleCylinderBoundary1,
    wordLinearMapTranspose_transpose]

/-- Actual auxiliary degree-zero cohomology carrier of the Q-local block.
There is no incoming degree, so this is the kernel of its concrete bottom
coboundary. -/
noncomputable abbrev RZQH0 (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) :=
  LinearMap.ker (wordLinearMapTranspose (rzCq P q S).boundary1)

/-- Actual auxiliary degree-zero cohomology carrier of the Z-local block. -/
noncomputable abbrev RZZH0 (P : TannerSquarePresentation) (z : P.Z)
    (S : OddScale) :=
  LinearMap.ker (wordLinearMapTranspose (rzCz P z S).boundary1)

/-- The full source-side degree-zero local-cohomology carrier in the order of
the source diagram: Z auxiliaries, the two-copy X summand, then Q auxiliaries. -/
noncomputable abbrev RZLocalH0 (P : TannerSquarePresentation) (S : OddScale) :=
  (∀ z : P.Z, RZZH0 P z S) ×
    (∀ x : P.X, RZXH0 P x) ×
      (∀ q : P.Q, RZQH0 P q S)

/-- Aggregate nonzero degree-one local-cohomology carrier. -/
abbrev RZLocalH1 (P : TannerSquarePresentation) (S : OddScale) :=
  ∀ q : P.Q, RZQH1 P q S

/-- Aggregate nonzero degree-two local-cohomology carrier. -/
abbrev RZLocalH2 (P : TannerSquarePresentation) (S : OddScale) :=
  ∀ z : P.Z, RZZH2 P z S

/-- The source codiagonal `Δ′ : ᵓ₂² → ᵓ₂`. -/
def rzCodiagonal : Field × Field →ₗ[Field] Field where
  toFun := fun pair => pair.1 + pair.2
  map_add' := by intros; simp [add_assoc, add_left_comm, add_comm]
  map_smul' := by intros; simp [mul_add]

@[simp] theorem rzCodiagonal_left (value : Field) :
    rzCodiagonal (value, 0) = value := by simp [rzCodiagonal]

@[simp] theorem rzCodiagonal_right (value : Field) :
    rzCodiagonal (0, value) = value := by simp [rzCodiagonal]

/-- Pointwise codiagonal on the old X layer. -/
def rzPointwiseCodiagonal (P : TannerSquarePresentation) :
    (P.X → Field × Field) →ₗ[Field] Word Field P.X where
  toFun := fun coordinates x => rzCodiagonal (coordinates x)
  map_add' := by intros; funext x; exact map_add rzCodiagonal _ _
  map_smul' := by intros; funext x; exact map_smul rzCodiagonal _ _

/-- The original X-Q Tanner adjacency coboundary as an explicit finite linear
map. -/
noncomputable def rzXQAdjacencyCoboundary (P : TannerSquarePresentation) :
    Word Field P.X →ₗ[Field] Word Field P.Q where
  toFun := fun word q =>
    ∑ x : P.X, if P.xq x q = true then word x else 0
  map_add' := by
    intro first second
    funext q
    change (∑ x : P.X, if P.xq x q = true then
      first x + second x else 0) =
        (∑ x : P.X, if P.xq x q = true then first x else 0) +
          ∑ x : P.X, if P.xq x q = true then second x else 0
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    split <;> simp
  map_smul' := by
    intro scalar word
    funext q
    change (∑ x : P.X, if P.xq x q = true then
      scalar * word x else 0) =
        scalar * ∑ x : P.X, if P.xq x q = true then word x else 0
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    split <;> simp

/-- The original Q-Z Tanner adjacency coboundary. -/
noncomputable def rzQZAdjacencyCoboundary (P : TannerSquarePresentation) :
    Word Field P.Q →ₗ[Field] Word Field P.Z where
  toFun := fun word z =>
    ∑ q : P.Q, if P.qz q z = true then word q else 0
  map_add' := by
    intro first second
    funext z
    change (∑ q : P.Q, if P.qz q z = true then
      first q + second q else 0) =
        (∑ q : P.Q, if P.qz q z = true then first q else 0) +
          ∑ q : P.Q, if P.qz q z = true then second q else 0
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    split <;> simp
  map_smul' := by
    intro scalar word
    funext z
    change (∑ q : P.Q, if P.qz q z = true then
      scalar * word q else 0) =
        scalar * ∑ q : P.Q, if P.qz q z = true then word q else 0
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    split <;> simp

/-- Named F07 charts on the X summand of the full degree-zero carrier. -/
noncomputable def rzAggregateXCoordinates (P : TannerSquarePresentation)
    (S : OddScale) : RZLocalH0 P S →ₗ[Field] (P.X → Field × Field) where
  toFun := fun classes x => rzCxH0Coordinates P x (classes.2.1 x)
  map_add' := by intros; funext x; exact map_add (rzCxH0Coordinates P x) _ _
  map_smul' := by intros; funext x; exact map_smul (rzCxH0Coordinates P x) _ _

/-- Named F07 parity charts on the aggregate Q carrier. -/
noncomputable def rzAggregateQCoordinates (P : TannerSquarePresentation)
    (S : OddScale) : RZLocalH1 P S →ₗ[Field] Word Field P.Q where
  toFun := fun classes q => rzCqH1Coordinate P q S (classes q)
  map_add' := by intros; funext q; exact map_add (rzCqH1Coordinate P q S) _ _
  map_smul' := by intros; funext q; exact map_smul (rzCqH1Coordinate P q S) _ _

/-- Named F07 parity charts on the aggregate Z carrier. -/
noncomputable def rzAggregateZCoordinates (P : TannerSquarePresentation)
    (S : OddScale) : RZLocalH2 P S →ₗ[Field] Word Field P.Z where
  toFun := fun classes z => rzCzH2Coordinate P z S (classes z)
  map_add' := by intros; funext z; exact map_add (rzCzH2Coordinate P z S) _ _
  map_smul' := by intros; funext z; exact map_smul (rzCzH2Coordinate P z S) _ _

/-- The actual aggregate X-Q quotient map.  Each target Q component is the
finite sum of the already constructed restriction-induced maps over incident
old X vertices; the Z/Q auxiliary summands are absent from this cellular
block, exactly as in the source direct-sum diagram. -/
noncomputable def rzAggregateXQH0ToH1 (P : TannerSquarePresentation)
    (S : OddScale) : RZLocalH0 P S →ₗ[Field] RZLocalH1 P S where
  toFun := fun classes q =>
    ∑ x : P.X, if hxq : P.xq x q = true then
      rzXQH0ToH1 P q x hxq S (classes.2.1 x)
    else 0
  map_add' := by
    intro first second
    funext q
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    split <;> simp
  map_smul' := by
    intro scalar classes
    funext q
    change (∑ x : P.X, if hxq : P.xq x q = true then
      rzXQH0ToH1 P q x hxq S (scalar • classes.2.1 x) else 0) =
        scalar • ∑ x : P.X, if hxq : P.xq x q = true then
          rzXQH0ToH1 P q x hxq S (classes.2.1 x) else 0
    simp only [map_smul]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro x _
    split <;> simp

/-- The source-diagram Z auxiliary summand has zero X-Q aggregate image. -/
@[simp] theorem rzAggregateXQH0ToH1_zAuxiliary_zero
    (P : TannerSquarePresentation) (S : OddScale)
    (auxiliary : ∀ z : P.Z, RZZH0 P z S) :
    rzAggregateXQH0ToH1 P S
        (auxiliary, (0, 0)) = 0 := by
  funext q
  simp [rzAggregateXQH0ToH1]

/-- The source-diagram Q auxiliary summand has zero X-Q aggregate image. -/
@[simp] theorem rzAggregateXQH0ToH1_qAuxiliary_zero
    (P : TannerSquarePresentation) (S : OddScale)
    (auxiliary : ∀ q : P.Q, RZQH0 P q S) :
    rzAggregateXQH0ToH1 P S
        (0, (0, auxiliary)) = 0 := by
  funext q
  simp [rzAggregateXQH0ToH1]

/-- F09 aggregate X-Q formula: after the named F07 charts, the actual quotient
map is old Tanner adjacency after pointwise codiagonal. -/
theorem rzAggregateXQH0ToH1_coordinate (P : TannerSquarePresentation)
    (S : OddScale) (classes : RZLocalH0 P S) (q : P.Q) :
    rzCqH1Coordinate P q S (rzAggregateXQH0ToH1 P S classes q) =
      ∑ x : P.X, if hxq : P.xq x q = true then
        (rzCxH0Coordinates P x (classes.2.1 x)).1 +
          (rzCxH0Coordinates P x (classes.2.1 x)).2
      else 0 := by
  classical
  change rzCqH1Coordinate P q S
      (∑ x : P.X, if hxq : P.xq x q = true then
        rzXQH0ToH1 P q x hxq S (classes.2.1 x) else 0) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro x _
  split
  · exact rzXQH0ToH1_coordinate P q x _ S (classes.2.1 x)
  · simp

/-- F09 as an equality of actual aggregate linear maps:
`H(g_XQ⁰) = δ⁰ ∘ Δ′`, with the two auxiliary summands killed by the
same left-hand map. -/
theorem rzAggregateXQH0ToH1_eq_adjacency_comp_codiagonal
    (P : TannerSquarePresentation) (S : OddScale) :
    (rzAggregateQCoordinates P S).comp (rzAggregateXQH0ToH1 P S) =
      (rzXQAdjacencyCoboundary P).comp
        ((rzPointwiseCodiagonal P).comp (rzAggregateXCoordinates P S)) := by
  classical
  apply LinearMap.ext
  intro classes
  funext q
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  change rzCqH1Coordinate P q S
      (rzAggregateXQH0ToH1 P S classes q) =
    ∑ x : P.X, if P.xq x q = true then
      rzCodiagonal (rzCxH0Coordinates P x (classes.2.1 x)) else 0
  rw [rzAggregateXQH0ToH1_coordinate]
  apply Finset.sum_congr rfl
  intro x _
  split <;> simp [rzCodiagonal]

/-- The actual aggregate Q-Z quotient map, summed over incident Q vertices. -/
noncomputable def rzAggregateQZH1ToH2 (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) :
    RZLocalH1 P S →ₗ[Field] RZLocalH2 P S where
  toFun := fun classes z =>
    ∑ q : P.Q, if hqz : P.qz q z = true then
      rzQZH1ToH2 P A q z hqz S (classes q)
    else 0
  map_add' := by
    intro first second
    funext z
    simp only [Pi.add_apply, map_add]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    split <;> simp
  map_smul' := by
    intro scalar classes
    funext z
    simp only [Pi.smul_apply, map_smul]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro q _
    split <;> simp

/-- F09 aggregate Q-Z formula: in the named F07 charts, the actual quotient
map is exactly the old Tanner Q-Z adjacency coboundary. -/
theorem rzAggregateQZH1ToH2_coordinate (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale)
    (classes : RZLocalH1 P S) (z : P.Z) :
    rzCzH2Coordinate P z S (rzAggregateQZH1ToH2 P A S classes z) =
      ∑ q : P.Q, if hqz : P.qz q z = true then
        rzCqH1Coordinate P q S (classes q)
      else 0 := by
  classical
  change rzCzH2Coordinate P z S
      (∑ q : P.Q, if hqz : P.qz q z = true then
        rzQZH1ToH2 P A q z hqz S (classes q) else 0) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q _
  split
  · exact rzQZH1ToH2_coordinate P A q z _ S (classes q)
  · simp

/-- F09 as an equality of actual aggregate linear maps:
`H(g_QZ¹) = δ¹` in the named F07 parity charts. -/
theorem rzAggregateQZH1ToH2_eq_adjacency
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) :
    (rzAggregateZCoordinates P S).comp (rzAggregateQZH1ToH2 P A S) =
      (rzQZAdjacencyCoboundary P).comp (rzAggregateQCoordinates P S) := by
  classical
  apply LinearMap.ext
  intro classes
  funext z
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  change rzCzH2Coordinate P z S
      (rzAggregateQZH1ToH2 P A S classes z) =
    ∑ q : P.Q, if P.qz q z = true then
      rzCqH1Coordinate P q S (classes q) else 0
  rw [rzAggregateQZH1ToH2_coordinate]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hqz : P.qz q z = true <;> simp [hqz]

/-! ## Nontrivial base fixture counts -/

-- Keep the computable base enumerations available to the API fixtures as well.
-- Unfolding the carrier aliases exposes their finite sums and products.
private abbrev baseScaleFiveRzXFintype : Fintype (RZX baseTannerSquarePresentation scaleFive) := by
  dsimp [RZX, ZDoubleCylinderFace, QDoubleCylinderEdge,
    DoubleCylinderFace, transposePresentation, transposeTannerSquareData]
  infer_instance

private abbrev baseScaleFiveRzQFintype : Fintype (RZQ baseTannerSquarePresentation scaleFive) := by
  dsimp [RZQ, ZDoubleCylinderEdge, QDoubleCylinderVertex,
    DoubleCylinderEdge, transposePresentation, transposeTannerSquareData]
  infer_instance

private abbrev baseScaleFiveRzZFintype : Fintype (RZZ baseTannerSquarePresentation scaleFive) := by
  dsimp [RZZ, ZDoubleCylinderVertex, DoubleCylinderVertex,
    transposePresentation, transposeTannerSquareData]
  infer_instance

private abbrev baseScaleFiveRzFaceFintype : Fintype (RZFace baseTannerSquarePresentation scaleFive) := by
  dsimp [RZFace, RZLocalFace, RZQZGlueFace, RZOldXFace,
    ZDoubleCylinderFace, QDoubleCylinderEdge, DoubleCylinderFace,
    transposePresentation, transposeTannerSquareData]
  infer_instance

attribute [instance] baseScaleFiveRzXFintype baseScaleFiveRzQFintype
  baseScaleFiveRzZFintype baseScaleFiveRzFaceFintype

@[simp] theorem baseScaleFive_rzX_card :
    Fintype.card (RZX baseTannerSquarePresentation scaleFive) = 82 := by
  simp only [RZX, ZDoubleCylinderFace, QDoubleCylinderEdge,
    DoubleCylinderFace, transposePresentation, transposeTannerSquareData]
  decide

set_option maxRecDepth 10000 in
@[simp] theorem baseScaleFive_rzQ_card :
    Fintype.card (RZQ baseTannerSquarePresentation scaleFive) = 140 := by
  simp only [RZQ, ZDoubleCylinderEdge, QDoubleCylinderVertex,
    DoubleCylinderEdge, transposePresentation,
    transposeTannerSquareData]
  decide

@[simp] theorem baseScaleFive_rzZ_card :
    Fintype.card (RZZ baseTannerSquarePresentation scaleFive) = 60 := by
  simp only [RZZ, ZDoubleCylinderVertex, DoubleCylinderVertex,
    transposePresentation, transposeTannerSquareData]
  decide

set_option maxRecDepth 10000 in
@[simp] theorem baseScaleFive_rzFace_card :
    Fintype.card (RZFace baseTannerSquarePresentation scaleFive) = 280 := by
  simp only [RZFace, RZLocalFace, RZQZGlueFace, RZOldXFace,
    ZDoubleCylinderFace, QDoubleCylinderEdge, DoubleCylinderFace,
    transposePresentation, transposeTannerSquareData]
  decide

end BDL26RZLocalReplacement
end Coding
end QEC
