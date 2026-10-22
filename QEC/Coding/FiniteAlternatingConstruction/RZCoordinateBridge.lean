import QEC.Coding.FiniteAlternatingConstruction.RZLocalReplacement
import QEC.Coding.CodeReduction.Classical.Core
import QEC.Coding.FourDimensionalToricCode.Decoder.Multiscale

/-!
# Concrete RZ degree-one coordinate bridge

This module constructs the degree-one coordinate map of the materialized RZ
replacement.  The construction uses one explicit Q-cylinder coordinate and
the actual Z-cylinder connecting chains obtained by subdividing the stored
old boundary paths.  It does not assemble a full adjacent-level cochain map;
that remains the responsibility of the downstream F03/F10 aggregator.
-/

namespace QEC
namespace Coding
namespace BDL26RZMap1CoordinateBridge

open scoped BigOperators
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity
open BDL26RZLocalReplacement
open MultiscaleDecoder

abbrev Field := BDL26FiniteTannerSquare.Field
abbrev Two := BDL26FiniteTannerSquare.Two

noncomputable local instance rzQDecidableEq
    (P : TannerSquarePresentation) (S : OddScale) :
    DecidableEq (RZQ P S) := Classical.decEq _

private noncomputable abbrev rzQFintype (P : TannerSquarePresentation) (S : OddScale) :
    Fintype (RZQ P S) := by
  classical
  infer_instance

attribute [local instance] rzQFintype

noncomputable local instance subdivisionEdgeDecidableEq
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    DecidableEq (SubdivisionEdge P x S) := by
  classical
  infer_instance

universe u

private def twoElim {motive : Fin 2 → Sort u}
    (zero : motive 0) (one : motive 1) (i : Fin 2) : motive i := by
  rcases i with ⟨i, hi⟩
  rcases i with _ | i
  · exact zero
  · rcases i with _ | i
    · exact one
    · omega

private theorem field_add_self (value : Field) : value + value = 0 := by
  fin_cases value <;> rfl

private theorem word_add_self {Index : Type} (word : Word Field Index) :
    word + word = 0 := by
  ext index
  exact field_add_self (word index)

/-- Binary indicator of one actual vertex, independent of caller equality instances. -/
noncomputable def vertexIndicator {Vertex : Type}
    (first second : Vertex) : Field := by
  classical
  exact if first = second then 1 else 0

/-- A constructor pushforward preserves the instance-independent unit basis. -/
@[simp] theorem wordPushforward_canonicalBasis {Source Target : Type}
    [Fintype Source] [Fintype Target] [DecidableEq Source] [DecidableEq Target]
    (map : Source → Target) (source : Source) :
    wordPushforward map (canonicalBasisWord (F := Field) source) =
      canonicalBasisWord (F := Field) (map source) := by
  classical
  ext target
  rw [wordPushforward_apply, Fintype.sum_eq_single source]
  · simp [canonicalBasisWord, Pi.single_apply]
  · intro other hne
    simp [canonicalBasisWord, Pi.single_apply, hne]

/-! ## Explicit paths inside one structurally owned subdivision face -/

private def gridIndex (S : OddScale) (step : Nat)
    (hstep : step ≤ S.half) : Fin (S.half + 1) :=
  ⟨step, by omega⟩

private def gridLast (S : OddScale) : Fin (S.half + 1) :=
  ⟨S.half, by omega⟩

private noncomputable def horizontalPrefixPath
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) :
    (step : Nat) → (hstep : step ≤ S.half) →
      UndirectedPath (subdivisionEdgeStart P x S)
        (subdivisionEdgeEnd P x S)
        (subdivisionGridVertex P x S face 0 0)
        (subdivisionGridVertex P x S face (gridIndex S step hstep) 0)
  | 0, _ => by simpa [gridIndex] using
      (UndirectedPath.nil : UndirectedPath
        (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S)
        (subdivisionGridVertex P x S face 0 0)
        (subdivisionGridVertex P x S face 0 0))
  | step + 1, hstep => by
      have hindex : step < S.half := by omega
      let index : Fin S.half := ⟨step, hindex⟩
      let edge := subdivisionHorizontalEdge P x S face index
        (0 : Fin (S.half + 1))
      apply UndirectedPath.step
        (horizontalPrefixPath P x S face step (by omega)) edge
      apply Or.inl
      constructor
      · exact subdivisionHorizontalEdge_start P x S face index
            (0 : Fin (S.half + 1))
      · exact subdivisionHorizontalEdge_end P x S face index
            (0 : Fin (S.half + 1))

private noncomputable def verticalPrefixPath
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) :
    (step : Nat) → (hstep : step ≤ S.half) →
      UndirectedPath (subdivisionEdgeStart P x S)
        (subdivisionEdgeEnd P x S)
        (subdivisionGridVertex P x S face 0 0)
        (subdivisionGridVertex P x S face 0 (gridIndex S step hstep))
  | 0, _ => by simpa [gridIndex] using
      (UndirectedPath.nil : UndirectedPath
        (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S)
        (subdivisionGridVertex P x S face 0 0)
        (subdivisionGridVertex P x S face 0 0))
  | step + 1, hstep => by
      have hindex : step < S.half := by omega
      let index : Fin S.half := ⟨step, hindex⟩
      let edge := subdivisionVerticalEdge P x S face
        (0 : Fin (S.half + 1)) index
      apply UndirectedPath.step
        (verticalPrefixPath P x S face step (by omega)) edge
      apply Or.inl
      constructor
      · exact subdivisionVerticalEdge_start P x S face
            (0 : Fin (S.half + 1)) index
      · exact subdivisionVerticalEdge_end P x S face
            (0 : Fin (S.half + 1)) index

private noncomputable def gridPathToCorner
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (corner : Two) :
    UndirectedPath (subdivisionEdgeStart P x S)
      (subdivisionEdgeEnd P x S)
      (subdivisionGridVertex P x S face 0 0)
      (twoSelect
        (subdivisionGridVertex P x S face (gridLast S) 0)
        (subdivisionGridVertex P x S face 0 (gridLast S)) corner) :=
  twoElim (motive := fun corner =>
      UndirectedPath (subdivisionEdgeStart P x S)
        (subdivisionEdgeEnd P x S)
        (subdivisionGridVertex P x S face 0 0)
        (twoSelect
          (subdivisionGridVertex P x S face (gridLast S) 0)
          (subdivisionGridVertex P x S face 0 (gridLast S)) corner))
    (by simpa [twoSelect, gridLast, gridIndex] using
      horizontalPrefixPath P x S face S.half (le_refl S.half))
    (by simpa [twoSelect, gridLast, gridIndex] using
      verticalPrefixPath P x S face S.half (le_refl S.half)) corner

private theorem pathChain_horizontalPrefixPath
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (step : Nat) (hstep : step ≤ S.half) :
    pathChain (horizontalPrefixPath P x S face step hstep) =
      ∑ i : Fin step, canonicalBasisWord
        (subdivisionHorizontalEdge P x S face
          ⟨i.1, lt_of_lt_of_le i.2 hstep⟩ 0) := by
  classical
  induction step with
  | zero =>
      change (0 : Word Field (SubdivisionEdge P x S)) = _
      simp
  | succ step ih =>
      change pathChain (horizontalPrefixPath P x S face step (by omega)) +
        Pi.single (subdivisionHorizontalEdge P x S face ⟨step, by omega⟩ 0) 1 = _
      rw [ih]
      rw [Fin.sum_univ_castSucc]
      congr 1
      ext coordinate
      simp [canonicalBasisWord, Pi.single_apply]

private theorem pathChain_verticalPrefixPath
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (step : Nat) (hstep : step ≤ S.half) :
    pathChain (verticalPrefixPath P x S face step hstep) =
      ∑ j : Fin step, canonicalBasisWord
        (subdivisionVerticalEdge P x S face 0
          ⟨j.1, lt_of_lt_of_le j.2 hstep⟩) := by
  classical
  induction step with
  | zero =>
      change (0 : Word Field (SubdivisionEdge P x S)) = _
      simp
  | succ step ih =>
      change pathChain (verticalPrefixPath P x S face step (by omega)) +
        Pi.single (subdivisionVerticalEdge P x S face 0 ⟨step, by omega⟩) 1 = _
      rw [ih]
      rw [Fin.sum_univ_castSucc]
      congr 1
      ext coordinate
      simp [canonicalBasisWord, Pi.single_apply]

private theorem pathChain_map
    {Vertex Edge Vertex' Edge' : Type}
    [Fintype Edge] [Fintype Edge'] [DecidableEq Edge] [DecidableEq Edge']
    {edgeStart edgeEnd : Edge → Vertex}
    {edgeStart' edgeEnd' : Edge' → Vertex'}
    (vertexMap : Vertex → Vertex') (edgeMap : Edge → Edge')
    (start_commutes : ∀ edge, edgeStart' (edgeMap edge) =
      vertexMap (edgeStart edge))
    (end_commutes : ∀ edge, edgeEnd' (edgeMap edge) =
      vertexMap (edgeEnd edge))
    {root target : Vertex}
    (path : UndirectedPath edgeStart edgeEnd root target) :
    pathChain
        (UndirectedPath.map vertexMap edgeMap start_commutes end_commutes path) =
      wordPushforward edgeMap (pathChain path) := by
  classical
  induction path with
  | nil => simp [UndirectedPath.map, pathChain]
  | @step u v path edge connects ih =>
      change
        pathChain
            (UndirectedPath.step
              (UndirectedPath.map vertexMap edgeMap start_commutes end_commutes path)
              (edgeMap edge) _) =
          wordPushforward edgeMap (pathChain path + Pi.single edge 1)
      rw [pathChain, ih, map_add, wordPushforward_single]

private theorem pathChain_eq_of_heq
    {Vertex Edge : Type} [DecidableEq Edge]
    {edgeStart edgeEnd : Edge → Vertex}
    {firstRoot firstTarget secondRoot secondTarget : Vertex}
    (first : UndirectedPath edgeStart edgeEnd firstRoot firstTarget)
    (second : UndirectedPath edgeStart edgeEnd secondRoot secondTarget)
    (hroot : firstRoot = secondRoot) (htarget : firstTarget = secondTarget)
    (hpath : HEq first second) : pathChain first = pathChain second := by
  subst secondRoot
  subst secondTarget
  exact congrArg pathChain (eq_of_heq hpath)

private theorem pathChain_gridPathToCorner_zero
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) :
    pathChain (gridPathToCorner P x S face 0) =
      ∑ i : Fin S.half, canonicalBasisWord
        (subdivisionHorizontalEdge P x S face i 0) := by
  classical
  have hpath : pathChain (gridPathToCorner P x S face 0) =
      pathChain
        (horizontalPrefixPath P x S face S.half (le_refl S.half)) := by
    apply pathChain_eq_of_heq
    · rfl
    · simp [gridLast, gridIndex, twoSelect]
    · change HEq
        (cast (by simp [gridLast, gridIndex, twoSelect])
          (horizontalPrefixPath P x S face S.half (le_refl S.half)))
        (horizontalPrefixPath P x S face S.half (le_refl S.half))
      exact cast_heq _ _
  rw [hpath, pathChain_horizontalPrefixPath]

private theorem pathChain_gridPathToCorner_one
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) :
    pathChain (gridPathToCorner P x S face 1) =
      ∑ j : Fin S.half, canonicalBasisWord
        (subdivisionVerticalEdge P x S face 0 j) := by
  classical
  have hpath : pathChain (gridPathToCorner P x S face 1) =
      pathChain
        (verticalPrefixPath P x S face S.half (le_refl S.half)) := by
    apply pathChain_eq_of_heq
    · rfl
    · simp [gridLast, gridIndex, twoSelect]
    · change HEq
        (cast (by simp [gridLast, gridIndex, twoSelect])
          (verticalPrefixPath P x S face S.half (le_refl S.half)))
        (verticalPrefixPath P x S face S.half (le_refl S.half))
      exact cast_heq _ _
  rw [hpath, pathChain_verticalPrefixPath]

/-! ## Canonical local roots and connecting chains -/

/-- The selected coordinate of the transposed Q cylinder. -/
def rzMap1QRoot (P : TannerSquarePresentation) (q : P.Q) (S : OddScale) :
    QDoubleCylinderVertex (transposePresentation P) q S :=
  (0, Sum.inl (Sum.inl ()))

/-- The fixed Z coordinate is the original Z-star centre on copy zero. -/
def rzMap1ZRoot
    (P : TannerSquarePresentation) (_A4 : TannerSquareAdmissibleV4 P)
    (z : P.Z) (S : OddScale) : ZDoubleCylinderVertex P z S :=
  (0, Sum.inl ⟨Vertex.x z, by
    simp only [xStarVertexMember, decide_eq_true_eq]
    rfl⟩)

private noncomputable def rzMap1QBoundaryVertex
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) :
    XStarBoundaryVertex (transposePresentation P) z :=
  (transposeXStarBoundaryVertexEquiv P z).symm
    (qToZBoundaryVertex P A4.toTannerSquareAdmissible q z hqz
      (Sum.inl ()))

private theorem rzMap1QBoundaryVertex_value
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) :
    (rzMap1QBoundaryVertex P A4 q z hqz).1 =
      (Vertex.q q : Vertex (transposePresentation P)) := by
  change (transposeVertexEquiv P).symm
      (qToZBoundaryVertex P A4.toTannerSquareAdmissible q z hqz
        (Sum.inl ())).1 = (Vertex.q q : Vertex (transposePresentation P))
  rw [qToZBoundaryVertex_center_value]
  rfl

private theorem qToZDoubleCylinderVertex_qRoot
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale) :
    qToZDoubleCylinderVertex P A4.toTannerSquareAdmissible q z hqz S
        (rzMap1QRoot P q S) =
      (0, (subdivisionOriginalBoundaryVertex (transposePresentation P) z S
        (rzMap1QBoundaryVertex P A4 q z hqz)).1) := by
  rfl

private noncomputable def rzMap1BoundaryEdge
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) :
    XStarBoundaryEdge (transposePresentation P) z :=
  (transposeXStarBoundaryEdgeEquiv P z).symm
    (qToZBoundaryEdge P q z hqz
      ⟨(A4.toTannerSquareAdmissible.xqRoot q).1,
        (A4.toTannerSquareAdmissible.xqRoot q).2⟩)

private def rzMap1BoundaryQZEdge
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (q : P.Q) : QZEdge (transposePresentation P) :=
  ⟨(q, (A4.toTannerSquareAdmissible.xqRoot q).1),
    (A4.toTannerSquareAdmissible.xqRoot q).2⟩

private theorem rzMap1BoundaryEdge_value
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) :
    (rzMap1BoundaryEdge P A4 q z hqz).1 =
      Sum.inr (rzMap1BoundaryQZEdge P A4 q) := by
  rfl

private theorem rzMap1BoundaryQZEdge_member
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) :
    xStarEdgeMember (transposePresentation P) z
      (Sum.inr (rzMap1BoundaryQZEdge P A4 q)) = true := by
  rw [← rzMap1BoundaryEdge_value P A4 q z hqz]
  exact (rzMap1BoundaryEdge P A4 q z hqz).2

private noncomputable def rzMap1Owner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) :
    XStarFace (transposePresentation P) z × Two :=
  let transposed := transposeTannerSquareAdmissibleV4 P A4
  (transposed.xBoundaryFaceOwner z (rzMap1BoundaryQZEdge P A4 q)
    (rzMap1BoundaryQZEdge_member P A4 q z hqz)).1

private theorem rzMap1Owner_faceX
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) :
    (transposePresentation P).faceX (rzMap1Owner P A4 q z hqz).1.1 = z := by
  simpa [xStarFaceMember] using (rzMap1Owner P A4 q z hqz).1.2

private theorem rzMap1Owner_faceQ
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) :
    (transposePresentation P).faceQ (rzMap1Owner P A4 q z hqz).1.1
      (rzMap1Owner P A4 q z hqz).2 = q := by
  let transposed := transposeTannerSquareAdmissibleV4 P A4
  let edge := rzMap1BoundaryQZEdge P A4 q
  let member := rzMap1BoundaryQZEdge_member P A4 q z hqz
  have hedge := (transposed.xBoundaryFaceOwner z edge member).2
  have hraw := congrArg Subtype.val hedge
  have hqzEdge := Sum.inr.inj hraw
  have hq := congrArg (fun value : QZEdge (transposePresentation P) =>
    value.1.1) hqzEdge
  exact hq

private theorem rzMap1Owner_gridCorner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale) :
    twoSelect
        (subdivisionGridVertex (transposePresentation P) z S
          (rzMap1Owner P A4 q z hqz).1 (gridLast S) 0)
        (subdivisionGridVertex (transposePresentation P) z S
          (rzMap1Owner P A4 q z hqz).1 0 (gridLast S))
        (rzMap1Owner P A4 q z hqz).2 =
      (subdivisionOriginalBoundaryVertex (transposePresentation P) z S
        (rzMap1QBoundaryVertex P A4 q z hqz)).1 := by
  have hfaceQ := rzMap1Owner_faceQ P A4 q z hqz
  apply twoElim (motive := fun corner =>
      (rzMap1Owner P A4 q z hqz).2 = corner →
        twoSelect
            (subdivisionGridVertex (transposePresentation P) z S
              (rzMap1Owner P A4 q z hqz).1 (gridLast S) 0)
            (subdivisionGridVertex (transposePresentation P) z S
              (rzMap1Owner P A4 q z hqz).1 0 (gridLast S))
            (rzMap1Owner P A4 q z hqz).2 =
          (subdivisionOriginalBoundaryVertex (transposePresentation P) z S
            (rzMap1QBoundaryVertex P A4 q z hqz)).1)
    (fun hcorner => by
      rw [hcorner] at hfaceQ ⊢
      have hboundary :
          (xStarBoundaryVertexToStar (transposePresentation P) z
            (rzMap1QBoundaryVertex P A4 q z hqz)).1 =
              (Vertex.q q : Vertex (transposePresentation P)) := by
        exact rzMap1QBoundaryVertex_value P A4 q z hqz
      simp [twoSelect, gridLast, subdivisionGridVertex,
        subdivisionOriginalBoundaryVertex, xStarFaceQVertex,
        hfaceQ, S.half_pos.ne']
      apply Subtype.ext
      exact hboundary.symm)
    (fun hcorner => by
      rw [hcorner] at hfaceQ ⊢
      have hboundary :
          (xStarBoundaryVertexToStar (transposePresentation P) z
            (rzMap1QBoundaryVertex P A4 q z hqz)).1 =
              (Vertex.q q : Vertex (transposePresentation P)) := by
        exact rzMap1QBoundaryVertex_value P A4 q z hqz
      simp [twoSelect, gridLast, subdivisionGridVertex,
        subdivisionOriginalBoundaryVertex, xStarFaceQVertex,
        hfaceQ, S.half_pos.ne']
      apply Subtype.ext
      exact hboundary.symm)
    (rzMap1Owner P A4 q z hqz).2 rfl

/-- The actual old-boundary path, subdivided on copy zero, joins the fixed Z
coordinate to the image of the selected Q coordinate. -/
noncomputable def rzMap1ConnectorPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale) :
    UndirectedPath
      (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
      (rzMap1ZRoot P A4 z S)
      (qToZDoubleCylinderVertex P A4.toTannerSquareAdmissible
        q z hqz S (rzMap1QRoot P q S)) := by
  let owner := rzMap1Owner P A4 q z hqz
  let path := gridPathToCorner (transposePresentation P) z S owner.1 owner.2
  let lifted := UndirectedPath.map
    (edgeStart := subdivisionEdgeStart (transposePresentation P) z S)
    (edgeEnd := subdivisionEdgeEnd (transposePresentation P) z S)
    (edgeStart' := tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
    (edgeEnd' := tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
    (fun vertex => (0, vertex)) (fun edge => Sum.inl (0, edge))
    (fun _ => rfl) (fun _ => rfl) path
  have hfaceX := rzMap1Owner_faceX P A4 q z hqz
  have htarget := rzMap1Owner_gridCorner P A4 q z hqz S
  convert lifted using 1
  · simp [rzMap1ZRoot, owner, subdivisionGridVertex,
      xStarFaceXVertex, hfaceX]
  · rw [htarget]
    exact (qToZDoubleCylinderVertex_qRoot P A4 q z hqz S).symm

/-- The Z-local connecting cochain attached to an adjacent old Q-Z pair. -/
noncomputable def rzMap1Connector
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale) :
    Word Field (ZDoubleCylinderEdge P z S) := by
  classical
  exact pathChain (rzMap1ConnectorPath P A4 q z hqz S)

/-- The explicit copy-zero outer side selected by the public V4 boundary-face
owner.  This is data only: it stores neither an owner/path field nor a
compatibility conclusion. -/
noncomputable def rzMap1ConnectorOuterSide
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale) :
    Word Field (ZDoubleCylinderEdge P z S) := by
  classical
  let boundary : QZEdge (transposePresentation P) :=
    ⟨(q, (A4.toTannerSquareAdmissible.xqRoot q).1),
      (A4.toTannerSquareAdmissible.xqRoot q).2⟩
  have member : xStarEdgeMember (transposePresentation P) z
      (Sum.inr boundary) = true := by
    simpa [boundary, rzMap1BoundaryQZEdge] using
      rzMap1BoundaryQZEdge_member P A4 q z hqz
  let owner :=
    ((transposeTannerSquareAdmissibleV4 P A4).xBoundaryFaceOwner
      z boundary member).1
  exact twoSelect
    (∑ i : Fin S.half, canonicalBasisWord
      (Sum.inl (0, subdivisionHorizontalEdge (transposePresentation P) z S
        owner.1 i 0) : ZDoubleCylinderEdge P z S))
    (∑ j : Fin S.half, canonicalBasisWord
      (Sum.inl (0, subdivisionVerticalEdge (transposePresentation P) z S
        owner.1 0 j) : ZDoubleCylinderEdge P z S)) owner.2

/-- The constructed connector is exactly the explicit outer-side chain of its
public V4 owner. -/
theorem rzMap1Connector_eq_outerSide
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale) :
    rzMap1Connector P A4 q z hqz S =
      rzMap1ConnectorOuterSide P A4 q z hqz S := by
  classical
  let owner := rzMap1Owner P A4 q z hqz
  let path := gridPathToCorner (transposePresentation P) z S owner.1 owner.2
  let lifted := UndirectedPath.map
    (edgeStart := subdivisionEdgeStart (transposePresentation P) z S)
    (edgeEnd := subdivisionEdgeEnd (transposePresentation P) z S)
    (edgeStart' := tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
    (edgeEnd' := tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
    (fun vertex => (0, vertex)) (fun edge => Sum.inl (0, edge))
    (fun _ => rfl) (fun _ => rfl) path
  have hconnector : pathChain (rzMap1ConnectorPath P A4 q z hqz S) =
      pathChain lifted := by
    apply pathChain_eq_of_heq
    · have hfaceX := rzMap1Owner_faceX P A4 q z hqz
      simp [rzMap1ZRoot, owner, path, lifted, subdivisionGridVertex,
        xStarFaceXVertex, hfaceX]
    · have htarget := rzMap1Owner_gridCorner P A4 q z hqz S
      rw [show (twoSelect
          (subdivisionGridVertex (transposePresentation P) z S owner.1
            (gridLast S) 0)
          (subdivisionGridVertex (transposePresentation P) z S owner.1
            0 (gridLast S)) owner.2) =
          (subdivisionOriginalBoundaryVertex (transposePresentation P) z S
            (rzMap1QBoundaryVertex P A4 q z hqz)).1 by
        simpa [owner] using htarget]
      exact (qToZDoubleCylinderVertex_qRoot P A4 q z hqz S).symm
    · simp [rzMap1ConnectorPath, owner, path, lifted]
  unfold rzMap1Connector
  rw [hconnector]
  have hlifted : pathChain lifted =
      wordPushforward (fun edge =>
        (Sum.inl (0, edge) : ZDoubleCylinderEdge P z S))
        (pathChain path) := by
    simpa [lifted] using pathChain_map
      (edgeStart := subdivisionEdgeStart (transposePresentation P) z S)
      (edgeEnd := subdivisionEdgeEnd (transposePresentation P) z S)
      (edgeStart' := tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
      (edgeEnd' := tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
      (fun vertex => (0, vertex))
      (fun edge => (Sum.inl (0, edge) : ZDoubleCylinderEdge P z S))
      (fun _ => rfl) (fun _ => rfl) path
  rw [hlifted]
  unfold rzMap1ConnectorOuterSide
  change wordPushforward (fun edge =>
        (Sum.inl (0, edge) : ZDoubleCylinderEdge P z S))
        (pathChain path) =
      twoSelect
        (∑ i : Fin S.half, canonicalBasisWord
          (Sum.inl (0, subdivisionHorizontalEdge (transposePresentation P) z S
            owner.1 i 0) : ZDoubleCylinderEdge P z S))
        (∑ j : Fin S.half, canonicalBasisWord
          (Sum.inl (0, subdivisionVerticalEdge (transposePresentation P) z S
            owner.1 0 j) : ZDoubleCylinderEdge P z S)) owner.2
  dsimp only [path]
  apply twoElim (motive := fun corner =>
      wordPushforward (fun edge =>
        (Sum.inl (0, edge) : ZDoubleCylinderEdge P z S))
          (pathChain (gridPathToCorner (transposePresentation P) z S
            owner.1 corner)) =
        twoSelect
          (∑ i : Fin S.half, canonicalBasisWord
            (Sum.inl (0, subdivisionHorizontalEdge (transposePresentation P)
              z S owner.1 i 0) : ZDoubleCylinderEdge P z S))
          (∑ j : Fin S.half, canonicalBasisWord
            (Sum.inl (0, subdivisionVerticalEdge (transposePresentation P)
              z S owner.1 0 j) : ZDoubleCylinderEdge P z S)) corner)
    (by
      have h := congrArg
        (wordPushforward (fun edge : SubdivisionEdge (transposePresentation P) z S =>
          (Sum.inl (0, edge) : ZDoubleCylinderEdge P z S)))
        (pathChain_gridPathToCorner_zero (transposePresentation P) z S owner.1)
      calc
        _ = _ := h
        _ = _ := by
          rw [map_sum]
          simp [wordPushforward_canonicalBasis, twoSelect])
    (by
      have h := congrArg
        (wordPushforward (fun edge : SubdivisionEdge (transposePresentation P) z S =>
          (Sum.inl (0, edge) : ZDoubleCylinderEdge P z S)))
        (pathChain_gridPathToCorner_one (transposePresentation P) z S owner.1)
      calc
        _ = _ := h
        _ = _ := by
          rw [map_sum]
          simp [wordPushforward_canonicalBasis, twoSelect]) owner.2

/-- The selected connector traverses the radial side to its old-Q vertex.
Any incident face gives the same tagged original-edge chain. -/
theorem rzMap1Connector_eq_face_radial
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale)
    (face : XStarFace (transposePresentation P) z) (corner : Two)
    (hcorner : P.faceQ face.1 corner = q) :
    rzMap1Connector P A4 q z hqz S =
      ∑ i : Fin S.half, canonicalBasisWord
        (Sum.inl (0, Sum.inl
          (xStarFaceXQEdge (transposePresentation P) z face corner, i)) :
            ZDoubleCylinderEdge P z S) := by
  classical
  rw [rzMap1Connector_eq_outerSide]
  let owner := rzMap1Owner P A4 q z hqz
  have hedge : xStarFaceXQEdge (transposePresentation P) z owner.1 owner.2 =
      xStarFaceXQEdge (transposePresentation P) z face corner := by
    apply Subtype.ext
    apply congrArg Sum.inl
    apply Subtype.ext
    apply Prod.ext
    · have hface : (transposePresentation P).faceX face.1 = z := by
        simpa [xStarFaceMember] using face.2
      exact (rzMap1Owner_faceX P A4 q z hqz).trans hface.symm
    · exact (rzMap1Owner_faceQ P A4 q z hqz).trans hcorner.symm
  change twoSelect
      (∑ i : Fin S.half, canonicalBasisWord
        (Sum.inl (0, subdivisionHorizontalEdge (transposePresentation P) z S
          owner.1 i 0) : ZDoubleCylinderEdge P z S))
      (∑ j : Fin S.half, canonicalBasisWord
        (Sum.inl (0, subdivisionVerticalEdge (transposePresentation P) z S
          owner.1 0 j) : ZDoubleCylinderEdge P z S)) owner.2 = _
  rw [← hedge]
  apply twoElim (motive := fun c => owner.2 = c →
      twoSelect
        (∑ i : Fin S.half, canonicalBasisWord
          (Sum.inl (0, subdivisionHorizontalEdge (transposePresentation P) z S
            owner.1 i 0) : ZDoubleCylinderEdge P z S))
        (∑ j : Fin S.half, canonicalBasisWord
          (Sum.inl (0, subdivisionVerticalEdge (transposePresentation P) z S
            owner.1 0 j) : ZDoubleCylinderEdge P z S)) owner.2 =
        ∑ i : Fin S.half, canonicalBasisWord
          (Sum.inl (0, Sum.inl
            (xStarFaceXQEdge (transposePresentation P) z owner.1 owner.2, i)) :
              ZDoubleCylinderEdge P z S))
    (fun h => by simp [h, twoSelect, subdivisionHorizontalEdge])
    (fun h => by simp [h, twoSelect, subdivisionVerticalEdge]) owner.2 rfl

/-! ## Basis formula and independently assembled map -/

private def embedQRoot
    (P : TannerSquarePresentation) (S : OddScale) (q : P.Q) :
    QDoubleCylinderVertex (transposePresentation P) q S → RZQ P S :=
  fun vertex => Sum.inr ⟨q, vertex⟩

private def embedZEdge
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z) :
    ZDoubleCylinderEdge P z S → RZQ P S :=
  fun edge => Sum.inl ⟨z, edge⟩

/-- Constructor-level extension by zero of one Z-local edge word. -/
def extendZEdgeWord
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z)
    (word : Word Field (ZDoubleCylinderEdge P z S)) : Word Field (RZQ P S)
  | Sum.inl localEdge =>
      if h : localEdge.1 = z then word (h ▸ localEdge.2) else 0
  | Sum.inr _ => 0

/-- Constructor-level extension by zero of one Z-local vertex word. -/
def extendZVertexWord
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z)
    (word : Word Field (ZDoubleCylinderVertex P z S)) : Word Field (RZZ P S)
  | ⟨targetZ, vertex⟩ =>
      if h : targetZ = z then word (h ▸ vertex) else 0

@[simp] theorem extendZVertexWord_add
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z)
    (first second : Word Field (ZDoubleCylinderVertex P z S)) :
    extendZVertexWord P S z (first + second) =
      extendZVertexWord P S z first + extendZVertexWord P S z second := by
  classical
  ext ⟨targetZ, vertex⟩
  by_cases h : targetZ = z <;>
    simp [extendZVertexWord, h]

@[simp] theorem extendZVertexWord_canonicalBasis
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z)
    (vertex : ZDoubleCylinderVertex P z S) :
    extendZVertexWord P S z (canonicalBasisWord vertex) =
      canonicalBasisWord (⟨z, vertex⟩ : RZZ P S) := by
  classical
  ext ⟨targetZ, targetVertex⟩
  by_cases h : targetZ = z
  · subst targetZ
    by_cases hvertex : targetVertex = vertex
    · subst targetVertex
      simp [extendZVertexWord, canonicalBasisWord]
    · have hsigma : (⟨z, targetVertex⟩ : RZZ P S) ≠ ⟨z, vertex⟩ := by
        intro heq
        exact hvertex (eq_of_heq (Sigma.mk.inj_iff.mp heq).2)
      simp [extendZVertexWord, canonicalBasisWord, hvertex, hsigma]
  · have hneq : (⟨targetZ, targetVertex⟩ : RZZ P S) ≠ ⟨z, vertex⟩ := by
      intro heq
      exact h (congrArg Sigma.fst heq)
    simp [extendZVertexWord, canonicalBasisWord, h, hneq]

/-- The explicit finite coordinate image of one old-Q basis word. -/
noncomputable def map1BasisImage
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q : P.Q) : Word Field (RZQ P S) := by
  classical
  exact Pi.single (embedQRoot P S q (rzMap1QRoot P q S)) 1 +
    ∑ z : P.Z, if hqz : P.qz q z = true then
      extendZEdgeWord P S z (rzMap1Connector P A4 q z hqz S)
    else 0

/-- The coordinate formula determined by the concrete finite basis images. -/
noncomputable def map1Coord
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) :
    Word Field P.Q →ₗ[Field] Word Field (RZQ P S) := by
  classical
  exact ClassicalWeightReduction.linearMapOfBasisImages
    (F := Field) (map1BasisImage P A4 S)

/-- Data-only carrier for the independently assembled RZ degree-one map. -/
structure RZMap1Data
    (P : TannerSquarePresentation) (S : OddScale) where
  map1 : Word Field P.Q →ₗ[Field] Word Field (RZQ P S)

private noncomputable def rzMap1LocalExtension
    (P : TannerSquarePresentation) (S : OddScale) :
    Word Field P.Q →ₗ[Field] Word Field (RZQ P S) := by
  classical
  exact wordPushforward (fun q => embedQRoot P S q (rzMap1QRoot P q S))

private noncomputable def rzMap1ConnectingExtension
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) :
    Word Field P.Q →ₗ[Field] Word Field (RZQ P S) := by
  classical
  exact
    { toFun := fun word => ∑ q : P.Q, word q •
        ∑ z : P.Z, if hqz : P.qz q z = true then
          extendZEdgeWord P S z (rzMap1Connector P A4 q z hqz S)
        else 0
      map_add' := by
        intro first second
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro coefficient word
        ext target
        simp [smul_eq_mul, Finset.mul_sum, mul_assoc] }

/-- The actual local-extension plus connecting-map construction. -/
noncomputable def rzMap
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) : RZMap1Data P S where
  map1 := rzMap1LocalExtension P S + rzMap1ConnectingExtension P A4 S

private theorem linearMap_ext_canonicalBasis
    {Source Target : Type} [Fintype Source] [DecidableEq Source]
    [Fintype Target] [DecidableEq Target]
    (first second : Word Field Source →ₗ[Field] Word Field Target)
    (hbasis : ∀ source,
      first (canonicalBasisWord source) = second (canonicalBasisWord source)) :
    first = second := by
  classical
  apply LinearMap.ext
  intro word
  have hdecompose : word =
      ∑ source : Source, word source • canonicalBasisWord source := by
    rw [← word_eq_sum_single word]
    apply Finset.sum_congr rfl
    intro source _
    ext target
    rw [Pi.single_apply, Pi.smul_apply]
    by_cases htarget : target = source
    · subst target
      simp [canonicalBasisWord]
    · simp [canonicalBasisWord, htarget]
  rw [hdecompose]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro source _
  rw [hbasis source]

@[simp] theorem map1Coord_canonicalBasis
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q : P.Q) :
    map1Coord P A4 S (canonicalBasisWord q) =
      map1BasisImage P A4 S q := by
  classical
  have hbasis : canonicalBasisWord (F := Field) q = Pi.single q 1 := by
    ext target
    by_cases htarget : target = q
    · subst target
      simp [canonicalBasisWord]
    · simp [canonicalBasisWord, htarget]
  rw [hbasis]
  exact ClassicalWeightReduction.linearMapOfBasisImages_single
    (F := Field) (map1BasisImage P A4 S) q

private theorem rzMap_map1_canonicalBasis
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q : P.Q) :
    (rzMap P A4 S).map1 (canonicalBasisWord q) =
      map1BasisImage P A4 S q := by
  classical
  have hbasis : canonicalBasisWord (F := Field) q = Pi.single q 1 := by
    ext target
    by_cases htarget : target = q
    · subst target
      simp [canonicalBasisWord]
    · simp [canonicalBasisWord, htarget]
  rw [hbasis]
  simp only [rzMap, LinearMap.add_apply]
  rw [show rzMap1LocalExtension P S (Pi.single q 1) =
      Pi.single (embedQRoot P S q (rzMap1QRoot P q S)) 1 by
    exact wordPushforward_single _ _ _]
  simp [rzMap1ConnectingExtension, map1BasisImage]

/-- The assembled local/gluing map is exactly the finite coordinate formula.
The proof compares every canonical basis vector. -/
theorem rzMap_map1_eq_map1Coord
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) :
    (rzMap P A4 S).map1 = map1Coord P A4 S := by
  classical
  apply linearMap_ext_canonicalBasis
  intro q
  rw [rzMap_map1_canonicalBasis, map1Coord_canonicalBasis]

/-! ## Exact constructor region and raw F03/F10/F11 witnesses -/

/-- The parent region is defined directly from the selected Q root and the
actual adjacent Z-connector chains.  It is independent of the support of the
assembled map. -/
noncomputable def rzMap1ParentRegion
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q : P.Q) : Finset (RZQ P S) := by
  classical
  exact Finset.univ.filter fun target => match target with
    | Sum.inl localEdge =>
        ∃ hqz : P.qz q localEdge.1 = true,
          rzMap1Connector P A4 q localEdge.1 hqz S localEdge.2 ≠ 0
    | Sum.inr qVertex =>
        qVertex = ⟨q, rzMap1QRoot P q S⟩

theorem map1BasisImage_apply_local
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q : P.Q) (z : P.Z)
    (edge : ZDoubleCylinderEdge P z S) :
    map1BasisImage P A4 S q (Sum.inl ⟨z, edge⟩) =
      if hqz : P.qz q z = true then
        rzMap1Connector P A4 q z hqz S edge
      else 0 := by
  classical
  unfold map1BasisImage
  rw [Pi.add_apply, Finset.sum_apply]
  have hroot : ((Pi.single
      (embedQRoot P S q (rzMap1QRoot P q S)) (1 : Field)) :
        Word Field (RZQ P S))
      (Sum.inl ⟨z, edge⟩) = 0 := by
    simp [embedQRoot]
  rw [hroot, zero_add]
  rw [Finset.sum_eq_single z]
  · by_cases hqz : P.qz q z = true
    · rw [dif_pos hqz, dif_pos hqz]
      simp [extendZEdgeWord]
    · rw [dif_neg hqz, dif_neg hqz]
      rfl
  · intro other _ hother
    by_cases hqz : P.qz q other = true
    · rw [dif_pos hqz]
      simp [extendZEdgeWord, Ne.symm hother]
    · rw [dif_neg hqz]
      rfl
  · intro hnot
    exact (hnot (Finset.mem_univ z)).elim

theorem map1BasisImage_apply_q
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q : P.Q)
    (qVertex : Σ q : P.Q,
      QDoubleCylinderVertex (transposePresentation P) q S) :
    map1BasisImage P A4 S q (Sum.inr qVertex) =
      if qVertex = ⟨q, rzMap1QRoot P q S⟩ then 1 else 0 := by
  classical
  unfold map1BasisImage
  rw [Pi.add_apply, Finset.sum_apply]
  have hconnecting : (∑ z : P.Z,
      (if hqz : P.qz q z = true then
        extendZEdgeWord P S z (rzMap1Connector P A4 q z hqz S)
      else 0) (Sum.inr qVertex)) = 0 := by
    apply Finset.sum_eq_zero
    intro z _
    by_cases hqz : P.qz q z = true
    · rw [dif_pos hqz]
      rfl
    · rw [dif_neg hqz]
      rfl
  rw [hconnecting, add_zero, Pi.single_apply]
  by_cases hq : qVertex = ⟨q, rzMap1QRoot P q S⟩
  · subst qVertex
    simp [embedQRoot]
  · have hsum : (Sum.inr qVertex : RZQ P S) ≠
        embedQRoot P S q (rzMap1QRoot P q S) := by
      intro heq
      exact hq (Sum.inr.inj heq)
    simp [hq, hsum]

theorem map1BasisImage_ne_zero_iff_mem_parentRegion
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q : P.Q) (target : RZQ P S) :
    map1BasisImage P A4 S q target ≠ 0 ↔
      target ∈ rzMap1ParentRegion P A4 S q := by
  classical
  rcases target with localEdge | qVertex
  · rcases localEdge with ⟨z, edge⟩
    rw [map1BasisImage_apply_local]
    simp only [rzMap1ParentRegion, Finset.mem_filter, Finset.mem_univ,
      true_and]
    by_cases hqz : P.qz q z = true
    · rw [dif_pos hqz]
      constructor
      · intro hnonzero
        exact ⟨hqz, hnonzero⟩
      · rintro ⟨hqz', hnonzero⟩
        simpa only [proof_irrel_heq] using hnonzero
    · rw [dif_neg hqz]
      constructor
      · intro hzero
        exact (hzero rfl).elim
      · rintro ⟨hqz', _⟩
        exact (hqz hqz').elim
  · rw [map1BasisImage_apply_q]
    simp [rzMap1ParentRegion]

/-- Exact F10 parent-support identity for every old-Q basis coordinate. -/
theorem map1BasisImage_support_eq_parentRegion
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q : P.Q) :
    hammingSupport (map1BasisImage P A4 S q) =
      rzMap1ParentRegion P A4 S q := by
  classical
  ext target
  simp only [hammingSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  exact map1BasisImage_ne_zero_iff_mem_parentRegion P A4 S q target

/-- Exact F11 image characterization, stated in both directions rather than
as a one-way support bound. -/
theorem map1BasisImage_target_mem_iff
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q : P.Q) (target : RZQ P S) :
    target ∈ rzMap1ParentRegion P A4 S q ↔
      map1BasisImage P A4 S q target ≠ 0 :=
  (map1BasisImage_ne_zero_iff_mem_parentRegion P A4 S q target).symm

/-- Raw F03 degree-one basis table, derived from the independently assembled
map equality rather than stored as a compatibility field. -/
noncomputable def rzMap1FiniteBasisAction
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) : TypedFiniteBasisAction (rzMap P A4 S).map1 where
  basisImage := map1BasisImage P A4 S
  basis_action := by
    intro q
    rw [rzMap_map1_eq_map1Coord, map1Coord_canonicalBasis]

/-- Raw #842 extension-by-zero/support/image witness for the concrete RZ
degree-one map. -/
noncomputable def rzMap1ExtensionZeroLocalSupportImage
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) :
    ExtensionZeroLocalSupportImage
      (Owner := P.Q) (Source := P.Q) (Target := RZQ P S)
      (rzMap P A4 S).map1 where
  sourceRegion := fun q => {q}
  targetRegion := rzMap1ParentRegion P A4 S
  extensionByZero := fun q => zeroExtendWord ({q} : Finset P.Q)
  extension_zero := by
    intro q localWord source hsource
    change (if h : source ∈ ({q} : Finset P.Q) then
      localWord ⟨source, h⟩ else 0) = 0
    rw [dif_neg hsource]
  extension_on_region := by
    intro q localWord source
    change (if h : source.1 ∈ ({q} : Finset P.Q) then
      localWord ⟨source.1, h⟩ else 0) = localWord source
    simp
  selectedMapBasisImage := map1BasisImage P A4 S
  selectedMap_basis_action := (rzMap1FiniteBasisAction P A4 S).basis_action
  selectedMap_basis_support := by
    intro owner source target hsource htarget
    have hsourceEq : source = owner := by simpa using hsource
    subst source
    by_contra hnonzero
    exact htarget
      ((map1BasisImage_ne_zero_iff_mem_parentRegion P A4 S owner target).1
        hnonzero)
  selectedMap_basis_image := by
    intro owner source target hsource hnonzero
    have hsourceEq : source = owner := by simpa using hsource
    subst source
    exact (map1BasisImage_ne_zero_iff_mem_parentRegion P A4 S owner target).1
      hnonzero

/-! ## Concrete Tanner coboundaries and canonical-basis equations -/

/-- Degree-zero Tanner coboundary on the exact finite X/Q carriers. -/
noncomputable def tannerCoboundary0 (P : TannerSquarePresentation) :
    Word Field P.X →ₗ[Field] Word Field P.Q where
  toFun word q := ∑ x : P.X,
    word x * if P.xq x q = true then 1 else 0
  map_add' first second := by
    ext q
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : P.xq x q = true <;> simp [h]
  map_smul' coefficient word := by
    ext q
    simp only [Pi.smul_apply, RingHom.id_apply]
    change (∑ x : P.X, coefficient * word x *
      if P.xq x q = true then 1 else 0) =
        coefficient * ∑ x : P.X,
          word x * if P.xq x q = true then 1 else 0
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : P.xq x q = true <;> simp [h]

/-- Degree-one Tanner coboundary on the exact finite Q/Z carriers. -/
noncomputable def tannerCoboundary1 (P : TannerSquarePresentation) :
    Word Field P.Q →ₗ[Field] Word Field P.Z where
  toFun word z := ∑ q : P.Q,
    word q * if P.qz q z = true then 1 else 0
  map_add' first second := by
    ext z
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    by_cases h : P.qz q z = true <;> simp [h]
  map_smul' coefficient word := by
    ext z
    simp only [Pi.smul_apply, RingHom.id_apply]
    change (∑ q : P.Q, coefficient * word q *
      if P.qz q z = true then 1 else 0) =
        coefficient * ∑ q : P.Q,
          word q * if P.qz q z = true then 1 else 0
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    by_cases h : P.qz q z = true <;> simp [h]

@[simp] theorem tannerCoboundary0_canonicalBasis_apply
    (P : TannerSquarePresentation) (x : P.X) (q : P.Q) :
    tannerCoboundary0 P (canonicalBasisWord x) q =
      if P.xq x q = true then 1 else 0 := by
  classical
  unfold tannerCoboundary0
  dsimp
  rw [Finset.sum_eq_single x]
  · simp [canonicalBasisWord]
  · intro other _ hne
    simp [canonicalBasisWord, hne]
  · simp

@[simp] theorem tannerCoboundary1_canonicalBasis_apply
    (P : TannerSquarePresentation) (q : P.Q) (z : P.Z) :
    tannerCoboundary1 P (canonicalBasisWord q) z =
      if P.qz q z = true then 1 else 0 := by
  classical
  unfold tannerCoboundary1
  dsimp
  rw [Finset.sum_eq_single q]
  · simp [canonicalBasisWord]
  · intro other _ hne
    simp [canonicalBasisWord, hne]
  · simp

private theorem tannerCoboundary1_canonicalBasis_sum
    (P : TannerSquarePresentation) (q : P.Q) :
    tannerCoboundary1 P (canonicalBasisWord q) =
      ∑ z : P.Z, if P.qz q z = true then canonicalBasisWord z else 0 := by
  classical
  ext target
  rw [tannerCoboundary1_canonicalBasis_apply, Finset.sum_apply]
  rw [Finset.sum_eq_single target]
  · by_cases h : P.qz q target = true <;> simp [h, canonicalBasisWord]
  · intro other _ hne
    by_cases h : P.qz q other = true <;>
      simp [h, canonicalBasisWord, hne]
  · intro hnot
    exact (hnot (Finset.mem_univ target)).elim

/-! ## Typed degree-zero gluing equation -/

/-- The successor X-coordinate carrying one edge of the transposed Q block. -/
def rzMap1QEdgeX
    (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (edge : QDoubleCylinderEdge (transposePresentation P) q S) : RZX P S :=
  Sum.inl (Sum.inr ⟨q, edge⟩)

/-- Explicit Q-endpoint plus adjacent-Z-edge coboundary of a Q-cylinder edge. -/
noncomputable def rzMap1QEdgeDelta0BasisImage
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q : P.Q)
    (edge : QDoubleCylinderEdge (transposePresentation P) q S) :
    Word Field (RZQ P S) := by
  classical
  exact canonicalBasisWord
      (Sum.inr ⟨q,
        qDoubleCylinderEdgeStart (transposePresentation P) q S edge⟩) +
    canonicalBasisWord
      (Sum.inr ⟨q,
        qDoubleCylinderEdgeEnd (transposePresentation P) q S edge⟩) +
    ∑ z : P.Z, if hqz : P.qz q z = true then
      canonicalBasisWord
        (Sum.inl ⟨z, qToZDoubleCylinderEdge P
          A4.toTannerSquareAdmissible q z hqz S edge⟩ : RZQ P S)
    else 0

private theorem rzMap1QEdgeDelta0BasisImage_apply_local
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q : P.Q)
    (edge : QDoubleCylinderEdge (transposePresentation P) q S)
    (z : P.Z) (targetEdge : ZDoubleCylinderEdge P z S) :
    rzMap1QEdgeDelta0BasisImage P A4 S q edge (Sum.inl ⟨z, targetEdge⟩) =
      if hqz : P.qz q z = true then
        vertexIndicator
          (qToZDoubleCylinderEdge P A4.toTannerSquareAdmissible
            q z hqz S edge) targetEdge
      else 0 := by
  classical
  unfold rzMap1QEdgeDelta0BasisImage
  simp only [Pi.add_apply, Finset.sum_apply]
  have hqzero : canonicalBasisWord (F := Field)
      (Sum.inr ⟨q,
        qDoubleCylinderEdgeStart (transposePresentation P) q S edge⟩ :
          RZQ P S) (Sum.inl ⟨z, targetEdge⟩) = 0 := by
    simp [canonicalBasisWord]
  have hqone : canonicalBasisWord (F := Field)
      (Sum.inr ⟨q,
        qDoubleCylinderEdgeEnd (transposePresentation P) q S edge⟩ :
          RZQ P S) (Sum.inl ⟨z, targetEdge⟩) = 0 := by
    simp [canonicalBasisWord]
  rw [hqzero, hqone, zero_add, zero_add]
  rw [Finset.sum_eq_single z]
  · by_cases hqz : P.qz q z = true
    · rw [dif_pos hqz, dif_pos hqz]
      by_cases hedge : qToZDoubleCylinderEdge P
          A4.toTannerSquareAdmissible q z hqz S edge = targetEdge
      · subst targetEdge
        simp [canonicalBasisWord, vertexIndicator]
      · have hreverse : targetEdge ≠ qToZDoubleCylinderEdge P
            A4.toTannerSquareAdmissible q z hqz S edge := Ne.symm hedge
        simp [canonicalBasisWord, vertexIndicator, hedge, hreverse]
    · rw [dif_neg hqz, dif_neg hqz]
      rfl
  · intro other _ hother
    by_cases hqz : P.qz q other = true
    · rw [dif_pos hqz]
      have hneq : (Sum.inl ⟨z, targetEdge⟩ : RZQ P S) ≠
          Sum.inl ⟨other, qToZDoubleCylinderEdge P
            A4.toTannerSquareAdmissible q other hqz S edge⟩ := by
        intro heq
        exact hother (congrArg (fun value : RZQ P S => match value with
          | Sum.inl localEdge => localEdge.1
          | Sum.inr _ => z) heq).symm
      simp [canonicalBasisWord, hneq]
    · rw [dif_neg hqz]
      rfl
  · intro hnot
    exact (hnot (Finset.mem_univ z)).elim

private theorem rzMap1QEdgeDelta0BasisImage_apply_q
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q : P.Q)
    (edge : QDoubleCylinderEdge (transposePresentation P) q S)
    (qVertex : Σ q : P.Q,
      QDoubleCylinderVertex (transposePresentation P) q S) :
    rzMap1QEdgeDelta0BasisImage P A4 S q edge (Sum.inr qVertex) =
      canonicalBasisWord (F := Field)
          (Sum.inr ⟨q, qDoubleCylinderEdgeStart
            (transposePresentation P) q S edge⟩ : RZQ P S)
          (Sum.inr qVertex) +
        canonicalBasisWord (F := Field)
          (Sum.inr ⟨q, qDoubleCylinderEdgeEnd
            (transposePresentation P) q S edge⟩ : RZQ P S)
          (Sum.inr qVertex) := by
  classical
  unfold rzMap1QEdgeDelta0BasisImage
  simp only [Pi.add_apply, Finset.sum_apply]
  have hlocal : (∑ z : P.Z, (if hqz : P.qz q z = true then
      canonicalBasisWord (F := Field)
        (Sum.inl ⟨z, qToZDoubleCylinderEdge P
          A4.toTannerSquareAdmissible q z hqz S edge⟩ : RZQ P S)
    else 0) (Sum.inr qVertex)) = 0 := by
    apply Finset.sum_eq_zero
    intro z _
    by_cases hqz : P.qz q z = true
    · rw [dif_pos hqz]
      simp [canonicalBasisWord]
    · rw [dif_neg hqz]
      rfl
  rw [hlocal, add_zero]

private theorem rzMap1QEdgeStart_ne_end
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (edge : QDoubleCylinderEdge (transposePresentation P) q S) :
    qDoubleCylinderEdgeStart (transposePresentation P) q S edge ≠
      qDoubleCylinderEdgeEnd (transposePresentation P) q S edge := by
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
        simp [hstart, hone, qStarEdgeStart]
    · by_cases hend : segment.1 + 1 = S.half
      · simp [hstart, hend]
      · simp [hstart, hend, Fin.ext_iff]
        omega
  · simp [qDoubleCylinderEdgeStart, qDoubleCylinderEdgeEnd]

private theorem rzXQIncidence_qEdge_q_iff
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q targetQ : P.Q)
    (edge : QDoubleCylinderEdge (transposePresentation P) q S)
    (vertex : QDoubleCylinderVertex (transposePresentation P) targetQ S) :
    rzXQIncidence P A4.toTannerSquareAdmissible S
        (rzMap1QEdgeX P S q edge) (Sum.inr ⟨targetQ, vertex⟩) = true ↔
      Exists fun hq : targetQ = q =>
        hq ▸ vertex =
            qDoubleCylinderEdgeStart (transposePresentation P) q S edge ∨
          hq ▸ vertex =
            qDoubleCylinderEdgeEnd (transposePresentation P) q S edge := by
  simp only [rzMap1QEdgeX, rzXQIncidence, decide_eq_true_eq]

private theorem rzXQIncidence_qEdge_q_coefficient
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q targetQ : P.Q)
    (edge : QDoubleCylinderEdge (transposePresentation P) q S)
    (vertex : QDoubleCylinderVertex (transposePresentation P) targetQ S) :
    (if rzXQIncidence P A4.toTannerSquareAdmissible S
          (rzMap1QEdgeX P S q edge) (Sum.inr ⟨targetQ, vertex⟩) = true
      then 1 else 0) =
      canonicalBasisWord (F := Field)
          (Sum.inr ⟨q, qDoubleCylinderEdgeStart
            (transposePresentation P) q S edge⟩ : RZQ P S)
          (Sum.inr ⟨targetQ, vertex⟩) +
        canonicalBasisWord (F := Field)
          (Sum.inr ⟨q, qDoubleCylinderEdgeEnd
            (transposePresentation P) q S edge⟩ : RZQ P S)
          (Sum.inr ⟨targetQ, vertex⟩) := by
  classical
  by_cases hq : targetQ = q
  · subst targetQ
    by_cases hstart : vertex = qDoubleCylinderEdgeStart
        (transposePresentation P) q S edge
    · subst vertex
      have hinc : rzXQIncidence P A4.toTannerSquareAdmissible S
          (rzMap1QEdgeX P S q edge)
          (Sum.inr ⟨q, qDoubleCylinderEdgeStart
            (transposePresentation P) q S edge⟩) = true :=
        (rzXQIncidence_qEdge_q_iff P A4 S q q edge _).2
          ⟨rfl, Or.inl rfl⟩
      rw [if_pos hinc]
      simp [canonicalBasisWord, rzMap1QEdgeStart_ne_end P q S edge]
    · by_cases hend : vertex = qDoubleCylinderEdgeEnd
          (transposePresentation P) q S edge
      · subst vertex
        have hinc : rzXQIncidence P A4.toTannerSquareAdmissible S
            (rzMap1QEdgeX P S q edge)
            (Sum.inr ⟨q, qDoubleCylinderEdgeEnd
              (transposePresentation P) q S edge⟩) = true :=
          (rzXQIncidence_qEdge_q_iff P A4 S q q edge _).2
            ⟨rfl, Or.inr rfl⟩
        rw [if_pos hinc]
        simp [canonicalBasisWord, hstart]
      · have hinc : rzXQIncidence P A4.toTannerSquareAdmissible S
            (rzMap1QEdgeX P S q edge) (Sum.inr ⟨q, vertex⟩) ≠ true := by
          intro h
          obtain ⟨_, hvertex⟩ :=
            (rzXQIncidence_qEdge_q_iff P A4 S q q edge vertex).1 h
          exact hvertex.elim hstart hend
        rw [if_neg hinc]
        simp [canonicalBasisWord, hstart, hend]
  · have hinc : rzXQIncidence P A4.toTannerSquareAdmissible S
        (rzMap1QEdgeX P S q edge) (Sum.inr ⟨targetQ, vertex⟩) ≠ true := by
      intro h
      obtain ⟨heq, _⟩ :=
        (rzXQIncidence_qEdge_q_iff P A4 S q targetQ edge vertex).1 h
      exact hq heq
    rw [if_neg hinc]
    simp [canonicalBasisWord, hq]

/-- Typed canonical-basis δ0 equation for the concrete Q-edge gluing row.
This exposes the actual two Q endpoints and every adjacent Z-edge image; it
does not assemble the downstream full cochain map. -/
theorem rzMap1QEdge_delta0_canonicalBasis
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q : P.Q)
    (edge : QDoubleCylinderEdge (transposePresentation P) q S) :
    tannerCoboundary0
        (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
        (canonicalBasisWord (rzMap1QEdgeX P S q edge)) =
      rzMap1QEdgeDelta0BasisImage P A4 S q edge := by
  classical
  ext target
  erw [tannerCoboundary0_canonicalBasis_apply]
  change (if rzXQIncidence P A4.toTannerSquareAdmissible S
      (rzMap1QEdgeX P S q edge) target = true then 1 else 0) = _
  rcases target with localEdge | qVertex
  · rcases localEdge with ⟨z, targetEdge⟩
    rw [rzMap1QEdgeDelta0BasisImage_apply_local]
    by_cases hqz : P.qz q z = true
    · rw [dif_pos hqz]
      by_cases hedge : qToZDoubleCylinderEdge P
          A4.toTannerSquareAdmissible q z hqz S edge = targetEdge
      · simp [vertexIndicator, hedge, rzMap1QEdgeX, rzXQIncidence, hqz]
      · simp [vertexIndicator, hedge, rzMap1QEdgeX, rzXQIncidence, hqz]
    · rw [dif_neg hqz]
      simp [rzMap1QEdgeX, rzXQIncidence, hqz]
  · rw [rzMap1QEdgeDelta0BasisImage_apply_q]
    rcases qVertex with ⟨targetQ, vertex⟩
    exact rzXQIncidence_qEdge_q_coefficient P A4 S q targetQ edge vertex

/-- The positive start-endpoint coordinate of the typed δ0 basis equation. -/
theorem rzMap1QEdge_delta0_start
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q : P.Q)
    (edge : QDoubleCylinderEdge (transposePresentation P) q S) :
    tannerCoboundary0
        (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
        (canonicalBasisWord (rzMap1QEdgeX P S q edge))
        (Sum.inr ⟨q, qDoubleCylinderEdgeStart
          (transposePresentation P) q S edge⟩) = 1 := by
  rw [rzMap1QEdge_delta0_canonicalBasis,
    rzMap1QEdgeDelta0BasisImage_apply_q]
  simp [canonicalBasisWord, rzMap1QEdgeStart_ne_end P q S edge]

/-- The positive end-endpoint coordinate of the typed δ0 basis equation. -/
theorem rzMap1QEdge_delta0_end
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q : P.Q)
    (edge : QDoubleCylinderEdge (transposePresentation P) q S) :
    tannerCoboundary0
        (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
        (canonicalBasisWord (rzMap1QEdgeX P S q edge))
        (Sum.inr ⟨q, qDoubleCylinderEdgeEnd
          (transposePresentation P) q S edge⟩) = 1 := by
  rw [rzMap1QEdge_delta0_canonicalBasis,
    rzMap1QEdgeDelta0BasisImage_apply_q]
  simp [canonicalBasisWord, rzMap1QEdgeStart_ne_end P q S edge]

/-- The connecting cochain has exactly the fixed Z root and embedded Q root
as its local degree-one coboundary. -/
theorem rzMap1Connector_delta1
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale) :
    rzCzGraphBoundary P z S (rzMap1Connector P A4 q z hqz S) =
      canonicalBasisWord (rzMap1ZRoot P A4 z S) +
        canonicalBasisWord
          (qToZDoubleCylinderVertex P A4.toTannerSquareAdmissible
            q z hqz S (rzMap1QRoot P q S)) := by
  classical
  exact graphBoundary_pathChain
    (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
    (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
    (rzMap1ZRoot P A4 z S)
    (rzMap1ConnectorPath P A4 q z hqz S)

/-- Every actual adjacent Q-Z connector is nonzero.  The proof uses its two
distinct constructor endpoints, not a selected support coordinate. -/
theorem rzMap1Connector_ne_zero
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale) :
    rzMap1Connector P A4 q z hqz S ≠ 0 := by
  classical
  intro hzero
  have hboundary := rzMap1Connector_delta1 P A4 q z hqz S
  rw [hzero, map_zero] at hboundary
  have hcoordinate := congrFun hboundary (rzMap1ZRoot P A4 z S)
  have hendpoint_ne :
      (0, (subdivisionOriginalBoundaryVertex (transposePresentation P) z S
        (rzMap1QBoundaryVertex P A4 q z hqz)).1) ≠
        rzMap1ZRoot P A4 z S := by
    intro heq
    have hstar := Sum.inl.inj (congrArg Prod.snd heq)
    have hvalue := congrArg
      (fun vertex : XStarVertex (transposePresentation P) z => vertex.1) hstar
    change (rzMap1QBoundaryVertex P A4 q z hqz).1 = Vertex.x z at hvalue
    rw [rzMap1QBoundaryVertex_value] at hvalue
    cases hvalue
  rw [qToZDoubleCylinderVertex_qRoot P A4 q z hqz S] at hcoordinate
  change (0 : Field) =
    ((canonicalBasisWord (F := Field) (rzMap1ZRoot P A4 z S) +
      canonicalBasisWord
        ((0, (subdivisionOriginalBoundaryVertex (transposePresentation P) z S
          (rzMap1QBoundaryVertex P A4 q z hqz)).1) :
            ZDoubleCylinderVertex P z S)) :
        Word Field (ZDoubleCylinderVertex P z S))
        (rzMap1ZRoot P A4 z S) at hcoordinate
  simp [canonicalBasisWord, hendpoint_ne] at hcoordinate

/-- The explicit degree-two coordinate map used by the RZ basis equation. -/
noncomputable def map2Coord
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) : Word Field P.Z →ₗ[Field] Word Field (RZZ P S) := by
  classical
  exact wordPushforward (fun z => ⟨z, rzMap1ZRoot P A4 z S⟩)

@[simp] theorem map2Coord_canonicalBasis
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) :
    map2Coord P A4 S (canonicalBasisWord z) =
      canonicalBasisWord ⟨z, rzMap1ZRoot P A4 z S⟩ := by
  classical
  have hbasis : canonicalBasisWord (F := Field) z = Pi.single z 1 := by
    ext target
    by_cases htarget : target = z
    · subst target
      simp [canonicalBasisWord]
    · simp [canonicalBasisWord, htarget]
  rw [hbasis]
  have htarget : canonicalBasisWord (F := Field)
      (⟨z, rzMap1ZRoot P A4 z S⟩ : RZZ P S) =
      Pi.single ⟨z, rzMap1ZRoot P A4 z S⟩ 1 := by
    ext target
    by_cases h : target = ⟨z, rzMap1ZRoot P A4 z S⟩
    · subst target
      simp [canonicalBasisWord]
    · simp [canonicalBasisWord, h]
  rw [htarget]
  exact wordPushforward_single
    (fun z => (⟨z, rzMap1ZRoot P A4 z S⟩ : RZZ P S)) z (1 : Field)

/-- A shifted Q vertex contributes once to each adjacent actual Z block. -/
theorem rzQZIncidence_q_coefficient
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (q : P.Q) (z : P.Z)
    (qVertex : QDoubleCylinderVertex (transposePresentation P) q S)
    (zVertex : ZDoubleCylinderVertex P z S) :
    (if rzQZIncidence P A S (Sum.inr ⟨q, qVertex⟩) ⟨z, zVertex⟩ = true
      then (1 : Field) else 0) =
      if hqz : P.qz q z = true then
        vertexIndicator (qToZDoubleCylinderVertex P A q z hqz S qVertex) zVertex
      else 0 := by
  classical
  by_cases hqz : P.qz q z = true <;>
    simp [rzQZIncidence, vertexIndicator, hqz]

private theorem successor_delta1_qRoot
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q : P.Q) :
    tannerCoboundary1
        (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
        (canonicalBasisWord (embedQRoot P S q (rzMap1QRoot P q S))) =
      ∑ z : P.Z, if hqz : P.qz q z = true then
        canonicalBasisWord
          ⟨z, qToZDoubleCylinderVertex P A4.toTannerSquareAdmissible
            q z hqz S (rzMap1QRoot P q S)⟩
      else 0 := by
  classical
  ext target
  rcases target with ⟨z, vertex⟩
  erw [tannerCoboundary1_canonicalBasis_apply]
  change (if rzQZIncidence P A4.toTannerSquareAdmissible S
      (Sum.inr ⟨q, rzMap1QRoot P q S⟩) ⟨z, vertex⟩ = true
    then (1 : Field) else 0) =
    (∑ other : P.Z, if hqz : P.qz q other = true then
      (canonicalBasisWord
        (⟨other, qToZDoubleCylinderVertex P A4.toTannerSquareAdmissible
          q other hqz S (rzMap1QRoot P q S)⟩ : RZZ P S) : Word Field (RZZ P S))
      else 0) ⟨z, vertex⟩
  rw [rzQZIncidence_q_coefficient, Finset.sum_apply]
  rw [Finset.sum_eq_single z]
  · by_cases hqz : P.qz q z = true
    · simp [hqz, vertexIndicator, canonicalBasisWord, Pi.single_apply,
        Sigma.mk.inj_iff, eq_comm]
    · simp [hqz]
  · intro other _ hne
    by_cases hother : P.qz q other = true
    · rw [dif_pos hother]
      simp only [canonicalBasisWord, Pi.single_apply]
      split
      · rename_i heq
        exact (hne (congrArg Sigma.fst heq).symm).elim
      · rfl
    · rw [dif_neg hother]
      rfl
  · intro hnot
    exact (hnot (Finset.mem_univ z)).elim

private theorem rzQZIncidence_local_same_coefficient
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (z : P.Z) (edge : ZDoubleCylinderEdge P z S)
    (vertex : ZDoubleCylinderVertex P z S) :
    (if rzQZIncidence P A S (Sum.inl ⟨z, edge⟩) ⟨z, vertex⟩ = true
      then (1 : Field) else 0) =
      doubleCylinderEdgeVertexMatrix (transposePresentation P) z S
        vertex edge := by
  classical
  rcases edge with ⟨copy, edge⟩ | boundaryVertex
  · rcases vertex with ⟨vertexCopy, vertex⟩
    fin_cases copy <;> fin_cases vertexCopy
    all_goals
      by_cases hstart : vertex =
        subdivisionEdgeStart (transposePresentation P) z S edge
      · subst vertex
        simp [rzQZIncidence, doubleCylinderEdgeVertexMatrix,
          subdivisionEdgeVertexMatrix,
          subdivisionEdgeStart_ne_end (transposePresentation P) z S edge]
      · by_cases hend : vertex =
          subdivisionEdgeEnd (transposePresentation P) z S edge
        · subst vertex
          simp [rzQZIncidence, doubleCylinderEdgeVertexMatrix,
            subdivisionEdgeVertexMatrix, hstart]
        · simp [rzQZIncidence, doubleCylinderEdgeVertexMatrix,
            subdivisionEdgeVertexMatrix, hstart, hend]
  · rcases vertex with ⟨copy, vertex⟩
    fin_cases copy <;>
      simp [rzQZIncidence, doubleCylinderEdgeVertexMatrix]

private theorem rzQZIncidence_local_different
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (z targetZ : P.Z) (hz : targetZ ≠ z)
    (edge : ZDoubleCylinderEdge P z S)
    (vertex : ZDoubleCylinderVertex P targetZ S) :
    rzQZIncidence P A S (Sum.inl ⟨z, edge⟩) ⟨targetZ, vertex⟩ = false := by
  classical
  simp [rzQZIncidence, hz]

private theorem rzQZIncidence_extendZEdgeWord
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (z : P.Z)
    (word : Word Field (ZDoubleCylinderEdge P z S)) (target : RZZ P S) :
    (∑ source : RZQ P S, extendZEdgeWord P S z word source *
      if rzQZIncidence P A S source target = true then 1 else 0) =
      extendZVertexWord P S z (rzCzGraphBoundary P z S word) target := by
  classical
  rcases target with ⟨targetZ, vertex⟩
  by_cases hz : targetZ = z
  · subst targetZ
    rw [Fintype.sum_sum_type]
    rw [Fintype.sum_sigma]
    rw [Finset.sum_eq_single z]
    · simp only [extendZEdgeWord, dite_true, zero_mul, Finset.sum_const_zero,
        add_zero, extendZVertexWord]
      rw [rzCzGraphBoundary_eq_boundary1 P z S]
      simp only [doubleCylinderBoundary1, Matrix.toLin'_apply,
        Matrix.mulVec, dotProduct]
      refine Finset.sum_congr (by ext edge; simp only [Finset.mem_univ]) ?_
      intro edge _
      rw [rzQZIncidence_local_same_coefficient P A
        S z edge vertex]
      exact mul_comm _ _
    · intro other _ hother
      simp only [extendZEdgeWord, hother, ↓reduceDIte, zero_mul,
        Finset.sum_const_zero]
    · intro hnot
      exact (hnot (Finset.mem_univ z)).elim
  · rw [Fintype.sum_sum_type]
    rw [Fintype.sum_sigma]
    rw [Finset.sum_eq_single z]
    · simp only [extendZEdgeWord, dite_true,
        rzQZIncidence_local_different P A S z
          targetZ hz, Bool.false_eq_true, ↓reduceIte, mul_zero,
        Finset.sum_const_zero, zero_add, extendZVertexWord, hz, dite_false,
        zero_mul]
    · intro other _ hother
      simp only [extendZEdgeWord, hother, ↓reduceDIte, zero_mul,
        Finset.sum_const_zero]
    · intro hnot
      exact (hnot (Finset.mem_univ z)).elim

/-- An extended local Z-edge chain has exactly its extended local graph boundary. -/
theorem rzCoboundary1_extendZEdgeWord
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z)
    (word : Word Field (ZDoubleCylinderEdge P z S)) :
    tannerCoboundary1
        (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
        (extendZEdgeWord P S z word) =
      extendZVertexWord P S z (rzCzGraphBoundary P z S word) := by
  classical
  ext target
  exact rzQZIncidence_extendZEdgeWord P A4.toTannerSquareAdmissible S z word target

/-- Canonical-basis degree-one equation for the concrete RZ map.  This is the
RZ map1/map2 commutation row consumed by the downstream full-map assembler. -/
theorem map1Coord_delta1_canonicalBasis
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q : P.Q) :
    tannerCoboundary1
        (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
        (map1Coord P A4 S (canonicalBasisWord q)) =
      map2Coord P A4 S
        (tannerCoboundary1 P (canonicalBasisWord q)) := by
  classical
  rw [map1Coord_canonicalBasis]
  have hroot : Pi.single
      (embedQRoot P S q (rzMap1QRoot P q S)) (1 : Field) =
      canonicalBasisWord (embedQRoot P S q (rzMap1QRoot P q S)) := by
    ext target
    simp [canonicalBasisWord, Pi.single_apply]
  have hrootMapped := congrArg
    (tannerCoboundary1
      (rzReplacementPresentation P A4.toTannerSquareAdmissible S)) hroot
  calc
    _ = (∑ z : P.Z, if hqz : P.qz q z = true then
          canonicalBasisWord
            ⟨z, qToZDoubleCylinderVertex P A4.toTannerSquareAdmissible
              q z hqz S (rzMap1QRoot P q S)⟩
        else 0) +
        ∑ z : P.Z, if hqz : P.qz q z = true then
          extendZVertexWord P S z
            (rzCzGraphBoundary P z S
              (rzMap1Connector P A4 q z hqz S))
        else 0 := by
      unfold map1BasisImage
      calc
        _ = tannerCoboundary1
              (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
              (Pi.single (embedQRoot P S q (rzMap1QRoot P q S)) 1) +
            tannerCoboundary1
              (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
              (∑ z : P.Z, if hqz : P.qz q z = true then
                extendZEdgeWord P S z
                  (rzMap1Connector P A4 q z hqz S) else 0) :=
          (tannerCoboundary1
            (rzReplacementPresentation P A4.toTannerSquareAdmissible S)).map_add
              _ _
        _ = _ := by
          calc
            _ = tannerCoboundary1
                  (rzReplacementPresentation P
                    A4.toTannerSquareAdmissible S)
                  (canonicalBasisWord
                    (embedQRoot P S q (rzMap1QRoot P q S))) +
                tannerCoboundary1
                  (rzReplacementPresentation P
                    A4.toTannerSquareAdmissible S)
                  (∑ z : P.Z, if hqz : P.qz q z = true then
                    extendZEdgeWord P S z
                      (rzMap1Connector P A4 q z hqz S) else 0) :=
              congrArg₂ (fun first second => first + second)
                hrootMapped rfl
            _ = _ := by
              rw [successor_delta1_qRoot, map_sum]
              apply congrArg (fun value => _ + value)
              apply Finset.sum_congr rfl
              intro z _
              by_cases hqz : P.qz q z = true
              · erw [dif_pos hqz, dif_pos hqz, rzCoboundary1_extendZEdgeWord]
              · erw [dif_neg hqz, dif_neg hqz, map_zero]
                rfl
    _ = (∑ z : P.Z, if hqz : P.qz q z = true then
          canonicalBasisWord
            ⟨z, qToZDoubleCylinderVertex P A4.toTannerSquareAdmissible
              q z hqz S (rzMap1QRoot P q S)⟩
        else 0) +
        ∑ z : P.Z, if hqz : P.qz q z = true then
          (canonicalBasisWord ⟨z, rzMap1ZRoot P A4 z S⟩ +
            canonicalBasisWord
              ⟨z, qToZDoubleCylinderVertex P A4.toTannerSquareAdmissible
                q z hqz S (rzMap1QRoot P q S)⟩)
        else 0 := by
      apply congrArg (fun value => _ + value)
      apply Finset.sum_congr rfl
      intro z _
      by_cases hqz : P.qz q z = true
      · rw [dif_pos hqz, dif_pos hqz,
          rzMap1Connector_delta1, extendZVertexWord_add,
          extendZVertexWord_canonicalBasis,
          extendZVertexWord_canonicalBasis]
      · rw [dif_neg hqz, dif_neg hqz]
    _ = ∑ z : P.Z, if hqz : P.qz q z = true then
          canonicalBasisWord ⟨z, rzMap1ZRoot P A4 z S⟩
        else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro z _
      by_cases hqz : P.qz q z = true
      · rw [dif_pos hqz, dif_pos hqz, dif_pos hqz]
        let qWord : Word Field (RZZ P S) := canonicalBasisWord
          ⟨z, qToZDoubleCylinderVertex P A4.toTannerSquareAdmissible
            q z hqz S (rzMap1QRoot P q S)⟩
        let zWord : Word Field (RZZ P S) :=
          canonicalBasisWord ⟨z, rzMap1ZRoot P A4 z S⟩
        change qWord + (zWord + qWord) = zWord
        calc
          qWord + (zWord + qWord) = (qWord + qWord) + zWord := by
            ac_rfl
          _ = 0 + zWord := by rw [word_add_self]
          _ = zWord := zero_add zWord
      · rw [dif_neg hqz, dif_neg hqz, dif_neg hqz, zero_add]
    _ = _ := by
      rw [tannerCoboundary1_canonicalBasis_sum, map_sum]
      apply Finset.sum_congr rfl
      intro z _
      by_cases hqz : P.qz q z = true
      · rw [dif_pos hqz, if_pos hqz, map2Coord_canonicalBasis]
      · rw [dif_neg hqz, if_neg hqz, map_zero]


end BDL26RZMap1CoordinateBridge
end Coding
end QEC
