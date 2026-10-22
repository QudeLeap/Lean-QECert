import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Encodable.Basic
import QEC.Coding.FiniteAlternatingConstruction.LevelTwoDistance
import QEC.Coding.FourDimensionalToricCode.Decoder.Assembly

/-!
# Finite level-two lookup decoder

The executable search prefers an actual owner-local preimage and otherwise
searches all finite errors. Its properties are proved separately. This module
uses the actual two-local-error separation theorem, not a distance-to-radius
inference. Enumeration is finite; no practical runtime bound is claimed.
-/

namespace QEC.Coding.BDL26LevelTwoDecoder

open BDL26FiniteTannerSquare BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26RXLocalReplacement BDL26TannerLocalRegularity
open BDL26RZMap1CoordinateBridge

/-! Structural instances are explicit so typeclass search does not have to
recover nested presentation parameters from projected carrier types. -/

local instance presentationXDecEq (P : TannerSquarePresentation) : DecidableEq P.X :=
  P.data.xDecidableEq
local instance presentationQDecEq (P : TannerSquarePresentation) : DecidableEq P.Q :=
  P.data.qDecidableEq
local instance presentationZDecEq (P : TannerSquarePresentation) : DecidableEq P.Z :=
  P.data.zDecidableEq
local instance presentationFaceDecEq (P : TannerSquarePresentation) : DecidableEq P.Face :=
  P.data.faceDecidableEq

local instance edgeDecEq (P : TannerSquarePresentation) :
    DecidableEq (Edge P) := by
  letI : DecidableEq P.X := P.data.xDecidableEq
  letI : DecidableEq P.Q := P.data.qDecidableEq
  letI : DecidableEq P.Z := P.data.zDecidableEq
  letI : DecidableEq P.Face := P.data.faceDecidableEq
  dsimp [Edge, XQEdge, QZEdge]
  infer_instance

local instance xStarVertexDecEq (P : TannerSquarePresentation) (x : P.X) :
    DecidableEq (XStarVertex P x) := by
  dsimp [XStarVertex]
  infer_instance

local instance xStarEdgeDecEq (P : TannerSquarePresentation) (x : P.X) :
    DecidableEq (XStarEdge P x) := by
  letI : DecidableEq (Edge P) := edgeDecEq P
  dsimp [XStarEdge]
  infer_instance

local instance xStarFaceDecEq (P : TannerSquarePresentation) (x : P.X) :
    DecidableEq (XStarFace P x) := by
  letI : DecidableEq P.Face := P.data.faceDecidableEq
  dsimp [XStarFace]
  infer_instance

local instance subdivisionVertexDecEq (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    DecidableEq (SubdivisionVertex P x S) := by
  letI : DecidableEq (XStarVertex P x) := xStarVertexDecEq P x
  letI : DecidableEq (XStarEdge P x) := xStarEdgeDecEq P x
  letI : DecidableEq (XStarFace P x) := xStarFaceDecEq P x
  dsimp [SubdivisionVertex]
  infer_instance

local instance subdivisionEdgeDecEq (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    DecidableEq (SubdivisionEdge P x S) := by
  letI : DecidableEq (XStarVertex P x) := xStarVertexDecEq P x
  letI : DecidableEq (XStarEdge P x) := xStarEdgeDecEq P x
  letI : DecidableEq (XStarFace P x) := xStarFaceDecEq P x
  dsimp [SubdivisionEdge]
  infer_instance

local instance subdivisionFaceDecEq (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    DecidableEq (SubdivisionFace P x S) := by
  letI : DecidableEq (XStarVertex P x) := xStarVertexDecEq P x
  letI : DecidableEq (XStarEdge P x) := xStarEdgeDecEq P x
  letI : DecidableEq (XStarFace P x) := xStarFaceDecEq P x
  dsimp [SubdivisionFace]
  infer_instance

local instance subdivisionBoundaryVertexDecEq (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    DecidableEq (SubdivisionBoundaryVertex P x S) := by
  letI : DecidableEq (SubdivisionVertex P x S) := subdivisionVertexDecEq P x S
  dsimp [SubdivisionBoundaryVertex]
  infer_instance

local instance subdivisionBoundaryEdgeDecEq (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    DecidableEq (SubdivisionBoundaryEdge P x S) := by
  letI : DecidableEq (SubdivisionEdge P x S) := subdivisionEdgeDecEq P x S
  dsimp [SubdivisionBoundaryEdge]
  infer_instance

local instance doubleCylinderVertexDecEq (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    DecidableEq (DoubleCylinderVertex P x S) := by
  letI : DecidableEq (SubdivisionVertex P x S) := subdivisionVertexDecEq P x S
  dsimp [DoubleCylinderVertex]
  infer_instance

local instance doubleCylinderEdgeDecEq (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    DecidableEq (DoubleCylinderEdge P x S) := by
  letI : DecidableEq (SubdivisionEdge P x S) := subdivisionEdgeDecEq P x S
  letI : DecidableEq (SubdivisionBoundaryVertex P x S) := subdivisionBoundaryVertexDecEq P x S
  dsimp [DoubleCylinderEdge]
  infer_instance

local instance doubleCylinderFaceDecEq (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    DecidableEq (DoubleCylinderFace P x S) := by
  letI : DecidableEq (SubdivisionFace P x S) := subdivisionFaceDecEq P x S
  letI : DecidableEq (SubdivisionBoundaryEdge P x S) := subdivisionBoundaryEdgeDecEq P x S
  dsimp [DoubleCylinderFace]
  infer_instance

local instance qStarEdgeDecEq (P : TannerSquarePresentation) (q : P.Q) :
    DecidableEq (QStarEdge P q) := by
  letI : DecidableEq P.Z := P.data.zDecidableEq
  dsimp [QStarEdge]
  infer_instance

local instance qStarVertexDecEq (P : TannerSquarePresentation) (q : P.Q) :
    DecidableEq (QStarVertex P q) := by
  letI : DecidableEq (QStarEdge P q) := qStarEdgeDecEq P q
  dsimp [QStarVertex]
  infer_instance

local instance qSubdivisionVertexDecEq (P : TannerSquarePresentation) (q : P.Q) (S : OddScale) :
    DecidableEq (QSubdivisionVertex P q S) := by
  letI : DecidableEq (QStarEdge P q) := qStarEdgeDecEq P q
  letI : DecidableEq (QStarVertex P q) := qStarVertexDecEq P q
  dsimp [QSubdivisionVertex]
  infer_instance

local instance qSubdivisionEdgeDecEq (P : TannerSquarePresentation) (q : P.Q) (S : OddScale) :
    DecidableEq (QSubdivisionEdge P q S) := by
  letI : DecidableEq (QStarEdge P q) := qStarEdgeDecEq P q
  letI : DecidableEq (QStarVertex P q) := qStarVertexDecEq P q
  dsimp [QSubdivisionEdge]
  infer_instance

local instance qDoubleCylinderVertexDecEq (P : TannerSquarePresentation) (q : P.Q) (S : OddScale) :
    DecidableEq (QDoubleCylinderVertex P q S) := by
  letI : DecidableEq (QSubdivisionVertex P q S) := qSubdivisionVertexDecEq P q S
  dsimp [QDoubleCylinderVertex]
  infer_instance

local instance qDoubleCylinderEdgeDecEq (P : TannerSquarePresentation) (q : P.Q) (S : OddScale) :
    DecidableEq (QDoubleCylinderEdge P q S) := by
  letI : DecidableEq (QSubdivisionEdge P q S) := qSubdivisionEdgeDecEq P q S
  letI : DecidableEq (QStarEdge P q) := qStarEdgeDecEq P q
  dsimp [QDoubleCylinderEdge]
  infer_instance

local instance rx0DecEq (P : TannerSquarePresentation) (S : OddScale) :
    DecidableEq (RX0 P S) := by
  letI : DecidableEq P.X := P.data.xDecidableEq
  letI : DecidableEq P.Q := P.data.qDecidableEq
  letI : DecidableEq P.Z := P.data.zDecidableEq
  letI : DecidableEq P.Face := P.data.faceDecidableEq
  letI : ∀ x : P.X, DecidableEq (DoubleCylinderVertex P x S) := fun x => doubleCylinderVertexDecEq P x S
  letI : ∀ x : P.X, DecidableEq (DoubleCylinderEdge P x S) := fun x => doubleCylinderEdgeDecEq P x S
  letI : ∀ x : P.X, DecidableEq (DoubleCylinderFace P x S) := fun x => doubleCylinderFaceDecEq P x S
  letI : ∀ q : P.Q, DecidableEq (QDoubleCylinderVertex P q S) := fun q => qDoubleCylinderVertexDecEq P q S
  letI : ∀ q : P.Q, DecidableEq (QDoubleCylinderEdge P q S) := fun q => qDoubleCylinderEdgeDecEq P q S
  dsimp [RX0]
  infer_instance

local instance rx1DecEq (P : TannerSquarePresentation) (S : OddScale) :
    DecidableEq (RX1 P S) := by
  letI : DecidableEq P.X := P.data.xDecidableEq
  letI : DecidableEq P.Q := P.data.qDecidableEq
  letI : DecidableEq P.Z := P.data.zDecidableEq
  letI : DecidableEq P.Face := P.data.faceDecidableEq
  letI : ∀ x : P.X, DecidableEq (DoubleCylinderVertex P x S) := fun x => doubleCylinderVertexDecEq P x S
  letI : ∀ x : P.X, DecidableEq (DoubleCylinderEdge P x S) := fun x => doubleCylinderEdgeDecEq P x S
  letI : ∀ x : P.X, DecidableEq (DoubleCylinderFace P x S) := fun x => doubleCylinderFaceDecEq P x S
  letI : ∀ q : P.Q, DecidableEq (QDoubleCylinderVertex P q S) := fun q => qDoubleCylinderVertexDecEq P q S
  letI : ∀ q : P.Q, DecidableEq (QDoubleCylinderEdge P q S) := fun q => qDoubleCylinderEdgeDecEq P q S
  dsimp [RX1]
  infer_instance

local instance rx2DecEq (P : TannerSquarePresentation) (S : OddScale) :
    DecidableEq (RX2 P S) := by
  letI : DecidableEq P.X := P.data.xDecidableEq
  letI : DecidableEq P.Q := P.data.qDecidableEq
  letI : DecidableEq P.Z := P.data.zDecidableEq
  letI : DecidableEq P.Face := P.data.faceDecidableEq
  letI : ∀ x : P.X, DecidableEq (DoubleCylinderVertex P x S) := fun x => doubleCylinderVertexDecEq P x S
  letI : ∀ x : P.X, DecidableEq (DoubleCylinderEdge P x S) := fun x => doubleCylinderEdgeDecEq P x S
  letI : ∀ x : P.X, DecidableEq (DoubleCylinderFace P x S) := fun x => doubleCylinderFaceDecEq P x S
  letI : ∀ q : P.Q, DecidableEq (QDoubleCylinderVertex P q S) := fun q => qDoubleCylinderVertexDecEq P q S
  letI : ∀ q : P.Q, DecidableEq (QDoubleCylinderEdge P q S) := fun q => qDoubleCylinderEdgeDecEq P q S
  dsimp [RX2]
  infer_instance

local instance rxLocalFaceDecEq (P : TannerSquarePresentation) (S : OddScale) :
    DecidableEq (RXLocalFace P S) := by
  letI : DecidableEq P.X := P.data.xDecidableEq
  letI : ∀ x : P.X, DecidableEq (DoubleCylinderFace P x S) :=
    fun x => doubleCylinderFaceDecEq P x S
  dsimp [RXLocalFace]
  infer_instance

local instance rxGlueFaceDecEq (P : TannerSquarePresentation) (S : OddScale) :
    DecidableEq (RXXQGlueFace P S) := by
  letI : DecidableEq (XQEdge P) := by
    letI : DecidableEq P.X := P.data.xDecidableEq
    letI : DecidableEq P.Q := P.data.qDecidableEq
    dsimp [XQEdge]
    infer_instance
  letI : ∀ q : P.Q, DecidableEq (QDoubleCylinderEdge P q S) :=
    fun q => qDoubleCylinderEdgeDecEq P q S
  dsimp [RXXQGlueFace]
  infer_instance

local instance rxFaceDecEq (P : TannerSquarePresentation) (S : OddScale) :
    DecidableEq (RXFace P S) := by
  letI : DecidableEq (RXLocalFace P S) := rxLocalFaceDecEq P S
  letI : DecidableEq (RXXQGlueFace P S) := rxGlueFaceDecEq P S
  letI : DecidableEq (RXOldZFace P) := by
    letI : DecidableEq P.Face := P.data.faceDecidableEq
    dsimp [RXOldZFace]
    infer_instance
  dsimp [RXFace]
  infer_instance

/-- Computable RX corner coordinates, identical to the materialized constructor.
The original declaration is conservatively marked noncomputable; these clauses
use only the existing grid and edge constructors. -/
def rxFaceXExecutable (P : TannerSquarePresentation) (S : OddScale) :
    RXFace P S → RX0 P S
  | .inl ⟨x, .inl copyFace, corner⟩ =>
      ⟨x, (copyFace.1, subdivisionGridVertex P x S copyFace.2.1
        (BDL26RXLocalReplacement.gridEndpoint copyFace.2.2.1 corner.1)
        (BDL26RXLocalReplacement.gridEndpoint copyFace.2.2.2 corner.2))⟩
  | .inl ⟨x, .inr rectangle, corner⟩ =>
      ⟨x, doubleCylinderRectangleCorner P x S rectangle corner⟩
  | .inr (.inl face) => BDL26RXLocalReplacement.glueFaceX P S face
  | .inr (.inr face) => oldZFaceX P S face

theorem rxFaceXExecutable_eq (P : TannerSquarePresentation) (S : OddScale) :
    rxFaceXExecutable P S = rxFaceX P S := by
  funext face
  rcases face with ⟨x, cell, corner⟩ | glue | old
  · cases cell <;> rfl
  · rfl
  · rfl

/-- Computable materialized RX Q corners. -/
def rxFaceQExecutable (P : TannerSquarePresentation) (S : OddScale) :
    RXFace P S → BDL26FiniteTannerSquare.Two → RX1 P S
  | .inl ⟨x, .inl copyFace, corner⟩, bit =>
      .inl ⟨x, .inl (copyFace.1, subdivisionFaceBoundaryEdge P x S copyFace.2
        (if bit = 0 then (0, corner.2) else (1, corner.1)))⟩
  | .inl ⟨x, .inr rectangle, corner⟩, bit =>
      .inl ⟨x, doubleCylinderRectangleBoundaryEdge P x S rectangle
        (if bit = 0 then (0, corner.1) else (1, corner.2))⟩
  | .inr (.inl face), bit =>
      BDL26RXLocalReplacement.twoSelect
        (BDL26RXLocalReplacement.glueFaceQ0 P S face)
        (BDL26RXLocalReplacement.glueFaceQ1 P S face) bit
  | .inr (.inr face), bit => oldZFaceQ P S bit face

theorem rxFaceQExecutable_eq (P : TannerSquarePresentation) (S : OddScale) :
    rxFaceQExecutable P S = rxFaceQ P S := by
  funext face bit
  rcases face with ⟨x, cell, corner⟩ | glue | old
  · cases cell <;> by_cases h : bit = 0 <;>
      simp [rxFaceQExecutable, rxFaceQ, BDL26RXLocalReplacement.twoSelect,
        BDL26RXLocalReplacement.localFaceQ0, BDL26RXLocalReplacement.localFaceQ1,
        localFaceQ0Edge, localFaceQ1Edge, localFaceQ0EdgeAt, localFaceQ1EdgeAt, h]
  · rfl
  · rfl

/-- Boolean decisions agree independently of their decision procedures. -/
theorem decide_congr_explicit (p q : Prop) (dp : Decidable p) (dq : Decidable q)
    (h : p ↔ q) : @decide p dp = @decide q dq := by
  cases dp <;> cases dq <;> simp_all

/-- Executable RX incidence, separated from its presentation packaging. -/
def rxXQExecutable (P : TannerSquarePresentation) (S : OddScale)
    (x : RX0 P S) (q : RX1 P S) : Bool :=
  decide (∃ f : RXFace P S, ∃ i : BDL26FiniteTannerSquare.Two,
    rxFaceXExecutable P S f = x ∧ rxFaceQExecutable P S f i = q)

def rxQZExecutable (P : TannerSquarePresentation) (S : OddScale)
    (q : RX1 P S) (z : RX2 P S) : Bool :=
  decide (∃ f : RXFace P S, ∃ i : BDL26FiniteTannerSquare.Two,
    rxFaceQExecutable P S f i = q ∧ rxFaceZ P S f = z)

theorem rxXQExecutable_eq (P : TannerSquarePresentation) (S : OddScale) :
    rxXQExecutable P S = rxXQIncidence P S := by
  funext x q
  unfold rxXQExecutable rxXQIncidence
  exact decide_congr_explicit _ _ _ _ (by
    simp only [rxFaceXExecutable_eq, rxFaceQExecutable_eq])

theorem rxQZExecutable_eq (P : TannerSquarePresentation) (S : OddScale) :
    rxQZExecutable P S = rxQZIncidence P S := by
  funext q z
  unfold rxQZExecutable rxQZIncidence
  exact decide_congr_explicit _ _ _ _ (by
    simp only [rxFaceQExecutable_eq])

/-- The actual RX raw presentation with structural decidable equality and
finite Boolean face-incidence tests. No selected face or correctness field. -/
def rxDataExecutable (P : TannerSquarePresentation) (S : OddScale) :
    TannerSquareData where
  X := RX0 P S
  Q := RX1 P S
  Z := RX2 P S
  Face := RXFace P S
  xFintype := inferInstance
  qFintype := inferInstance
  zFintype := inferInstance
  faceFintype := inferInstance
  xDecidableEq := inferInstance
  qDecidableEq := inferInstance
  zDecidableEq := inferInstance
  faceDecidableEq := inferInstance
  xq := rxXQExecutable P S
  qz := rxQZExecutable P S
  faceX := rxFaceXExecutable P S
  faceQ := rxFaceQExecutable P S
  faceZ := rxFaceZ P S
  faceQ_xq := by
    intro f i
    apply decide_eq_true
    exact ⟨f, i, rfl, rfl⟩
  faceQ_qz := by
    intro f i
    apply decide_eq_true
    exact ⟨f, i, rfl, rfl⟩

/-- Reification preserves every raw field, including the actual incidence. -/
theorem rxDataExecutable_eq (P : TannerSquarePresentation) (S : OddScale) :
    rxDataExecutable P S = rxReplacementData P S := by
  unfold rxDataExecutable rxReplacementData
  simp only [rxXQExecutable_eq, rxQZExecutable_eq,
    rxFaceXExecutable_eq, rxFaceQExecutable_eq]
  congr 1 <;> exact Subsingleton.elim _ _

/-- Executable packaging of the same RX presentation. Validity is transported
from its existing proof, never supplied by the decoder caller. -/
def rxPresentationExecutable (P : TannerSquarePresentation) (S : OddScale) :
    TannerSquarePresentation where
  data := rxDataExecutable P S
  perfectPairing := by
    rw [rxDataExecutable_eq]
    exact rxReplacementPerfectPairing P S

theorem rxPresentationExecutable_eq (P : TannerSquarePresentation) (S : OddScale) :
    rxPresentationExecutable P S = rxReplacementPresentation P S := by
  unfold rxPresentationExecutable rxReplacementPresentation
  congr 1
  exact rxDataExecutable_eq P S

/-- Transposition changes only finite raw fields at runtime. -/
def transposeExecutable (P : TannerSquarePresentation) : TannerSquarePresentation where
  data := transposeTannerSquareData P
  perfectPairing := (transposePresentation P).perfectPairing

theorem transposeExecutable_eq (P : TannerSquarePresentation) :
    transposeExecutable P = transposePresentation P := rfl

/-- Choice-free Q-to-Z vertex coordinates. The admissibility witness is used
only to certify membership of the explicit tags, and is erased at runtime. -/
def qToZVertexExecutable (P : TannerSquarePresentation)
    (hasA : Nonempty (TannerSquareAdmissible P))
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale) :
    QDoubleCylinderVertex (transposePresentation P) q S →
      ZDoubleCylinderVertex P z S
  | (copy, .inl (.inl _)) =>
      (copy, .inl ⟨Vertex.q q, by
        obtain ⟨A⟩ := hasA
        exact (xStarBoundaryVertexToStar (transposePresentation P) z
          ((transposeXStarBoundaryVertexEquiv P z).symm
            (qToZBoundaryVertex P A q z hqz (.inl ())))).property⟩)
  | (copy, .inl (.inr edge)) =>
      (copy, .inl ⟨Vertex.z edge.1, by
        obtain ⟨A⟩ := hasA
        exact (xStarBoundaryVertexToStar (transposePresentation P) z
          ((transposeXStarBoundaryVertexEquiv P z).symm
            (qToZBoundaryVertex P A q z hqz (.inr edge)))).property⟩)
  | (copy, .inr edgeInterior) =>
      (copy, .inr (.inl (⟨.inr ⟨(q, edgeInterior.1.1), edgeInterior.1.2⟩, by
        obtain ⟨A⟩ := hasA
        exact (xStarBoundaryEdgeToStar (transposePresentation P) z
          ((transposeXStarBoundaryEdgeEquiv P z).symm
            (qToZBoundaryEdge P q z hqz edgeInterior.1))).property⟩,
        edgeInterior.2)))

/-- The explicit Q-to-Z coordinates erase no physical tag. -/
theorem qToZVertexExecutable_eq (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q) (z : P.Z)
    (hqz : P.qz q z = true) (S : OddScale) :
    qToZVertexExecutable P ⟨A⟩ q z hqz S =
      qToZDoubleCylinderVertex P A q z hqz S := by
  funext vertex
  rcases vertex with ⟨copy, (unit | endpoint) | interior⟩ <;> rfl

/-- Structural endpoint matrix with computational equality tests. -/
def cylinderVertexMatrixExecutable (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) :
    DoubleCylinderVertex P x S → DoubleCylinderEdge P x S → ZMod 2
  | v, .inl e =>
      if v.1 = e.1 then
        (if v.2 = subdivisionEdgeStart P x S e.2 then 1 else 0) +
          (if v.2 = subdivisionEdgeEnd P x S e.2 then 1 else 0)
      else 0
  | v, .inr endpoint => if v.2 = endpoint.1 then 1 else 0

theorem cylinderVertexMatrixExecutable_eq (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) :
    cylinderVertexMatrixExecutable P x S = doubleCylinderEdgeVertexMatrix P x S := by
  funext v e
  cases e <;> simp only [cylinderVertexMatrixExecutable,
    doubleCylinderEdgeVertexMatrix, subdivisionEdgeVertexMatrix] <;> split_ifs <;> rfl

local instance zCylinderVertexDecEq (P : TannerSquarePresentation) (z : P.Z)
    (S : OddScale) : DecidableEq (ZDoubleCylinderVertex P z S) := by
  letI : DecidableEq (SubdivisionVertex (transposePresentation P) z S) :=
    subdivisionVertexDecEq (transposeExecutable P) z S
  change DecidableEq (BDL26FiniteTannerSquare.Two ×
    SubdivisionVertex (transposePresentation P) z S)
  infer_instance

local instance rzQExecutableFintype (P : TannerSquarePresentation) (S : OddScale) :
    Fintype (BDL26RZLocalReplacement.RZQ P S) := by
  dsimp [BDL26RZLocalReplacement.RZQ, ZDoubleCylinderEdge, QDoubleCylinderVertex,
    DoubleCylinderEdge, transposePresentation, transposeTannerSquareData]
  infer_instance

/-- Computational RZ Q-Z incidence on the actual constructor coordinates. -/
def rzIncidenceExecutable (P : TannerSquarePresentation)
    (hasA : Nonempty (TannerSquareAdmissible P)) (S : OddScale) :
    BDL26RZLocalReplacement.RZQ P S → BDL26RZLocalReplacement.RZZ P S → Bool
  | .inl e, v =>
      if h : v.1 = e.1 then
        decide (cylinderVertexMatrixExecutable (transposeExecutable P) e.1 S
          (h ▸ v.2) e.2 = 1)
      else false
  | .inr q, v =>
      if h : P.qz q.1 v.1 = true then
        decide (qToZVertexExecutable P hasA q.1 v.1 h S q.2 = v.2)
      else false

/-- Every incidence bit is the original materialized RZ bit. -/
theorem rzIncidenceExecutable_eq (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) :
    rzIncidenceExecutable P ⟨A⟩ S = BDL26RZLocalReplacement.rzQZIncidence P A S := by
  funext q v
  rcases q with e | q
  · by_cases h : v.1 = e.1
    · simp only [rzIncidenceExecutable, dif_pos h, transposeExecutable_eq]
      erw [cylinderVertexMatrixExecutable_eq (transposePresentation P) e.1 S]
      simp [BDL26RZLocalReplacement.rzQZIncidence, h]
      exact @Bool.decide_congr _ _ _ _ Iff.rfl
    · simp [rzIncidenceExecutable, BDL26RZLocalReplacement.rzQZIncidence, h]
  · by_cases h : P.qz q.1 v.1 = true
    · simp only [rzIncidenceExecutable, dif_pos h]
      rw [qToZVertexExecutable_eq P A q.1 v.1 h S]
      simp [BDL26RZLocalReplacement.rzQZIncidence, h]
    · simp [rzIncidenceExecutable, BDL26RZLocalReplacement.rzQZIncidence, h]

/-- Constructor-tag encoding of Tanner vertices. -/
instance vertexEncodable (P : TannerSquarePresentation)
    [Encodable P.X] [Encodable P.Q] [Encodable P.Z] : Encodable (Vertex P) :=
  Encodable.ofEquiv (P.X ⊕ (P.Q ⊕ P.Z))
    { toFun := fun v => match v with
        | .x x => .inl x
        | .q q => .inr (.inl q)
        | .z z => .inr (.inr z)
      invFun := fun v => match v with
        | .inl x => .x x
        | .inr (.inl q) => .q q
        | .inr (.inr z) => .z z
      left_inv := by intro v; cases v <;> rfl
      right_inv := by rintro (x | q | z) <;> rfl }

/-- A deterministic, executable ordering of an explicitly encodable finite
carrier. Sorting its finite set does not use `Fintype.equivFin` or choice. -/
def coordinates (α : Type) [Fintype α] [Encodable α] : List α :=
  letI : LinearOrder α := LinearOrder.lift' Encodable.encode Encodable.encode_injective
  Finset.univ.sort

theorem mem_coordinates (α : Type) [Fintype α] [Encodable α] (a : α) :
    a ∈ coordinates α := by
  unfold coordinates
  simp

/-- Enumerate all binary words supported on the listed coordinates. -/
def wordsOn {α : Type} [DecidableEq α] : List α → List (Word (ZMod 2) α)
  | [] => [0]
  | q :: rest =>
      (wordsOn rest).map (fun e => Function.update e q 0) ++
        (wordsOn rest).map (fun e => Function.update e q 1)

/-- Every binary word vanishing off the coordinate list is enumerated. -/
theorem mem_wordsOn {α : Type} [DecidableEq α] (qs : List α)
    (e : Word (ZMod 2) α) (houtside : ∀ q, q ∉ qs → e q = 0) :
    e ∈ wordsOn qs := by
  induction qs generalizing e with
  | nil =>
      have he : e = 0 := by funext q; exact houtside q (by simp)
      simp [wordsOn, he]
  | cons q rest ih =>
      let tail := Function.update e q 0
      have htail : tail ∈ wordsOn rest := by
        apply ih
        intro r hr
        by_cases h : r = q
        · subst r; simp [tail]
        · simp [tail, h, houtside r (by simp [h, hr])]
      have he : Function.update tail q (e q) = e := by
        funext r
        by_cases h : r = q <;> simp [tail, h]
      have hbinary : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
      rcases hbinary (e q) with hzero | hone
      · apply List.mem_append_left
        exact List.mem_map.mpr ⟨tail, htail, by simpa [hzero] using he⟩
      · apply List.mem_append_right
        exact List.mem_map.mpr ⟨tail, htail, by simpa [hone] using he⟩

/-- Complete executable finite error table, with no promise of feasible size. -/
def allWords (α : Type) [Fintype α] [Encodable α] [DecidableEq α] :
    List (Word (ZMod 2) α) := wordsOn (coordinates α)

theorem mem_allWords (α : Type) [Fintype α] [Encodable α] [DecidableEq α]
    (e : Word (ZMod 2) α) : e ∈ allWords α :=
  mem_wordsOn _ e (fun q h => False.elim (h (mem_coordinates α q)))

/-- Left-to-right finite search with no representative-choice primitive. -/
def search {α : Type} (accept : α → Bool) : List α → Option α
  | [] => none
  | a :: rest => if accept a then some a else search accept rest

/-- Every returned entry belongs to the input table and passes its test. -/
theorem search_sound {α : Type} (accept : α → Bool) (entries : List α)
    (a : α) (h : search accept entries = some a) :
    a ∈ entries ∧ accept a = true := by
  induction entries with
  | nil => simp [search] at h
  | cons b rest ih =>
      by_cases hb : accept b = true
      · simp [search, hb] at h
        subst a
        exact ⟨List.mem_cons_self, hb⟩
      · have hr : search accept rest = some a := by simpa [search, hb] using h
        obtain ⟨hm, ha⟩ := ih hr
        exact ⟨List.mem_cons_of_mem b hm, ha⟩

/-- A passing entry guarantees successful finite search. -/
theorem search_complete {α : Type} (accept : α → Bool) (entries : List α)
    (hex : ∃ a ∈ entries, accept a = true) :
    ∃ a, search accept entries = some a := by
  induction entries with
  | nil => simp at hex
  | cons b rest ih =>
      by_cases hb : accept b = true
      · exact ⟨b, by simp [search, hb]⟩
      · obtain ⟨a, hm, ha⟩ := hex
        have hm' : a ∈ rest := by
          rcases List.mem_cons.mp hm with heq | hm
          · subst a
            exact False.elim (hb ha)
          · exact hm
        obtain ⟨r, hr⟩ := ih ⟨a, hm', ha⟩
        exact ⟨r, by simpa [search, hb] using hr⟩

/-- Executable local-first lookup. The last default is used only for inputs
outside the represented syndrome domain; range correctness excludes it. -/
def lookup {Error Syndrome : Type} [DecidableEq Syndrome]
    (entries : List Error) (syndrome : Error → Syndrome)
    (isLocal : Error → Bool) (fallback : Error) (sigma : Syndrome) : Error :=
  match search (fun e => isLocal e && decide (syndrome e = sigma)) entries with
  | some e => e
  | none => (search (fun e => decide (syndrome e = sigma)) entries).getD fallback

/-- Exhaustive finite lookup is a right inverse on the actual represented image. -/
theorem lookup_syndrome {Error Syndrome : Type} [DecidableEq Syndrome]
    (entries : List Error) (syndrome : Error → Syndrome)
    (isLocal : Error → Bool) (fallback : Error) (sigma : Syndrome)
    (hex : ∃ e ∈ entries, syndrome e = sigma) :
    syndrome (lookup entries syndrome isLocal fallback sigma) = sigma := by
  unfold lookup
  cases hlocal : search (fun e => isLocal e && decide (syndrome e = sigma)) entries with
  | some e =>
      have h := (search_sound _ _ _ hlocal).2
      simpa using ((Bool.and_eq_true_eq_eq_true_and_eq_true _ _).mp h).2
  | none =>
      obtain ⟨e, hm, he⟩ := hex
      obtain ⟨r, hr⟩ := search_complete
        (fun e => decide (syndrome e = sigma)) entries ⟨e, hm, by simpa using he⟩
      simp only [hr, Option.getD_some]
      simpa using (search_sound _ _ _ hr).2

/-- When a local preimage exists, the selected representative is local. -/
theorem lookup_local {Error Syndrome : Type} [DecidableEq Syndrome]
    (entries : List Error) (syndrome : Error → Syndrome)
    (isLocal : Error → Bool) (fallback : Error) (sigma : Syndrome)
    (hex : ∃ e ∈ entries, isLocal e = true ∧ syndrome e = sigma) :
    isLocal (lookup entries syndrome isLocal fallback sigma) = true := by
  obtain ⟨e, hm, hl, hs⟩ := hex
  obtain ⟨r, hr⟩ := search_complete
    (fun e => isLocal e && decide (syndrome e = sigma)) entries
    ⟨e, hm, by simp [hl, hs]⟩
  unfold lookup
  rw [hr]
  exact ((Bool.and_eq_true_eq_eq_true_and_eq_true _ _).mp (search_sound _ _ _ hr).2).1

local instance baseXEncodable : Encodable baseTannerSquarePresentation.X :=
  inferInstanceAs (Encodable (Fin 2))
local instance baseQEncodable : Encodable baseTannerSquarePresentation.Q :=
  inferInstanceAs (Encodable (Fin 5))
local instance baseZEncodable : Encodable baseTannerSquarePresentation.Z :=
  inferInstanceAs (Encodable (Fin 2))
local instance baseFaceEncodable : Encodable baseTannerSquarePresentation.Face :=
  inferInstanceAs (Encodable (Fin 4))

local instance subdivisionVertexEncodable (P : TannerSquarePresentation)
    [Encodable P.X] [Encodable P.Q] [Encodable P.Z] [Encodable P.Face]
    (x : P.X) (S : OddScale) : Encodable (SubdivisionVertex P x S) := by
  dsimp [SubdivisionVertex, XStarVertex, XStarEdge, XStarFace, Edge, XQEdge, QZEdge]
  infer_instance

local instance subdivisionEdgeEncodable (P : TannerSquarePresentation)
    [Encodable P.X] [Encodable P.Q] [Encodable P.Z] [Encodable P.Face]
    (x : P.X) (S : OddScale) : Encodable (SubdivisionEdge P x S) := by
  dsimp [SubdivisionEdge, XStarEdge, XStarFace, Edge, XQEdge, QZEdge]
  infer_instance

/-- Computable representation of the actual first replacement. -/
def executableLevelOne (S : OddScale) : TannerSquarePresentation :=
  rxPresentationExecutable baseTannerSquarePresentation S

theorem executableLevelOne_eq (S : OddScale) :
    executableLevelOne S = levelOnePresentation S :=
  rxPresentationExecutable_eq baseTannerSquarePresentation S

instance executableLevelOneXEncodable (S : OddScale) :
    Encodable (executableLevelOne S).X := by
  change Encodable (RX0 baseTannerSquarePresentation S)
  dsimp [RX0, RXLocalFace, RXXQGlueFace, RXOldZFace,
    DoubleCylinderVertex, DoubleCylinderEdge, DoubleCylinderFace,
    SubdivisionVertex, SubdivisionEdge, SubdivisionFace,
    SubdivisionBoundaryVertex, SubdivisionBoundaryEdge,
    XStarVertex, XStarEdge, XStarFace, Edge, XQEdge, QZEdge,
    QDoubleCylinderVertex, QDoubleCylinderEdge, QSubdivisionVertex,
    QSubdivisionEdge, QStarVertex, QStarEdge]
  infer_instance

instance executableLevelOneQEncodable (S : OddScale) :
    Encodable (executableLevelOne S).Q := by
  change Encodable (RX1 baseTannerSquarePresentation S)
  dsimp [RX1, RXLocalFace, RXXQGlueFace, RXOldZFace,
    DoubleCylinderVertex, DoubleCylinderEdge, DoubleCylinderFace,
    SubdivisionVertex, SubdivisionEdge, SubdivisionFace,
    SubdivisionBoundaryVertex, SubdivisionBoundaryEdge,
    XStarVertex, XStarEdge, XStarFace, Edge, XQEdge, QZEdge,
    QDoubleCylinderVertex, QDoubleCylinderEdge, QSubdivisionVertex,
    QSubdivisionEdge, QStarVertex, QStarEdge]
  infer_instance

instance executableLevelOneZEncodable (S : OddScale) :
    Encodable (executableLevelOne S).Z := by
  change Encodable (RX2 baseTannerSquarePresentation S)
  dsimp [RX2, RXLocalFace, RXXQGlueFace, RXOldZFace,
    DoubleCylinderVertex, DoubleCylinderEdge, DoubleCylinderFace,
    SubdivisionVertex, SubdivisionEdge, SubdivisionFace,
    SubdivisionBoundaryVertex, SubdivisionBoundaryEdge,
    XStarVertex, XStarEdge, XStarFace, Edge, XQEdge, QZEdge,
    QDoubleCylinderVertex, QDoubleCylinderEdge, QSubdivisionVertex,
    QSubdivisionEdge, QStarVertex, QStarEdge]
  infer_instance

instance executableLevelOneFaceEncodable (S : OddScale) :
    Encodable (executableLevelOne S).Face := by
  change Encodable (RXFace baseTannerSquarePresentation S)
  dsimp [RXFace, RXLocalFace, RXXQGlueFace, RXOldZFace,
    DoubleCylinderVertex, DoubleCylinderEdge, DoubleCylinderFace,
    SubdivisionVertex, SubdivisionEdge, SubdivisionFace,
    SubdivisionBoundaryVertex, SubdivisionBoundaryEdge,
    XStarVertex, XStarEdge, XStarFace, Edge, XQEdge, QZEdge,
    QDoubleCylinderVertex, QDoubleCylinderEdge, QSubdivisionVertex,
    QSubdivisionEdge, QStarVertex, QStarEdge]
  infer_instance

/-- The physical degree-one coordinates in the executable presentation. -/
abbrev ExecutableQ (S : OddScale) :=
  BDL26RZLocalReplacement.RZQ (executableLevelOne S) S

/-- The physical syndrome coordinates in the executable presentation. -/
abbrev ExecutableZ (S : OddScale) :=
  BDL26RZLocalReplacement.RZZ (executableLevelOne S) S

/-- Reified RZ coordinate instances use structural sums, products and decidable
subtypes; none is supplied by a choice of an equivalence with `Fin`. -/
instance executableQFintype (S : OddScale) : Fintype (ExecutableQ S) := by
  dsimp [ExecutableQ, BDL26RZLocalReplacement.RZQ, ZDoubleCylinderEdge,
    DoubleCylinderEdge, QDoubleCylinderVertex, transposePresentation,
    transposeTannerSquareData]
  infer_instance

instance executableZFintype (S : OddScale) : Fintype (ExecutableZ S) := by
  dsimp [ExecutableZ, BDL26RZLocalReplacement.RZZ, ZDoubleCylinderVertex,
    DoubleCylinderVertex, transposePresentation, transposeTannerSquareData]
  infer_instance

instance executableQDecidableEq (S : OddScale) : DecidableEq (ExecutableQ S) := by
  let P := executableLevelOne S
  letI : DecidableEq P.Z := P.data.zDecidableEq
  letI : DecidableEq P.Q := P.data.qDecidableEq
  letI : ∀ z : P.Z, DecidableEq (ZDoubleCylinderEdge P z S) :=
    fun z => doubleCylinderEdgeDecEq (transposeExecutable P) z S
  letI : ∀ q : P.Q, DecidableEq (QDoubleCylinderVertex (transposePresentation P) q S) :=
    fun q => qDoubleCylinderVertexDecEq (transposeExecutable P) q S
  change DecidableEq (((z : P.Z) × ZDoubleCylinderEdge P z S) ⊕
    ((q : P.Q) × QDoubleCylinderVertex (transposePresentation P) q S))
  infer_instance

instance executableZDecidableEq (S : OddScale) : DecidableEq (ExecutableZ S) := by
  let P := executableLevelOne S
  letI : DecidableEq P.Z := P.data.zDecidableEq
  letI : ∀ z : P.Z, DecidableEq (ZDoubleCylinderVertex P z S) :=
    fun z => zCylinderVertexDecEq P z S
  change DecidableEq ((z : P.Z) × ZDoubleCylinderVertex P z S)
  infer_instance

instance executableQEncodable (S : OddScale) : Encodable (ExecutableQ S) := by
  dsimp [ExecutableQ, BDL26RZLocalReplacement.RZQ, ZDoubleCylinderEdge,
    DoubleCylinderEdge, QDoubleCylinderVertex, transposePresentation,
    transposeTannerSquareData]
  infer_instance

/-- Admissibility is used only in erased membership certificates. -/
theorem executableLevelOne_admissible (S : OddScale) :
    Nonempty (TannerSquareAdmissible (executableLevelOne S)) := by
  rw [executableLevelOne_eq]
  exact ⟨(BDL26DecodingGraph.rxState S BDL26DecodingGraph.baseState).admissible.toTannerSquareAdmissible⟩

open scoped BigOperators

/-- Finite syndrome evaluation with an explicit, computational enumeration. -/
def syndromeFromBits {Q Z : Type} (F : Fintype Q) (incidence : Q → Z → Bool)
    (e : Word (ZMod 2) Q) : Word (ZMod 2) Z := fun z =>
  ∑ q ∈ F.elems, if incidence q z then e q else 0

/-- A finite sum is independent of the particular finite-enumeration witness. -/
theorem syndromeFromBits_fintype {Q Z : Type} (F G : Fintype Q)
    (incidence : Q → Z → Bool) (e : Word (ZMod 2) Q) :
    syndromeFromBits F incidence e = syndromeFromBits G incidence e := by
  have h : F = G := Subsingleton.elim _ _
  exact congrArg (fun H => syndromeFromBits H incidence e) h

/-- Generic incidence evaluation agrees with its Tanner linear map, without
expanding any RX/RZ presentation. -/
theorem syndromeFromBits_tanner (P : TannerSquarePresentation)
    (e : Word (ZMod 2) P.Q) :
    syndromeFromBits P.data.qFintype P.qz e = tannerCoboundary1 P e := by
  funext z
  change (∑ q, if P.qz q z then e q else 0) =
    ∑ q, e q * if P.qz q z = true then 1 else 0
  apply Finset.sum_congr rfl
  intro q _
  cases h : P.qz q z <;> simp [h]

/-- Generic computational syndrome before specialization, keeping transports
small enough to prove by equality elimination on presentation variables. -/
def rawSyndrome (P : TannerSquarePresentation)
    (hasA : Nonempty (TannerSquareAdmissible P)) (S : OddScale)
    (e : Word (ZMod 2) (BDL26RZLocalReplacement.RZQ P S)) :
    Word (ZMod 2) (BDL26RZLocalReplacement.RZZ P S) :=
  syndromeFromBits (rzQExecutableFintype P S) (rzIncidenceExecutable P hasA S) e

/-- Generic finite physical owner test. -/
def rawLocal (P : TannerSquarePresentation) (S : OddScale)
    (e : Word (ZMod 2) (BDL26RZLocalReplacement.RZQ P S)) : Bool :=
  decide (∃ center : Vertex P, ∀ q, e q ≠ 0 →
    BDL26ReplacementSupport.rzCorrectionOwner P S q = center)

/-- Direct finite syndrome evaluation from actual RZ incidence bits. -/
def executableSyndrome (S : OddScale) (e : Word (ZMod 2) (ExecutableQ S)) :
    Word (ZMod 2) (ExecutableZ S) :=
  rawSyndrome (executableLevelOne S) (executableLevelOne_admissible S) S e

/-- Executable actual-error support test: one physical owner fibre contains
all nonzero coordinates. No syndrome-support-only predicate is involved. -/
def executableLocal (S : OddScale) (e : Word (ZMod 2) (ExecutableQ S)) : Bool :=
  rawLocal (executableLevelOne S) S e

/-- Coordinate transport commutes with the generic finite syndrome evaluation. -/
theorem rawSyndrome_cast (P Q : TannerSquarePresentation) (h : P = Q)
    (hP : Nonempty (TannerSquareAdmissible P))
    (hQ : Nonempty (TannerSquareAdmissible Q)) (S : OddScale)
    (e : Word (ZMod 2) (BDL26RZLocalReplacement.RZQ Q S)) :
    rawSyndrome P hP S
      (fun q => e (cast (congrArg (fun R => BDL26RZLocalReplacement.RZQ R S) h) q)) =
    fun z => rawSyndrome Q hQ S e
      (cast (congrArg (fun R => BDL26RZLocalReplacement.RZZ R S) h) z) := by
  subst Q
  rfl

/-- Coordinate transport preserves precisely the physical owner-local test. -/
theorem rawLocal_cast (P Q : TannerSquarePresentation) (h : P = Q)
    (S : OddScale) (e : Word (ZMod 2) (BDL26RZLocalReplacement.RZQ Q S)) :
    rawLocal P S
      (fun q => e (cast (congrArg (fun R => BDL26RZLocalReplacement.RZQ R S) h) q)) =
      rawLocal Q S e := by
  subst Q
  rfl

/-- Generic computational incidence evaluation is the actual RZ coboundary. -/
theorem rawSyndrome_eq (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale)
    (e : Word (ZMod 2) (BDL26RZLocalReplacement.RZQ P S)) :
    rawSyndrome P ⟨A⟩ S e =
      tannerCoboundary1 (BDL26RZLocalReplacement.rzReplacementPresentation P A S) e := by
  have hi := congrArg
    (fun incidence => syndromeFromBits (rzQExecutableFintype P S) incidence e)
    (rzIncidenceExecutable_eq P A S)
  have hf := syndromeFromBits_fintype (rzQExecutableFintype P S)
    (BDL26RZLocalReplacement.rzReplacementPresentation P A S).data.qFintype
    (BDL26RZLocalReplacement.rzQZIncidence P A S) e
  exact hi.trans (hf.trans
    (syndromeFromBits_tanner (BDL26RZLocalReplacement.rzReplacementPresentation P A S) e))

/-- Executable finite lookup for the physical C2 representation. -/
def executableDecode (S : OddScale) (sigma : Word (ZMod 2) (ExecutableZ S)) :
    Word (ZMod 2) (ExecutableQ S) :=
  lookup (allWords (ExecutableQ S)) (executableSyndrome S)
    (executableLocal S) 0 sigma

/-- Executable lookup is a right inverse on its exactly represented image. -/
theorem executableDecode_syndrome (S : OddScale)
    (sigma : Word (ZMod 2) (ExecutableZ S))
    (h : ∃ e, executableSyndrome S e = sigma) :
    executableSyndrome S (executableDecode S sigma) = sigma := by
  obtain ⟨e, he⟩ := h
  exact lookup_syndrome _ _ _ _ _ ⟨e, mem_allWords _ e, he⟩

/-- Local attainability forces the local search branch to succeed. -/
theorem executableDecode_local (S : OddScale)
    (e : Word (ZMod 2) (ExecutableQ S)) (h : executableLocal S e = true) :
    executableLocal S (executableDecode S (executableSyndrome S e)) = true :=
  lookup_local _ _ _ _ _ ⟨e, mem_allWords _ e, h, rfl⟩

/-- Equality of physical error carriers, derived from the actual RX/RZ pair. -/
theorem executableQ_eq (S : OddScale) :
    ExecutableQ S = (levelTwoPresentation S).Q := by
  change BDL26RZLocalReplacement.RZQ (executableLevelOne S) S =
    BDL26RZLocalReplacement.RZQ (levelOnePresentation S) S
  rw [executableLevelOne_eq]

theorem executableZ_eq (S : OddScale) :
    ExecutableZ S = (levelTwoPresentation S).Z := by
  change BDL26RZLocalReplacement.RZZ (executableLevelOne S) S =
    BDL26RZLocalReplacement.RZZ (levelOnePresentation S) S
  rw [executableLevelOne_eq]

/-- Proof-erased coordinate transport, not a chosen finite equivalence. -/
def toExecutableError (S : OddScale)
    (e : Word (ZMod 2) (levelTwoPresentation S).Q) : Word (ZMod 2) (ExecutableQ S) :=
  fun q => e (cast (executableQ_eq S) q)

def toActualError (S : OddScale) (e : Word (ZMod 2) (ExecutableQ S)) :
    Word (ZMod 2) (levelTwoPresentation S).Q :=
  fun q => e (cast (executableQ_eq S).symm q)

def toExecutableSyndrome (S : OddScale)
    (sigma : Word (ZMod 2) (levelTwoPresentation S).Z) :
    Word (ZMod 2) (ExecutableZ S) :=
  fun z => sigma (cast (executableZ_eq S) z)

@[simp] theorem toActualError_toExecutableError (S : OddScale)
    (e : Word (ZMod 2) (levelTwoPresentation S).Q) :
    toActualError S (toExecutableError S e) = e := by
  funext q
  simp [toActualError, toExecutableError]

@[simp] theorem toExecutableError_toActualError (S : OddScale)
    (e : Word (ZMod 2) (ExecutableQ S)) :
    toExecutableError S (toActualError S e) = e := by
  funext q
  simp [toActualError, toExecutableError]

theorem toExecutableSyndrome_injective (S : OddScale) :
    Function.Injective (toExecutableSyndrome S) := by
  intro first second heq
  funext z
  have h := congrFun heq (cast (executableZ_eq S).symm z)
  simpa [toExecutableSyndrome] using h

/-- Actual finite incidence evaluation agrees with the original Tanner delta1. -/
theorem executableSyndrome_eq (S : OddScale)
    (e : Word (ZMod 2) (levelTwoPresentation S).Q) :
    executableSyndrome S (toExecutableError S e) =
      toExecutableSyndrome S (tannerCoboundary1 (levelTwoPresentation S) e) := by
  let actualError : Word (ZMod 2)
      (BDL26RZLocalReplacement.RZQ (levelOnePresentation S) S) := e
  have h := rawSyndrome_cast (executableLevelOne S) (levelOnePresentation S)
    (executableLevelOne_eq S) (executableLevelOne_admissible S)
    ⟨(BDL26DecodingGraph.rxState S BDL26DecodingGraph.baseState).admissible.toTannerSquareAdmissible⟩ S actualError
  have hr := rawSyndrome_eq (levelOnePresentation S)
    (BDL26DecodingGraph.rxState S BDL26DecodingGraph.baseState).admissible.toTannerSquareAdmissible S actualError
  exact h.trans (congrArg (fun f => toExecutableSyndrome S f) hr)

/-- Executable support test is exactly approved physical owner-fibre locality. -/
theorem executableLocal_iff (S : OddScale)
    (e : Word (ZMod 2) (levelTwoPresentation S).Q) :
    executableLocal S (toExecutableError S e) = true ↔ levelTwoLocalError S e := by
  let actualError : Word (ZMod 2)
      (BDL26RZLocalReplacement.RZQ (levelOnePresentation S) S) := e
  have h := rawLocal_cast (executableLevelOne S) (levelOnePresentation S)
    (executableLevelOne_eq S) S actualError
  have hr : rawLocal (levelOnePresentation S) S actualError = true ↔
      levelTwoLocalError S e := by
    rw [levelTwoLocalError_iff_owner]
    simp only [rawLocal, decide_eq_true_eq]
    rfl
  exact (congrArg (fun b => b = true) h).to_iff.trans hr

/-- The executable decoder on the original physical C2 coordinates. Coordinate
casts are proofs erased by code generation, and no correctness field is used. -/
def decode (S : OddScale) (sigma : Word (ZMod 2) (levelTwoPresentation S).Z) :
    Word (ZMod 2) (levelTwoPresentation S).Q :=
  toActualError S (executableDecode S (toExecutableSyndrome S sigma))

/-- Right inverse on the actual image of the physical syndrome map. -/
theorem decode_rightInverse (S : OddScale)
    (sigma : Word (ZMod 2) (levelTwoPresentation S).Z)
    (hsigma : sigma ∈ LinearMap.range (tannerCoboundary1 (levelTwoPresentation S))) :
    tannerCoboundary1 (levelTwoPresentation S) (decode S sigma) = sigma := by
  apply toExecutableSyndrome_injective S
  rw [← executableSyndrome_eq]
  unfold decode
  rw [toExecutableError_toActualError]
  apply executableDecode_syndrome
  obtain ⟨e, he⟩ := hsigma
  exact ⟨toExecutableError S e, by rw [executableSyndrome_eq, he]⟩

/-- Local actual errors receive local representatives with the same syndrome. -/
theorem decode_local (S : OddScale)
    (e : Word (ZMod 2) (levelTwoPresentation S).Q) (he : levelTwoLocalError S e) :
    levelTwoLocalError S (decode S (tannerCoboundary1 (levelTwoPresentation S) e)) := by
  apply (executableLocal_iff S _).1
  unfold decode
  rw [toExecutableError_toActualError, ← executableSyndrome_eq]
  exact executableDecode_local S _ ((executableLocal_iff S e).2 he)

/-- The exact v2 small-error theorem follows from actual topology-derived
separation of two independently local errors proved in #851. -/
theorem decode_corrects_local (S : OddScale)
    (e : Word (ZMod 2) (levelTwoPresentation S).Q) (he : levelTwoLocalError S e) :
    e + decode S (tannerCoboundary1 (levelTwoPresentation S) e) ∈
      (levelTwoChainComplex S).firstCoboundaryCheckCode.carrier := by
  apply levelTwoLocalError_sameSyndrome S e _ he (decode_local S e he)
  symm
  exact decode_rightInverse S _ ⟨e, rfl⟩

/-! ## Actual depth-two F17 family

Levels zero, one and two are the seed, RX(seed), and RZ(RX(seed)). Both
storage slots of BDL26DecoderData hold the actual map on the given edge;
selectedMap consequently chooses RX at edge zero and RZ at edge one. No
unused slot is used to assert a replacement with the wrong target carrier.
-/

open MultiscaleDecoder BDL26DecodingGraph BDL26ReplacementCochainMaps

/-- Actual incidence chain complex for each concrete presentation. -/
noncomputable def presentationComplex (P : TannerSquarePresentation) :
    ChainComplexData (ZMod 2) (Word (ZMod 2) P.X)
      (Word (ZMod 2) P.Q) (Word (ZMod 2) P.Z) where
  boundary1 := Matrix.toLin' (xqIncidenceMatrix P)
  boundary2 := Matrix.toLin' (qzIncidenceMatrix P)
  boundary_squared := by
    rw [← Matrix.toLin'_mul, xqIncidenceMatrix_mul_qzIncidenceMatrix]
    simp

abbrev FamilyX (S : OddScale) (i : LevelIndex 2) := (state S i.val).presentation.X
abbrev FamilyQ (S : OddScale) (i : LevelIndex 2) := (state S i.val).presentation.Q
abbrev FamilyZ (S : OddScale) (i : LevelIndex 2) := (state S i.val).presentation.Z

noncomputable def decoderFamily (S : OddScale) :
    BDL26CochainFamily 2 (FamilyX S) (FamilyQ S) (FamilyZ S) where
  complex := fun i => presentationComplex (state S i.val).presentation

theorem decoderFamily_coboundary0 (S : OddScale) (i : LevelIndex 2) :
    (decoderFamily S).coboundary0 i = tannerCoboundary0 (state S i.val).presentation := by
  apply LinearMap.ext
  intro e
  funext q
  exact wordLinearMapTranspose_toLin'_apply _ e q

theorem decoderFamily_coboundary1 (S : OddScale) (i : LevelIndex 2) :
    (decoderFamily S).coboundary1 i = tannerCoboundary1 (state S i.val).presentation := by
  apply LinearMap.ext
  intro e
  funext z
  exact wordLinearMapTranspose_toLin'_apply _ e z

/-- Each adjacent map is the actual previously proved RX or RZ cochain map. -/
noncomputable def decoderRZEdgeMap (S : OddScale) :
    BDL26CochainMap (decoderFamily S) (1 : StepIndex 2) := by
  let P := levelOnePresentation S
  let A := (rxState S baseState).admissible
  refine
    { map0 := (rzCochainMap P A S).map0
      map1 := (rzCochainMap P A S).map1
      map2 := (rzCochainMap P A S).map2
      commutes_coboundary0 := ?_
      commutes_coboundary1 := ?_ }
  · rw [decoderFamily_coboundary0, decoderFamily_coboundary0]
    exact rzMap_commutes_coboundary0 P A S
  · rw [decoderFamily_coboundary1, decoderFamily_coboundary1]
    exact rzMap_commutes_coboundary1 P A S


noncomputable def decoderEdgeMap (S : OddScale) (i : StepIndex 2) :
    BDL26CochainMap (decoderFamily S) i := by
  rcases i with ⟨n, hn⟩
  rcases n with _ | n
  · refine
      { map0 := (rxMap baseTannerSquarePresentation S).map0
        map1 := (rxMap baseTannerSquarePresentation S).map1
        map2 := (rxMap baseTannerSquarePresentation S).map2
        commutes_coboundary0 := ?_
        commutes_coboundary1 := ?_ }
    · rw [decoderFamily_coboundary0, decoderFamily_coboundary0]
      change (tannerCoboundary0 (rxReplacementPresentation baseTannerSquarePresentation S)).comp _ = _
      rw [rxPresentation_coboundary0_eq baseTannerSquarePresentation
        baseTannerSquareAdmissibleV4 baseTannerSquareCellularRegular S]
      exact rxMap_commutes_coboundary0 baseTannerSquarePresentation
        baseTannerSquareAdmissibleV4.toTannerSquareAdmissible S
    · rw [decoderFamily_coboundary1, decoderFamily_coboundary1]
      change (tannerCoboundary1 (rxReplacementPresentation baseTannerSquarePresentation S)).comp _ = _
      rw [rxPresentation_coboundary1_eq baseTannerSquarePresentation
        baseTannerSquareAdmissibleV4 baseTannerSquareCellularRegular S]
      exact rxMap_commutes_coboundary1 baseTannerSquarePresentation S
  · rcases n with _ | n
    · exact decoderRZEdgeMap S
    · omega

/-- Actual three-level data; all adjacent commutations are theorems above. -/
noncomputable def decoderData (S : OddScale) :
    BDL26DecoderData 2 (FamilyX S) (FamilyQ S) (FamilyZ S) where
  family := decoderFamily S
  rxMap := decoderEdgeMap S
  rzMap := decoderEdgeMap S

/-- The active first edge retains the genuine RX degree-one map. -/
theorem decoderData_selected_zero (S : OddScale) :
    ((decoderData S).selectedMap (0 : StepIndex 2)).map1 =
      (rxMap baseTannerSquarePresentation S).map1 := rfl

/-- The active second edge retains the genuine RZ degree-one map. -/
theorem decoderData_selected_one (S : OddScale) :
    ((decoderData S).selectedMap (1 : StepIndex 2)).map1 =
      (rzCochainMap (levelOnePresentation S) (rxState S baseState).admissible S).map1 := rfl

/-- The repaired adapter stores only the concrete executable decoder. -/
noncomputable def baseAdapter (S : OddScale) :
    F17LevelTwoBaseAdapterV2 (decoderData S) (decodingGraph S 2) (by decide) where
  decode := fun sigma => decode S sigma.1

/-- Its unconditional right-inverse obligation is proved on the actual image. -/
theorem baseAdapter_rightInverse (S : OddScale) :
    (baseAdapter S).IsRightInverse := by
  intro sigma
  change (decoderFamily S).coboundary1 (levelTwoIndex (by decide))
    (decode S sigma.1) = sigma.1
  rw [decoderFamily_coboundary1]
  apply decode_rightInverse
  have hsigma : sigma.1 ∈ LinearMap.range
      ((decoderFamily S).coboundary1 (levelTwoIndex (show 2 ≤ 2 from le_rfl))) := sigma.property
  rw [decoderFamily_coboundary1] at hsigma
  exact hsigma

/-- The repaired F17 actual-error-local property, independently proved for the
actual shifted level-two graph carriers and physical owner regions. -/
theorem baseAdapter_correctsLocalErrors (S : OddScale) :
    (baseAdapter S).CorrectsLocalErrors (levelTwoLocalComplex S) := by
  intro input hlocal
  have he : levelTwoLocalError S input.error := hlocal
  have h := decode_corrects_local S input.error he
  let e : Word (ZMod 2) (levelTwoPresentation S).Q := input.error
  change e + decode S ((decoderFamily S).coboundary1
      (levelTwoIndex (show 2 ≤ 2 from le_rfl)) e) ∈
        (levelTwoChainComplex S).firstCoboundaryCheckCode.carrier
  rw [decoderFamily_coboundary1]
  exact h

end QEC.Coding.BDL26LevelTwoDecoder
